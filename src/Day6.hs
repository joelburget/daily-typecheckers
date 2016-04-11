{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE OverloadedStrings #-}
-- Day 5 + pretty printing
module Day6 where

import qualified Data.Map as M
import Data.Monoid
import Data.String
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Either

import Text.PrettyPrint.ANSI.Leijen ()
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data Name
  = Free String
  -- de bruijn index
  | Bound Int
  deriving (Show, Eq, Ord)

-- Note: this is really a (multi-) binding form
type RecordDesc = [
  ( String -- name
  , Desc -- what it points to
  )
  ]

type Env = (M.Map Int Data, M.Map Int Desc)
type EnvM = Reader Env

type Printing = EitherT PP.Doc EnvM

-- wow it looks the same as RecordDesc :P
type VariantDesc = [(String, Desc)]

data FunDesc = Arrow Desc Desc
  deriving (Show, Eq)

prettyArrow :: FunDesc -> Printing PP.Doc
prettyArrow (Arrow domain codomain) = do
  pDomain <- prettyDesc domain
  pCodomain <- prettyDesc codomain
  return $ pDomain <> PP.text " -> " <> pCodomain

encloseRecord :: [PP.Doc] -> PP.Doc
encloseRecord = PP.encloseSep "{" "}" ","

encloseVariant :: [PP.Doc] -> PP.Doc
encloseVariant = PP.encloseSep "{" "}" "|"

prettyRecordDesc :: RecordDesc -> Printing PP.Doc
prettyRecordDesc rs = do
  rs' <- forM rs $ \(name, desc) ->
    ((PP.magenta (PP.text name) <> ": ") <>) <$> prettyDesc desc
  return $ encloseRecord rs'

prettyVariantDesc :: VariantDesc -> Printing PP.Doc
prettyVariantDesc rs = do
  rs' <- forM rs $ \(name, desc) ->
    ((PP.red (PP.text name) <> ": ") <>) <$> prettyDesc desc
  return $ encloseVariant rs'

runPrinter :: Printing PP.Doc -> Env -> IO ()
runPrinter printer env = do
  either PP.putDoc PP.putDoc $ runReader (runEitherT printer) env
  putStrLn ""

emptyEnv :: Env
emptyEnv = (M.empty, M.empty)

data Desc
  = DescRecord RecordDesc
  | DescVariant VariantDesc
  | DescFun FunDesc
  | DescName Name
  deriving (Show, Eq)

prettyDesc :: Desc -> Printing PP.Doc
prettyDesc (DescRecord record) = prettyRecordDesc record
prettyDesc (DescVariant var) = prettyVariantDesc var
prettyDesc (DescFun fun) = prettyArrow fun
prettyDesc (DescName name) = case name of
  Free name' -> return $ PP.cyan (PP.text name')
  _ -> left "encountered an unexpected bound variable when pretty-printing"

listDesc :: Desc
listDesc = DescVariant
  [ ("listNil", DescRecord [])
  , ("listCons", DescRecord
      [ ("listHead", DescName (Free "a")) -- XXX bind
      , ("listTail", DescName (Free "mu"))
      ]
    )
  ]

-- that gives us sums, products, and exponentials
--
-- now, to instantiate, typecheck, and eliminate (pattern match / execute) them

-- Match against the alternatives in a sum
type VariantMatch = [(String, Match, Data)]

-- Match a product (whoa, we just pairwise match)
type RecordPattern = [Match]

data Match
  = MatchVariant VariantMatch
  | MatchRecord RecordPattern
  | MatchWildcard
  | MatchVariable

--

type Record = [(String, Data)]
type Variant = (String, Data)

-- we need pattern match the argument and emit Data
data Fun = Fun Match Data

data Data
  = DataRecord Record
  | DataVariant Variant
  | DataFun Fun
  | DataName Name

-- [Int]
-- [1,2] <-> (Cons 1 (Cons 2 Nil))

listData :: Data
listData = DataVariant
  ( "listCons"
  , DataRecord
    [ ("listHead", DataName (Free "x"))
    , ("listTail", DataVariant
        ( "listCons", DataRecord
          [ ("listHead", DataName (Free "y"))
          , ("listTail", DataVariant ("listNil", DataRecord []))
          ]
        )
      )
    ]
  )

data tm :<: ty = tm :<: ty  deriving (Show, Eq)
infix 4 :<:

listCheck :: Either String Bool
listCheck =
  let x = Free "x"
      y = Free "y"
      head = Bound 0
      tail = Bound 1
      env = ( M.fromList [(0, DataName x), (1, DataName y)]
            , M.fromList [(0, DescName head), (1, DescName tail)]
            )
  in flip runReader env $
     runEitherT $
     check (listData :<: listDesc)

--

type Check = EitherT String EnvM

hoistMaybe :: Monad m => s -> Maybe a -> EitherT s m a
hoistMaybe msg = maybe (left msg) right

resolveTmName :: IsString s => Int -> EitherT s EnvM Data
resolveTmName ix = do
  (boundData, _) <- ask
  hoistMaybe "failed type name resolution" $ M.lookup ix boundData

resolveTyName :: IsString s => Int -> EitherT s EnvM Desc
resolveTyName ix = do
  (_, boundDesc) <- ask
  hoistMaybe "failed type name resolution" $ M.lookup ix boundDesc

--

check :: Data :<: Desc -> Check Bool

-- check that r has a superset of the keys in rd, and each checks
check (DataRecord r :<: DescRecord rd) =
  let tmMap = M.fromList r
      tyMap = M.fromList rd

      -- tm must have a superset of keys in ty, so ty can't have keys tm doesn't
      -- have
      supersetCondition = M.null (M.difference tyMap tmMap)

      -- typecheck pairwise
      tmTyMap = M.intersectionWith (:<:) tmMap tyMap
      pairwiseCondition = foldM
        (\accum typing -> (accum &&) <$> check typing)
        True
        tmTyMap
  in (supersetCondition &&) <$> pairwiseCondition

-- just check that this variant is in the row and it checks
check (DataVariant (varName, varBody) :<: DescVariant vd) =
  let tyMap = M.fromList vd
  in case M.lookup varName tyMap of
       Just ty -> check (varBody :<: ty)
       Nothing -> return False

-- check that
-- * the match checks the right type?
-- * the result is in the codomain
check (DataFun (Fun match result) :<: DescFun (Arrow dom codom)) =
  -- XXX
  check (result :<: codom)

-- just resolve the name and move on
check (DataName name :<: ty) = case name of
  -- XXX I think this is totally wrong
  -- * Names should be free at this point
  Free name' -> left "we don't support unquantified names in data"
  Bound ix -> do
    tm <- resolveTmName ix
    check (tm :<: ty)
check (tm :<: DescName name) = case name of
  Free name' -> left "we don't support unquantified names in descriptions"
  Bound ix -> do
    ty <- resolveTyName ix
    check (tm :<: ty)

check _ = return False

-- TODO eliminators are significantly more work
