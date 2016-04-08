{-# LANGUAGE TypeOperators #-}
-- Day 4 + pattern matching, typechecking, elimination
module Day5 where

import qualified Data.Map as M
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Trans.Either

data Name
  = Free String
  -- de bruijn index
  | Bound Int
  deriving (Show, Eq, Ord)

type RecordDesc = [
  ( String -- name
  , Desc -- what it points to
  )
  ]

-- wow it looks the same as RecordDesc :P
type VariantDesc = [(String, Desc)]

data FunDesc = Arrow Desc Desc
  deriving (Show, Eq)

data Desc
  = DescRecord RecordDesc
  | DescVariant VariantDesc
  | DescFun FunDesc
  | DescName Name
  deriving (Show, Eq)

listDesc :: Desc
listDesc = DescVariant
  [ ("listNil", DescRecord [])
  , ("listCons", DescRecord
      [ ("listHead", DescName (Bound 0))
      , ("listTail", DescName (Bound 1))
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

listCheck =
  let x = Free "x"
      y = Free "y"
      head = Bound 0
      tail = Bound 1
      env = ( M.fromList [(x, DataName x), (y, DataName y)]
            , M.fromList [(head, DescName head), (tail, DescName tail)]
            )
  in flip runReader env $
     runEitherT $
     check (listData :<: listDesc)

--

type Env = EitherT String (Reader (M.Map Name Data, M.Map Name Desc))

hoistMaybe :: Monad m => String -> Maybe a -> EitherT String m a
hoistMaybe msg = maybe (left msg) right

resolveTmName :: Name -> Env Data
resolveTmName name = do
  (boundData, _) <- ask
  hoistMaybe "failed type name resolution" $ M.lookup name boundData

resolveTyName :: Name -> Env Desc
resolveTyName name = do
  (_, boundDesc) <- ask
  hoistMaybe "failed type name resolution" $ M.lookup name boundDesc

--

check :: Data :<: Desc -> Env Bool

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
check (DataName name :<: ty) = do
  tm <- resolveTmName name
  check (tm :<: ty)
check (tm :<: DescName name) = do
  ty <- resolveTyName name
  check (tm :<: ty)

check _ = return False

-- TODO eliminators are significantly more work
