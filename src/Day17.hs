{-# LANGUAGE TupleSections #-}
module Day17 where

-- Improvements to Day12

import Control.Monad.Reader
import Control.Monad.Trans.Either
-- import Data.Set (Set)
-- import qualified Data.Set as Set
import qualified Data.Map as Map


data Type
  = Function Type Type
  | RecordT [(String, Type)]
  | VariantT [(String, Type)]
  deriving (Eq, Show)


data CheckTerm
  = Let InferTerm Type CheckTerm
  | Neutral InferTerm

  -- "constructors"
  | Abs CheckTerm
  | Record [(String, CheckTerm)]
  | Variant String CheckTerm
  deriving Show


data InferTerm
  = BVar Int
  | FVar String Type
  | Annot CheckTerm Type

  -- eliminators
  | App InferTerm CheckTerm
  | AccessField InferTerm String Type CheckTerm
  | Case InferTerm Type [(String, CheckTerm)]
  deriving Show


type Ctx = [Type]
type InCtx = EitherT String (Reader Ctx)

runChecker :: InCtx () -> Maybe String
runChecker calc = case runReader (runEitherT calc) [] of
  Right () -> Nothing
  Left str -> Just str

unifyTy :: Type -> Type -> InCtx Type
unifyTy (Function dom1 codom1) (Function dom2 codom2) =
  Function <$> unifyTy dom1 dom2 <*> unifyTy codom1 codom2
unifyTy (RecordT lTy) (RecordT rTy) = do
  -- RecordT [(String, Type)]
  -- Take the intersection of possible records. Make sure the overlap matches!

  let isect = Map.intersectionWith (,) (Map.fromList lTy) (Map.fromList rTy)
  isect' <- mapM (uncurry unifyTy) isect

  return $ RecordT (Map.toList isect')
unifyTy (VariantT lTy) (VariantT rTy) = do
  -- Take the union of possible variants. Make sure overlap matches!

  let isect = Map.intersectionWith (,) (Map.fromList lTy) (Map.fromList rTy)
  isect' <- mapM (uncurry unifyTy) isect

  let union = Map.union (Map.fromList lTy) (Map.fromList rTy)

  -- Overwrite with extra data we may have learned from unifying the types in
  -- the intersection
  let result = Map.union isect' union

  return $ VariantT (Map.toList result)
unifyTy l r = left ("failed unification " ++ show (l, r))

check :: CheckTerm -> Type -> InCtx ()
check tm ty = case tm of
  -- t1: infered, t2: checked
  Let t1 ty' t2 -> do
    t1Ty <- infer t1
    _ <- unifyTy t1Ty ty'
    local (ty':) (check t2 ty)

  Abs t' -> do
    let Function domain codomain = ty
    local (domain:) $ check t' codomain

  Record fields -> do
    -- Record [(String, CheckTerm)]
    --
    -- Here we define our notion of record subtyping -- we check that the
    -- record we've been given has at least the fields expected of it and of
    -- the right type.
    let fieldMap = Map.fromList fields
    case ty of
      RecordT fieldTys -> mapM_
        (\(name, subTy) -> do
          case Map.lookup name fieldMap of
            Just subTm -> check subTm subTy
            Nothing -> left "failed to find required field in record"
        )
        fieldTys
      _ -> left "failed to check a record against a non-record type"

  Variant name t' -> do
    -- Variant String CheckTerm
    --
    -- Here we define our notion of variant subtyping -- we check that the
    -- variant we've been given is in the row
    case ty of
      VariantT fieldTys -> case Map.lookup name (Map.fromList fieldTys) of
        Just expectedTy -> check t' expectedTy
        Nothing -> left "failed to find required field in record"
      _ -> left "failed to check a record against a non-record type"

  Neutral tm' -> do
    ty' <- infer tm'
    _ <- unifyTy ty ty'
    return ()


infer :: InferTerm -> InCtx Type
infer t = case t of
  BVar i -> (!! i) <$> ask
  FVar _ ty -> pure ty
  Annot _ ty -> pure ty

  App t1 t2 -> do
    Function domain codomain <- infer t1
    check t2 domain
    return codomain

  -- k (rec.name : ty)
  AccessField recTm name ty' kTm -> do
    inspectTy <- infer recTm
    case inspectTy of
      RecordT parts -> case Map.lookup name (Map.fromList parts) of
        Just subTy -> do
          local (subTy:) (check kTm ty')
          return ty'
        Nothing -> left "didn't find the accessed key"
      _ -> left "found non-record unexpectedly"

  Case varTm ty cases -> do
    varTmTy <- infer varTm
    case varTmTy of
      VariantT tyParts -> do
        let tyMap = Map.fromList tyParts
            caseMap = Map.fromList cases
            bothMatch = (Map.null (tyMap Map.\\ caseMap))
                     && (Map.null (caseMap Map.\\ tyMap))

        when (not bothMatch) (left "case misalignment")

        let mergedMap = Map.mergeWithKey
              (\k a b -> Just (k, a, b))
              (const (Map.fromList []))
              (const (Map.fromList []))
              tyMap
              caseMap

        mapM_
          (\(_name, branchTy, rhs) -> local (branchTy:) (check rhs ty))
          mergedMap
      _ -> left "found non-variant in case"
    return ty


main :: IO ()
main = do
  let unit = Record []
      unitTy = RecordT []
      xy = Record
        [ ("x", unit)
        , ("y", unit)
        ]
      xyTy = RecordT
        [ ("x", unitTy)
        , ("y", unitTy)
        ]

  -- boring
  print $ runChecker $
    let tm = Abs (Neutral (BVar 0))
        ty = Function unitTy unitTy
    in check tm ty

  -- standard record
  print $ runChecker $
    let tm = Let
          (Annot xy xyTy)
          xyTy
          (Neutral
            (AccessField (BVar 0) "x" unitTy (Neutral (BVar 0)))
          )
    in check tm unitTy

  -- record subtyping
  print $ runChecker $
    let xRecTy = RecordT [("x", unitTy)]
        tm = Let
          (Annot xy xRecTy)
          xRecTy
          (Neutral
            (AccessField (BVar 0) "x" unitTy (Neutral (BVar 0)))
          )
    in check tm unitTy

  -- variant subtyping
  print $ runChecker $
    let eitherTy = VariantT
          [ ("left", unitTy)
          , ("right", unitTy)
          ]
        tm = Let
          (Annot (Variant "left" unit) eitherTy)
          eitherTy
          (Neutral
            (Case (BVar 0) unitTy
              [ ("left", (Neutral (BVar 0)))
              , ("right", (Neutral (BVar 0)))
              ]
            )
          )
    in check tm unitTy
