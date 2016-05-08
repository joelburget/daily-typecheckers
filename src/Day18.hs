{-# LANGUAGE TupleSections #-}
module Day17 where

-- Improvements to Day12

import Control.Monad (when)
import Control.Monad.Gen
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Either
import qualified Data.Map as Map


data Type
  = Function Type Type
  | RecordT [(String, Type)]
  | VariantT [(String, Type)]
  deriving (Eq, Show)


data CheckTerm
  -- neither a constructor nor change of direction
  = Let InferTerm Type (InferTerm -> CheckTerm)

  | Gen Int Type

  -- switch direction (check -> infer)
  | Neutral InferTerm

  -- constructors
  -- \x -> CheckedTerm
  | Abs (CheckTerm -> CheckTerm)
  | Record [(String, CheckTerm)]
  | Variant String CheckTerm


data InferTerm
  -- switch direction (infer -> check)
  = Annot CheckTerm Type

  -- eliminators
  --
  -- note that eliminators always take an InferTerm as the inspected term,
  -- since that's the neutral position, then CheckTerms for the rest
  | App InferTerm CheckTerm
  | AccessField InferTerm String
  | Case InferTerm Type [(String, CheckTerm -> CheckTerm)]

-- xxx = error "not yet implemented"

-- eval :: InferTerm -> EvalCtx CheckTerm
-- eval t = case t of
--   Annot cTerm _ -> return cTerm
--   App f x -> do
--     f' <- eval f
--     case f' of
--       Neutral _ -> xxx
--       Abs f'' -> return $ f'' x
--   AccessField iTm name _ -> do
--     evaled <- eval iTm
--     case evaled of
--       Neutral _ -> return $ Neutral (AccessField xxx xxx xxx)
--       Record fields -> case Map.lookup name (Map.fromList fields) of
--         Just field -> return field
--         Nothing -> left "didn't find field in record"
--       _ -> left "unexpected"

--   Case iTm _ branches -> do
--     evaled <- eval iTm
--     case evaled of
--       Neutral _ -> xxx
--       Variant name cTm -> case Map.lookup name (Map.fromList branches) of
--         Just branch -> return $ branch evaled


type EvalCtx = EitherT String (Gen Int)
type CheckCtx = EitherT String (Gen Int)

runChecker :: CheckCtx () -> String
runChecker calc = case runGen (runEitherT calc) of
  Right () -> "success!"
  Left str -> str

unifyTy :: Type -> Type -> CheckCtx Type
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

check :: CheckTerm -> Type -> CheckCtx ()
check tm ty = case tm of
  -- t1: infered, t2: infer -> check
  Let t1 ty' body -> do
    t1Ty <- infer t1
    _ <- unifyTy t1Ty ty'
    let bodyVal = body t1
    check bodyVal ty

  Gen _ ty' -> do
    _ <- unifyTy ty ty'
    return ()

  Neutral iTm -> do
    iTy <- infer iTm
    _ <- unifyTy ty iTy
    return ()

  Abs t' -> do
    let Function domain codomain = ty
    v <- Gen <$> lift gen <*> pure domain
    let evaled = t' v
    check evaled codomain

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


infer :: InferTerm -> CheckCtx Type
infer t = case t of
  Annot _ ty -> pure ty

  App t1 t2 -> do
    Function domain codomain <- infer t1
    check t2 domain
    return codomain

  -- rec.name
  AccessField recTm name -> do
    inspectTy <- infer recTm
    case inspectTy of
      RecordT parts -> case Map.lookup name (Map.fromList parts) of
        Just subTy -> do
          return subTy
        Nothing -> left "didn't find the accessed key"
      _ -> left "found non-record unexpectedly"

  -- (case [varTm] of [cases]) : [ty]
  Case varTm ty cases -> do
    -- check that the inspected value is a variant,
    -- check all of its cases and the branches to see if all are aligned,
    -- finally that each typechecks
    varTmTy <- infer varTm
    case varTmTy of
      VariantT tyParts -> do
        let tyMap = Map.fromList tyParts
            caseMap = Map.fromList cases
            bothMatch = (Map.null (tyMap Map.\\ caseMap))
                     && (Map.null (caseMap Map.\\ tyMap))

        when (not bothMatch) (left "case misalignment")

        let mergedMap = Map.mergeWithKey
              (\name l r -> Just (name, l, r))
              (const (Map.fromList []))
              (const (Map.fromList []))
              tyMap
              caseMap

        mapM_
          (\(_name, branchTy, rhs) -> do
            v <- Gen <$> lift gen <*> pure branchTy
            check (rhs v) ty
          )
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
    let tm = Abs (\x -> x)
        ty = Function unitTy unitTy
    in check tm ty

  -- standard record
  print $ runChecker $
    let tm = Let
          (Annot xy xyTy)
          xyTy
          (\x -> Neutral
            (AccessField x "x")
          )
    in check tm unitTy

  -- record subtyping
  print $ runChecker $
    let xRecTy = RecordT [("x", unitTy)]
        tm = Let
          (Annot xy xRecTy)
          xRecTy
          (\x -> Neutral
            (AccessField x "x")
          )
    in check tm unitTy

  -- variant subtyping
  --
  -- left () : { left () | right () }
  print $ runChecker $
    let eitherTy = VariantT
          [ ("left", unitTy)
          , ("right", unitTy)
          ]
    in check (Variant "left" unit) eitherTy

  -- let x = left () : { left : () | right : () }
  -- in case x of
  --      left y -> y
  --      right y -> y
  print $ runChecker $
    let eitherTy = VariantT
          [ ("left", unitTy)
          , ("right", unitTy)
          ]
        tm = Let
          (Annot (Variant "left" unit) eitherTy)
          eitherTy
          (\x -> Neutral
            (Case x unitTy
              [ ("left", \y -> y)
              , ("right", \y -> y)
              ]
            )
          )
    in check tm unitTy
