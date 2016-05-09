module Day20 where
{-# LANGUAGE TupleSections #-}

-- Improvements to Day18

import Control.Monad.Gen
import Control.Monad.Trans.Either
import Control.Monad.Reader
import qualified Data.Map as Map


data Type
  = Function Type Type        -- a -> b
  | RecordT [(String, Type)]  -- a * b
  | VariantT [(String, Type)] -- a + b
  deriving (Eq, Show)


-- t2 = { x: 10, y: 20 } : { x : Int, y : Int }
-- t3 = { x: 10, y: 20, z: 30 } : { x : Int, y : Int, z : Int }

-- f : { x : Int } -> Int
-- f tuple = tuple.x

-- f t3


-- eitherIS = { left : Int | right : String }

-- x = left 5 : eitherIS

-- Note: In a bidirectional HOAS, functions always take a checked term to
-- checked term. Why? Because we want to take in and return canonical values
-- (which are possibly neutral), not computations.

-- Canonical values
data CheckTerm
  -- Neither a constructor nor change of direction.
  --
  -- The type is the return type.
  = Let String InferTerm Type (CheckTerm -> CheckTerm)

  -- switch direction (infer -> check)
  | Neutral InferTerm

  -- constructors
  -- \x -> CheckedTerm
  | Abs String (CheckTerm -> CheckTerm)
  | Record [(String, CheckTerm)]
  | Variant String CheckTerm

-- Computations
data InferTerm
  -- switch direction (check -> infer)
  = Annot CheckTerm Type
  | InferGen Int

  -- eliminators
  --
  -- note that eliminators always take an InferTerm as the inspected term,
  -- since that's the neutral position, then CheckTerms for the rest
  | App InferTerm CheckTerm
  | AccessField InferTerm String
  | Case InferTerm Type [(String, CheckTerm -> CheckTerm)]


data NCheckTerm
  = NLet String NInferTerm Type NCheckTerm
  | NNeutral NInferTerm
  | NAbs String NCheckTerm
  | NRecord [(String, NCheckTerm)]
  | NVariant String NCheckTerm
  deriving Show

data NInferTerm
  = NVar String
  | NAnnot NCheckTerm Type
  | NApp NInferTerm NCheckTerm
  | NAccessField NInferTerm String
  | NCase NInferTerm Type [(String, NCheckTerm)]
  deriving Show

iReify :: InferTerm -> ReaderT (Map.Map Int (NInferTerm, Type)) (Gen Int) NInferTerm
iReify t = case t of
  InferGen ident -> fst . (Map.! ident) <$> ask
  Annot cTm ty -> NAnnot <$> cReify cTm <*> pure ty
  App t1 t2 -> NApp <$> iReify t1 <*> cReify t2
  AccessField subTm name -> NAccessField <$> iReify subTm <*> pure name
  Case iTm ty branches -> do
    iTm' <- iReify iTm
    let iTmTy = undefined
    branches' <- (`Map.traverseWithKey` Map.fromList branches) $ \name f -> do
      ident <- gen
      -- XXX we can't easily infer iTmTy here
      local (Map.insert ident (NVar name, iTmTy)) $
        cReify (f (Neutral (InferGen ident)))
    return $ NCase iTm' ty (Map.toList branches')

cReify :: CheckTerm -> ReaderT (Map.Map Int (NInferTerm, Type)) (Gen Int) NCheckTerm
cReify t = case t of
  Let name iTm ty f -> do
    iTm' <- iReify iTm
    ident <- gen
    nom <- local (Map.insert ident (NVar name, ty)) $
      cReify (f (Neutral (InferGen ident)))
    return $ NLet name iTm' ty nom
  Neutral iTm -> NNeutral <$> iReify iTm
  Abs name f -> do
    ident <- gen
    let varTy = undefined
    nom <- local (Map.insert ident (NVar name, varTy)) $
      cReify (f (Neutral (InferGen ident)))
    return $ NAbs name nom
  Record fields -> do
    fields' <- Map.toList <$> traverse cReify (Map.fromList fields)
    return $ NRecord fields'
  Variant tag content -> NVariant tag <$> cReify content

reflect :: NCheckTerm -> CheckTerm
reflect t = runReader (cReflect t) Map.empty

cReflect :: NCheckTerm -> Reader (Map.Map String CheckTerm) CheckTerm
cReflect nTm = case nTm of
  NLet name iTm ty cTm -> do
    table <- ask
    iTm' <- iReflect iTm
    return $ Let name iTm' ty $ \arg ->
      runReader (cReflect cTm) (Map.insert name arg table)
  NNeutral iTm -> Neutral <$> iReflect iTm
  NAbs name cTm -> do
    table <- ask
    return $ Abs name $ \arg ->
      runReader (cReflect cTm) (Map.insert name arg table)

  NRecord fields -> do
    fields' <- Map.toList <$> traverse cReflect (Map.fromList fields)
    return $ Record fields'
  NVariant str cTm -> Variant str <$> cReflect cTm

iReflect :: NInferTerm -> Reader (Map.Map String CheckTerm) InferTerm
iReflect nTm = case nTm of
  NVar name -> do
    let ty = undefined
    cTm <- reader (Map.! name)
    return $ Annot cTm ty
  NAnnot cTm ty -> Annot <$> cReflect cTm <*> pure ty
  NApp iTm cTm -> App <$> iReflect iTm <*> cReflect cTm
  NAccessField iTm name -> AccessField <$> iReflect iTm <*> pure name
  NCase iTm ty cases -> do
    iTm' <- iReflect iTm
    table <- ask
    cases' <- (`Map.traverseWithKey` Map.fromList cases) $ \name cTm ->
      return $ \cTmArg ->
        runReader (cReflect cTm) (Map.insert name cTmArg table)
    return $ Case iTm' ty (Map.toList cases')

reify :: CheckTerm -> NCheckTerm
reify t = runGen (runReaderT (cReify t) Map.empty)

type EvalCtx = Either String
type CheckCtx = EitherT String (Gen Int)

eval :: InferTerm -> EvalCtx CheckTerm
eval t = case t of
  Annot cTerm _ -> return cTerm
  InferGen _ -> Left "invariant violation: found InferGen in evaluation"

  App f x -> do
    f' <- eval f
    case f' of
      Neutral f'' -> return $ Neutral (App f'' x)
      Abs _ f'' -> return $ f'' x
      _ -> Left "invariant violation: eval found non-Neutral / Abs in function position"

  AccessField iTm name -> do
    evaled <- eval iTm
    case evaled of
      Neutral nTm -> return $ Neutral (AccessField nTm name)
      Record fields -> case Map.lookup name (Map.fromList fields) of
        Just field -> return field
        Nothing -> Left "didn't find field in record"
      _ -> Left "unexpected"

  Case iTm ty branches -> do
    evaled <- eval iTm
    case evaled of
      Neutral nTm -> return $ Neutral (Case nTm ty branches)
      Variant name cTm -> case Map.lookup name (Map.fromList branches) of
        Just branch -> return $ branch cTm
        Nothing -> Left "invariant violation: evaluation didn't find matching variant in case"
      _ -> Left "invariant violation: evalutaion found non neutral - variant in case"

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
check eTm ty = case eTm of
  -- t1: infered, t2: infer -> check
  Let _name t1 ty' body -> do
    t1Ty <- infer t1
    _ <- unifyTy t1Ty ty'
    let bodyVal = body (Neutral t1)
    check bodyVal ty

  Neutral iTm -> do
    iTy <- infer iTm
    _ <- unifyTy ty iTy
    return ()

  Abs _ body -> do
    let Function domain codomain = ty
    v <- InferGen <$> lift gen
    let evaled = body (Neutral (Annot (Neutral v) domain))
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
        (\(name, subTy) -> case Map.lookup name fieldMap of
          Just subTm -> check subTm subTy
          Nothing -> left "failed to find required field in record"
        )
        fieldTys
      _ -> left "failed to check a record against a non-record type"

  -- Variant String CheckTerm
  --
  -- Here we define our notion of variant subtyping -- we check that the
  -- variant we've been given is in the row
  Variant name t' -> case ty of
    VariantT fieldTys -> case Map.lookup name (Map.fromList fieldTys) of
      Just expectedTy -> check t' expectedTy
      Nothing -> left "failed to find required field in record"
    _ -> left "failed to check a record against a non-record type"


infer :: InferTerm -> CheckCtx Type
infer t = case t of
  Annot _ ty -> pure ty

  InferGen _ -> left "invariant violation: infer found InferGen"

  App t1 t2 -> do
    Function domain codomain <- infer t1
    check t2 domain
    return codomain

  -- rec.name
  AccessField recTm name -> do
    inspectTy <- infer recTm
    case inspectTy of
      RecordT parts -> case Map.lookup name (Map.fromList parts) of
        Just subTy -> return subTy
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
            bothMatch = Map.null (tyMap Map.\\ caseMap)
                     && Map.null (caseMap Map.\\ tyMap)

        when (not bothMatch) (left "case misalignment")

        let mergedMap = Map.mergeWithKey
              (\name l r -> Just (name, l, r))
              (const (Map.fromList []))
              (const (Map.fromList []))
              tyMap
              caseMap

        mapM_
          (\(_name, branchTy, rhs) -> do
            v <- InferGen <$> lift gen
            check (rhs (Neutral (Annot (Neutral v) branchTy))) ty
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
    let tm = Abs "id" (\x -> x)
        ty = Function unitTy unitTy
    in check tm ty

  -- standard record
  print $ runChecker $
    let tm = Let
          "xy"
          (Annot xy xyTy)
          xyTy
          (\x -> Neutral
            (AccessField (Annot x xyTy) "x")
          )
    in check tm unitTy

  -- record subtyping
  print $ runChecker $
    let xRecTy = RecordT [("x", unitTy)]
        tm = Let
          "xy"
          (Annot xy xRecTy)
          xRecTy
          (\x -> Neutral
            (AccessField (Annot x xRecTy) "x")
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
  print $
    let eitherTy = VariantT
          [ ("left", unitTy)
          , ("right", unitTy)
          ]
        tm = Let
          "e"
          (Annot (Variant "left" unit) eitherTy)
          eitherTy
          (\x -> Neutral
            (Case (Annot x eitherTy) unitTy
              [ ("left", \y -> y)
              , ("right", \y -> y)
              ]
            )
          )
    in (runChecker (check tm unitTy), reify <$> eval (Annot tm unitTy))
