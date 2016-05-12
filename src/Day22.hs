{-# LANGUAGE FlexibleContexts #-}
module Day22 where

import Control.Monad.Error.Class
import Control.Monad.Gen
import Control.Monad.Reader
import Control.Monad.Trans.Either
import Data.Functor.Identity
import qualified Data.Map as Map

-- * reify / reflect (i, c)
-- * infer, check
-- * eval (i, c)

data Type
  = Function Type Type        -- a -> b
  | RecordT [(String, Type)]  -- a * b
  | VariantT [(String, Type)] -- a + b
  deriving (Eq, Show)

unifyTy :: MonadError String m => Type -> Type -> m Type
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
unifyTy l r = throwError ("failed unification " ++ show (l, r))


data Hoas
  = HAnnot Hoas Type
  | HUnique Int

  -- is anything above here necessary?
  -- XXX isn't it the case that all variables here need to be free? ie no int?
  | HVar String Int
  | HNeutral Hoas
  | HLet String Hoas Type (Hoas -> Hoas)
  | HAbs String (Hoas -> Hoas)
  | HApp Hoas Hoas


-- Canonical values
data CheckNom
  = NLet String InferNom Type CheckNom
  | NNeutral InferNom
  | NAbs String CheckNom
  deriving Show

-- Computations
data InferNom
  -- question: do we want this string here? how easy is it to reconstruct the
  -- name? maybe we need a transformer for this in the reification monad
  = NVar String Int
  | NAnnot CheckNom Type
  | NApp InferNom CheckNom
  deriving Show

type ReflectM = Reader [Hoas]

type CheckInferM = EitherT String (Reader [Type])
type ReifyM = GenT Int (EitherT String Identity)

reifyI :: Hoas -> ReifyM InferNom
reifyI t = case t of
  HApp iTm cTm -> NApp <$> reifyI iTm <*> reifyC cTm
  HAnnot cTm ty -> NAnnot <$> reifyC cTm <*> pure ty
  HVar name i -> pure $ NVar name i
  _ -> throwError "[reifyI] unexpectedly called with a checked term"

reifyC :: Hoas -> ReifyM CheckNom
reifyC t = case t of
  HNeutral h -> NNeutral <$> reifyI h
  HLet name iTm ty cTm -> do
    unique <- gen
    iTm' <- reifyI iTm
    cTm' <- reifyC (cTm (HUnique unique))
    return $ NLet name iTm' ty cTm'
  HAbs name f -> do
    unique <- gen
    body <- reifyC (f (HUnique unique))
    return $ NAbs name body
  _ -> throwError "[reifyI] unexpectedly called with an infered term"


runReflectM :: InferNom -> Hoas
runReflectM iTm = runReader (reflectI iTm) []

reflectI :: InferNom -> ReflectM Hoas
reflectI t = case t of
  NVar name i -> do
    ls <- ask
    if length ls > i
      then return (ls !! i)
      else pure $ HVar name i -- XXX free var!
  NAnnot cTm ty -> HAnnot <$> reflectC cTm <*> pure ty
  NApp iTm cTm -> HApp <$> reflectI iTm <*> reflectC cTm

-- traverse the nominal syntax tree, collecting open continuations.
--
-- what is the continuation in this case? something that takes
reflectC :: CheckNom -> ReflectM Hoas
reflectC t = case t of
  NLet name iTm ty cTm -> do
    iTm' <- reflectI iTm
    f <- reflectCapture (reflectC cTm)
    return $ HLet name iTm' ty f
  NNeutral iTm -> HNeutral <$> reflectI iTm
  NAbs name cTm -> do
    f <- reflectCapture (reflectC cTm)
    return $ HAbs name f

reflectCapture :: ReflectM Hoas -> ReflectM (Hoas -> Hoas)
reflectCapture refl = do
  table <- ask
  return $ \x -> runReader refl (x:table)


check :: CheckNom -> Type -> CheckInferM ()
check tm ty = case tm of
  NLet _name iTm retTy cTm -> do
    iTmTy <- infer iTm
    local (iTmTy:) (check cTm retTy)
  NNeutral iTm -> do
    iTmTy <- infer iTm
    _ <- unifyTy iTmTy ty
    return ()
  NAbs _name cTm ->
    case ty of
      Function dom codom ->
        local (dom:) (check cTm codom)
      _ -> throwError "[check] found function where non-function was expected"

infer :: InferNom -> CheckInferM Type
infer t = case t of
  NVar _name i -> reader (!! i)
  NAnnot _tm ty -> pure ty
  NApp iNom cNom -> do
    fTy <- infer iNom
    case fTy of
      Function dom codom -> do
        local (dom:) (check cNom fTy)
        return codom
      _ -> throwError "[infer] unexpectedly found non-function in application inference"


eval :: Hoas -> Either String Hoas
eval t = case t of
  HVar _ _ -> pure t
  HAnnot cTm _ty -> eval cTm
  HUnique _ -> Left "[eval] unexpectedly found unique"
  HApp iTm cTm -> do
    iTm' <- eval iTm
    case iTm' of
      HAbs _ f -> return (f cTm)
      _ -> Left "[eval] unexpectedly found non-abs in application"
  HLet _name iTm _ty f -> do
    iTm' <- eval iTm
    return (f iTm')
  HNeutral iTm -> eval iTm
  HAbs _name _f -> return t
