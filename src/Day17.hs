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


-- bidirectionality: binders always carry a type
data Term
  = BVar Int                            -- infer
  | FVar String Type                    -- infer
  | Let Term Type Term                  -- check

  -- * fun intro / elim
  | Abs Term Type                       -- check
  | App Term Term                       -- infer

  -- * new stuff
  -- * record intro / elim
  | Record [(String, Term)]             -- check
  | AccessField Term String Type Term   -- infer

  -- * variant intro / elim
  | Variant String Term                 -- check
  | Case Term [(String, Term)]          -- infer
  deriving Show

-- t ^ u
--
-- Replace `BVar i j` with the j-th value from u, when the de Bruijn indices
-- match.
open :: Term -> Term -> Term
open = open' 0

-- { k -> u } t
open' :: Int -> Term -> Term -> Term
open' k u t = case t of
  BVar i
    | i == k -> u
    | otherwise -> t
  FVar _ _ -> t
  Let t1 ty t2 -> Let (open' k u t1) ty (open' (k + 1) u t2)

  Abs t' ty -> Abs (open' (k + 1) u t') ty
  App t1 t2 -> App (open' k u t1) (open' k u t2)

  Record fields -> Record (map (\(name, tm) -> (name, open' k u tm)) fields)
  AccessField recTm name ty kTm ->
    AccessField (open' k u recTm) name ty (open' (k + 1) u kTm)

  Variant name t' -> Variant name (open' k u t')
  Case varTm cases -> Case (open' k u varTm) (map (\(name, tm) -> (name, open' k u tm)) cases)

close :: Term -> String -> Term
close = close' 0

close' :: Int -> Term -> String -> Term
close' k t x = case t of
  BVar _ -> t
  FVar y _
    | x == y -> BVar k
    | otherwise -> t
  Let t1 ty t2 -> Let (close' k t1 x) ty (close' (k + 1) t2 x)

  Abs t' ty -> Abs (close' (k + 1) t' x) ty
  App t1 t2 -> App (close' k t1 x) (close' k t2 x)

  Record fields -> Record (map (\(name, tm) -> (name, close' k tm x)) fields)
  AccessField recTm name ty kTm ->
    AccessField (close' k recTm x) name ty (close' (k + 1) kTm x)

  Variant name t' -> Variant name (close' k t' x)
  Case varTm cases -> Case (close' k varTm x) (map (\(name, tm) -> (name, close' k tm x)) cases)

type Ctx = [Type]
type InCtx = EitherT String (Reader Ctx)

runChecker :: InCtx () -> Maybe String
runChecker calc = case runReader (runEitherT calc) [] of
  Right () -> Nothing
  Left str -> Just str

unifyTy :: Type -> Type -> InCtx Type
unifyTy (Function dom1 codom1) (Function dom2 codom2) =
  Function <$> unifyTy dom1 dom2 <*> unifyTy codom1 codom2
unifyTy (RecordT left) (RecordT right) = do
  -- take the intersection of possible records
  -- TODO
  return $ RecordT left
unifyTy (VariantT left) (VariantT right) =
  -- take the union of possible variants
  -- overlap?
  --
  -- TODO
  -- VariantT $ Map.union (Map.
  return $ VariantT left
unifyTy _ _ = left "failed unification"

check :: Term -> Type -> InCtx ()
check tm ty = case tm of
  Let t1 ty' t2 -> do
    check t1 ty'
    t2Ty <- local (ty':) (infer t2)
    _ <- unifyTy t2Ty ty
    return ()

  -- XXX - bleh how to type the variable
  Abs t' ty -> do
    check t' ty
    return ()

  AccessField recTm name ty' kTm -> do
    case recTm of
      Record parts -> case Map.lookup name (Map.fromList parts) of
        Just subTm -> do
          check subTm ty'
          rhsTy <- local (ty':) (infer kTm)
          _ <- unifyTy rhsTy ty
          return ()
        Nothing -> left "didn't find the accessed key"
      _ -> left "found non-record unexpectedly"

  Case varTm cases -> do
    varTmTy <- infer varTm
    caseTy:caseTys <- local (varTmTy:) $
      mapM (\(_, rhsTm) -> infer rhsTm) cases
    rhsTy <- foldM unifyTy caseTy caseTys
    _ <- unifyTy rhsTy ty
    return ()

  _ -> left $ "unexpected checked term: " ++ show tm

infer :: Term -> InCtx Type
infer t = case t of
  BVar i -> (!! i) <$> ask
  FVar _ ty -> pure ty

  App t1 t2 -> do
    -- t1Ty <- infer t1
    Function domain codomain <- infer t1
    t2Ty <- infer t2

    when (domain /= t2Ty) (left "app failed to type")
    return codomain

  Record fields -> do
    fieldTys <- mapM (\(name, tm) -> (name,) <$> infer tm) fields
    return (RecordT fieldTys)
  -- kTm (recTm.name : ty)

  -- XXX bleh need subtyping here since we can only determine specific variant
  -- this inhabits
  Variant name t' -> do
    t'Ty <- infer t'
    return (VariantT [(name, t'Ty)])

  _ -> left "unexpected infered term"

main :: IO ()
main = do
  print $ runChecker $
    let tm = Abs (BVar 0) ty
        ty = Function (RecordT []) (RecordT [])
    in check tm ty
