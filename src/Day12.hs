{-# LANGUAGE TupleSections #-}
module Day12 where

-- As many improvements as I can squeeze in to Day 11 before this show...

import Control.Monad.Reader
import Control.Monad.Trans.Either
-- import Data.Set (Set)
-- import qualified Data.Set as Set
-- import qualified Data.Map as Map


data Type
  = Function Type Type
  | RecordT [(String, Type)]
  | VariantT [(String, Type)]
  deriving Eq


-- bidirectionality: binders always carry a type
data Term
  = BVar Int
  | FVar String Type
  | Let Term Type Term

  -- * fun intro / elim
  | Abs Term Type
  | App Term Term

  -- * new stuff
  -- * record intro / elim
  | Record [(String, Term)]
  | AccessField Term String Type Term

  -- * variant intro / elim
  | Variant String Term
  | Case Term [(String, Term)]

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

-- idea: set up a propagator network for the entire term, they should be able
-- to solve it efficiently. With provenance!
infer :: Term -> InCtx Type
infer t = case t of
  BVar i -> (!! i) <$> ask
  FVar y ty -> pure ty
  Let t1 ty t2 -> do
    check t1 ty
    withReader (ty:) (infer t2)

  -- XXX - bleh how to type the variable
  Abs t' ty -> do
    check t' ty
    pure ty
  App t1 t2 -> do
    t1Ty <- infer t1
    t2Ty <- infer t2

    Function domain codomain <- t1Ty
    when (domain != t2Ty) (left "app failed to type")
    return t2Ty

  Record fields -> do
    fieldTys <- mapM (\(name, tm) -> (name,) <$> infer tm) fields
    return (Record fieldTys)
  -- kTm (recTm.name : ty)
  AccessField recTm name ty kTm -> do
    case recTm of
      Record parts -> case Map.lookup name (Map.fromList parts) of
        Just subTm -> do
          check subTm ty
          withReader (ty:) (infer kTm)
        Nothing -> left "didn't find the accessed key"
      _ -> left "found non-record unexpectedly"

  -- XXX bleh need subtyping here since we can only determine specific variant
  -- this inhabits
  Variant name t' -> do
    t'Ty <- infer t'
    return (VariantT [(name, t'Ty)])
  Case varTm cases -> do
    varTmTy <- infer varTm
    caseTys <- withReader (varTmTy:) $
      mapM (\(_, tm) -> infer tm) cases
    -- XXX assert they all unify
