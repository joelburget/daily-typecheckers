module Day11 where

-- first hack at records / variants
-- * fields can't refer to each other

import Control.Monad.Reader
-- import Data.Set (Set)
-- import qualified Data.Set as Set
-- import qualified Data.Map as Map


data Type
  = Function Type Type
  | RecordT [(String, Type)]
  | VariantT [(String, Type)]


data Term
  = BVar Int
  | FVar String
  | Let Term Term

  -- * fun intro / elim
  | Abs Term
  | App Term Term

  -- * new stuff
  -- * record intro / elim
  | Record [(String, Term)]
  | AccessField Term String Term

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
  FVar _ -> t
  Let t1 t2 -> Let (open' k u t1) (open' (k + 1) u t2)

  Abs t' -> Abs (open' (k + 1) u t')
  App t1 t2 -> App (open' k u t1) (open' k u t2)

  Record fields -> Record (map (\(name, tm) -> (name, open' k u tm)) fields)
  AccessField recTm name kTm -> AccessField (open' k u recTm) name (open' (k + 1) u kTm)

  Variant name t' -> Variant name (open' k u t')
  Case varTm cases -> Case (open' k u varTm) (map (\(name, tm) -> (name, open' k u tm)) cases)

close :: Term -> String -> Term
close = close' 0

close' :: Int -> Term -> String -> Term
close' k t x = case t of
  BVar _ -> t
  FVar y
    | x == y -> BVar k
    | otherwise -> t
  Let t1 t2 -> Let (close' k t1 x) (close' (k + 1) t2 x)

  Abs t' -> Abs (close' (k + 1) t' x)
  App t1 t2 -> App (close' k t1 x) (close' k t2 x)

  Record fields -> Record (map (\(name, tm) -> (name, close' k tm x)) fields)
  AccessField recTm name kTm -> AccessField (close' k recTm x) name (close' (k + 1) kTm x)

  Variant name t' -> Variant name (close' k t' x)
  Case varTm cases -> Case (close' k varTm x) (map (\(name, tm) -> (name, close' k tm x)) cases)

type Ctx = [Type]
type InCtx = Reader Ctx

infer :: Term -> InCtx Type
infer t = case t of
  BVar i -> (!! i) <$> ask
  FVar y -> error "unexpectedly found a free var in typechecking"
  Let t1 t2 = do
    t1Ty <- infer t1
    withReader (t1Ty:) (infer t2)

  -- bleh how to type the variable
  Abs t' ->
