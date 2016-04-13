module Day10 where

-- "Advanced binding structures" from Chargueraud

import Data.Set (Set)
import qualified Data.Set as Set


data Term
  = BVar Int Int
  | FVar String
  | Abs Term
  | App Term Term
  | Let [Term] Term

-- t ^ [u]
--
-- Replace `BVar i j` with the j-th value from u, when the de Bruijn indices
-- match.
open :: [Term] -> Term -> Term
open = open' 0

-- { k -> [u] } t
open' :: Int -> [Term] -> Term -> Term
open' k u t = case t of
  BVar i j -> if i == k then u !! j else t
  FVar _ -> t
  Abs t' -> open' (k + 1) u t'
  App t1 t2 -> App (open' k u t1) (open' k u t2)
  Let ts t1 ->
    -- XXX double check this
    let open'' = open' (k + 1) u
    in Let (map open'' ts) (open'' t1)
