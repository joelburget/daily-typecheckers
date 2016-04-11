module Day8 where

import Data.Set (Set)
import qualified Data.Set as Set

--

data Term
  = BVar Int
  | FVar String
  | Abs Term
  | App Term Term
  deriving (Show, Eq)

alphaEquivalent4 = (==)


alphaEquivs4 =
  let l1 = Abs (BVar 0)
      l2 = Abs (BVar 0)
      l3 = Abs (FVar "x")
  in -- reflexivity
     alphaEquivalent4 l1 l1 &&
     alphaEquivalent4 l2 l2 &&
     alphaEquivalent4 l3 l3 &&
     -- symmetry
     alphaEquivalent4 l1 l2 &&
     alphaEquivalent4 l2 l1 &&

     not (alphaEquivalent4 l1 l3) &&
     not (alphaEquivalent4 l2 l3) &&

     alphaEquivalent4 (App l1 l3) (App l2 l3) &&
     not (alphaEquivalent4 (App l1 l3) (App l3 l3))


open :: Int -> String -> Term -> Term
open k x tm = case tm of
  BVar i -> if i == k then FVar x else BVar i
  FVar _ -> tm
  App t1 t2 -> App (open k x t1) (open k x t2)
  Abs subTm -> Abs (open (k + 1) x subTm)

openOuter :: String -> Term -> Term
openOuter = open 0

exampleFrom = App (Abs (App (BVar 0) (BVar 1))) (BVar 0)
exampleTo = App (Abs (App (BVar 0) (FVar "x"))) (FVar "x")

-- openExample :: Bool
openExample = openOuter "x" exampleFrom == exampleTo

close :: Int -> String -> Term -> Term
close k x tm = case tm of
  BVar _ -> tm
  FVar y -> if x == y then BVar k else tm
  App t1 t2 -> App (close k x t1) (close k x t2)
  Abs subTm -> Abs (close (k + 1) x subTm)

closeOuter :: String -> Term -> Term
closeOuter = close 0

closeExample = closeOuter "x" exampleTo == exampleFrom

close_open_var :: String -> Term -> Bool
close_open_var x tm = (closeOuter x (openOuter x tm)) == tm

open_close_var :: String -> Term -> Bool
open_close_var x tm = (openOuter x (closeOuter x tm)) == tm

invariantExamples =
  close_open_var "y" exampleFrom &&
  close_open_var "y" exampleTo &&
  open_close_var "y" exampleFrom &&
  open_close_var "y" exampleTo

locallyClosed :: Term -> Bool
locallyClosed = locallyClosedAt 0

locallyClosedAt :: Int -> Term -> Bool
locallyClosedAt k tm = case tm of
  BVar i -> i < k
  FVar _ -> True
  App t1 t2 -> locallyClosedAt k t1 && locallyClosedAt k t2
  Abs subTm -> locallyClosedAt (k + 1) subTm

lc_from_lc_at :: Term -> Bool
lc_from_lc_at tm = locallyClosed tm == locallyClosedAt 0 tm

-- body :: Term -> Bool

-- lc_abs_iff_body :: Term -> Bool
-- lc_abs_iff_body t = locallyClosed (Abs t) = body t

freeVars :: Term -> Set String
freeVars tm = case tm of
  BVar _ -> Set.empty
  FVar x -> Set.singleton x
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Abs subTm -> freeVars subTm

fresh :: String -> Term -> Bool
fresh name tm = not (name `Set.member` freeVars tm)

closed :: Term -> Bool
closed = Set.null . freeVars

open_var_fv :: String -> Term -> Bool
open_var_fv x t = freeVars (openOuter x t) `Set.isSubsetOf` (Set.insert x (freeVars t))

close_var_fv :: String -> Term -> Bool
close_var_fv x t = freeVars (closeOuter x t) == Set.delete x (freeVars t)

subst :: String -> Term -> Term -> Term
subst x u tm = case tm of
  BVar _ -> tm
  FVar y -> if x == y then u else tm
  App t1 t2 -> App (subst x u t1) (subst x u t2)
  Abs t -> Abs (subst x u t)
