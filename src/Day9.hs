module Day9 where

-- Add some finishing touches to Day 8, two cps transformations.

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

-- there are no dangling bound variables. for instance, `Abs 3` is not locally
-- closed.
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

-- body: `t` describes the body of a locally closed abstraction
-- body :: Term -> Bool

-- lc_abs_iff_body :: Term -> Bool
-- lc_abs_iff_body t = locallyClosed (Abs t) = body t

freeVars :: Term -> Set String
freeVars tm = case tm of
  BVar _ -> Set.empty
  FVar x -> Set.singleton x
  App t1 t2 -> freeVars t1 `Set.union` freeVars t2
  Abs subTm -> freeVars subTm

isFresh :: String -> Term -> Bool
isFresh name tm = not (name `Set.member` freeVars tm)

genFresh :: Int -> Set String -> [String]
genFresh _ _ = repeat "TODO"

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

close_var_rename :: Term -> String -> String -> Bool
close_var_rename t x y = if y `isFresh` t
  then closeOuter x t == closeOuter y (subst x (FVar y) t)
  else error "y isn't fresh in t so this isn't really meaningful"

-- nice alternative definition of substitution:
-- capturing x then opening with u is the same as substituting [x -> u]
subst_as_close_open :: String -> Term -> Term -> Bool
subst_as_close_open x u t = subst x u t == gOpen0 u (closeOuter x t)

-- generalize opening to replace the targeted bound variable with a term
-- instead of a free variable.
gOpen :: Int -> Term -> Term -> Term
gOpen k u tm = case tm of
  BVar i -> if i == k then u else BVar i
  FVar _ -> tm
  App t1 t2 -> App (gOpen k u t1) (gOpen k u t2)
  Abs subTm -> Abs (gOpen (k + 1) u subTm)

gOpen0 :: Term -> Term -> Term
gOpen0 = gOpen 0

varOpen :: Term -> String -> Term
varOpen tm x = gOpen0 tm (FVar x)

-- [[x]]         \k -> k x
-- [[\x -> t]]   \k -> k (\x -> [[t]])
-- [[t1 t2]]     \k -> [[cps2 t1]] (\x -> [[cps2 t2]] (\y. x y k))

cps1 :: Term -> Term
cps1 t = case t of
  FVar x -> Abs (App (BVar 0) (FVar x))
  Abs t1 ->
    let (x:_) = genFresh 1 (freeVars t1)
        t1' = closeOuter x (cps1 (openOuter x t1))
    in Abs (App (BVar 0) (Abs t1'))
  App t1 t2 ->
    let k = Abs (App (App (BVar 1) (BVar 0)) (BVar 2))
    in Abs (App (cps1 t1) (Abs (App (cps1 t2) k)))
  BVar i -> error "cps1 found an unexpected bound variable"

cps2 :: Term -> Term
cps2 t = case t of
  FVar x ->
    let (k:_) = genFresh 1 (freeVars t)
    in Abs (closeOuter k (App (FVar k) t))
  Abs t1 ->
    let (k:x:_) = genFresh 2 (freeVars t)
        t1' = closeOuter x (cps2 (openOuter x t1))
    in Abs (closeOuter k (App (FVar k) (Abs t1')))
  App t1 t2 ->
    let (k:x:y:_) = genFresh 3 (freeVars t)
        k' = Abs (closeOuter k (App (App (FVar x) (FVar y)) (FVar k)))
    in Abs (App (cps2 t1) (Abs (App (cps2 t2) k')))
  BVar i -> error "cps2 found an unexpected bound variable"
