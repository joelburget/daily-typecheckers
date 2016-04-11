module Day7 where

-- import qualified Data.Map as M

-- raw / quotiented terms

data Term1
  = Var1 String
  | Abs1 String Term1
  | App1 Term1 Term1

subst1 :: String -> String -> Term1 -> Term1
subst1 from to tm = case tm of
  Var1 v
    | v == from -> Var1 to
    | otherwise -> tm
  Abs1 v subTm
    -- shadowing, stop substituting!
    | v == from -> tm
    | otherwise -> Abs1 v (subst1 from to subTm)
  App1 tm1 tm2 -> App1 (subst1 from to tm1) (subst1 from to tm2)

alphaEquivalent1 :: Term1 -> Term1 -> Bool
alphaEquivalent1 (Var1 v1) (Var1 v2) = v1 == v2
alphaEquivalent1 (Abs1 b1 t1) (Abs1 b2 t2) =
  alphaEquivalent1 (subst1 b1 b2 t1) t2
alphaEquivalent1 (App1 f1 x1) (App1 f2 x2) =
  alphaEquivalent1 f1 f2 && alphaEquivalent1 x1 x2
alphaEquivalent1 _ _ = False


alphaEquivs1 =
  let l1 = Abs1 "x" (Var1 "x")
      l2 = Abs1 "y" (Var1 "y")
      l3 = Abs1 "y" (Var1 "x")
  in -- reflexivity
     alphaEquivalent1 l1 l1 &&
     alphaEquivalent1 l2 l2 &&
     alphaEquivalent1 l3 l3 &&
     -- symmetry
     alphaEquivalent1 l1 l2 &&
     alphaEquivalent1 l2 l1 &&

     not (alphaEquivalent1 l1 l3) &&
     not (alphaEquivalent1 l2 l3) &&

     alphaEquivalent1 (App1 l1 l3) (App1 l2 l3) &&
     not (alphaEquivalent1 (App1 l1 l3) (App1 l3 l3))


-- locally named

data Term2
  = BVar2 String
  | FVar2 String
  | Abs2 String Term2
  | App2 Term2 Term2

subst2 :: String -> String -> Term2 -> Term2
subst2 from to tm = case tm of
  BVar2 v
    | v == from -> BVar2 to
    | otherwise -> tm
  FVar2 _ -> tm
  Abs2 v subTm
    | v == from -> tm
    | otherwise -> Abs2 v (subst2 from to subTm)
  App2 tm1 tm2 -> App2 (subst2 from to tm1) (subst2 from to tm2)

alphaEquivalent2 :: Term2 -> Term2 -> Bool
alphaEquivalent2 (BVar2 x1) (BVar2 x2) = x1 == x2
alphaEquivalent2 (FVar2 x1) (FVar2 x2) = x1 == x2
alphaEquivalent2 (Abs2 x1 tm1) (Abs2 x2 tm2) =
  alphaEquivalent2 (subst2 x1 x2 tm1) tm2
alphaEquivalent2 (App2 f1 x1) (App2 f2 x2) =
  alphaEquivalent2 f1 f2 && alphaEquivalent2 x1 x2
alphaEquivalent2 _ _ = False

alphaEquivs2 =
  let l1 = Abs2 "x" (BVar2 "x")
      l2 = Abs2 "y" (BVar2 "y")
      l3 = Abs2 "y" (FVar2 "x")
  in -- reflexivity
     alphaEquivalent2 l1 l1 &&
     alphaEquivalent2 l2 l2 &&
     alphaEquivalent2 l3 l3 &&
     -- symmetry
     alphaEquivalent2 l1 l2 &&
     alphaEquivalent2 l2 l1 &&

     not (alphaEquivalent2 l1 l3) &&
     not (alphaEquivalent2 l2 l3) &&

     alphaEquivalent2 (App2 l1 l3) (App2 l2 l3) &&
     not (alphaEquivalent2 (App2 l1 l3) (App2 l3 l3))


-- de bruijn indices

data Term3
  = Var3 Int
  | Abs3 Term3
  | App3 Term3 Term3

alphaEquivalent3 :: Term3 -> Term3 -> Bool
alphaEquivalent3 (Var3 x) (Var3 y) = x == y
alphaEquivalent3 (Abs3 x) (Abs3 y) = alphaEquivalent3 x y
alphaEquivalent3 (App3 f1 x1) (App3 f2 x2) =
  alphaEquivalent3 f1 f2 && alphaEquivalent3 x1 x2
alphaEquivalent3 _ _ = False

-- locally nameless

data Term4
  = BVar4 Int
  | FVar4 String
  | Abs4 Term4
  | App4 Term4 Term4

alphaEquivalent4 :: Term4 -> Term4 -> Bool
alphaEquivalent4 (BVar4 x) (BVar4 y) = x == y
alphaEquivalent4 (FVar4 x) (FVar4 y) = x == y
alphaEquivalent4 (Abs4 x) (Abs4 y) = alphaEquivalent4 x y
alphaEquivalent4 (App4 f1 x1) (App4 f2 x2) =
  alphaEquivalent4 f1 f2 && alphaEquivalent4 x1 x2
alphaEquivalent4 _ _ = False


alphaEquivs4 =
  let l1 = Abs4 (BVar4 0)
      l2 = Abs4 (BVar4 0)
      l3 = Abs4 (FVar4 "x")
  in -- reflexivity
     alphaEquivalent4 l1 l1 &&
     alphaEquivalent4 l2 l2 &&
     alphaEquivalent4 l3 l3 &&
     -- symmetry
     alphaEquivalent4 l1 l2 &&
     alphaEquivalent4 l2 l1 &&

     not (alphaEquivalent4 l1 l3) &&
     not (alphaEquivalent4 l2 l3) &&

     alphaEquivalent4 (App4 l1 l3) (App4 l2 l3) &&
     not (alphaEquivalent4 (App4 l1 l3) (App4 l3 l3))

