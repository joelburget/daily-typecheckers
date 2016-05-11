module Day21 where

data Desc
  = Unit
  | Var String

  | Desc :+: Desc
  | Desc :*: Desc
  | Desc :->: Desc

  | Lfix String Desc
  | Gfix String Desc

  | All String Desc
  | Exists String Desc

-- Lfix X. 1 + A * X
list :: Desc
list = Lfix "X" (Unit :+: (Var "A" :*: Var "X"))

-- Lfix X. A + X * X
binaryTree :: Desc
binaryTree = Lfix "X" (Var "A" :+: (Var "X" :*: Var "X"))

-- Gfix X. A * X
stream :: Desc
stream = Gfix "X" (Var "A" :*: Var "X")

-- Lfix X. 1 + (X -> X)
--
-- Has terms with no normal form. We should disallow this because it has a
-- recursive type variable in a negative position.
bad :: Desc
bad = Lfix "X" (Unit :+: (Var "X" :->: Var "X"))
