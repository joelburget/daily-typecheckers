module Day23 where

data Infer
  = Var Int
  | App Infer Check
  | Case Infer Type Check Check
  | Cut Check Type

data Check
  = Lam Check
  | Let Pattern Infer Check
  | Inl Check
  | Inr Check
  | Prd Check Check
  | Neu Infer

data Pattern
  = Matching Int

data Type
  = Const String
  | Lolly Type Type
  | SumTy Type Type
  | PrdTy Type Type

swap, illTyped, diagonal :: Check

swap = Lam (Let
  (Matching 2)
  (Var 0)
  (Prd (Neu (Var 1)) (Neu (Var 0)))
  )

illTyped = Let
  (Matching 2)
  (Cut (Lam (Neu (Var 0))) (Lolly (Const "a") (Const "a")))
  (Prd (Neu (Var 0)) (Neu (Var 1)))

diagonal = Lam (Prd (Neu (Var 0)) (Neu (Var 0)))

type Context = [Type]

data Usage
  = Fresh
  | Stale

type Usages = [Usage]
