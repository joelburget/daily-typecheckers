{-# LANGUAGE FlexibleContexts #-}
-- A barebones bidirectional dependent typechecker with HOAS
module Day1 where

import Control.Monad.Gen

import Control.Monad (guard)
import Data.Maybe (isNothing)

data IExpr
  = Var Int
  | App IExpr CExpr
  | Type
  | Pi CExpr CExpr
  | Annot CExpr CExpr
  deriving (Eq, Show, Ord)

data CExpr
  = Lam CExpr
  | CheckI IExpr
  deriving (Eq, Show, Ord)

data Val
  = VType
  | VPi Val (Val -> Val)
  | VLam (Val -> Val)
  -- used only by eqVal to compare HOAS terms
  | VGen Int

instance Enum Val where
  toEnum = VGen
  fromEnum _ = error "You're a bad person."

eqVal :: Val -> Val -> Bool
eqVal l r = runGen $ go l r where
  go VType VType = return True
  go (VPi d c) (VPi d' c') = (&&) <$> go d d' <*> go (c d) (c' d')
  go (VLam f) (VLam g) = do
    v <- gen
    go (f v) (g v)
  go (VGen i) (VGen j) = return $ i == j
  go _ _ = return False

-- de bruijn indexed environment
iEval :: [Val] -> IExpr -> Val
iEval _ Type = VType
iEval env (Var i) = env !! i
iEval env (App l r) =
  case iEval env l of
    VLam f -> f (cEval env r)
    _ -> error "Impossible: evaluated ill-typed expression"
iEval env (Pi l r) = VPi (cEval env l) (\v -> cEval (v:env) r)
iEval env (Annot e _) = cEval env e

cEval :: [Val] -> CExpr -> Val
cEval env (Lam c) = VLam $ \v -> cEval (v:env) c
cEval env (CheckI ie) = iEval env ie

eval :: CExpr -> Val
eval = cEval []

quote :: Val -> IExpr
quote = runGen . go where
  go VType = return Type
  go (VPi d c) = do
    d' <- go d
    c' <- go (c d)
    return $ Pi (CheckI d') (CheckI c')
  go (VLam _) = Var <$> gen
  go _ = error "quoting a VGen"

infer :: [Val] -> IExpr -> Maybe Val
infer _ (Var _) = Nothing -- open term!
infer env (App ie oe) =
  let v = cEval env oe
  in infer (v:env) ie
infer _ Type = Just VType
infer env (Pi d c) = do
  check' env d VType
  let v = cEval env d
  check' (v:env) c VType
  return VType
infer env (Annot tm ty) = do
  check' env tm VType
  let v = cEval [] ty
  check' env tm v
  return v

check :: [Val] -> CExpr -> Val -> Bool
check env l = eqVal (cEval env l)

check' :: [Val] -> CExpr -> Val -> Maybe ()
check' env cExpr val = guard (check env cExpr val)

tests :: IO ()
tests = do
      -- (\x -> x :: Type -> Type) Type
  let expr1 :: IExpr
      expr1 = App
        (Annot
          (Lam (CheckI (Var 0)))
          (CheckI (Pi (CheckI Type) (CheckI (Var 0)))))
        (CheckI Type)
  putStrLn "normalizing:"
  putStrLn $ "quote> " ++ show expr1
  -- quote . eval performs normalization by evaluation
  print (quote (iEval [] expr1))

  let expr2 :: CExpr
      expr2 = CheckI expr1
  putStrLn ""
  putStrLn "checking:"
  putStrLn $ "check> " ++ show expr2
  print $ check [] expr2 VType

  putStrLn ""
  putStrLn "but now with the wrong type:"
  let expr3 :: CExpr
      expr3 = CheckI
        (App
          (Annot
            (Lam (CheckI (Var 0)))
            (CheckI (Pi (CheckI Type) (CheckI (Var 0)))))
          (CheckI (Pi (CheckI Type) (CheckI (Var 0)))))
  putStrLn $ "check> " ++ show expr3
  print $ check [] expr3 VType

  putStrLn ""
  putStrLn "pi inference:"
  print $ eqVal <$> infer [] (Pi (CheckI Type) (CheckI (Var 0))) <*> Just VType

  putStrLn ""
  putStrLn "open (failed) inference:"
  -- XXX not done
  print $ isNothing $ infer [] (Pi (CheckI (Var 0)) (CheckI (Var 0)))
  print $ isNothing $ infer [] (Pi (CheckI Type) (CheckI (Var 1)))
