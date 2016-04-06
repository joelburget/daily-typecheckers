{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
-- Putting some polish on Day 2
module Day3 where

import Control.Monad.Gen
import Control.Monad (when)

import Data.Either (isRight)

data IExpr
  = Var Int
  | App IExpr CExpr
  | Type
  | Pi CExpr CExpr
  | Annot CExpr CExpr
  | Num
  | Lit Int
  -- | Const String
  -- | Free Int
  deriving (Eq, Show, Ord)

data CExpr
  = Lam CExpr
  | CheckI IExpr
  deriving (Eq, Show, Ord)

data VConst
  = CAp VConst Val
  | CVar String
  | CFree Int

data Val
  = VType
  | VNum
  | VLit Int
  -- | VConst VConst
  | VPi Val (Val -> Val)
  | VLam (Val -> Val)
  | VVar Int

type Type = Val
newtype Ctx = Ctx [Val :<: Type]

data tm :<: ty = tm :<: ty  deriving (Show, Eq)
infix 4 :<:

-- -- Add a value and its type to the context
(<:) :: (Val :<: Type) -> Ctx -> Ctx
x <: (Ctx xs) = Ctx (x:xs)

-- -- Add a neutral variable to the context
-- (<::) :: Type -> Ctx -> Ctx
-- (<::) t (Ctx vs ts) = Ctx (VVar 0:vs) (t:ts)

-- XXX add invariant to only ever evaluate typechecked terms

-- XXX audit all uses
extractTerms :: Ctx -> [Val]
extractTerms (Ctx xs) = map (\(tm :<: _) -> tm) xs

extractTypes :: Ctx -> [Type]
extractTypes (Ctx xs) = map (\(_ :<: ty) -> ty) xs

instance Enum Val where
  toEnum = VVar
  fromEnum _ = error "You're a bad person."

eqVal :: Val -> Val -> Bool
eqVal l r = runGen $ go l r where
  go VType VType = pure True
  go VNum VNum = pure True
  go (VLit n) (VLit m) = pure $ n == m
  go (VPi d c) (VPi d' c') = (&&) <$> go d d' <*> go (c d) (c' d')
  go (VLam f) (VLam g) = do
    v <- gen
    go (f v) (g v)
  go (VVar i) (VVar j) = pure $ i == j
  go _ _ = pure False

instance Eq Val where
  (==) = eqVal

iEval :: [Val] -> IExpr -> Val
iEval env = \case
  Type -> VType
  Num -> VNum
  Lit n -> VLit n
  Var i -> env !! i
  App l r -> case iEval env l of
    VLam f -> f (cEval env r)
    _ -> error "Impossible: evaluated ill-typed expression"
  Pi l r -> VPi (cEval env l) (\v -> cEval (v:env) r)
  Annot e _ -> cEval env e

cEval :: [Val] -> CExpr -> Val
cEval env = \case
  Lam c -> VLam $ \v -> cEval (v:env) c
  CheckI ie -> iEval env ie

eval :: CExpr -> Val
eval = cEval []

quote :: Val -> CExpr
quote = \case
  VType -> CheckI Type
  VNum -> CheckI Num
  VLit n -> CheckI (Lit n)
  VPi dom codom -> CheckI (Pi (quote dom) (quote (codom (VVar 0))))
  VLam f -> Lam (quote (f (VVar 0)))
  VVar i -> CheckI $ Var i

-- An infered type is either completely determined, or dependent on the value
-- of some earlier type (... telescope...)
data Infer
  = Ok Type
  | IPi Type (Val -> Either String Infer)

ok :: Val -> Either String Infer
ok = pure . Ok

infer :: Ctx -> IExpr -> Either String Infer
infer ctx =
  let vs = extractTerms ctx
      ts = extractTypes ctx
  in \case
       Var i -> if length ts > i
         then ok (ts !! i)
         else Left "Can't infer this open term!"
       Num -> ok VType
       Lit _ -> ok VNum
       App f x -> do
         fTy <- infer ctx f
         case fTy of
           Ok (VPi dom codom) -> do
             check ctx (x :<: dom)
             ok (codom (cEval vs x))
           IPi dom codom -> do
             check ctx (x :<: dom)
             codom (cEval vs x)
           _ -> Left "Applied a non-pi!"
       Type -> ok VType
       Pi dom codom -> do
         check ctx (dom :<: VType)
         let domV = cEval vs dom
             ctx' = (domV :<: VType) <: ctx
         check ctx' (codom :<: VType)
         ok VType
       Annot tm ty -> do
         check ctx (ty :<: VType)
         let tyV = cEval (extractTerms ctx) ty
         check ctx (tm :<: tyV)
         ok tyV

quoteInfer :: Infer -> Either String CExpr
quoteInfer (Ok ty) = pure (quote ty)
quoteInfer (IPi a b) = (CheckI . Pi (quote a)) <$> (quoteInfer =<< b (VVar 0))

checkB :: Ctx -> (CExpr :<: Val) -> Bool
checkB ctx typing = isRight (check ctx typing)

check :: Ctx -> (CExpr :<: Val) -> Either String ()
check ctx (tm :<: ty) = case tm of
  Lam expr -> case ty of
    VPi specDomTy codomTy ->
      -- just check that the body returns the codomain given an input of the
      -- domain
      check ((VVar 0 :<: specDomTy) <: ctx) (expr :<: codomTy specDomTy)
    _ -> Left "this lambda is not that other thing"
  CheckI expr -> do
    iTy <- infer ctx expr
    case (ty, iTy) of
      (_, Ok iTy') -> if iTy' == ty then Right () else Left "failed checking!"
      (VPi specDomTy specCodomTy, IPi iDomTy iCodomTy) -> do
        when (specDomTy /= iDomTy) $ Left "failed checking!"
        _ <- iCodomTy specDomTy
        return ()
      _ -> Left "okay, well this doesn't match at all"

tests :: IO ()
tests = do
  let ctx = Ctx []
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
  print $ checkB ctx (expr2 :<: VType)

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
  print $ checkB ctx (expr3 :<: VType)

  putStrLn ""
  putStrLn "pi inference:"
  print $ checkB ctx (CheckI (Pi (CheckI Type) (CheckI (Var 0))) :<: VPi VType id)

  putStrLn ""
  putStrLn "lit inference"
  print $ checkB ctx (CheckI Num :<: VType)
  print $ checkB ctx (CheckI (Lit 5) :<: VNum)
  print $ checkB (Ctx [VLit 5 :<: VNum]) (CheckI (Var 0) :<: VNum)

  -- putStrLn ""
  -- putStrLn "open (failed) inference:"
  -- -- XXX not done
  -- print $ isLeft $ infer ctx (Pi (CheckI (Var 0)) (CheckI (Var 0)))
  -- print $ isLeft $ infer ctx (Pi (CheckI Type) (CheckI (Var 1)))
