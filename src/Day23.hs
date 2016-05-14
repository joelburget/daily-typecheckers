{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
module Day23 where
-- Straight-up implementation of "Typing with Leftovers" by Guillaume Allais

import Control.Lens hiding (Const)
import Control.Monad.Error.Class
import Control.Monad.State
import Control.Monad.Trans.Either

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

data Usage = Fresh | Stale deriving Eq

type CheckCtx = EitherT String (State [(Type, Usage)])

runChecker :: CheckCtx () -> String
runChecker checker = either id (const "success!") (evalState (runEitherT checker) [])

assert :: MonadError String m => Bool -> String -> m ()
assert True _ = return ()
assert False str = throwError str

inferVar :: Int -> CheckCtx Type
inferVar k = do
  -- find the type, toggle usage from fresh to stale
  -- TODO what's the lens for this?
  (ty, usage) <- (!! k) <$> get
  assert (usage == Fresh) "[inferVar] you can't use a linear variable twice!"
  ix k._2 .= Stale
  return ty

infer :: Infer -> CheckCtx Type
infer t = case t of
  Var i -> inferVar i
  App iTm cTm -> do
    iTmTy <- infer iTm
    case iTmTy of
      Lolly sigma tau -> do
        check sigma cTm
        return tau
      _ -> throwError "[infer App] infered non Lolly in LHS of application"
  Case iTm ty lcTm rcTm -> do
    iTmTy <- infer iTm
    case iTmTy of
      SumTy sigma tau -> do
        id %= cons (sigma, Fresh)

        -- XXX need to enforce both sides have same leftovers
        -- (need to make sure leftovers are right everywhere, really)
        check ty lcTm
        lUsage <- (snd . head) <$> get
        assert (lUsage == Stale) "[infer Case] must consume linear variable in left case"
        id %= tail

        id %= cons (tau, Fresh)
        check ty rcTm
        rUsage <- (snd . head) <$> get
        assert (rUsage == Stale) "[infer Case] must consume linear variable in right case"
        id %= tail

        return ty
      _ -> throwError "[infer] infered non SumTy in case"
  Cut cTm ty -> do
    check ty cTm
    return ty

check :: Type -> Check -> CheckCtx ()
check ty tm = case tm of
  Lam body -> case ty of
    Lolly sigma tau -> do
      id %= cons (sigma, Fresh)
      check tau body
      rUsage <- (snd . head) <$> get
      assert (rUsage == Stale) "[check Lam] must consume linear bound variable"
      id %= tail
    _ -> throwError "[check Lam] checking lambda against non-lolly type"
  Let pat iTm cTm -> do
    sigma <- infer iTm
    let delta = typePat sigma pat
        delta' = map (, Fresh) delta
    id %= (delta'++)
    check ty cTm
    rUsage <- (snd . head) <$> get
    -- XXX what's the binding story here?
    assert (rUsage == Stale) "[check Let] must consume linear bound variables"
    id %= drop (length delta')
  Inl cTm -> case ty of
    SumTy sigma _tau -> check sigma cTm
    _ -> throwError "[check Inl] checking Inl agains non-sum type"
  Inr cTm -> case ty of
    SumTy _sigma tau -> check tau cTm
    _ -> throwError "[check Inr] checking Inr agains non-sum type"
  Prd aTm bTm -> case ty of
    PrdTy sigma tau -> do
      check sigma aTm
      check tau bTm
    _ -> throwError "[check Prd] checking Prd agains non-product type"
  Neu iTm -> do
    iTmTy <- infer iTm
    assert (iTmTy == ty) "[check Neu] checking infered neutral type"

-- TODO stop being lazy and give these variables better names not from the
-- paper
typePat :: Type -> Pattern -> [Type]
typePat (PrdTy sigma tau) (PrdPat p q) =
  let gamma = typePat sigma p
      delta = typePat tau q
  -- note ordering of results (gamma at head of list, delta at end) (this is
  -- the opposite order the paper returns them in but we're accessing from the
  -- front, not the rear)
  in gamma ++ delta
typePat sigma VPat = [sigma]
-- TODO handle better
typePat _ _ = error "[typePat] matching non PrdTy agains PrdPat"

data Pattern
  = VPat
  | PrdPat Pattern Pattern

data Type
  = Const String
  | Lolly Type Type
  | SumTy Type Type
  | PrdTy Type Type
  deriving Eq

swap, illTyped, diagonal :: Check

swap = Lam (Let
  (PrdPat VPat VPat)
  (Var 0)
  (Prd (Neu (Var 1)) (Neu (Var 0)))
  )

illTyped = Let
  (PrdPat VPat VPat)
  (Cut (Lam (Neu (Var 0))) (Lolly (Const "a") (Const "a")))
  (Prd (Neu (Var 0)) (Neu (Var 1)))

diagonal = Lam (Prd (Neu (Var 0)) (Neu (Var 0)))


main :: IO ()
main = do
  -- this typechecks
  let swapTy =
        let x = Const "x"
            y = Const "y"
        in Lolly (PrdTy x y) (PrdTy y x)
  putStrLn $ runChecker $ check swapTy swap

  -- but this doesn't -- it duplicates its linear variable
  let diagonalTy =
        let x = Const "x"
        in Lolly x (PrdTy x x)
  putStrLn $ runChecker $ check diagonalTy diagonal
