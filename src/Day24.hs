{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
module Day24 where

-- * n-tuples, n-functions
-- * working towards:
--   - usage annotations
--   - dependency
--   - desugaring records, variants, etc

import Control.Lens hiding (Const)
import Control.Monad.Error.Class
import Control.Monad.State
import Control.Monad.Trans.Either
import Data.Vector (Vector)
import qualified Data.Vector as V


data Infer
  = Var Int
  | App Infer (Vector Check)
  -- questions arise re the eliminator for tuples
  -- * is it case, or was case just the eliminator for sums?
  -- * is let a suitable eliminator? but let's a checked term, not infered
  -- * in a way, eliminating tuples is not computation! whereas functions and
  --   cases branch (justifying no infered term for eliminating tuples).
  --
  -- ... actually we need case or there is no branching!
  | Case Infer Type (Vector Check)
  | Cut Check Type

data Check
  = Lam Check
  | Prd (Vector Check)
  | Let Pattern (Vector Infer) Check
  | Neu Infer

-- how many variables does this match (kind of redundant)
newtype Pattern = Matching Int

-- floating point numbers suck http://blog.plover.com/prog/#fp-sucks
-- (so do dates and times)
data Primitive
  = String String
  | Nat Int
  | Symbol String

data PrimTy
  = StringTy
  | NatTy
  | SymbolTy
  deriving Eq

data Type
  = PrimTy PrimTy
  | Lolly (Vector Type) Type
  | Tuple (Vector Type)
  deriving Eq

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
  App iTm appTms -> do
    iTmTy <- infer iTm
    case iTmTy of
      Lolly inTys outTy -> do
        forM_ (V.zip inTys appTms) $ \(ty, tm) -> check ty tm
        return outTy
      _ -> throwError "[infer App] infered non Lolly in LHS of application"
  Case iTm ty cTms -> do
    iTmTy <- infer iTm

    forM_ cTms $ \cTm -> do
      id %= cons (iTmTy, Fresh)
      check ty cTm
      lUsage <- (snd . head) <$> get
      -- TODO who this is really scary I haven't been maintaining the stack
      -- hygienically
      id %= tail
      assert (lUsage == Stale) "[infer Case] must consume linear variable in case branch"

    case iTmTy of
      PrimTy _prim -> do
        assert (iTmTy == ty) "[infer Case] primitive mismatch"
        return ty
      Tuple _values -> do
        assert (iTmTy == ty) "[infer Case] tuple mismatch"
        return ty
      Lolly _ _ -> throwError "[infer] can't case on function"
  Cut cTm ty -> do
    check ty cTm
    return ty

check :: Type -> Check -> CheckCtx ()
check ty tm = case tm of
  Lam body -> case ty of
    Lolly argTys tau -> do
      -- XXX do we need to reverse these?
      let delta = V.toList $ V.map (, Fresh) argTys
          arity = length argTys
      id %= (delta++)
      check tau body
      -- TODO remove all the duplication between this and Let
      (usageL, rest) <- (splitAt arity) <$> get
      id .= rest
      forM_ usageL $ \(_ty, usage) ->
        assert (usage == Stale) "[check Lam] must consume linear bound variables"
    _ -> throwError "[check Lam] checking lambda against non-lolly type"
  Let (Matching arity) letTms cTm -> do
    assert (length letTms == arity) "[check Let] unexpected arity"
    letTmTys <- mapM infer letTms
    -- XXX do we need to reverse these?
    let delta = V.toList $ V.map (, Fresh) letTmTys
    id %= (delta++)
    check ty cTm
    (usageL, rest) <- (splitAt arity) <$> get
    id .= rest
    forM_ usageL $ \(_ty, usage) ->
      assert (usage == Stale) "[check Let] must consume linear bound variables"
  Prd cTms -> case ty of
    -- TODO check vectors lign up
    Tuple tys -> V.forM_ (V.zip cTms tys) $ \(tm', ty') -> check ty' tm'
    _ -> throwError "[check Prd] checking Prd agains non-product type"
  Neu iTm -> do
    iTmTy <- infer iTm
    assert (iTmTy == ty) "[check Neu] checking infered neutral type"
