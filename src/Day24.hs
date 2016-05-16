{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
module Day24 where

-- Significant features of this treatment include:
-- * n-tuples as a generalization of 2-tuples. This is an easy optimization
--   win for little extra work.
-- * labels (as a branching mechanism)
-- * bidirectional checking. we're following the treatment from Guillaume
--   Allais' "Typing with Leftovers" with modifications.
-- * linearity
--
-- * working towards:
--   - explicit usage annotations, so we can have variables that are used
--     multiple times (or not at all)
--   - dependency
--   - desugaring records, variants, etc

-- TODO things to check:
-- * arities line up in all places
-- * threading contexts specifies calling convention in a very real way
-- * what data structures are we using (list vs vector / ralist)

import Control.Lens hiding (Const)
import Control.Monad.Error.Class
import Control.Monad.State
import Data.Vector (Vector)
import qualified Data.Vector as V


data Infer
  = Var Int
  | App Infer Check
  -- questions arise re the eliminator for tuples
  -- * is it case, or was case just the eliminator for sums?
  -- * is let a suitable eliminator? but let's a checked term, not infered
  -- * in a way, eliminating tuples is not computation! whereas functions and
  --   cases branch (justifying no infered term for eliminating tuples).
  --
  -- ... actually we need case or there is no branching!
  | Case Infer Type (Vector Check)
  | Cut Check Type
  | Label String

data Check
  = Lam Check
  | Prd (Vector Check)
  | Let Pattern Infer Check
  | Neu Infer

-- Match nested n-tuples.
--
-- Easy extension: `Underscore` doesn't bind any variables. Useful?
data Pattern
  = MatchTuple (Vector Pattern)
  | MatchVar

-- floating point numbers suck http://blog.plover.com/prog/#fp-sucks
-- (so do dates and times)
data Primitive
  = String String
  | Nat Int

data PrimTy
  = StringTy
  | NatTy
  deriving Eq

data Type
  = PrimTy PrimTy
  | LabelTy String
  | Lolly Type Type
  | Tuple (Vector Type)
  deriving Eq

data Usage = Fresh | Stale deriving Eq

type Ctx = [(Type, Usage)]

-- I (Joel) made the explicit choice to not use the state monad to track
-- leftovers, since I want to take a little more care with tracking linearity.
-- We layer it on in some places where it's helpful.
--
-- TODO do we need to check all linear variables have been consumed here?
-- * we should just fix this so it passes in the empty context to the checker
runChecker :: Either String Ctx -> String
runChecker checker = either id (const "success!") checker

assert :: MonadError String m => Bool -> String -> m ()
assert True _ = return ()
assert False str = throwError str

inferVar :: Ctx -> Int -> Either String (Ctx, Type)
inferVar ctx k = do
  -- find the type, toggle usage from fresh to stale
  let (ty, usage) = ctx !! k
  assert (usage == Fresh) "[inferVar] you can't use a linear variable twice!"
  return (ctx & ix k . _2 .~ Stale, ty)

allTheSame :: (Eq a) => [a] -> Bool
allTheSame xs = and $ map (== head xs) (tail xs)

infer :: Ctx -> Infer -> Either String (Ctx, Type)
infer ctx t = case t of
  Var i -> inferVar ctx i
  App iTm appTm -> do
    (leftovers, iTmTy) <- infer ctx iTm
    case iTmTy of
      Lolly inTy outTy -> do
        leftovers2 <- check leftovers inTy appTm
        return (leftovers2, outTy)
      _ -> throwError "[infer App] infered non Lolly in LHS of application"
  Case iTm ty cTms -> do
    (leftovers1, iTmTy) <- infer ctx iTm

    leftovers2 <- flip execStateT leftovers1 $ forM cTms $ \cTm -> do
      let subCtx = (iTmTy, Fresh):ctx
      (_, hopefullyStale):newCtx <- lift $ check subCtx ty cTm
      assert (hopefullyStale == Stale)
        "[infer Case] must consume linear variable in case branch"
      return newCtx

    assert (allTheSame leftovers2) "[infer Case] all branches must consume the same linear variables"

    case iTmTy of
      LabelTy _label -> assert (iTmTy == ty) "[infer Case] label mismatch"
      PrimTy _prim -> assert (iTmTy == ty) "[infer Case] primitive mismatch"
      Tuple _values -> assert (iTmTy == ty) "[infer Case] tuple mismatch"
      Lolly _ _ -> throwError "[infer] can't case on function"

    return (leftovers2, ty)

  Cut cTm ty -> do
    leftovers <- check ctx ty cTm
    return (leftovers, ty)

  Label name -> return (ctx, LabelTy name)

check :: Ctx -> Type -> Check -> Either String Ctx
check ctx ty tm = case tm of
  Lam body -> case ty of
    Lolly argTy tau -> do
      let bodyCtx = (argTy, Fresh):ctx
      (_, usage):leftovers <- check bodyCtx tau body
      assert (usage == Stale) "[check Lam] must consume linear bound variable"
      return leftovers
    _ -> throwError "[check Lam] checking lambda against non-lolly type"
  Let pattern letTm cTm -> do
    (leftovers, tmTy) <- infer ctx letTm
    let patternTy = typePattern pattern tmTy
    -- XXX do we need to reverse these?
    let freshVars = map (, Fresh) patternTy
        bodyCtx = freshVars ++ leftovers
        arity = length patternTy
    newCtx <- check bodyCtx ty cTm

    -- Check that the body consumed all the arguments
    let (bodyUsage, leftovers2) = splitAt arity newCtx
    forM_ bodyUsage $ \(_ty, usage) ->
      assert (usage == Stale) "[check Let] must consume linear bound variables"
    return leftovers2
  Prd cTms -> case ty of
    -- Thread the leftover context through from left to right.
    Tuple tys ->
      -- Layer on a state transformer for this bit, since we're passing
      -- leftovers from one term to the next
      let calc = forM (V.zip cTms tys) $ \(tm', ty') -> do
            leftovers <- get
            newLeftovers <- lift $ check leftovers ty' tm'
            put newLeftovers
      -- execState gives back the final state
      in execStateT calc ctx
    _ -> throwError "[check Prd] checking Prd agains non-product type"
  Neu iTm -> do
    (leftovers, iTmTy) <- infer ctx iTm
    assert (iTmTy == ty) "[check Neu] checking infered neutral type"
    return leftovers

typePattern :: Pattern -> Type -> [Type]
typePattern MatchVar ty = [ty]
-- TODO check these line up
typePattern (MatchTuple subPats) (Tuple subTys) =
  let zipped = V.zip subPats subTys
  in concatMap (uncurry typePattern) zipped
typePattern _ _ = error "[typePattern] misaligned pattern"

swap, illTyped, diagonal :: Check

swap = Lam (Let
  (MatchTuple (V.fromList [MatchVar, MatchVar]))
  (Var 0)
  (Prd (V.fromList [Neu (Var 1), Neu (Var 0)]))
  )

illTyped = Let
  (MatchTuple (V.fromList [MatchVar, MatchVar]))
  (Cut (Lam (Neu (Var 0))) (Lolly (PrimTy NatTy) (PrimTy NatTy)))
  (Prd (V.fromList [Neu (Var 0), Neu (Var 1)]))

diagonal = Lam (Prd (V.fromList [Neu (Var 0), Neu (Var 0)]))


main :: IO ()
main = do
  -- this typechecks
  let swapTy =
        let x = PrimTy StringTy
            y = PrimTy NatTy
        in Lolly (Tuple (V.fromList [x, y])) (Tuple (V.fromList [y, x]))
  putStrLn "> checking swap"
  putStrLn $ runChecker $ check [] swapTy swap

  -- but this doesn't -- it duplicates its linear variable
  let diagonalTy =
        let x = PrimTy StringTy
        in Lolly x (Tuple (V.fromList [x, x]))
  putStrLn "> checking diagonal (expected failure due to duplicating linear variable)"
  putStrLn $ runChecker $ check [] diagonalTy diagonal
