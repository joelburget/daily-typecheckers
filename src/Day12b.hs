{-# LANGUAGE PatternSynonyms #-}
module Day12b where

import Control.Monad.ST
import Data.Propagator
import Data.Propagator.Cell

-- let's start with a simple two-level stratification

-- All terms carry a type, annot does so explicitly.
data Term a
  = BVar Type Int
  | FVar Type String
  | Abs Type a
  | App Type a a
  | Annot {- explicit -} Type a
  -- | Type
  deriving (Show, Eq, Functor)

data Type
  = TyFVar String
  | TyApp Type Type
  -- | Type
  deriving (Show, Eq)

pattern BVarT ty i = TotalTerm (BVar ty i)
pattern FVarT ty s = TotalTerm (FVar ty s)
pattern AbsT ty t = TotalTerm (Abs ty t)
pattern AppT ty t1 t2 = TotalTerm (App ty t1 t2)
pattern AnnotT ty tm = TotalTerm (Annot ty tm)

pattern BVarP ty i = PartialTerm (BVar ty i)
pattern FVarP ty s = PartialTerm (FVar ty s)
pattern AbsP ty t = PartialTerm (Abs ty t)
pattern AppP ty t1 t2 = PartialTerm (App ty t1 t2)
pattern AnnotP ty tm = PartialTerm (Annot ty tm)

-- also for total terms?
pTmTy :: PartialTerm -> Type
pTmTy (BVarP ty _) = ty
pTmTy (FVarP ty _) = ty
pTmTy (AbsP ty _) = ty
pTmTy (AppP ty _ _) = ty
pTmTy (AnnotP ty _) = ty

newtype PartialTerm = PartialTerm (Term (Maybe PartialTerm)) deriving (Show, Eq)
newtype TotalTerm = TotalTerm (Term TotalTerm) deriving (Show, Eq)

tToP :: TotalTerm -> PartialTerm
tToP (TotalTerm t) =
  let f = Just . tToP
  in PartialTerm $ case t of
       BVar ty i -> BVar ty i
       FVar ty x -> FVar ty x
       Abs ty t' -> Abs ty (f t')
       App ty t1 t2 -> App ty (f t1) (f t2)
       Annot ty tm -> Annot ty (f tm)
       -- Type -> Type

typecheck
  :: forall s.
     Cell s PartialTerm
  -> Cell s Type
  -> Cell s Bool
  -> ST s ()
typecheck = lift2 $ \tm ty -> pTmTy tm == ty

instance Propagated Type where

-- many orphans!

-- XXX there are a couple possible instances for Maybe -- this one where it
-- represents partial information and the other where it represents
-- contradiction.
instance Propagated a => Propagated (Maybe a) where
  merge (Just x) (Just y) = Just <$> merge x y
  merge Nothing y@(Just _) = Change True y
  merge x@(Just _) Nothing = Change False x
  merge Nothing Nothing = Change False Nothing

instance (Propagated a, Propagated b, Propagated c) => Propagated (a, b, c) where
  merge (a, b, c) (d, e, f) = (,,) <$> merge a d <*> merge b e <*> merge c f

instance Propagated PartialTerm where
  merge px@(PartialTerm x) (PartialTerm y) = case (x, y) of
    (BVar i, BVar j)
      | i == j -> Change False px
      -- TODO: might this be possible?
      -- this isn't allowed on its own -- they're unique variables, but maybe
      -- it's possible to do something if there's a proof that they're the same
      | otherwise -> Contradiction mempty "unable to merge bound vars"
    (FVar x', FVar y')
      | x' == y' -> Change False px
      -- TODO: might this be possible?
      -- see note about bound vars
      | otherwise -> Contradiction mempty "unable to merge free vars"
    (Abs x', Abs y') -> PartialTerm . Abs <$> merge x' y'
    (App x1 x2, App y1 y2) -> PartialTerm <$> (App <$> merge x1 y1 <*> merge x2 y2)

    (Annot ty1 tm1, Annot ty2 tm2) ->
      PartialTerm <$> (Annot <$> merge ty1 ty2 <*> merge tm1 tm2)
    (Annot ty tm1, tm2) ->
      PartialTerm <$> (Annot ty <$> merge tm1 (Just (PartialTerm tm2)))
    (tm1, Annot ty tm2) ->
      PartialTerm <$> (Annot ty <$> merge (Just (PartialTerm tm1)) tm2)

    -- Attempts to merge variables and non-variables
    -- Some or all of these cases may not be valid.
    (BVar _, t) -> Change True (PartialTerm t)
    (FVar _, t) -> Change True (PartialTerm t)
    (_, BVar _) -> Change False px
    (_, FVar _) -> Change False px

    -- TODO Apps should merge with their reduced form (when normalization is a
    -- thing (dynamic graphs??))
    --
    -- Actually the dynamic graph thing might not be that big of an issue since
    -- some cell will contain other cells or some other hand-wavy thing

    -- (Type, Type) -> Change False (PartialTerm Type)
    _ -> Contradiction mempty "can't unify"

main :: IO ()
main = do
  -- unify: `x: y` with `_: y`
  print $ runST $ do
    x <- known (tToP (AnnotT (TyFVar "y") (FVarT "x")))
    y <- known (PartialTerm (Annot (TyFVar "y") Nothing))
    unify x y
    content x

  -- unify: `_` with `_: y`
  print $ runST $ do
    x <- known Nothing
    y <- known (Just (PartialTerm (Annot (TyFVar "y") Nothing)))
    unify x y
    content x

  -- unify: `_` with `x: y`
  print $ runST $ do
    x <- known (Just (tToP (AnnotT (TyFVar "y") (FVarT "x"))))
    y <- known Nothing
    unify x y
    content x

  print $ runST $ do
    x <- known (tToP (AnnotT (TyApp (TyFVar "a") (TyFVar "b")) (FVarT "x")))
    y <- known (TyApp (TyFVar "a") (TyFVar "b"))
    result <- cell
    typecheck x y result
    content result

  -- we should be able to do this!
  print $ runST $ do
    x <- known (tToP (AppT (AnnotT (TyFVar "a") (FVarT "x"))
                           (AnnotT (TyFVar "b") (FVarT "y"))))
    y <- known (TyApp (TyFVar "a") (TyFVar "b"))
    result <- cell
    typecheck x y result
    content result

  -- we want this typechecking to fail
  print $ runST $ do
    x <- known (tToP (AnnotT (TyApp (TyFVar "a") (TyFVar "b")) (FVarT "x")))
    y <- known (TyFVar "a")
    result <- cell
    typecheck x y result
    content result
