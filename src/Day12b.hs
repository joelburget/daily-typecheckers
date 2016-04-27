{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
module Day12b where

import Control.Lens (Lens')
import Control.Monad
import Control.Monad.ST
import Data.Propagator
import Data.Propagator.Cell

import Debug.Trace

-- let's start with a simple two-level stratification

-- XXX can't store cells in a cell!
data Term
  = BVar Int (Maybe Type)
  | FVar String (Maybe Type)
  | Abs (Maybe Term) (Maybe Type)
  | App (Maybe Term) (Maybe Term) (Maybe Type)
  -- | Annot (Maybe Term) (Maybe Type)
  -- | Type
  deriving Show

-- orphans!
instance Propagated a => Propagated (Maybe a) where
  merge (Just a) (Just b) = Just <$> merge a b
  merge a@(Just _) Nothing = Change False a
  merge Nothing b@(Just _) = Change True b
  merge n _ = Change False n

instance Propagated String where

instance Propagated Term where
  merge (BVar i1 ty1) (BVar i2 ty2) =
    BVar <$> merge i1 i2 <*> merge ty1 ty2
  merge (FVar s1 ty1) (FVar s2 ty2) =
    FVar <$> merge s1 s2 <*> merge ty1 ty2
  merge (Abs t1 ty1) (Abs t2 ty2) =
    Abs <$> merge t1 t2 <*> merge ty1 ty2
  merge (App t11 t12 ty1) (App t21 t22 ty2) =
    App <$> merge t11 t21 <*> merge t12 t22 <*> merge ty1 ty2
  merge _ _ = Contradiction mempty "term merge"

termTy :: Lens' Term (Maybe Type)
termTy f tm = case tm of
  BVar i ty -> BVar i <$> f ty
  FVar s ty -> FVar s <$> f ty
  Abs body ty -> Abs body <$> f ty
  App t1 t2 ty -> App t1 t2 <$> f ty


bVar :: Cell s Int -> Cell s Type -> Cell s Term -> ST s ()
bVar iCell tyCell c = do
  watch iCell $ \iVal ->
    with tyCell $ \tyVal ->
      write c (BVar iVal (Just tyVal))
  watch tyCell $ \tyVal ->
    with iCell $ \iVal ->
      write c (BVar iVal (Just tyVal))
  watch c $ \(BVar iVal mTyVal) -> do
    write iCell iVal
    maybe (return ()) (write tyCell) mTyVal

fVar :: Cell s String -> Cell s Type -> Cell s Term -> ST s ()
fVar sCell tyCell c = do
  watch sCell $ \sVal ->
    with tyCell $ \tyVal ->
      write c (FVar sVal (Just tyVal))
  watch tyCell $ \tyVal ->
    with sCell $ \sVal ->
      write c (FVar sVal (Just tyVal))
  watch c $ \(FVar sVal mTyVal) -> do
    write sCell sVal
    maybe (return ()) (write tyCell) mTyVal

abs :: Cell s Term -> Cell s Type -> Cell s Term -> ST s ()
abs tmCell tyCell c = do
  watch tmCell $ \tmVal ->
    with tyCell $ \tyVal ->
      write c (Abs (Just tmVal) (Just tyVal))
  watch tyCell $ \tyVal ->
    with tmCell $ \tmVal ->
      write c (Abs (Just tmVal) (Just tyVal))
  watch c $ \(Abs mTmVal mTyVal) -> do
    maybe (return ()) (write tmCell) mTmVal
    maybe (return ()) (write tyCell) mTyVal

app :: Cell s Term -> Cell s Term -> Cell s Type -> Cell s Term -> ST s ()
app t1Cell t2Cell tyCell c = do
  watch t1Cell $ \t1Val ->
    with t2Cell $ \t2Val ->
      with tyCell $ \tyVal ->
        write c (App (Just t1Val) (Just t2Val) (Just tyVal))
  watch t2Cell $ \t2Val ->
    with t1Cell $ \t1Val ->
      with tyCell $ \tyVal ->
        write c (App (Just t1Val) (Just t2Val) (Just tyVal))

  watch tyCell $ \tyVal ->
    with t1Cell $ \t1Val ->
      with t2Cell $ \t2Val ->
        write c (App (Just t1Val) (Just t2Val) (Just tyVal))

  watch c $ \(App mT1Val mT2Val mTyVal) -> do
    maybe (return ()) (write t1Cell) mT1Val
    maybe (return ()) (write t2Cell) mT2Val
    maybe (return ()) (write tyCell) mTyVal

data Type
  = TyFVar String
  | TyApp (Maybe Type) (Maybe Type)
  -- | Type
  deriving Show

instance Propagated Type where
  merge (TyFVar s1) (TyFVar s2) =
    TyFVar <$> merge s1 s2
  merge (TyApp t11 t12) (TyApp t21 t22) = trace "here" $
    TyApp <$> merge t11 t21 <*> merge t12 t22
  merge _ _ = Contradiction mempty "type merge"

tyFVar :: Cell s String -> Cell s Type -> ST s ()
tyFVar sCell c = do
  watch sCell $ \sVal ->
    write c (TyFVar sVal)
  watch c $ \(TyFVar sVal) ->
    write sCell sVal


tyApp :: Cell s Type -> Cell s Type -> Cell s Type -> ST s ()
tyApp t1Cell t2Cell c = do
  watch t1Cell $ \t1Val ->
    with t2Cell $ \t2Val ->
      write c (TyApp (Just t1Val) (Just t2Val))
  watch t2Cell $ \t2Val ->
    with t1Cell $ \t1Val ->
      write c (TyApp (Just t1Val) (Just t2Val))
  watch c $ \(TyApp mT1Val mT2Val) -> do
    maybe (return ()) (write t1Cell) mT1Val
    maybe (return ()) (write t2Cell) mT2Val

withCell :: Propagated a => (Cell s a -> ST s ()) -> ST s (Cell s a)
withCell f = do
  x <- cell
  f x
  return x

withCell' :: Propagated a => (Cell s a -> ST s (ST s ())) -> ST s (Cell s a)
withCell' f = withCell (join . f)

main :: IO ()
main = do
  -- we want this typechecking to fail
  print $ runST $ do
    a <- withCell' $ \a -> tyFVar <$> known "a" <*> pure a
    a' <- withCell' $ \a' -> tyFVar <$> known "a" <*> pure a'

    unify a a'

    (,) <$> content a <*> content a'

  print $ runST $ do
    [c1, c2] <- replicateM 2 cell
    a <- withCell' $ \a -> tyFVar <$> known "a" <*> pure a
    b <- withCell' $ \b -> tyFVar <$> known "b" <*> pure b

    x <- withCell $ \x -> tyApp a c1 x
    y <- withCell $ \y -> tyApp c2 b y

    unify x y
    (,) <$> content x <*> content y
