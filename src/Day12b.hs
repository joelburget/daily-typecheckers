{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Day12b where

import Control.Lens
import Control.Monad
import Control.Monad.ST
import Data.Propagator
import Data.Propagator.Cell

-- let's start with a simple two-level stratification

-- XXX can't store cells in a cell!
data Term
  = BVar (Maybe Int) (Maybe Type)
  | FVar (Maybe String) (Maybe Type)
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

-- | Write only when the cell is not @Nothing@.
write' :: Maybe a -> Cell s a -> ST s ()
write' val cell = maybe (return ()) (write cell) val

bVar :: Cell s Int -> Cell s Type -> ST s (Cell s Term)
bVar iCell tyCell = withCell $ \c -> do
  watch iCell $ \iVal -> write c (BVar (Just iVal) Nothing)
  watch tyCell $ \tyVal -> write c (BVar Nothing (Just tyVal))
  watch c $ \(BVar iVal tyVal) -> do
    write' iVal iCell
    write' tyVal tyCell

fVar :: Cell s String -> Cell s Type -> ST s (Cell s Term)
fVar sCell tyCell = withCell $ \c -> do
  watch sCell $ \sVal -> write c (FVar (Just sVal) Nothing)
  watch tyCell $ \tyVal -> write c (FVar Nothing (Just tyVal))
  watch c $ \(FVar sVal tyVal) -> do
    write' sVal sCell
    write' tyVal tyCell

abs :: Cell s Term -> Cell s Type -> ST s (Cell s Term)
abs tmCell tyCell = withCell $ \c -> do
  watch tmCell $ \tmVal -> write c (Abs (Just tmVal) Nothing)
  watch tyCell $ \tyVal -> write c (Abs Nothing (Just tyVal))
  watch c $ \(Abs tmVal tyVal) -> do
    write' tmVal tmCell
    write' tyVal tyCell

app :: Cell s Term -> Cell s Term -> Cell s Type -> ST s (Cell s Term)
app t1Cell t2Cell tyCell = withCell $ \c -> do
  watch t1Cell $ \t1Val -> write c (App (Just t1Val) Nothing Nothing)
  watch t2Cell $ \t2Val -> write c (App Nothing (Just t2Val) Nothing)
  watch tyCell $ \tyVal -> write c (App Nothing Nothing (Just tyVal))

  watch c $ \(App t1Val t2Val tyVal) -> do
    write' tyVal tyCell
    write' t1Val t1Cell
    write' t2Val t2Cell

data Type
  = TyFVar String
  | TyApp (Maybe Type) (Maybe Type)
  -- | Type
  deriving Show

_TyApp1 :: Prism' Type Type
_TyApp1 = prism'
  (\x -> TyApp (Just x) Nothing)
  (\(TyApp x _) -> x)

_TyApp2 :: Prism' Type Type
_TyApp2 = prism'
  (\x -> TyApp Nothing (Just x))
  (\(TyApp _ x) -> x)

instance Propagated Type where
  merge (TyFVar s1) (TyFVar s2) =
    TyFVar <$> merge s1 s2
  merge (TyApp t11 t12) (TyApp t21 t22) =
    TyApp <$> merge t11 t21 <*> merge t12 t22
  merge _ _ = Contradiction mempty "type merge"

tyFVar :: Cell s String -> ST s (Cell s Type)
tyFVar sCell = withCell $ \c -> do
  watch sCell $ \sVal -> write c (TyFVar sVal)
  watch c $ \(TyFVar sVal) -> write sCell sVal

tyApp' :: Cell s Type -> Cell s Type -> ST s (Cell s Type)
tyApp' t1Cell t2Cell = withCell $ \c -> do
  link' c _TyApp1 t1Cell
  link' c _TyApp2 t2Cell

link' :: Cell s a -> Prism' a b -> Cell s b -> ST s ()
link' outer prism inner = do
  watch outer $ \outerVal -> write' (outerVal ^? prism) inner
  watch inner $ \innerVal -> write outer (innerVal ^. re prism)

tyApp :: Cell s Type -> Cell s Type -> ST s (Cell s Type)
tyApp t1Cell t2Cell = withCell $ \c -> do
  watch t1Cell $ \t1Val -> write c (TyApp (Just t1Val) Nothing)
  watch t2Cell $ \t2Val -> write c (TyApp Nothing (Just t2Val))
  watch c $ \(TyApp t1Val t2Val) -> do
    write' t1Val t1Cell
    write' t2Val t2Cell

withCell :: Propagated a => (Cell s a -> ST s ()) -> ST s (Cell s a)
withCell f = do
  x <- cell
  f x
  return x

withCell' :: Propagated a => (Cell s a -> ST s (ST s ())) -> ST s (Cell s a)
withCell' f = withCell (join . f)

main :: IO ()
main = do
  print $ runST $ do
    a <- join $ tyFVar <$> known "a"
    a' <- join $ tyFVar <$> known "a"

    unify a a'

    (,) <$> content a <*> content a'

  print $ runST $ do
    [c1, c2] <- replicateM 2 cell
    a <- join $ tyFVar <$> known "a"
    b <- join $ tyFVar <$> known "b"

    x <- tyApp' a c1
    y <- tyApp' c2 b

    unify x y
    (,) <$> content x <*> content y
