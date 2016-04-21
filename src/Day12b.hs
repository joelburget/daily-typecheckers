{-# LANGUAGE PatternSynonyms #-}
module Day12b where

import Control.Monad.ST
import Data.Maybe (isJust)
import Data.Propagator
import Data.Propagator.Cell

-- util

-- this starts to get expensive!
watch3 :: Cell s a -> Cell s b -> -> Cell s c -> (a -> b -> c -> ST s ()) -> ST s ()
watch3 x y z f = do
  watch2 x y $ \a b -> with z $ \c -> f a b c
  watch2 x z $ \a c -> with y $ \b -> f a b c
  watch2 y z $ \b c -> with x $ \a -> f a b c

lift3 :: (a -> b -> c) -> Cell s a -> Cell s b -> Cell s c -> ST s ()
lift3 f x y z = watch3 x y z $ \a b c -> write z (f a b c)

-- let's start with a simple two-level stratification

-- XXX can't store cells in a cell!
data Term s
  = BVar Int
  | FVar String
  | Abs Term
  | App Term Term
  -- | Annot (TypeCell s) (TermCell s)
  -- | Type

bVar :: Cell s Int -> Cell s Type -> Cell s Term
bVar = lift2 BVar

fVar :: Cell s String -> Cell s Type -> Cell s Term
fVar = lift2 FVar

abs :: Cell s Term -> Cell s Type -> Cell s Term
abs = lift2 Abs

app :: Cell s Term -> Cell s Term -> Cell s Type -> Cell s Term
app = lift3 App

data Type s
  = TyFVar String
  | TyApp (TypeCell s) (TypeCell s)
  -- | Type

tyFVar :: Cell s String -> Cell s Type
tyFVar = undefined

tyApp :: Cell s Type -> Cell s Type -> Cell s Type
tyApp = undefined

-- just check whether term's TypeCell merges with the given TypeCell
typecheck
  :: forall s.
     TermCell s
  -> TypeCell s
  -- XXX I don't think we should have another cell, just reject!
  -> Cell s Bool
  -> ST s ()
typecheck (TermCell tmCell) (TypeCell tyCell) result = do
  maybeTm <- content tmCell
  resultVal <- case maybeTm of
    Just (TypeCell tyCell', _) -> do
      unify tyCell tyCell'
      isJust <$> content tyCell
    Nothing -> return False
  write result resultVal

mkTm :: Term s -> ST s (TermCell s)
mkTm tm = do
  tyCell <- cell
  tmCell <- known (TypeCell tyCell, tm)
  return $ TermCell tmCell

main :: IO ()
main =
  -- we want this typechecking to fail
  print $ runST $ do
    a <- known $ TyFVar "a"
    b <- known $ TyFVar "b"
    app <- known $ TyApp a b
    x <- mkTm $ FVar "x"
    tm <- mkTm $ Annot app x
    a' <- mkTm $ TyFVar "a"
    result <- cell
    typecheck tm a' result
    content result
