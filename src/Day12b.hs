{-# LANGUAGE PatternSynonyms #-}
module Day12b where

import Control.Monad.ST
import Data.Maybe (isJust)
import Data.Propagator
import Data.Propagator.Cell

-- let's start with a simple two-level stratification

-- XXX can't store cells in a cell!
data Term s
  = BVar Int
  | FVar String
  | Abs (TermCell s)
  | App (TermCell s) (TermCell s)
  | Annot (TypeCell s) (TermCell s)
  -- | Type

-- All terms carry a type, annot does so explicitly.
newtype TermCell s = TermCell (Cell s (TypeCell s, Term s))

data Type s
  = TyFVar String
  | TyApp (TypeCell s) (TypeCell s)
  -- | Type

newtype TypeCell s = TypeCell (Cell s (Type s))

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
