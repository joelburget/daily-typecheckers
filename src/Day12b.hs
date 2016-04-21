{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
module Day12b where

import Control.Monad.ST
import Data.Maybe (isJust)
import Data.Propagator
import Data.Propagator.Cell

-- let's start with a simple two-level stratification

-- XXX can't store cells in a cell!
data Term
  = BVar Int (Maybe Type)
  | FVar String (Maybe Type)
  | Abs (Maybe Term) (Maybe Type)
  | App (Maybe Term) (Maybe Term) (Maybe Type)
  -- | Annot (TypeCell s) (TermCell s)
  -- | Type

bVar :: Cell s Int -> Cell s Type -> Cell s Term -> ST s ()
bVar iCell tyCell cell = do
  watch iCell $ \iVal ->
    with tyCell $ \tyVal ->
      write cell (BVar iVal (Just tyVal))
  watch tyCell $ \tyVal ->
    with iCell $ \iVal ->
      write cell (BVar iVal (Just tyVal))
  watch cell $ \(BVar iVal mTyVal) -> do
    write iCell iVal
    maybe (return ()) (write tyCell) mTyVal

fVar :: Cell s String -> Cell s Type -> Cell s Term -> ST s ()
fVar sCell tyCell cell = do
  watch sCell $ \sVal ->
    with tyCell $ \tyVal ->
      write cell (FVar sVal (Just tyVal))
  watch tyCell $ \tyVal ->
    with sCell $ \sVal ->
      write cell (FVar sVal (Just tyVal))
  watch cell $ \(FVar sVal mTyVal) -> do
    write sCell sVal
    maybe (return ()) (write tyCell) mTyVal

abs :: Cell s Term -> Cell s Type -> Cell s Term -> ST s ()
abs tmCell tyCell cell = do
  watch tmCell $ \tmVal ->
    with tyCell $ \tyVal ->
      write cell (Abs (Just tmVal) (Just tyVal))
  watch tyCell $ \tyVal ->
    with tmCell $ \tmVal ->
      write cell (Abs (Just tmVal) (Just tyVal))
  watch cell $ \(Abs mTmVal mTyVal) -> do
    maybe (return ()) (write tmCell) mTmVal
    maybe (return ()) (write tyCell) mTyVal

app :: Cell s Term -> Cell s Term -> Cell s Type -> Cell s Term -> ST s ()
app t1Cell t2Cell tyCell cell = do
  watch t1Cell $ \t1Val ->
    with t2Cell $ \t2Val ->
      with tyCell $ \tyVal ->
        write cell (App (Just t1Val) (Just t2Val) (Just tyVal))
  watch t2Cell $ \t2Val ->
    with t1Cell $ \t1Val ->
      with tyCell $ \tyVal ->
        write cell (App (Just t1Val) (Just t2Val) (Just tyVal))

  watch tyCell $ \tyVal ->
    with t1Cell $ \t1Val ->
      with t2Cell $ \t2Val ->
        write cell (App (Just t1Val) (Just t2Val) (Just tyVal))

  watch cell $ \(App mT1Val mT2Val mTyVal) -> do
    maybe (return ()) (write t1Cell) mT1Val
    maybe (return ()) (write t2Cell) mT2Val
    maybe (return ()) (write tyCell) mTyVal

data Type
  = TyFVar String
  | TyApp (Maybe Type) (Maybe Type)
  -- | Type

tyFVar :: Cell s String -> Cell s Type -> ST s ()
tyFVar sCell cell = do
  watch sCell $ \sVal ->
    write cell (TyFVar sVal)
  watch cell $ \(TyFVar sVal) ->
    write sCell sVal


tyApp :: Cell s Type -> Cell s Type -> Cell s Type -> ST s ()
tyApp t1Cell t2Cell cell = do
  watch t1Cell $ \t1Val ->
    with t2Cell $ \t2Val ->
      write cell (TyApp (Just t1Val) (Just t2Val))
  watch t2Cell $ \t2Val ->
    with t1Cell $ \t1Val ->
      write cell (TyApp (Just t1Val) (Just t2Val))
  watch cell $ \(TyApp mT1Val mT2Val) -> do
    maybe (return ()) (write t1Cell) mT1Val
    maybe (return ()) (write t2Cell) mT2Val

-- just check whether term's TypeCell merges with the given TypeCell
typecheck :: forall s. Cell s (Term, Type)
          -> Cell s Type
          -- XXX I don't think we should have another cell, just reject!
          -> Cell s Bool
          -> ST s ()
typecheck tmCell tyCell result = do
  maybeTm <- content tmCell
  resultVal <- case maybeTm of
    Just (_, tyCell') -> do
      unify tyCell tyCell'
      isJust <$> content tyCell
    Nothing -> return False
  write result resultVal

mkTm :: Term -> ST s (Cell s (Term, Type))
mkTm tm = do
  tmCell <- known (tm, Nothing)
  return tmCell

main :: IO ()
main =
  putStrLn "here"

--   -- we want this typechecking to fail
--   print $ runST $ do
--     a <- known $ TyFVar "a"
--     b <- known $ TyFVar "b"
--     app <- known $ TyApp a b
--     x <- mkTm $ FVar "x"
--     tm <- mkTm $ Annot app x
--     a' <- mkTm $ TyFVar "a"
--     result <- cell
--     typecheck tm a' result
--     content result
