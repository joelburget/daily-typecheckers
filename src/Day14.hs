{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Day14 where

import Control.Lens
import Control.Monad
import Control.Monad.ST
import qualified Data.Map as Map
import Data.Propagator
import Data.Propagator.Cell


-- boilerplate!

link' :: Cell s a -> Prism' a b -> Cell s b -> ST s ()
link' outer prism inner = do
  watch outer $ \outerVal -> write' (outerVal ^? prism) inner
  watch inner $ \innerVal -> write outer (innerVal ^. re prism)

-- | Write only when the cell is not @Nothing@.
write' :: Maybe a -> Cell s a -> ST s ()
write' val cell = maybe (return ()) (write cell) val

withCell :: Propagated a => (Cell s a -> ST s ()) -> ST s (Cell s a)
withCell f = do
  x <- cell
  f x
  return x


-- orphans!

instance Propagated a => Propagated (Maybe a) where
  merge (Just a) (Just b) = Just <$> merge a b
  merge a@(Just _) Nothing = Change False a
  merge Nothing b@(Just _) = Change True b
  merge n _ = Change False n

instance Propagated String where

-- instance (Propagated v, Eq v, Show v) => Propagated (Map.Map String v) where
instance (Propagated v) => Propagated (Map.Map String v) where
  merge l r = do
    let isect = Map.intersectionWith merge l r
        lOnly = Map.difference l r
        rOnly = Map.difference r l
    isect' <- sequence isect
    return $ Map.unions [isect', lOnly, rOnly]


-- terms

data SubTerm
  = SubInt { unSubInt :: Int }
  | SubString { unSubString :: String }
  | SubType { unSubType :: Type }
  | SubTerm { unSubTerm :: Term }
  deriving (Eq, Show)

instance Propagated SubTerm where
  merge (SubInt l) (SubInt r) = SubInt <$> merge l r
  merge (SubString l) (SubString r) = SubString <$> merge l r
  merge (SubType l) (SubType r) = SubType <$> merge l r
  merge (SubTerm l) (SubTerm r) = SubTerm <$> merge l r
  merge _ _ = Contradiction mempty "subterm merge"

-- TODO could probably make this safer with a GADT:
--
-- varName :: Prism (Term FVar) String
data TermZ
  = BVar -- Int Type
  | FVar -- String Type
  | Abs -- Term Type
  | App -- Term Term Type
  | Type
  deriving (Eq, Show)

instance Propagated TermZ where
  merge BVar BVar = Change False BVar
  merge FVar FVar = Change False FVar
  merge Abs Abs = Change False Abs
  merge App App = Change False App
  merge Type Type = Change False Type
  merge _ _ = Contradiction mempty "term merge"

normalize :: Cell s Term -> ST s ()
normalize = normalize' []

normalize' :: [Cell s Term] -> Cell s Term -> ST s ()
normalize' ctx cell = do
  let done = return ()

  mTm <- content cell
  case mTm of
    Nothing -> done
    Just (Term tmZ subTms) -> case tmZ of
      -- we're stuck / done
      FVar -> done
      Type -> done

      -- need to substitute in
      BVar -> do
        let mLinkCell = do
              SubInt i <- subTms ^? ix "ix"
              ctx ^? ix i
        case mLinkCell of
          Nothing -> error "found over-reaching de bruijn index"
          Just linkCell -> do
            unify cell linkCell
            -- TODO: when content has changed:
            -- normalize' ctx cell
      Abs -> error "normalizing a bare Abs"
      App -> do
        SubTerm t1 <- subTms ^? ix "t1"
        SubTerm t2 <- subTms ^? ix "t2"
        case t2 of
          (Term Abs subTms') -> do
            SubTerm subTm <- subTms' ^? ix "subTm"
            -- XXX this is a term but we're normalizing cells...
            normalize' (t1:ctx) subTm
            write cell $ subTm


data Term = Term {
  termZ :: TermZ,
  subTerms :: Map.Map String SubTerm
  } deriving Eq

instance Show Term where
  showsPrec prec (Term termZ subTerms) = showParen (prec > 10) $
    shows termZ . showString " " . shows subTerms

type Type = Term

instance Propagated Term where
  merge (Term tag1 sub1) (Term tag2 sub2) =
    Term <$> merge tag1 tag2 <*> merge sub1 sub2


-- lenses

ty :: TermZ -> Prism' Term Type
ty tag = prism'
  (\subTy -> Term tag (Map.singleton "ty" (SubType subTy)))
  (\tm -> unSubType <$> Map.lookup "ty" (subTerms tm))

varName :: Prism' Term String
varName = prism'
  (\name -> Term FVar (Map.singleton "name" (SubString name)))
  (\tm -> unSubString <$> Map.lookup "name" (subTerms tm))

varIx :: Prism' Term Int
varIx = prism'
  (\ix -> Term BVar (Map.singleton "ix" (SubInt ix)))
  (\tm -> unSubInt <$> Map.lookup "ix" (subTerms tm))

t1 :: Prism' Term Term
t1 = prism'
  (\subT1 -> Term App (Map.singleton "t1" (SubTerm subT1)))
  (\tm -> unSubTerm <$> Map.lookup "t1" (subTerms tm))

t2 :: Prism' Term Term
t2 = prism'
  (\subT2 -> Term App (Map.singleton "t2" (SubTerm subT2)))
  (\tm -> unSubTerm <$> Map.lookup "t2" (subTerms tm))

subTm :: Prism' Term Term
subTm = prism'
  (\subTmm -> Term Abs (Map.singleton "subTm" (SubTerm subTmm)))
  (\tm -> unSubTerm <$> Map.lookup "subTm" (subTerms tm))


-- smart constructors

fVar :: Cell s String -> ST s (Cell s Term)
fVar sCell = withCell $ \c -> link' c varName sCell

app :: Cell s Type -> Cell s Type -> ST s (Cell s Type)
app t1Cell t2Cell = withCell $ \c -> do
  link' c t1 t1Cell
  link' c t2 t2Cell

-- finally, doing stuff

main :: IO ()
main = do
  -- a ~ a => a
  print $ runST $ do
    a <- join $ fVar <$> known "a"
    a' <- join $ fVar <$> known "a"

    unify a a'

    (,) <$> content a <*> content a'

  -- a _ ~ _ b => a b
  print $ runST $ do
    [c1, c2] <- replicateM 2 cell
    a <- join $ fVar <$> known "a"
    b <- join $ fVar <$> known "b"

    x <- app a c1
    y <- app c2 b

    unify x y
    (,) <$> content x <*> content y

--   print $ runST $ do
--     app <$> (abs <$> (bVar <$> known 0)) <*> ty
--     app <$> cell <*> cell
