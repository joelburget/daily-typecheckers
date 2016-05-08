-- Reflection, reification, evalation, normalization
module Day19 where

import Control.Monad.Reader
import Control.Monad.Gen
import qualified Data.Map as Map

-- An easily evaluated HOAS syntax
data Hoas
  = HLam String (Hoas -> Hoas)
  | HApp Hoas Hoas
  | HBase String

  -- exotic
  | HGen Int

-- An easily written nominal syntax
data Nom
  = NLam String Nom
  | NApp Nom Nom
  | NVar String
  | NBase String
  deriving Show


eval :: Hoas -> Hoas
eval t = case t of
  HGen _ -> error "unexpected HGen in eval"
  HBase _ -> t
  HApp (HLam _ f) x -> f x
  _ -> t

reflect :: Nom -> Hoas
reflect t = runReader (reflect' t) Map.empty

reflect' :: Nom -> Reader (Map.Map String Hoas) Hoas
reflect' t = case t of
  NLam name body -> do
    table <- ask
    return $ HLam name $ \subst ->
      runReader (reflect' body) (Map.insert name subst table)
  NApp t1 t2 -> HApp <$> reflect' t1 <*> reflect' t2
  NVar name -> reader (Map.! name)
  NBase str -> return $ HBase str

reify :: Hoas -> Nom
reify t = runGen (runReaderT (reify' t) Map.empty)

reify' :: Hoas -> ReaderT (Map.Map Int Nom) (Gen Int) Nom
reify' t = case t of
  HLam name f -> do
    ident <- gen
    nom <- local (Map.insert ident (NVar name)) $ reify' $ f (HGen ident)
    return $ NLam name nom
  HGen ident -> (Map.! ident) <$> ask
  HApp t1 t2 -> NApp <$> reify' t1 <*> reify' t2
  HBase str -> return $ NBase str

normalize :: Nom -> Nom
normalize = reify . eval . reflect


main :: IO ()
main = do
  let nomTm = NLam "f" (NApp (NVar "f") (NBase "xyz"))
  print (reify (reflect nomTm))
  print (normalize nomTm)

  let nomId = NLam "x" (NVar "x")
  let nomTm2 = NApp nomId (NBase "xyz")
  print (reify (reflect nomTm2))
  print (normalize nomTm2)

  let nomTm3 = NApp nomId nomId
  print (reify (reflect nomTm3))
  print (normalize nomTm3)
