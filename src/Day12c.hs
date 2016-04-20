{-# LANGUAGE PatternSynonyms #-}
module Day12c where

import Control.Monad.ST

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product

import Data.Propagator
import Data.Propagator.Cell
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map

data Term a
  = BVarT Int
  | FVarT String
  | AbsT a
  | AppT a a
  | AnnotT a a
  | TypeT
  deriving (Show, Eq, Functor)

data PartialF a
  = KnownF a
  | UnknownF
  deriving (Show, Eq, Functor)

newtype Fix f = Fix (f (Fix f))

type TypedPartialTermF = Compose PartialF (Product Identity Term)
type TypedPartialTerm = Fix TypedPartialTermF

-- type Typing a = (IntMap a, Map.Map String a, a)
-- newtype TypedPartialTerm = TypedPartialTerm (Typing PartialTerm)

pattern Unknown = Fix (Compose (InL UnknownF))
pattern Boilerplate x = Fix (Compose (InR (Pair (
pattern BVar i = Fix (Compose (Pair TypeT (BVarT i)))

-- pattern BVar i = TotalTerm (BVarT i)
-- pattern FVar s = TotalTerm (FVarT s)
-- pattern Abs t = TotalTerm (AbsT t)
-- pattern App t1 t2 = TotalTerm (AppT t1 t2)
-- pattern Annot tm ty = TotalTerm (AnnotT tm ty)
-- pattern Type = TotalTerm TypeT
