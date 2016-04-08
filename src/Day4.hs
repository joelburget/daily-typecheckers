-- just variants, records, functions
module Day4 where

type RecordDesc = [
  ( String -- name
  , Desc -- what it points to
  )
  ]

-- wow it looks the same as RecordDesc :P
type VariantDesc = [(String, Desc)]

data FunDesc = Arrow Desc Desc
  deriving (Show, Eq)

data Desc
  = DescRecord RecordDesc
  | DescVariant VariantDesc
  | DescFun FunDesc
  | Param Int
  deriving (Show, Eq)

list :: Desc
list = DescVariant
  [ ("listNil", DescRecord [])
  --                                      v- `a`                 v- `self`
  , ("listCons", DescRecord [("listHead", Param 0), ("listTail", Param 1)])
  ]

-- that gives us sums, products, and exponentials
--
-- now, to instantiate, typecheck, and eliminate (pattern match / execute) them

-- Match against the alternatives in a sum
type VariantMatch = [(String, Match, Data)]

-- Match a product (whoa, we just pairwise match)
type RecordPattern = [Match]

data Match
  = MatchVariant VariantMatch
  | MatchRecord RecordPattern
  | MatchWildcard
  | MatchVariable

--

type Record = [(String, Data)]
type Variant = (String, Data)

-- we need pattern match the argument and emit Data
data Fun = Fun Match Data

data Data
  = DataRecord Record
  | DataVariant Variant
  | DataFun Fun

data tm :<: ty = tm :<: ty  deriving (Show, Eq)
infix 4 :<:

-- TODO typechecking
check :: Data :<: Desc -> Bool
check (DataRecord r :<: DescRecord rd) = undefined
check (DataVariant v :<: DescVariant vd) = undefined
check (DataFun f :<: DescFun fd) = undefined
check (_ :<: Param _) = undefined
check _ = False

-- TODO eliminators are significantly more work
