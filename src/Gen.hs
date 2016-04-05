-- Quick and dirty monad to generate unique numbers
module Gen where

newtype Gen a = Gen { runGen :: Int -> (Int, a) }

instance Functor Gen where
  fmap f gen = Gen $ \x ->
    let (x', a) = runGen gen x
    in (x', f a)

instance Applicative Gen where
  pure a = Gen (\x -> (x, a))
  f <*> a = Gen $ \x ->
    let (x', a') = runGen a x
        (x'', f') = runGen f x'
    in (x'', f' a')

instance Monad Gen where
  return = pure
  a >>= f = Gen $ \x ->
    let (x', a') = runGen a x
    in runGen (f a') x'

gen :: Gen Int
gen = Gen $ \x -> (x+1, x)

execGen :: Gen a -> a
execGen gen = snd $ runGen gen 0
