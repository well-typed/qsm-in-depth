{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

-- | Utilities for working with the 'StateModel' infrastructure
module StateModel.Util (
    thenGen
  , elementsOrFail
  , monadicInit
  ) where

import Test.QuickCheck
import Test.QuickCheck.StateModel
import Data.Typeable
import Data.Functor.Const
import Test.QuickCheck.Monadic

-- | Bind-like operator for generators that can fail
thenGen :: forall f g.
     Gen (Any f)
  -> (forall a. f a -> Gen (Any g))
  -> Gen (Any g)
thenGen x f = x >>= f'
  where
    f' :: Any f -> Gen (Any g)
    f' (Some fa) = f fa
    f' (Error e) = return $ Error e

-- | Take advantage of 'Any' to define a total version of 'elements'
elementsOrFail :: forall a.
     (Typeable a, Show a, Eq a)
  => [a] -> Gen (Any (Const a))
elementsOrFail [] = return $ Error "empty list"
elementsOrFail xs = Some @(Const a a) . Const <$> elements xs

-- | Thin wrapper around 'monadicIO' that allows a separate initialation step
--
-- This is useful when testing stateful code that requires a single setup
-- call before the tests are run (the initializer will be run for every test,
-- including for every shrunk test).
monadicInit :: Testable b => IO a -> (a -> PropertyM IO b) -> Property
monadicInit init prop = monadicIO $ run init >>= prop
