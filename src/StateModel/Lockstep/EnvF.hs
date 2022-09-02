{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}

{-# OPTIONS_GHC -Wall -Wredundant-constraints #-}

-- | Environment parameterised by functor @f@
--
-- Intended for qualified import:
--
-- > import StateModel.Lockstep.EnvF (EnvF)
-- > import StateModel.Lockstep.EnvF qualified as EnvF
module StateModel.Lockstep.EnvF (
    EnvF -- opaque
    -- * Construction
  , empty
  , insert
    -- * Query
  , lookup
  , keysOfType
  ) where

import Prelude hiding (lookup)

import Control.Monad
import Data.Foldable (asum)
import Data.Maybe (mapMaybe)
import Data.Typeable

import Test.QuickCheck.StateModel (Var(..))

{-------------------------------------------------------------------------------
  Types
-------------------------------------------------------------------------------}

data EnvEntry f where
  EnvEntry :: (Typeable a, Show (f a)) => Var a -> f a -> EnvEntry f

deriving instance Show (EnvEntry f)

newtype EnvF f = EnvF [EnvEntry f]
  deriving (Show)

{-------------------------------------------------------------------------------
  Construction
-------------------------------------------------------------------------------}

empty :: EnvF f
empty = EnvF []

insert :: (Typeable a, Show (f a)) => Var a -> f a -> EnvF f -> EnvF f
insert x fa (EnvF env) = EnvF (EnvEntry x fa : env)

{-------------------------------------------------------------------------------
  Query
-------------------------------------------------------------------------------}

lookup :: forall f a.
     (Typeable f, Typeable a)
  => Var a -> EnvF f -> Maybe (f a)
lookup = \var (EnvF env) ->
    asum $ map (\(EnvEntry var' fa') -> aux var var' fa') env
  where
    aux :: Typeable a' => Var a -> Var a' -> f a' -> Maybe (f a)
    aux (Var x) (Var y) fa' = do
        guard (x == y)
        cast fa'

keysOfType :: forall proxy f a. Typeable a => proxy a -> EnvF f -> [Var a]
keysOfType _ (EnvF env) = mapMaybe (\(EnvEntry var _) -> cast var) env
