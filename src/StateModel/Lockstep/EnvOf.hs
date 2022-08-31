{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}

{-# OPTIONS_GHC -Wall #-}

-- | Environments with support for errors
--
--  One of the key datatypes in quickcheck-dynamic is the 'Action' GADT, which
--  represents the commands that we can execute in tests. The type index to
--  action indicates the result @a@ of each command. If our commands can return
--  errors, than that @a@ will reflect that possibility. It is important that it
--  does, because this is what allows us to verify the response in the
--  postcondition:
--
--  > postcondition :: state -> Action state a -> LookUp -> a -> Bool
--
--  Notice that we get an @a@ here: the result of running the command. We want
--  to compare that result against the model implementation, /including errors/.
--
--  This all makes sense, but becomes problematic when dealing with references
--  to the results of previous commands. Consider the type of 'nextState':
--
--  > nextState :: state -> Action state a -> Var a -> state
--
--  This is intended to compute an action against the model state, and is given
--  a variable that we can use to refer back to the result of the action in
--  later actions. In the case that the action can fail, that @a@ will
--  be of the form @Either Err ..@, but we don't want to record the results of
--  failed actions! Indeed, we want to exclude that possibility in the 'Action'
--  GADT itself. We want to write, say
--
--  > data Action State a where
--  >   Open  :: File -> Action State (Either Err IO.Handle)
--  >   Close :: Var IO.Handle -> Action State (Either Err ())
--
--  rather than
--
--  > data Action State a where
--  >   Open  :: File -> Action State (Either Err IO.Handle)
--  >   Close :: Var (Either Err IO.Handle) -> Action State (Either Err ())
--
--  We deal with this disconnect here: a variable of type @Either e a@ will have
--  an associated value of type @f a@. The generalization over a type
--  constructor @f@ is independent of the support for errors.
--
-- Intended for qualified import.
--
-- > import StateModel.Lockstep.EnvOf (EnvOf)
-- > import StateModel.Lockstep.EnvOf qualified as EnvOf
module StateModel.Lockstep.EnvOf (
    -- * Environments with support for errors
    EnvOf -- opaque
    -- ** Construction
  , empty
  , insert
    -- ** Query
  , lookup
  , keysOfType
  , member
  ) where

import Prelude hiding (lookup)

import Control.Monad
import Data.Foldable (asum)
import Data.Maybe (mapMaybe)
import Data.Typeable

import Test.QuickCheck.StateModel

{-------------------------------------------------------------------------------
  Types
-------------------------------------------------------------------------------}

data EnvOfEntry e f where
  EnvOfEntry ::
       (Show (f a), Typeable a)
    => Var (Either e a) -> f a -> EnvOfEntry e f

deriving instance Show (EnvOfEntry e f)

newtype EnvOf e f = EnvOf [EnvOfEntry e f]
  deriving (Show)

{-------------------------------------------------------------------------------
  Construction

  IMPLEMENTATION NOTE: 'Var' is just a newtype around an 'Int'. It does not
  itself carry any type information.
-------------------------------------------------------------------------------}

empty :: EnvOf e f
empty = EnvOf []

-- | Extend the environment
--
-- When we /extend/ the environment with the result of an execution action, we
-- get a variable that reflects the possibility of failure in its type.
--
-- Of course, we can only
insert ::
     (Show (f a), Typeable a)
  => Var (Either e a) -> f a -> EnvOf e f -> EnvOf e f
insert var fa (EnvOf env) = EnvOf (EnvOfEntry var fa : env)

{-------------------------------------------------------------------------------
  Query
-------------------------------------------------------------------------------}

-- | Lookup a variable in the environment
--
-- When we /look up/ a variable, we want to /exclude/ the possibility of
-- failure.
lookup :: forall a e f.
     (Typeable f, Typeable a)
  => Var a -> EnvOf e f -> Maybe (f a)
lookup (Var x) (EnvOf env) =
    asum $ map (\(EnvOfEntry var' a) -> aux var' a) env
  where
    aux :: forall a'. Typeable a' => Var (Either e a') -> f a' -> Maybe (f a)
    aux (Var x') fa' = do
        guard (x == x')
        cast fa'

-- | All variables with the given type
--
-- We use this to generate the inputs actions, and hence want to exclude the
-- possibility of failure, like in 'lookUpEnvOf'.
keysOfType :: forall a e f. Typeable a => Proxy a -> EnvOf e f -> [Var a]
keysOfType _ (EnvOf env) =
    mapMaybe (\(EnvOfEntry var _) -> aux var) env
  where
    aux :: forall a'. Typeable a' => Var (Either e a') -> Maybe (Var a)
    aux (Var x) = do
        guard $ typeOf (Proxy @a) == typeOf (Proxy @a')
        return $ Var x

-- | Check that all the given variables are in the domain of the environment
--
-- We use this to verify that all the arguments to actions can be looked up.
member :: forall e f. EnvOf e f -> Any Var -> Bool
member (EnvOf env) = \case
    Error _  -> False
    Some var -> any (\(EnvOfEntry var' _) -> aux var var') env
  where
    aux :: forall a a'.
         (Typeable a, Typeable a')
      => Var a -> Var (Either e a') -> Bool
    aux (Var x) (Var x') = and [
          x == x'
        , typeOf (Proxy @a) == typeOf (Proxy @a')
        ]

