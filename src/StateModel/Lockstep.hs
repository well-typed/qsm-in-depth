{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall #-}

-- | Lockstep-style testing using @quickcheck-dynamic@
--
-- Intended for qualified import.
--
-- > import StateModel.Lockstep (Lockstep(..))
-- > import StateModel.Lockstep qualified as Lockstep
module StateModel.Lockstep (
    InLockstep(..)
  , Lockstep(..)
  , LockstepAction
  , ModelVar
  , ModelLookUp
  , ModelFindVariables
    -- * Default implementations for methods of 'StateModel'
  , StateModel.Lockstep.initialState
  , StateModel.Lockstep.nextState
  , StateModel.Lockstep.precondition
  , StateModel.Lockstep.postcondition
  , StateModel.Lockstep.arbitraryAction
    -- * Utilities for running the tests
  , propLockstep
  ) where

import Control.Monad
import Data.Kind
import Data.Typeable

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.QuickCheck.StateModel

import StateModel.Lockstep.EnvF (EnvF)
import StateModel.Lockstep.EnvF qualified as EnvF
import StateModel.Lockstep.GVar (GVar, InterpretOp)
import StateModel.Lockstep.GVar qualified as GVar

{-------------------------------------------------------------------------------
  Lockstep
-------------------------------------------------------------------------------}

data Lockstep state = Lockstep {
      lockstepModel :: state
    , lockstepEnvF  :: EnvF (ModelValue state)
    }
  deriving (Show)

class
     ( StateModel (Lockstep state)
     , Typeable state
     , InterpretOp (ModelVarOp state) (ModelValue state)
     , forall a. Show (ModelValue state a)
     , forall a. Eq   (Observable state a)
     , forall a. Show (Observable state a)
     )
  => InLockstep state where

  -- | Type of operations required on the results of actions
  --
  -- Whenever an action has a result of type @a@, but we later need a variable
  -- of type @b@, we need a constructor
  --
  -- > GetB :: ModelVarOp state a b
  --
  -- in the 'ModelVarOp' type. For many tests, the standard 'Op' type will
  -- suffice, but not always.
  type ModelVarOp state :: Type -> Type -> Type

  -- | Values in the mock environment
  --
  -- 'ModelValue' witnesses the relation between values returned by the real
  -- system and values returned by the model.
  --
  -- In most cases, we expect the real system and the model to return the
  -- /same/ value. However, for some things we must allow them to diverge:
  -- consider file handles for example.
  data ModelValue state a

  -- | Observable responses
  --
  -- The real system returns values of type @a@, and the model returns values
  -- of type @MockValue a@. @Observable a@ defines the parts of those results
  -- that expect to be the /same/ for both.
  data Observable state a

  -- | Extract the observable part of a response from the system under test
  --
  -- See also 'Observable'
  observeReal :: LockstepAction state a -> a -> Observable state a

  -- | Extract the observable part of a response from the model
  observeModel :: ModelValue state a-> Observable state a

  -- | All variables required by a command
  usedVars :: LockstepAction state a -> [Any (ModelVar state)]

  -- | Step the model
  modelNextState ::
       ModelLookUp state
    -> LockstepAction state a
    -> state
    -> (ModelValue state a, state)

  arbitraryActionWithVars ::
       ModelFindVariables state
    -> state
    -> Gen (Any (LockstepAction state))

-- | An action in the lock-step model
type LockstepAction state = Action (Lockstep state)

-- | Variables with a "functor-like" instance
type ModelVar state = GVar (ModelVarOp state)

-- | Look up a variable for model execution
--
-- The type of the variable is the type in the /real/ system.
type ModelLookUp state = forall a.
          Typeable a
       => ModelVar state a -> ModelValue state a

-- | Pick variable of the appropriate type
--
-- This is used when generation actions. The type you pass must be the result
-- type of (previously executed) actions.
--
-- If you want to @fmap@ (in quotes..) over the type of that variable, see
-- 'StateModel.Lockstep.GVar.map'.
type ModelFindVariables state = forall proxy a.
          Typeable a
       => proxy a -> Maybe (Gen (GVar (ModelVarOp state) a))

{-------------------------------------------------------------------------------
  Internal auxiliary
-------------------------------------------------------------------------------}

-- | Think wrapper around 'modelNextState' that constructs the lookup function
modelNextState' :: forall state a.
     InLockstep state
  => Lockstep state
  -> LockstepAction state a
  -> (ModelValue state a, state)
modelNextState' (Lockstep state env) action =
    modelNextState modelLookUp action state
  where
    modelLookUp :: ModelLookUp state
    modelLookUp x =
        case GVar.lookUpEnvF x env of
          Left  err -> error err -- Ruled out by the precondition
          Right val -> val

-- | Thin wrapper around 'monadicIO' that allows a separate initialation step
--
-- This is useful when testing stateful code that requires a single setup
-- call before the tests are run (the initializer will be run for every test,
-- including for every shrunk test).
monadicInit :: Testable b => IO a -> (a -> PropertyM IO b) -> Property
monadicInit initState prop = monadicIO $ run initState >>= prop

{-------------------------------------------------------------------------------
  Default implementations for members of 'StateModel'
-------------------------------------------------------------------------------}

-- | Default implementation for 'Test.QuickCheck.StateModel.initialState'
initialState :: state -> Lockstep state
initialState state = Lockstep {
      lockstepModel = state
    , lockstepEnvF  = EnvF.empty
    }

-- | Default implementation for 'Test.QuickCheck.StateModel.nextState'
nextState :: forall state a. (InLockstep state, Typeable a)
  => Lockstep state
  -> LockstepAction state a
  -> Var a
  -> Lockstep state
nextState st@(Lockstep _ env) action var =
     Lockstep state' (EnvF.insert var modelResp env)
  where
    modelResp :: ModelValue state a
    state'    :: state
    (modelResp, state') = modelNextState' st action

-- | Default implementation for 'Test.QuickCheck.StateModel.precondition'
--
-- The default precondition only checks that all variables have a value
-- and that the operations on them are defined.
precondition ::
     InLockstep state
  => Lockstep state -> LockstepAction state a -> Bool
precondition (Lockstep _ env) = all (GVar.definedInEnvF env) . usedVars

-- | Default implementation for 'Test.QuickCheck.StateModel.postcondition'
--
-- The default postcondition verifies that the real system and the model
-- return the same results, up to " observability ".
postcondition :: forall state a.
     InLockstep state
  => Lockstep state -> LockstepAction state a -> LookUp -> a -> Maybe String
postcondition st action _lookUp a =
    compareEquality (observeReal action a) (observeModel modelResp)
  where
    modelResp :: ModelValue state a
    modelResp = fst $ modelNextState' st action

    compareEquality ::  Observable state a -> Observable state a -> Maybe String
    compareEquality real mock
      | real == mock = Nothing
      | otherwise    = Just $ concat [
            "System under test returned "
          , show real
          , " but model returned "
          , show mock
          ]

-- | Default implementation for 'Test.QuickCheck.StateModel.arbitraryAction'
arbitraryAction :: forall state.
     InLockstep state
  => Lockstep state -> Gen (Any (LockstepAction state))
arbitraryAction (Lockstep state env) =
    arbitraryActionWithVars findVars state
  where
    findVars :: Typeable a => proxy a -> Maybe (Gen (GVar (ModelVarOp state) a))
    findVars p =
        case EnvF.keysOfType p env of
          [] -> Nothing
          xs -> Just $ elements (map GVar.fromVar xs)

{-------------------------------------------------------------------------------
  Utilities for running the tests
-------------------------------------------------------------------------------}

-- | Run the test
--
-- This is a thin wrapper around 'runActions' that allows for a separate
-- state initialization step.
propLockstep ::
     StateModel state
  => IO st
  -> (st -> RunModel state IO)
  -> Actions state -> Property
propLockstep initState runner actions =
    monadicInit initState $ \st ->
      void $ runActions (runner st) actions
