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
  , MockEnv
    -- * Default implementations for methods of 'StateModel'
  , StateModel.Lockstep.initialState
  , StateModel.Lockstep.nextState
  , StateModel.Lockstep.precondition
  , StateModel.Lockstep.postcondition
  ) where

import Data.Kind

import Test.QuickCheck.StateModel

import StateModel.Lockstep.EnvOf (EnvOf)
import StateModel.Lockstep.EnvOf qualified as EnvOf

{-------------------------------------------------------------------------------
  Lockstep
-------------------------------------------------------------------------------}

data Lockstep state = Lockstep {
      lockstepModel :: state
    , lockstepEnv   :: MockEnv state
    }
  deriving (Show)

type LockstepAction state = Action (Lockstep state)

class
     ( StateModel (Lockstep state)
     , forall a. Eq   (Observable state a)
     , forall a. Show (Observable state a)
     )
  => InLockstep state where
  -- | Type of errors
  --
  -- These are errors as defined in the model. The real system will need to
  -- reflect exceptions and other errors as these model errors.
  type MockError state :: Type

  -- | Values in the mock environment
  --
  -- Consider the type of 'nextState':
  --
  -- > nextState :: state -> Action state a -> Var a -> state
  --
  -- Type @a@ will record the type of the system under test; for example, it
  -- might refer to IO handles. In the model, however, we want to record the
  -- corresponding /mock/ handles. 'MockValue' witnesses this mapping.
  data MockValue state a

  -- | Observable responses
  --
  -- We want to verify that the system under test and the model agree, but we
  -- don't want to insist that they agree on /everything/. For example,
  -- the real system might return an IO handle, where the model returns a mock
  -- handle. We should not try to compare these. 'Observable' witnesses the
  -- relation between actual results and observable results.
  data Observable state a

  -- | Extract the observable part of a response from the system under test
  --
  -- See also 'Observable'
  observe ::
       LockstepAction state a
    -> a
    -> Observable state a

  -- | Run an action against the model
  runModel ::
        MockEnv state
     -> LockstepAction state a
     -> state
     -> ((Observable state a, Maybe (Var a -> MockEnv state)), state)

  -- | All variables required by a command
  usedVars :: LockstepAction state a -> [Any Var]

type MockEnv state = EnvOf (MockError state) (MockValue state)

{-------------------------------------------------------------------------------
  Internal auxiliary
-------------------------------------------------------------------------------}

modelResponse ::
     InLockstep state
  => Lockstep state
  -> LockstepAction state a
  -> Observable state a
modelResponse (Lockstep state env) action =
    fst . fst $ runModel env action state

{-------------------------------------------------------------------------------
  Default implementations for members of 'StateModel'
-------------------------------------------------------------------------------}

initialState :: state -> Lockstep state
initialState state = Lockstep {
      lockstepModel = state
    , lockstepEnv   = EnvOf.empty
    }

nextState :: forall state a.
     InLockstep state
  => Lockstep state
  -> LockstepAction state a
  -> Var a
  -> Lockstep state
nextState (Lockstep state env) action var =
    case mEnv' of
      Nothing   -> Lockstep state' $ env
      Just env' -> Lockstep state' $ env' var
  where
    mEnv' :: Maybe (Var a -> EnvOf (MockError state) (MockValue state))
    state'     :: state
    ((_modelResp, mEnv'), state') = runModel env action state

precondition ::
     InLockstep state
  => Lockstep state -> LockstepAction state a -> Bool
precondition (Lockstep _ env) =
    all (EnvOf.member env) . usedVars

postcondition ::
     InLockstep state
  => Lockstep state -> LockstepAction state a -> LookUp -> a -> Maybe String
postcondition state action _lookUp a =
    compareEquality (observe action a) (modelResponse state action)
  where
    compareEquality :: (Eq a, Show a) => a -> a -> Maybe String
    compareEquality real mock
      | real == mock = Nothing
      | otherwise    = Just $ concat [
            "System under test returned "
          , show real
          , " but model returned "
          , show mock
          ]

