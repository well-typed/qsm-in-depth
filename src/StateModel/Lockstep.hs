{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Wredundant-constraints #-}

-- | Lockstep-style testing using @quickcheck-dynamic@
--
-- Intended for qualified import.
--
-- > import StateModel.Lockstep (Lockstep(..))
-- > import StateModel.Lockstep qualified as Lockstep
module StateModel.Lockstep (
    InLockstep(..)
  , Lockstep -- opaque
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
  , StateModel.Lockstep.shrinkAction
  , StateModel.Lockstep.monitoring
    -- * Utilities for running the tests
  , tagActions
  , StateModel.Lockstep.runActions
  , StateModel.Lockstep.labelledExamples
  ) where

import Prelude hiding (init)

import Control.Exception
import Control.Monad
import Control.Monad.Reader
import Data.Kind
import Data.Set (Set)
import Data.Typeable
import qualified Data.Set as Set
import Test.QuickCheck.Gen.Unsafe

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.QuickCheck.StateModel

import StateModel.Lockstep.EnvF (EnvF)
import StateModel.Lockstep.EnvF qualified as EnvF
import StateModel.Lockstep.GVar (GVar, AnyGVar(..), InterpretOp)
import StateModel.Lockstep.GVar qualified as GVar

{-------------------------------------------------------------------------------
  Lockstep
-------------------------------------------------------------------------------}

data Lockstep state = Lockstep {
      lockstepModel :: state
    , lockstepEnv   :: EnvF (ModelValue state)
    }
  deriving (Show)

class
     ( StateModel (Lockstep state)
     , Typeable state
     , InterpretOp (ModelOp state) (ModelValue state)
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
  -- > GetB :: ModelOp state a b
  --
  -- in the 'ModelOp' type. For many tests, the standard 'Op' type will
  -- suffice, but not always.
  type ModelOp state :: Type -> Type -> Type

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
  usedVars :: LockstepAction state a -> [AnyGVar (ModelOp state)]

  -- | Step the model
  modelNextState ::
       ModelLookUp state
    -> LockstepAction state a
    -> state
    -> (ModelValue state a, state)

  arbitraryWithVars ::
       ModelFindVariables state
    -> state
    -> Gen (Any (LockstepAction state))

  shrinkWithVars ::
       ModelFindVariables state
    -> state
    -> LockstepAction state a
    -> [Any (LockstepAction state)]

  tagStep ::
       Show a
    => (state, state)
    -> LockstepAction state a
    -> ModelValue state a
    -> [String]

-- | An action in the lock-step model
type LockstepAction state = Action (Lockstep state)

-- | Variables with a "functor-esque" instance
type ModelVar state = GVar (ModelOp state)

-- | Look up a variable for model execution
--
-- The type of the variable is the type in the /real/ system.
type ModelLookUp state = forall a.
          (Show a, Typeable a, Eq a)
       => ModelVar state a -> ModelValue state a

-- | Pick variable of the appropriate type
--
-- The type you pass must be the result type of (previously executed) actions.
-- If you want to change the type of the variable, see
-- 'StateModel.Lockstep.GVar.map'.
type ModelFindVariables state = forall proxy a.
          (Show a, Typeable a, Eq a)
       => proxy a -> [GVar (ModelOp state) a]

{-------------------------------------------------------------------------------
  Internal auxiliary
-------------------------------------------------------------------------------}

varsOfType ::
     InLockstep state
  => EnvF (ModelValue state) -> ModelFindVariables state
varsOfType env p = map GVar.fromVar $ EnvF.keysOfType p env

{-------------------------------------------------------------------------------
  Default implementations for members of 'StateModel'
-------------------------------------------------------------------------------}

-- | Default implementation for 'Test.QuickCheck.StateModel.initialState'
initialState :: state -> Lockstep state
initialState state = Lockstep {
      lockstepModel = state
    , lockstepEnv   = EnvF.empty
    }

-- | Default implementation for 'Test.QuickCheck.StateModel.nextState'
nextState :: forall state a.
     (InLockstep state, Typeable a)
  => Lockstep state
  -> LockstepAction state a
  -> Var a
  -> Lockstep state
nextState (Lockstep state env) action var =
    Lockstep state' $ EnvF.insert var modelResp env
  where
    modelResp :: ModelValue state a
    state'    :: state
    (modelResp, state') = modelNextState (GVar.lookUpEnvF env) action state

-- | Default implementation for 'Test.QuickCheck.StateModel.precondition'
--
-- The default precondition only checks that all variables have a value
-- and that the operations on them are defined.
precondition ::
     InLockstep state
  => Lockstep state -> LockstepAction state a -> Bool
precondition (Lockstep _ env) =
    all (\(SomeGVar var) -> GVar.definedInEnvF env var) . usedVars

-- | Default implementation for 'Test.QuickCheck.StateModel.postcondition'
--
-- The default postcondition verifies that the real system and the model
-- return the same results, up to " observability ".
postcondition :: forall state a.
     InLockstep state
  => Lockstep state -> LockstepAction state a -> LookUp -> a -> Maybe String
postcondition (Lockstep state env) action _lookUp a =
    compareEquality (observeReal action a) (observeModel modelResp)
  where
    modelResp :: ModelValue state a
    modelResp = fst $ modelNextState (GVar.lookUpEnvF env) action state

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
arbitraryAction ::
     InLockstep state
  => Lockstep state -> Gen (Any (LockstepAction state))
arbitraryAction (Lockstep state env) =
    arbitraryWithVars (varsOfType env) state

shrinkAction ::
     InLockstep state
  => Lockstep state
  -> LockstepAction state a -> [Any (LockstepAction state)]
shrinkAction (Lockstep state env) =
    shrinkWithVars (varsOfType env) state

monitoring :: forall state a.
     (InLockstep state, Show a)
  => (Lockstep state, Lockstep state)
  -> LockstepAction state a
  -> LookUp
  -> a
  -> Property -> Property
monitoring (before, after) action _lookUp _realResp =
      counterexample ("State: " ++ show after)
    . tabulate "Tags" tags
  where
    tags :: [String]
    tags = tagStep (lockstepModel before, lockstepModel after) action modelResp

    modelResp :: ModelValue state a
    modelResp = fst $ modelNextState
                        (GVar.lookUpEnvF $ lockstepEnv before)
                        action
                        (lockstepModel before)

{-------------------------------------------------------------------------------
  Finding labelled examples
-------------------------------------------------------------------------------}

-- | Tag a list of actions
--
-- This is primarily useful for use with QuickCheck's 'labelledExamples':
-- the 'monitoring' hook from 'StateModel' is not useful here, because it will
-- be called multiple times during test execution, which means we must use it
-- with 'tabulate', not 'label'; but 'tabulate' is not supported by
-- 'labelledExamples'.
--
-- So, here we run through the actions independent from 'StateModel', collecting
-- all tags, and then finish on a /single/ call to 'label' at the end with all
-- collected tags.
--
-- The other advantage of this function over 'runAction' is that we do not need
-- a test runner here: this uses the model /only/.
tagActions :: forall proxy state.
     InLockstep state
  => proxy state
  -> Actions (Lockstep state)
  -> Property
tagActions _proxy (Actions steps) =
    go Set.empty Test.QuickCheck.StateModel.initialState steps
  where
    go :: Set String -> Lockstep state -> [Step (Lockstep state)] -> Property
    go tags _st []            = label ("Tags: " ++ show (Set.toList tags)) True
    go tags  st ((v:=a) : ss) = go' tags st v a ss

    go' :: forall a.
         (Typeable a, Show a)
      => Set String                 -- accumulated set of tags
      -> Lockstep state             -- current state
      -> Var a                      -- variable for the result of this action
      -> Action (Lockstep state) a  -- action to execute
      -> [Step (Lockstep state)]    -- remaining steps to execute
      -> Property
    go' tags (Lockstep before env) var action ss =
        go (Set.union (Set.fromList tags') tags) st' ss
      where
        st' :: Lockstep state
        st' = Lockstep after (EnvF.insert var modelResp env)

        modelResp :: ModelValue state a
        after     :: state
        (modelResp, after) = modelNextState (GVar.lookUpEnvF env) action before

        tags' :: [String]
        tags' = tagStep (before, after) action modelResp

{-------------------------------------------------------------------------------
  Auxiliary QuickCheck
-------------------------------------------------------------------------------}

ioPropertyBracket ::
     Testable a
  => IO st
  -> (st -> IO ())
  -> ReaderT st IO a
  -> Property
ioPropertyBracket init cleanup (ReaderT prop) = do
    ioProperty $ mask $ \restore -> do
      st <- init
      a  <- restore (prop st) `onException` cleanup st
      cleanup st
      return a

-- | Variation on 'monadicIO' that allows for state initialisation/cleanup
monadicBracketIO :: forall st a.
     Testable a
  => IO st
  -> (st -> IO ())
  -> (st -> PropertyM IO a)
  -> Property
monadicBracketIO init cleanup prop =
    monadic (ioPropertyBracket init cleanup) $ hoistReaderT prop

hoistReaderT :: forall m r a. (r -> PropertyM m a) -> PropertyM (ReaderT r m) a
hoistReaderT prop =
    MkPropertyM $ \k -> fmap ReaderT $ aux (fmap runReaderT . k)
  where
    aux :: (a -> Gen (r -> m Property)) -> Gen (r -> m Property)
    aux k = do
        eval <- delay
        pure $ \r -> eval $ (unPropertyM $ prop r) (fmap ($ r) . k)

{-------------------------------------------------------------------------------
  Utilities for running the tests
-------------------------------------------------------------------------------}

-- | Run the test
--
-- This is a thin wrapper around 'runActions' that allows for a separate
-- state initialization step.
runActions ::
     StateModel state
  => IO st                     -- ^ Initialisation
  -> (st -> IO ())             -- ^ Cleanup
  -> (st -> RunModel state IO) -- ^ Interpreter
  -> Actions state -> Property
runActions init cleanup runner actions =
    monadicBracketIO init cleanup $ \st ->
      void $ Test.QuickCheck.StateModel.runActions (runner st) actions

labelledExamples :: InLockstep state => proxy state -> IO ()
labelledExamples = Test.QuickCheck.labelledExamples . tagActions
