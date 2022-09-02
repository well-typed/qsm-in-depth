{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

module UsingQD (tests) where

import Prelude hiding (init)

import Control.Arrow ((&&&))
import Control.Exception (catch, throwIO)
import Control.Monad
import Data.Bifunctor
import Data.Functor.Const
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable
import System.Directory qualified as IO
import System.IO qualified as IO
import System.IO.Temp (createTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)
import Test.Tasty.QuickCheck (testProperty)

import Test.QuickCheck (Property, Gen)
import Test.QuickCheck qualified as QC
import Test.QuickCheck.StateModel

import StateModel.Lockstep
import StateModel.Lockstep qualified as Lockstep
import StateModel.Lockstep.GVar (GVar, Op(..), Operation(..), InterpretOp(..))
import StateModel.Lockstep.GVar qualified as GVar

import Mock (Mock, Dir(..), File(..), Err)
import Mock qualified as Mock

{-------------------------------------------------------------------------------
  Example
-------------------------------------------------------------------------------}

data State = State {
      stateMock  :: Mock
    , stateStats :: Stats
    }
  deriving (Show)

initState :: State
initState = State {
      stateMock  = Mock.emptyMock
    , stateStats = initStats
    }

instance StateModel (Lockstep State) where
  data Action (Lockstep State) a where
    MkDir :: Dir                                 -> Action (Lockstep State) (Either Err ())
    Open  :: File                                -> Action (Lockstep State) (Either Err IO.Handle)
    Write :: ModelVar State IO.Handle  -> String -> Action (Lockstep State) (Either Err ())
    Close :: ModelVar State IO.Handle            -> Action (Lockstep State) (Either Err ())
    Read  :: File                                -> Action (Lockstep State) (Either Err String)

  initialState    = Lockstep.initialState initState
  nextState       = Lockstep.nextState
  precondition    = Lockstep.precondition
  postcondition   = Lockstep.postcondition
  arbitraryAction = Lockstep.arbitraryAction
  monitoring      = Lockstep.monitoring

  shrinkAction ::
       (Show a, Typeable a)
    => Lockstep State
    -> LockstepAction State a
    -> [Any (LockstepAction State)]
  shrinkAction _ = \case
      Open (File (Dir []) ('t' : n)) ->
        [openTemp n' | n' <- QC.shrink (read n)]
      Open _ ->
        [openTemp 100]
      _otherwise ->
        []
    where
      openTemp :: Int -> Any (LockstepAction State)
      openTemp n = Some $ Open (File (Dir []) ('t' : show n))

deriving instance Show (Action (Lockstep State) a)
deriving instance Eq   (Action (Lockstep State) a)

instance InterpretOp (Op Err) (ModelValue State) where
  interpretOp = go
    where
      go :: Op Err a b -> ModelValue State a -> Either String (ModelValue State b)
      go OpId         = Right
      go (OpRight op) = distrib <=< go op

      distrib ::
           ModelValue State (Either Err a)
        -> Either String (ModelValue State a)
      distrib (ModelErr (Left  err)) = Left (show err)
      distrib (ModelErr (Right val)) = Right val

instance InLockstep State where
  type ModelVarOp State = Op Err

  data ModelValue State a where
    ModelErr :: Either Err (ModelValue State a) -> ModelValue State (Either Err a)

    -- primitive types

    ModelString :: String       -> ModelValue State String
    ModelUnit   :: ()           -> ModelValue State ()
    ModelHandle :: Mock.MHandle -> ModelValue State IO.Handle

  data Observable State a where
    ObserveErr    :: Either Err (Observable State a) -> Observable State (Either Err a)
    ObserveId     :: (Show a, Eq a) => a -> Observable State a
    ObserveHandle :: Observable State IO.Handle

  observeReal :: LockstepAction State a -> a -> Observable State a
  observeReal = \case
      MkDir{} -> ObserveErr . fmap ObserveId
      Open{}  -> ObserveErr . fmap (const ObserveHandle)
      Write{} -> ObserveErr . fmap ObserveId
      Close{} -> ObserveErr . fmap ObserveId
      Read{}  -> ObserveErr . fmap ObserveId

  observeModel :: ModelValue State a -> Observable State a
  observeModel = \case
      ModelErr    x -> ObserveErr $ fmap observeModel x
      ModelString x -> ObserveId x
      ModelUnit   x -> ObserveId x
      ModelHandle _ -> ObserveHandle

  usedVars = \case
      MkDir{}   -> []
      Open{}    -> []
      Write h _ -> [Some h]
      Close h   -> [Some h]
      Read{}    -> []

  modelNextState ::
       ModelLookUp State
    -> LockstepAction State a
    -> State
    -> (ModelValue State a, State)
  modelNextState lookUp = \action (State mock stats) ->
      let (result, state') = go action mock
      in (result, State state' $ updateStats action result stats)
    where
      go :: Action (Lockstep State) a -> Mock -> (ModelValue State a, Mock)
      go = \case
          MkDir d   -> first (liftErr ModelUnit)   . Mock.mMkDir d
          Open  f   -> first (liftErr ModelHandle) . Mock.mOpen f
          Write h s -> first (liftErr ModelUnit)   . Mock.mWrite (lookUpHandle h) s
          Close h   -> first (liftErr ModelUnit)   . Mock.mClose (lookUpHandle h)
          Read f    -> first (liftErr ModelString) . Mock.mRead f

      lookUpHandle :: ModelVar State IO.Handle -> Mock.MHandle
      lookUpHandle var =
          case lookUp var of
            ModelHandle h -> h

      liftErr ::
          (a -> ModelValue State b)
        -> Either Err a -> ModelValue State (Either Err b)
      liftErr f = ModelErr . fmap f

  arbitraryActionWithVars ::
       ModelFindVariables State
    -> State
    -> Gen (Any (LockstepAction State))
  arbitraryActionWithVars findVars _mock = QC.oneof $ concat [
        withoutVars
      , case findVars (Proxy @((Either Err IO.Handle))) of
          Nothing     -> []
          Just genVar -> withVars genVar
      ]
    where
      withoutVars :: [Gen (Any (LockstepAction State))]
      withoutVars = [
            fmap Some $ MkDir <$> genDir
          , fmap Some $ Open  <$> genFile
          , fmap Some $ Read  <$> genFile
          ]

      withVars ::
           Gen (GVar (Op Err) (Either Err IO.Handle))
        -> [Gen (Any (LockstepAction State))]
      withVars genVar = [
            fmap Some $ Write <$> genVar' <*> genString
          , fmap Some $ Close <$> genVar'
          ]
        where
          genVar' :: Gen (GVar (Op Err) IO.Handle)
          genVar' = GVar.map OpRight <$> genVar

      genDir :: Gen Dir
      genDir = do
          n <- QC.choose (0, 3)
          Dir <$> replicateM n (QC.elements ["x", "y", "z"])

      genFile :: Gen File
      genFile = File <$> genDir <*> QC.elements ["a", "b", "c"]

      genString :: Gen String
      genString = QC.sized $ \n -> replicateM n (QC.elements "ABC")

  tagStep ::
       Show a
    => (State, State)
    -> LockstepAction State a
    -> ModelValue State a
    -> [String]
  tagStep (before, after) action result = map (show :: Tag -> String) $
      case (action, result) of
        (Read _, ModelErr (Right _)) ->
          [SuccessfulRead]
        (Open _, ModelErr (Right _)) ->
          [ OpenTwo
          | Set.size (statsOpenedFiles (stateStats after)) > 1
          ]
        _otherwise -> []

deriving instance Show (Observable State a)
deriving instance Eq   (Observable State a)

deriving instance Show (ModelValue State a)

{-------------------------------------------------------------------------------
  Interpreter for IO
-------------------------------------------------------------------------------}

runIO :: FilePath -> RunModel (Lockstep State) IO
runIO root = RunModel go
  where
    go :: forall a.
         Lockstep State
      -> LockstepAction State a
      -> LookUp
      -> IO a
    go _st action lookUp = do
        case action of
          MkDir d -> catchErr $
            IO.createDirectory (Mock.dirFP root d)
          Open f -> catchErr $
            IO.openFile (Mock.fileFP root f) IO.AppendMode
          Write h s -> catchErr $
            IO.hPutStr (lookUp' h) s
          Close h -> catchErr $
            IO.hClose (lookUp' h)
          Read f -> catchErr $
            IO.readFile (Mock.fileFP root f)
      where
        lookUp' :: ModelVar State IO.Handle -> IO.Handle
        lookUp' = either (error "impossible") id . GVar.lookUpEnv lookUp

catchErr :: forall a. IO a -> IO (Either Err a)
catchErr act = catch (Right <$> act) handler
  where
    handler :: IOError -> IO (Either Err h)
    handler e = maybe (throwIO e) (return . Left) (Mock.fromIOError e)

{-------------------------------------------------------------------------------
  Statistics and tagging
-------------------------------------------------------------------------------}

data Stats = Stats {
      statsOpenedFiles :: Set File
    }
  deriving (Show)

initStats :: Stats
initStats = Stats {
      statsOpenedFiles = Set.empty
    }

updateStats :: LockstepAction State a -> ModelValue State a -> Stats -> Stats
updateStats action result stats@Stats{..} =
   case (action, result) of
     (Open f, ModelErr (Right _)) ->
       stats { statsOpenedFiles = Set.insert f statsOpenedFiles }
     _otherwise ->
       stats

data Tag = OpenTwo | SuccessfulRead
  deriving (Show)

{-------------------------------------------------------------------------------
  Top-level test
-------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "UsingQD" [
      testProperty "propLockstep" $
        Lockstep.runActions (createTempDirectory tmpDir "QSM") runIO
    , testCase "labelledExamples" $
        Lockstep.labelledExamples (Proxy @State)
    ]
  where
    -- TODO: tmpDir should really be a parameter to the test suite
    tmpDir :: FilePath
    tmpDir = "./tmp"
