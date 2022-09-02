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
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Wredundant-constraints #-}

module UsingQD (tests) where

import Prelude hiding (init)

import Control.Exception (catch, throwIO)
import Control.Monad
import Data.Bifunctor
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable
import System.Directory qualified as IO
import System.IO qualified as IO
import System.IO.Temp (createTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)
import Test.Tasty.QuickCheck (testProperty)

import Test.QuickCheck (Gen)
import Test.QuickCheck qualified as QC
import Test.QuickCheck.StateModel

import StateModel.Lockstep
import StateModel.Lockstep qualified as Lockstep
import StateModel.Lockstep.GVar (GVar, AnyGVar(..), Op(..), InterpretOp(..))
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
    Open  :: File                                -> Action (Lockstep State) (Either Err (IO.Handle, File))
    Write :: ModelVar State IO.Handle  -> String -> Action (Lockstep State) (Either Err ())
    Close :: ModelVar State IO.Handle            -> Action (Lockstep State) (Either Err ())
    Read  :: Either (ModelVar State File) File   -> Action (Lockstep State) (Either Err String)

  initialState    = Lockstep.initialState initState
  nextState       = Lockstep.nextState
  precondition    = Lockstep.precondition
  postcondition   = Lockstep.postcondition
  arbitraryAction = Lockstep.arbitraryAction
  shrinkAction    = Lockstep.shrinkAction
  monitoring      = Lockstep.monitoring

deriving instance Show (Action (Lockstep State) a)
deriving instance Eq   (Action (Lockstep State) a)

instance InterpretOp Op (ModelValue State) where
  intOp OpId         = Right
  intOp OpFst        = \case MPair   x -> Right (fst x)
  intOp OpSnd        = \case MPair   x -> Right (snd x)
  intOp OpLeft       = \case MEither x -> either Right (const $ Left "Not Left") x
  intOp OpRight      = \case MEither x -> bimap show id x
  intOp (OpComp g f) = intOp g <=< intOp f

instance InLockstep State where
  type ModelOp State = Op

  data Observable State a where
    OEither :: Either (Observable State a) (Observable State b) -> Observable State (Either a b)
    OPair   :: (Observable State a, Observable State b) -> Observable State (a, b)
    OId     :: (Show a, Typeable a, Eq a) => a -> Observable State a
    OHandle :: Observable State IO.Handle

  -- | Model values
  --
  -- For model values, we must be sure that if we have a value of type
  --
  -- > ModelValue State IO.Handle
  --
  -- that it is a in fact mock handle. This means that here we cannot define
  --
  -- > ModelId :: a -> ModelValue State a
  --
  -- unlike in @Observable State@.
  data ModelValue State a where
    MEither :: Either (ModelValue State a) (ModelValue State b) -> ModelValue State (Either a b)
    MPair   :: (ModelValue State a, ModelValue State b) -> ModelValue State (a, b)

    -- primitive types

    MErr    :: Err          -> ModelValue State Err
    MFile   :: File         -> ModelValue State File
    MString :: String       -> ModelValue State String
    MUnit   :: ()           -> ModelValue State ()
    MHandle :: Mock.MHandle -> ModelValue State IO.Handle

  observeReal :: LockstepAction State a -> a -> Observable State a
  observeReal = \case
      MkDir{} -> OEither . bimap OId OId
      Open{}  -> OEither . bimap OId (OPair . bimap (const OHandle) OId)
      Write{} -> OEither . bimap OId OId
      Close{} -> OEither . bimap OId OId
      Read{}  -> OEither . bimap OId OId

  observeModel :: ModelValue State a -> Observable State a
  observeModel = \case
      MEither x -> OEither $ bimap observeModel observeModel x
      MPair   x -> OPair   $ bimap observeModel observeModel x
      MErr    x -> OId x
      MString x -> OId x
      MUnit   x -> OId x
      MFile   x -> OId x
      MHandle _ -> OHandle

  usedVars = \case
      MkDir{}        -> []
      Open{}         -> []
      Write h _      -> [SomeGVar h]
      Close h        -> [SomeGVar h]
      Read (Left h)  -> [SomeGVar h]
      Read (Right _) -> []

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
          MkDir d   -> first (liftErr MUnit)     . Mock.mMkDir d
          Open f    -> first (liftErr (modelOpen f)) . Mock.mOpen f
          Write h s -> first (liftErr MUnit)     . Mock.mWrite (lookUpHandle h) s
          Close h   -> first (liftErr MUnit)     . Mock.mClose (lookUpHandle h)
          Read f    -> first (liftErr MString)   . Mock.mRead (either lookUpFile id f)

      modelOpen :: File -> Mock.MHandle -> ModelValue State (IO.Handle, File)
      modelOpen f h = MPair (MHandle h, MFile f)

      lookUpHandle :: ModelVar State IO.Handle -> Mock.MHandle
      lookUpHandle var = case lookUp var of MHandle h -> h

      lookUpFile :: ModelVar State File -> File
      lookUpFile var = case lookUp var of MFile f -> f

      liftErr ::
           (a -> ModelValue State b)
        -> Either Err a -> ModelValue State (Either Err b)
      liftErr f = MEither . bimap MErr f

  arbitraryActionWithVars ::
       ModelFindVariables State
    -> State
    -> Gen (Any (LockstepAction State))
  arbitraryActionWithVars findVars _mock = QC.oneof $ concat [
        withoutVars
      , case findVars (Proxy @((Either Err (IO.Handle, File)))) of
          []   -> []
          vars -> withVars (QC.elements vars)
      ]
    where
      withoutVars :: [Gen (Any (LockstepAction State))]
      withoutVars = [
            fmap Some $ MkDir <$> genDir
          , fmap Some $ Open  <$> genFile
          , fmap Some $ Read  <$> (Right <$> genFile)
          ]

      withVars ::
           Gen (GVar (ModelOp State) (Either Err (IO.Handle, File)))
        -> [Gen (Any (LockstepAction State))]
      withVars genVar = [
            fmap Some $ Write <$> genVarHandle <*> genString
          , fmap Some $ Close <$> genVarHandle
          ]
        where
          genVarHandle :: Gen (GVar (ModelOp State) IO.Handle)
          genVarHandle =
              GVar.map (\op -> OpFst `OpComp` OpRight `OpComp` op) <$> genVar

      genDir :: Gen Dir
      genDir = do
          n <- QC.choose (0, 3)
          Dir <$> replicateM n (QC.elements ["x", "y", "z"])

      genFile :: Gen File
      genFile = File <$> genDir <*> QC.elements ["a", "b", "c"]

      genString :: Gen String
      genString = QC.sized $ \n -> replicateM n (QC.elements "ABC")

  shrinkActionWithVars ::
       ModelFindVariables State
    -> State
    -> LockstepAction State a
    -> [Any (LockstepAction State)]
  shrinkActionWithVars findVars _state = \case
      Open (File (Dir []) ('t' : n)) ->
        [openTemp n' | n' <- QC.shrink (read n)]
      Open _ ->
        [openTemp 100]
      Read (Right _) ->
        [ Some $ Read (Left $ GVar.map (\op -> OpSnd `OpComp` OpRight `OpComp` op) v)
        | v <- findVars (Proxy @((Either Err (IO.Handle, File))))
        ]
      _otherwise ->
        []
    where
      openTemp :: Int -> Any (LockstepAction State)
      openTemp n = Some $ Open (File (Dir []) ('t' : show n))

  tagStep ::
       (State, State)
    -> LockstepAction State a
    -> ModelValue State a
    -> [String]
  tagStep (_before, after) action result = map (show :: Tag -> String) $
      case (action, result) of
        (Read _, MEither (Right _)) ->
          [SuccessfulRead]
        (Open _, MEither (Right _)) ->
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
            (,f) <$> IO.openFile (Mock.fileFP root f) IO.AppendMode
          Write h s -> catchErr $
            IO.hPutStr (lookUp' h) s
          Close h -> catchErr $
            IO.hClose (lookUp' h)
          Read f -> catchErr $
            IO.readFile (Mock.fileFP root $ either lookUp' id f)
      where
        lookUp' :: (Show x, Typeable x, Eq x) => ModelVar State x -> x
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
     (Open f, MEither (Right _)) ->
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
