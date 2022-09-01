{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Wno-orphans #-}

-- TODO: Temporary
{-# OPTIONS_GHC -Wno-unused-imports #-}

module UsingQD (tests) where

import Prelude hiding (init)

import Control.Exception (catch, throwIO)
import Control.Monad
import Data.Bifunctor
import Data.Functor.Const
import Data.Typeable
import System.Directory qualified as IO
import System.IO qualified as IO
import System.IO.Temp (createTempDirectory)
import Test.Tasty
import Test.Tasty.QuickCheck (testProperty)
import Control.Arrow ((&&&))

import Test.QuickCheck (Gen)
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

instance StateModel (Lockstep Mock) where
  data Action (Lockstep Mock) a where
    MkDir :: Dir                                -> Action (Lockstep Mock) (Either Err ())
    Open  :: File                               -> Action (Lockstep Mock) (Either Err IO.Handle)
    Write :: ModelVar Mock IO.Handle  -> String -> Action (Lockstep Mock) (Either Err ())
    Close :: ModelVar Mock IO.Handle            -> Action (Lockstep Mock) (Either Err ())
    Read  :: File                               -> Action (Lockstep Mock) (Either Err String)

  initialState    = Lockstep.initialState Mock.emptyMock
  nextState       = Lockstep.nextState
  precondition    = Lockstep.precondition
  postcondition   = Lockstep.postcondition
  arbitraryAction = Lockstep.arbitraryAction

deriving instance Show (Action (Lockstep Mock) a)
deriving instance Eq   (Action (Lockstep Mock) a)

instance InterpretOp (Op Err) (ModelValue Mock) where
  interpretOp = go
    where
      go :: Op Err a b -> ModelValue Mock a -> Either String (ModelValue Mock b)
      go OpId         = Right
      go (OpRight op) = distrib <=< go op

      distrib ::
           ModelValue Mock (Either Err a)
        -> Either String (ModelValue Mock a)
      distrib (ModelErr (Left  err)) = Left (show err)
      distrib (ModelErr (Right val)) = Right val

instance InLockstep Mock where
  type ModelVarOp Mock = Op Err

  data ModelValue Mock a where
    ModelErr :: Either Err (ModelValue Mock a) -> ModelValue Mock (Either Err a)

    -- primitive types

    ModelString :: String       -> ModelValue Mock String
    ModelUnit   :: ()           -> ModelValue Mock ()
    ModelHandle :: Mock.MHandle -> ModelValue Mock IO.Handle

  data Observable Mock a where
    ObserveErr    :: Either Err (Observable Mock a) -> Observable Mock (Either Err a)
    ObserveId     :: (Show a, Eq a) => a -> Observable Mock a
    ObserveHandle :: Observable Mock IO.Handle

  observeReal :: LockstepAction Mock a -> a -> Observable Mock a
  observeReal = \case
      MkDir{} -> ObserveErr . fmap ObserveId
      Open{}  -> ObserveErr . fmap (const ObserveHandle)
      Write{} -> ObserveErr . fmap ObserveId
      Close{} -> ObserveErr . fmap ObserveId
      Read{}  -> ObserveErr . fmap ObserveId

  observeModel :: ModelValue Mock a -> Observable Mock a
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
       ModelLookUp Mock
    -> LockstepAction Mock a
    -> Mock
    -> (ModelValue Mock a, Mock)
  modelNextState lookUp = \case
      MkDir d   -> first (liftErr ModelUnit)   . Mock.mMkDir d
      Open  f   -> first (liftErr ModelHandle) . Mock.mOpen f
      Write h s -> first (liftErr ModelUnit)   . Mock.mWrite (lookUpHandle h) s
      Close h   -> first (liftErr ModelUnit)   . Mock.mClose (lookUpHandle h)
      Read f    -> first (liftErr ModelString) . Mock.mRead f
    where
      lookUpHandle :: ModelVar Mock IO.Handle -> Mock.MHandle
      lookUpHandle var =
          case lookUp var of
            ModelHandle h -> h

      liftErr ::
          (a -> ModelValue Mock b)
        -> Either Err a -> ModelValue Mock (Either Err b)
      liftErr f = ModelErr . fmap f

  arbitraryActionWithVars findVars _mock = QC.oneof $ concat [
        withoutVars
      , case findVars (Proxy @((Either Err IO.Handle))) of
          Nothing     -> []
          Just genVar -> withVars genVar
      ]
    where
      withoutVars :: [Gen (Any (LockstepAction Mock))]
      withoutVars = [
            fmap Some $ MkDir <$> genDir
          , fmap Some $ Open  <$> genFile
          , fmap Some $ Read  <$> genFile
          ]

      withVars ::
           Gen (GVar (Op Err) (Either Err IO.Handle))
        -> [Gen (Any (LockstepAction Mock))]
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

deriving instance Show (Observable Mock a)
deriving instance Eq   (Observable Mock a)

deriving instance Show (ModelValue Mock a)

{-------------------------------------------------------------------------------
  Interpreter for IO
-------------------------------------------------------------------------------}

runIO :: FilePath -> RunModel (Lockstep Mock) IO
runIO root = RunModel go
  where
    go :: forall a.
         Lockstep Mock
      -> LockstepAction Mock a
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
        lookUp' :: ModelVar Mock IO.Handle -> IO.Handle
        lookUp' = either (error "impossible") id . GVar.lookUpEnv lookUp

catchErr :: forall a. IO a -> IO (Either Err a)
catchErr act = catch (Right <$> act) handler
  where
    handler :: IOError -> IO (Either Err h)
    handler e = maybe (throwIO e) (return . Left) (Mock.fromIOError e)

{-------------------------------------------------------------------------------
  Top-level test
-------------------------------------------------------------------------------}

tests :: TestTree
tests = testGroup "UsingQD" [
      testProperty "runActions" $
        propLockstep (createTempDirectory tmpDir "QSM") runIO
    ]
  where
    -- TODO: tmpDir should really be a parameter to the test suite
    tmpDir :: FilePath
    tmpDir = "./tmp"