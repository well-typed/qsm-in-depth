{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -Wall -Wno-orphans #-}

module UsingQD (tests) where

import Prelude hiding (init)

import Control.Exception
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
import StateModel.Lockstep.EnvOf (EnvOf)
import StateModel.Lockstep.EnvOf qualified as EnvOf
import StateModel.Lockstep qualified as Lockstep
import StateModel.Util

import Mock (Mock, Dir(..), File(..), Err)
import Mock qualified as Mock

{-------------------------------------------------------------------------------
  Example
-------------------------------------------------------------------------------}

instance StateModel (Lockstep Mock) where
  data Action (Lockstep Mock) a where
    MkDir :: Dir                     -> Action (Lockstep Mock) (Either Err ())
    Open  :: File                    -> Action (Lockstep Mock) (Either Err IO.Handle)
    Write :: Var IO.Handle -> String -> Action (Lockstep Mock) (Either Err ())
    Close :: Var IO.Handle           -> Action (Lockstep Mock) (Either Err ())
    Read  :: File                    -> Action (Lockstep Mock) (Either Err String)

  arbitraryAction (Lockstep _mock env) = QC.oneof [
        fmap Some $ MkDir <$> genDir
      , fmap Some $ Open  <$> genFile
      , fmap Some $ Read  <$> genFile
      , genHandle `thenGen` \(Const h) -> QC.oneof [
            fmap Some $ Write h <$> genString
          , fmap Some $ pure $ Close h
          ]
      ]
    where
      genDir :: Gen Dir
      genDir = do
          n <- QC.choose (0, 3)
          Dir <$> replicateM n (QC.elements ["x", "y", "z"])

      genFile :: Gen File
      genFile = File <$> genDir <*> QC.elements ["a", "b", "c"]

      genString :: Gen String
      genString = QC.sized $ \n -> replicateM n (QC.elements "ABC")

      genHandle :: Gen (Any (Const (Var IO.Handle)))
      genHandle = elementsOrFail $ EnvOf.keysOfType (Proxy @IO.Handle) env

  initialState  = Lockstep.initialState Mock.emptyMock
  nextState     = Lockstep.nextState
  precondition  = Lockstep.precondition
  postcondition = Lockstep.postcondition

deriving instance Show (Action (Lockstep Mock) a)
deriving instance Eq   (Action (Lockstep Mock) a)

instance InLockstep Mock where
  type MockError Mock = Mock.Err

  data Observable Mock a where
    ObserveUnit   :: Either Err ()     -> Observable Mock (Either Err ())
    ObserveHandle :: Either Err ()     -> Observable Mock (Either Err IO.Handle)
    ObserveString :: Either Err String -> Observable Mock (Either Err String)

  data MockValue Mock a where
    MockHandle :: Mock.MHandle -> MockValue Mock IO.Handle

  observe ::
       LockstepAction Mock a
    -> a
    -> Observable Mock a
  observe = \case
      MkDir{} -> ObserveUnit
      Open{}  -> ObserveHandle . fmap (const ())
      Write{} -> ObserveUnit
      Close{} -> ObserveUnit
      Read{}  -> ObserveString

  runModel ::
        MockEnv Mock
     -> LockstepAction Mock a
     -> Mock
     -> ((Observable Mock a, Maybe (Var a -> MockEnv Mock)), Mock)
  runModel env = \case
      MkDir d   -> first (ObserveUnit          &&& const Nothing)     . Mock.mMkDir d
      Open  f   -> first (ObserveHandle . hide &&& extend MockHandle) . Mock.mOpen f
      Write h s -> first (ObserveUnit          &&& const Nothing)     . Mock.mWrite (lookUpHandle h) s
      Close h   -> first (ObserveUnit          &&& const Nothing)     . Mock.mClose (lookUpHandle h)
      Read f    -> first (ObserveString        &&& const Nothing)     . Mock.mRead f
    where
      hide :: Either Err a -> Either Err ()
      hide = fmap (const ())

      extend ::
           Typeable real
        => (mock -> MockValue Mock real)
        -> Either Err mock
        -> Maybe (Var (Either Err real) -> EnvOf Err (MockValue Mock))
      extend wrapMock = either (const Nothing) $ \val ->
          Just $ \var -> EnvOf.insert var (wrapMock val) env

      lookUpHandle :: Var IO.Handle -> Mock.MHandle
      lookUpHandle var =
          case EnvOf.lookup var env of
            Just (MockHandle h) -> h
            Nothing -> error "this should be impossible due to preconditions"

  usedVars = \case
      MkDir{}   -> []
      Open{}    -> []
      Write h _ -> [Some h]
      Close h   -> [Some h]
      Read{}    -> []

deriving instance Show (MockValue Mock a)

deriving instance Show (Observable Mock a)
deriving instance Eq   (Observable Mock a)

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
        lookUp' :: Var IO.Handle -> IO.Handle
        lookUp' (Var x) =
            either (error "impossible") id $ lookUp var'
          where
            var' :: Var (Either Err IO.Handle)
            var' = Var x

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
      testProperty "runActions" $ \actions ->
        monadicInit (createTempDirectory tmpDir "QSM") $ \root ->
          void $ runActions (runIO root) actions
    ]
  where
    -- TODO: tmpDir should really be a parameter to the test suite
    tmpDir :: FilePath
    tmpDir = "./tmp"