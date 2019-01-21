{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Version1 (
    prop_sequential
  , prop_sequential'
  , showLabelledExamples
  , showLabelledExamples'
  , openThenWrite -- unused, just an example
    -- Various iterations of the shrinker discussed in the blog post
  , shrinker0
  , shrinker1
  , badShrinker
  , shrinker2
  ) where

import Prelude hiding (elem)

import Control.Exception
import Control.Foldl          (Fold (..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Bifunctor
import Data.Foldable          (toList)
import Data.Functor.Classes
import Data.Maybe             (catMaybes, fromJust)
import Data.Monoid            ((<>))
import Data.Set               (Set)
import Data.TreeDiff          (ToExpr (..), defaultExprViaShow)
import Data.Typeable
import GHC.Generics           (Generic)
import System.IO.Temp         (createTempDirectory)
import System.Random          (getStdRandom, randomR)
import Test.QuickCheck        (Gen)
import Text.Show.Pretty       (ppShow)

import qualified Control.Foldl           as Foldl
import qualified Data.List               as List
import qualified Data.Set                as Set
import qualified System.Directory        as IO
import qualified System.IO               as IO
import qualified Test.QuickCheck         as QC
import qualified Test.QuickCheck.Monadic as QC
import qualified Test.QuickCheck.Random  as QC

import           Test.StateMachine
import qualified Test.StateMachine.Sequential  as QSM
import qualified Test.StateMachine.Types       as QSM
import qualified Test.StateMachine.Types.Rank2 as Rank2

import Mock

{-------------------------------------------------------------------------------
  Language
-------------------------------------------------------------------------------}

data Cmd h =
    MkDir Dir
  | Open File
  | Write h String
  | Close h
  | Read File
  deriving (Show, Functor, Foldable, Traversable)

data Success h =
    Unit ()
  | Handle h
  | String String
  deriving (Show, Eq, Functor, Foldable, Traversable)

newtype Resp h = Resp (Either Err (Success h))
  deriving (Show, Eq, Functor, Foldable, Traversable)

{-------------------------------------------------------------------------------
  Interpreter: mock implementation
-------------------------------------------------------------------------------}

runMock :: Cmd MHandle -> Mock -> (Resp MHandle, Mock)
runMock (MkDir d)   = first (Resp . fmap Unit)   . mMkDir d
runMock (Open  f)   = first (Resp . fmap Handle) . mOpen  f
runMock (Write h s) = first (Resp . fmap Unit)   . mWrite h s
runMock (Close h)   = first (Resp . fmap Unit)   . mClose h
runMock (Read  f)   = first (Resp . fmap String) . mRead  f

{-------------------------------------------------------------------------------
  Interpreter: real I/O
-------------------------------------------------------------------------------}

catchErr :: IO (Success h) -> IO (Resp h)
catchErr act = catch (Resp . Right <$> act) handler
  where
    handler :: IOError -> IO (Resp h)
    handler e = maybe (throwIO e) (return . Resp . Left) (fromIOError e)

runIO :: FilePath -> Cmd IO.Handle -> IO (Resp IO.Handle)
runIO root = catchErr . go
  where
    go :: Cmd IO.Handle -> IO (Success IO.Handle)
    go (MkDir d)   = Unit   <$> IO.createDirectory (dirFP root d)
    go (Open  f)   = Handle <$> IO.openFile (fileFP root f) IO.AppendMode
    go (Write h s) = Unit   <$> IO.hPutStr h s
    go (Close h)   = Unit   <$> IO.hClose  h
    go (Read  f)   = String <$> IO.readFile (fileFP root f)

{-------------------------------------------------------------------------------
  Reference example
-------------------------------------------------------------------------------}

openThenWrite :: Typeable h => [Cmd (Reference h Symbolic)]
openThenWrite = [
      Open (File (Dir []) "a")
    , Open (File (Dir []) "b")
    , Write (QSM.Reference (QSM.Symbolic (QSM.Var 0))) "Hi"
    ]

{-------------------------------------------------------------------------------
  Working with references
-------------------------------------------------------------------------------}

newtype At f r = At (f (Reference IO.Handle r))

deriving instance Show (f (Reference IO.Handle r)) => Show (At f r)

type f :@ r = At f r

type RefEnv k a r = [(Reference k r, a)]

(!) :: (Eq1 r, Eq k) => RefEnv k a r -> Reference k r -> a
env ! r = fromJust (lookup r env)

{-------------------------------------------------------------------------------
  Relating the mock model to the real implementation
-------------------------------------------------------------------------------}

type HandleRefs r = RefEnv IO.Handle MHandle r

data Model r = Model Mock (HandleRefs r)
  deriving (Generic)

deriving instance Show1 r => Show (Model r)

initModel :: Model r
initModel = Model emptyMock []

toMock :: (Functor f, Eq1 r) => Model r -> f :@ r -> f MHandle
toMock (Model _ hs) (At fr) = (hs !) <$> fr

step :: Eq1 r => Model r -> Cmd :@ r -> (Resp MHandle, Mock)
step m@(Model mock _) c = runMock (toMock m c) mock

{-------------------------------------------------------------------------------
  Events
-------------------------------------------------------------------------------}

data Event r = Event {
    before   :: Model  r
  , cmd      :: Cmd :@ r
  , after    :: Model  r
  , mockResp :: Resp MHandle
  }

deriving instance Show1 r => Show (Event r)

lockstep :: Eq1 r
         => Model   r
         -> Cmd  :@ r
         -> Resp :@ r
         -> Event   r
lockstep m@(Model _ hs) c (At resp) = Event {
      before   = m
    , cmd      = c
    , after    = Model mock' (hs <> hs')
    , mockResp = resp'
    }
  where
    (resp', mock') = step m c
    hs' = zip (toList resp) (toList resp')

{-------------------------------------------------------------------------------
  Generator
-------------------------------------------------------------------------------}

generator :: Model Symbolic -> Maybe (Gen (Cmd :@ Symbolic))
generator (Model _ hs) = Just $ QC.oneof $ concat [
      withoutHandle
    , if null hs then [] else withHandle
    ]
  where
    withoutHandle :: [Gen (Cmd :@ Symbolic)]
    withoutHandle = [
          fmap At $ MkDir <$> genDir
        , fmap At $ Open  <$> genFile
        , fmap At $ Read  <$> genFile
        ]

    withHandle :: [Gen (Cmd :@ Symbolic)]
    withHandle = [
          fmap At $ Write <$> genHandle <*> genString
        , fmap At $ Close <$> genHandle
        ]

    genDir :: Gen Dir
    genDir = do
        n <- QC.choose (0, 3)
        Dir <$> replicateM n (QC.elements ["x", "y", "z"])

    genFile :: Gen File
    genFile = File <$> genDir <*> QC.elements ["a", "b", "c"]

    genString :: Gen String
    genString = QC.sized $ \n -> replicateM n (QC.elements "ABC")

    genHandle :: Gen (Reference IO.Handle Symbolic)
    genHandle = QC.elements (map fst hs)

shrinker :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker = shrinker2

shrinker0 :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker0 _ _ = []

shrinker1 :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker1 _ (At cmd) =
    case cmd of
      Open (File (Dir d) f) ->
        [At $ Open (File (Dir d') f) | d' <- QC.shrink d]
      _otherwise ->
        []

badShrinker :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
badShrinker _ (At cmd) =
    case cmd of
      Open _ ->
        [At $ Open (File (Dir []) f') | f' <- ["t1", "t2"]]
      _otherwise ->
        []

shrinker2 :: Model Symbolic -> Cmd :@ Symbolic -> [Cmd :@ Symbolic]
shrinker2 _ (At cmd) =
    case cmd of
      Open (File (Dir []) ('t' : n)) ->
        [openTemp n' | n' <- QC.shrink (read n)]
      Open _ ->
        [openTemp 100]
      _otherwise ->
        []
  where
    openTemp :: Int -> Cmd :@ Symbolic
    openTemp n = At $ Open (File (Dir []) ('t' : show n))

{-------------------------------------------------------------------------------
  The state machine proper
-------------------------------------------------------------------------------}

transition :: Eq1 r => Model r -> Cmd :@ r -> Resp :@ r -> Model r
transition m c = after . lockstep m c

precondition :: Model Symbolic -> Cmd :@ Symbolic -> Logic
precondition (Model _ hs) (At c) =
    forall (toList c) (`elem` map fst hs)

postcondition :: Model Concrete -> Cmd :@ Concrete -> Resp :@ Concrete -> Logic
postcondition m c r =
    toMock (after e) r .== mockResp e
  where
    e = lockstep m c r

semantics :: FilePath -> Cmd :@ Concrete -> IO (Resp :@ Concrete)
semantics root (At c) =
    (At . fmap QSM.reference) <$>
      runIO root (QSM.concrete <$> c)

symbolicResp :: Model Symbolic -> Cmd :@ Symbolic -> GenSym (Resp :@ Symbolic)
symbolicResp m c = At <$> traverse (const QSM.genSym) resp
  where
    (resp, _mock') = step m c

sm :: FilePath -> StateMachine Model (At Cmd) IO (At Resp)
sm root = QSM.StateMachine {
      initModel     = initModel
    , transition    = transition
    , precondition  = precondition
    , postcondition = postcondition
    , invariant     = Nothing
    , generator     = generator
    , distribution  = Nothing
    , shrinker      = shrinker
    , semantics     = semantics root
    , mock          = symbolicResp
    }

{-------------------------------------------------------------------------------
  Additional type class instances required to run the QSM tests
-------------------------------------------------------------------------------}

instance CommandNames (At Cmd) where
  cmdName (At MkDir{}) = "MkDir"
  cmdName (At Open{})  = "Open"
  cmdName (At Write{}) = "Write"
  cmdName (At Close{}) = "Close"
  cmdName (At Read{})  = "Read"
  cmdNames _ = ["MkDir", "Open", "Write", "Close", "Read"]

instance Functor f => Rank2.Functor (At f) where
  fmap = \f (At x) -> At $ fmap (lift f) x
    where
      lift :: (r x -> r' x) -> QSM.Reference x r -> QSM.Reference x r'
      lift f (QSM.Reference x) = QSM.Reference (f x)

instance Foldable f => Rank2.Foldable (At f) where
  foldMap = \f (At x) -> foldMap (lift f) x
    where
      lift :: (r x -> m) -> QSM.Reference x r -> m
      lift f (QSM.Reference x) = f x

instance Traversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> traverse (lift f) x
    where
      lift :: Functor f
           => (r x -> f (r' x)) -> QSM.Reference x r -> f (QSM.Reference x r')
      lift f (QSM.Reference x) = QSM.Reference <$> f x

deriving instance ToExpr (Model Concrete)
deriving instance ToExpr Mock
deriving instance ToExpr Dir
deriving instance ToExpr File

instance ToExpr IO.Handle where
  toExpr = defaultExprViaShow

{-------------------------------------------------------------------------------
  Top-level tests
-------------------------------------------------------------------------------}

prop_sequential :: FilePath -> QC.Property
prop_sequential tmpDir =
    forAllCommands (sm rootUnused) Nothing $ \cmds ->
      QC.monadicIO $ do
        tstTmpDir <- liftIO $ createTempDirectory tmpDir "QSM"
        let sm' = sm tstTmpDir
        (hist, _model, res) <- runCommands sm' cmds
        prettyCommands sm' hist
          $ checkCommandNames cmds
          $ res QC.=== Ok

prop_sequential' :: FilePath -> QC.Property
prop_sequential' tmpDir =
    forAllCommands (sm rootUnused) Nothing $ \cmds ->
      QC.monadicIO $ do
        tstTmpDir <- liftIO $ createTempDirectory tmpDir "QSM"
        let sm' = sm tstTmpDir
        (hist, _model, res) <- runCommands sm' cmds
        prettyCommands sm' hist
          $ QC.tabulate "Tags" (map show $ tag (execCmds cmds))
          $ res QC.=== Ok

rootUnused :: FilePath
rootUnused = error "root not used during command generation"

{-------------------------------------------------------------------------------
  Tagging
-------------------------------------------------------------------------------}

data Tag =
    OpenTwo
  | SuccessfulRead
  deriving (Show)

tag :: [Event Symbolic] -> [Tag]
tag = Foldl.fold $ catMaybes <$> sequenceA [
      openTwo
    , successfulRead
    ]
  where
    openTwo :: Fold (Event Symbolic) (Maybe Tag)
    openTwo = Fold update Set.empty extract
      where
        update :: Set File -> Event Symbolic -> Set File
        update opened ev =
            case (cmd ev, mockResp ev) of
              (At (Open f), Resp (Right _)) ->
                Set.insert f opened
              _otherwise ->
                opened

        extract :: Set File -> Maybe Tag
        extract opened = do
            guard (Set.size opened >= 2)
            return $ OpenTwo

    successfulRead :: Fold (Event Symbolic) (Maybe Tag)
    successfulRead = Fold update False extract
      where
        update :: Bool -> Event Symbolic -> Bool
        update didRead ev = didRead ||
            case (cmd ev, mockResp ev) of
              (At (Read _), Resp (Right _)) ->
                True
              _otherwise ->
                False

        extract :: Bool -> Maybe Tag
        extract didRead = do
            guard didRead
            return SuccessfulRead

execCmd :: Model Symbolic
        -> QSM.Command (At Cmd) (At Resp)
        -> Event Symbolic
execCmd model (QSM.Command cmd resp _vars) =
    lockstep model cmd resp

execCmds :: QSM.Commands (At Cmd) (At Resp) -> [Event Symbolic]
execCmds = \(QSM.Commands cs) -> go initModel cs
  where
    go :: Model Symbolic
       -> [QSM.Command (At Cmd) (At Resp)]
       -> [Event Symbolic]
    go _ []       = []
    go m (c : cs) = e : go (after e) cs
      where
        e = execCmd m c

{-------------------------------------------------------------------------------
  Finding minimal labelled examples

  With shrinker, non-minimal example for SuccessfulRead: 617213
-------------------------------------------------------------------------------}

showLabelledExamples :: Maybe Int -> IO ()
showLabelledExamples mReplay = do
    replaySeed <- case mReplay of
                    Nothing   -> getStdRandom $ randomR (1, 999999)
                    Just seed -> return seed

    putStrLn $ "Using replaySeed " ++ show replaySeed

    let args = QC.stdArgs {
            QC.maxSuccess = 10000
          , QC.replay     = Just (QC.mkQCGen replaySeed, 0)
          }

    QC.labelledExamplesWith args $
      forAllCommands (sm rootUnused) Nothing $ \cmds ->
        repeatedly QC.collect (tag . execCmds $ cmds) $
          QC.property True

-- | Like 'showLabelledExamples', but disable the shrinker
showLabelledExamples' :: Maybe Int -> IO ()
showLabelledExamples' mReplay = do
    replaySeed <- case mReplay of
                    Nothing   -> getStdRandom $ randomR (1, 999999)
                    Just seed -> return seed

    putStrLn $ "Using replaySeed " ++ show replaySeed

    let args = QC.stdArgs {
            QC.maxSuccess = 10000
          , QC.replay     = Just (QC.mkQCGen replaySeed, 0)
          }

    QC.labelledExamplesWith args $
      QC.forAllShrinkShow (QSM.generateCommands (sm rootUnused) Nothing)
                          (const [])
                          ppShow $ \cmds ->
        repeatedly QC.collect (tag . execCmds $ cmds) $
          QC.property True

repeatedly :: (a -> b -> b) -> ([a] -> b -> b)
repeatedly = flip . List.foldl' . flip
