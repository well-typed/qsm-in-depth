{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Version2 (prop_sequential, showLabelledExamples) where

import Prelude hiding (elem)

import Control.Exception
import Control.Foldl          (Fold (..))
import Control.Monad
import Control.Monad.IO.Class
import Data.Bifoldable
import Data.Bifunctor
import Data.Bitraversable
import Data.Functor.Classes
import Data.Maybe             (catMaybes, fromJust, mapMaybe)
import Data.Monoid            ((<>))
import Data.Set               (Set)
import Data.TreeDiff          (ToExpr (..), defaultExprViaShow)
import GHC.Generics           (Generic)
import System.IO.Temp         (createTempDirectory)
import System.Random          (getStdRandom, randomR)
import Test.QuickCheck        (Gen)

import qualified Control.Foldl           as Foldl
import qualified Data.Bifunctor.TH       as TH
import qualified Data.List               as List
import qualified Data.Set                as Set
import qualified System.Directory        as IO
import qualified System.IO               as IO
import qualified Test.QuickCheck         as QC
import qualified Test.QuickCheck.Monadic as QC
import qualified Test.QuickCheck.Random  as QC

import           Test.StateMachine
import qualified Test.StateMachine.Types       as QSM
import qualified Test.StateMachine.Types.Rank2 as Rank2

import Mock

{-------------------------------------------------------------------------------
  File expressions
-------------------------------------------------------------------------------}

data Expr fp =
    Val File
  | Var fp
  deriving (Show, Functor, Foldable, Traversable)

eval :: Expr File -> File
eval (Val f) = f
eval (Var f) = f

{-------------------------------------------------------------------------------
  Language
-------------------------------------------------------------------------------}

data Cmd fp h =
    MkDir Dir
  | Open File
  | Write h String
  | Close h
  | Read (Expr fp)
  deriving (Show)

data Success fp h =
    Unit ()
  | Handle fp h
  | String String
  deriving (Show, Eq)

newtype Resp fp h = Resp (Either Err (Success fp h))
  deriving (Show, Eq)

TH.deriveBifunctor     ''Cmd
TH.deriveBifoldable    ''Cmd
TH.deriveBitraversable ''Cmd

TH.deriveBifunctor     ''Success
TH.deriveBifoldable    ''Success
TH.deriveBitraversable ''Success

TH.deriveBifunctor     ''Resp
TH.deriveBifoldable    ''Resp
TH.deriveBitraversable ''Resp

{-------------------------------------------------------------------------------
  Interpreter: mock implementation
-------------------------------------------------------------------------------}

runMock :: Cmd File MHandle -> Mock -> (Resp File MHandle, Mock)
runMock (MkDir d)   = first (Resp . fmap Unit)       . mMkDir d
runMock (Open  f)   = first (Resp . fmap (Handle f)) . mOpen  f
runMock (Write h s) = first (Resp . fmap Unit)       . mWrite h s
runMock (Close h)   = first (Resp . fmap Unit)       . mClose h
runMock (Read  e)   = first (Resp . fmap String)     . mRead  (eval e)

{-------------------------------------------------------------------------------
  Interpreter: real I/O
-------------------------------------------------------------------------------}

catchErr :: IO (Success fp h) -> IO (Resp fp h)
catchErr act = catch (Resp . Right <$> act) handler
  where
    handler :: IOError -> IO (Resp fp h)
    handler e = maybe (throwIO e) (return . Resp . Left) (fromIOError e)

runIO :: FilePath -> Cmd File IO.Handle -> IO (Resp File IO.Handle)
runIO root = catchErr . go
  where
    go :: Cmd File IO.Handle -> IO (Success File IO.Handle)
    go (MkDir d)   = Unit     <$> IO.createDirectory (dirFP root d)
    go (Open  f)   = Handle f <$> IO.openFile (fileFP root f) IO.AppendMode
    go (Write h s) = Unit     <$> IO.hPutStr h s
    go (Close h)   = Unit     <$> IO.hClose  h
    go (Read  e)   = String   <$> IO.readFile (fileFP root (eval e))

{-------------------------------------------------------------------------------
  Working with references
-------------------------------------------------------------------------------}

newtype At f r = At (f (Reference File r) (Reference IO.Handle r))

deriving instance Show (f (Reference File r) (Reference IO.Handle r))
               => Show (At f r)

type f :@ r = At f r

type RefEnv k a r = [(Reference k r, a)]

(!) :: (Eq1 r, Eq k) => RefEnv k a r -> Reference k r -> a
env ! r = fromJust (lookup r env)

{-------------------------------------------------------------------------------
  Relating the mock model to the real implementation
-------------------------------------------------------------------------------}

type HandleRefs r = RefEnv IO.Handle MHandle r
type FileRefs   r = RefEnv File      File       r

data Model r = Model Mock (FileRefs r) (HandleRefs r)
  deriving (Generic)

deriving instance Show1 r => Show (Model r)

initModel :: Model r
initModel = Model emptyMock [] []

toMock :: (Bifunctor t, Eq1 r) => Model r -> t :@ r -> t File MHandle
toMock (Model _ fs hs) (At fr) = bimap (fs !) (hs !) fr

step :: Eq1 r => Model r -> Cmd :@ r -> (Resp File MHandle, Mock)
step m@(Model mock _ _) c = runMock (toMock m c) mock

{-------------------------------------------------------------------------------
  Events
-------------------------------------------------------------------------------}

data Event r = Event {
    before   :: Model  r
  , cmd      :: Cmd :@ r
  , after    :: Model  r
  , mockResp :: Resp File MHandle
  }

deriving instance Show1 r => Show (Event r)

lockstep :: Eq1 r
         => Model   r
         -> Cmd  :@ r
         -> Resp :@ r
         -> Event   r
lockstep m@(Model _ fs hs) c (At resp) = Event {
      before   = m
    , cmd      = c
    , after    = Model mock' (fs <> fs') (hs <> hs')
    , mockResp = resp'
    }
  where
    (resp', mock') = step m c
    fs' = zip (toList1 resp) (toList1 resp')
    hs' = zip (toList2 resp) (toList2 resp')

toList1 :: Bifoldable t => t a b -> [a]
toList1 = bifoldMap (:[]) (const [])

toList2 :: Bifoldable t => t a b -> [b]
toList2 = bifoldMap (const []) (:[])

{-------------------------------------------------------------------------------
  Generator
-------------------------------------------------------------------------------}

generator :: Model Symbolic -> Maybe (Gen (Cmd :@ Symbolic))
generator (Model _ _ hs) = Just $ QC.oneof $ concat [
      withoutHandle
    , if null hs then [] else withHandle
    ]
  where
    withoutHandle :: [Gen (Cmd :@ Symbolic)]
    withoutHandle = [
          fmap At $ MkDir <$> genDir
        , fmap At $ Open  <$> genFile
        , fmap At $ Read  <$> (Val <$> genFile)
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
shrinker (Model _ fs _) (At cmd) =
    case cmd of
      Open (File (Dir []) ('t' : n)) ->
        [openTemp n' | n' <- QC.shrink (read n)]
      Open _ ->
        [openTemp 100]
      Read (Val f) ->
        [At $ Read (Var r) | r <- mapMaybe (matches f) fs ]
      _otherwise ->
        []
  where
    matches :: File -> (r, File) -> Maybe r
    matches f (r, f') | f == f'   = Just r
                      | otherwise = Nothing

    openTemp :: Int -> Cmd :@ Symbolic
    openTemp n = At $ Open (File (Dir []) ('t' : show n))

{-------------------------------------------------------------------------------
  The state machine proper
-------------------------------------------------------------------------------}

transition :: Eq1 r => Model r -> Cmd :@ r -> Resp :@ r -> Model r
transition m c = after . lockstep m c

precondition :: Model Symbolic -> Cmd :@ Symbolic -> Logic
precondition (Model _ fs hs) (At c) =
        forall (toList1 c) (`elem` map fst fs)
    :&& forall (toList2 c) (`elem` map fst hs)

postcondition :: Model Concrete -> Cmd :@ Concrete -> Resp :@ Concrete -> Logic
postcondition m c r =
    toMock (after e) r .== mockResp e
  where
    e = lockstep m c r

semantics :: FilePath -> Cmd :@ Concrete -> IO (Resp :@ Concrete)
semantics root (At c) =
    At . bimap QSM.reference QSM.reference <$>
      runIO root (bimap QSM.concrete QSM.concrete c)

symbolicResp :: Model Symbolic -> Cmd :@ Symbolic -> GenSym (Resp :@ Symbolic)
symbolicResp m c = At <$> bitraverse (const QSM.genSym) (const QSM.genSym) resp
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

instance Bifunctor f => Rank2.Functor (At f) where
  fmap = \f (At x) -> At $ bimap (lift f) (lift f) x
    where
      lift :: (r x -> r' x) -> QSM.Reference x r -> QSM.Reference x r'
      lift f (QSM.Reference x) = QSM.Reference (f x)

instance Bifoldable f => Rank2.Foldable (At f) where
  foldMap = \f (At x) -> bifoldMap (lift f) (lift f) x
    where
      lift :: (r x -> m) -> QSM.Reference x r -> m
      lift f (QSM.Reference x) = f x

instance Bitraversable t => Rank2.Traversable (At t) where
  traverse = \f (At x) -> At <$> bitraverse (lift f) (lift f) x
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

repeatedly :: (a -> b -> b) -> ([a] -> b -> b)
repeatedly = flip . List.foldl' . flip
