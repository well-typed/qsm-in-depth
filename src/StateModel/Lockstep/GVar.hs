{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wall -Wredundant-constraints #-}

-- | Generalized variables
--
-- Crucially, these variables support `Functor` as well as `fmapEither`.
--
-- Intended for qualified import.
--
-- > import StateModel.Lockstep.GVar (GVar, AnyGVar(..), InterpretOp(..))
-- > import StateModel.Lockstep.GVar qualified as GVar
module StateModel.Lockstep.GVar (
    GVar -- opaque
  , AnyGVar(..)
    -- * Operations
  , Operation(..)
  , InterpretOp(..)
    -- ** Example operation type
  , Op(..)
    -- * Construction
  , fromVar
  , map
    -- * Interaction with 'Env' and 'EnvF'
  , lookUpEnv
  , lookUpEnvF
  , definedInEnvF
  ) where

import Prelude hiding (map)

import Control.Monad
import Data.Functor.Identity
import Data.Maybe (isJust, fromJust)
import Data.Typeable

import Test.QuickCheck.StateModel (Var(..), LookUp)

import StateModel.Lockstep.EnvF (EnvF)
import StateModel.Lockstep.EnvF qualified as EnvF
import GHC.Show (appPrec)

{-------------------------------------------------------------------------------
  Main type
-------------------------------------------------------------------------------}

data GVar op f where
  GVar :: (Show x, Typeable x, Eq x) => Var x -> op x y -> GVar op y

data AnyGVar op where
  SomeGVar :: (Show y, Typeable y, Eq y) => GVar op y -> AnyGVar op

deriving instance (forall x. Show (op x a)) => Show (GVar op a)

instance (forall x. Eq (op x a)) => Eq (GVar op a) where
  (==) = \(GVar x op) (GVar x' op') -> aux x x' op op'
    where
      aux :: forall x x'.
           (Typeable x, Typeable x')
        => Var x -> Var x' -> op x a -> op x' a -> Bool
      aux x x' op op' =
          case eqT @x @x' of
            Nothing   -> False
            Just Refl -> (x, op) == (x', op')

{-------------------------------------------------------------------------------
  Operations

  This is basically reified functions. We reify them for two reasons:

  1. It means we can define proper Show/Eq instances for 'GVar'
  2. It allows us to give separate interpretations of 'Op' for mock values
     and for real values.
-------------------------------------------------------------------------------}

class Operation op where
  opIdentity :: op a a

class Operation op => InterpretOp op f where
  intOp ::
       (Show a, Show b, Typeable a, Typeable b, Eq a, Eq b)
    => op a b -> f a -> Maybe (f b)

{-------------------------------------------------------------------------------
  Example (but very useful) 'Operation' example

  Because this is designed for testing where we want everything to be 'Show'able
  and 'Typeable', matching on 'Op' might reveal some additonal constrants.
  This is useful in 'OpComp' where we have an existential variable (@b@), but
  it's also useful for example in 'OpRight': the caller might have a constraint
  @Show (Either a b)@, but that doesn't give them a way to obtain a constraint
  @Show a@; the implication only goes one way.

  (These are the same constraints that 'Any' imposes.)
-------------------------------------------------------------------------------}

data Op a b where
  OpId    :: Op a a
  OpFst   :: (Show b, Typeable b, Eq b) => Op (a, b) a
  OpSnd   :: (Show b, Typeable b, Eq b) => Op (b, a) a
  OpLeft  :: (Show b, Typeable b, Eq b) => Op (Either a b) a
  OpRight :: (Show b, Typeable b, Eq b) => Op (Either b a) a
  OpComp  :: (Show b, Typeable b, Eq b) => Op b c -> Op a b -> Op a c

instance Eq (Op a b) where
  op == op' =
      case (op, op') of
        (OpId       , OpId        ) -> True
        (OpFst      , OpFst       ) -> True
        (OpSnd      , OpSnd       ) -> True
        (OpLeft     , OpLeft      ) -> True
        (OpRight    , OpRight     ) -> True
        (OpComp g f , OpComp g' f') -> auxComp (g, f) (g', f')
        _otherwise                  -> False
    where
      auxComp :: forall x y1 y2 z.
           (Typeable y1, Typeable y2)
        => (Op y1 z, Op x y1) -> (Op y2 z, Op x y2) -> Bool
      auxComp (g, f) (g', f') =
          case eqT @y1 @y2 of
            Nothing   -> False
            Just Refl -> (g, f) == (g', f')

      _coveredAllCases :: Op a b -> ()
      _coveredAllCases = \case
          OpId     -> ()
          OpFst    -> ()
          OpSnd    -> ()
          OpLeft   -> ()
          OpRight  -> ()
          OpComp{} -> ()

instance Show (Op a b) where
  showsPrec p = \op -> case op of
      OpComp{} -> showParen (p > appPrec) (go op)
      _        -> go op
    where
      go :: Op x y -> String -> String
      go OpId         = showString "id"
      go OpFst        = showString "fst"
      go OpSnd        = showString "snd"
      go OpLeft       = showString "fromLeft"
      go OpRight      = showString "fromRight"
      go (OpComp g f) = go g . showString " . " . go f

instance Operation Op where
  opIdentity = OpId

instance InterpretOp Op Identity where
  intOp = \op -> fmap Identity . go op . runIdentity
    where
      go :: Op a b -> a -> Maybe b
      go OpId         = Just
      go OpFst        = Just . fst
      go OpSnd        = Just . snd
      go OpLeft       = either Just (const Nothing)
      go OpRight      = either (const Nothing) Just
      go (OpComp g f) = go g <=< go f

{-------------------------------------------------------------------------------
  Construction
-------------------------------------------------------------------------------}

fromVar :: (Operation op, Show a, Typeable a, Eq a) => Var a -> GVar op a
fromVar var = GVar var opIdentity

map :: (forall x. op x a -> op x b) -> GVar op a -> GVar op b
map f (GVar var op) = GVar var (f op)

{-------------------------------------------------------------------------------
  Interaction with 'Env' and 'EnvF'
-------------------------------------------------------------------------------}

-- | Lookup 'GVar' given a lookup function for 'Var'
--
-- The variable must be in the environment and evaluation must succeed.
-- This is normally guaranteed by the default test 'precondition'.
lookUpEnv ::
     (InterpretOp op Identity, Show a, Typeable a, Eq a)
  => LookUp -> GVar op a -> a
lookUpEnv lookUp (GVar var op) =
    fromJust $ fmap runIdentity $ intOp op (Identity (lookUp var))

-- | Lookup 'GVar'
--
-- The variable must be in the environment and evaluation must succeed.
-- This is normally guaranteed by the default test 'precondition'.
lookUpEnvF ::
      (Typeable f, Typeable a, Show a, Eq a, InterpretOp op f)
   => EnvF f -> GVar op a -> f a
lookUpEnvF env (GVar var op) = fromJust $
    EnvF.lookup var env >>= intOp op

-- | Check if the variable is well-defined and evaluation will succeed.
definedInEnvF :: (Typeable f, InterpretOp op f) => EnvF f -> AnyGVar op -> Bool
definedInEnvF env (SomeGVar (GVar var op)) = isJust $
    EnvF.lookup var env >>= intOp op
