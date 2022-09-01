{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

{-# OPTIONS_GHC -Wall #-}

-- | Generalized variables
--
-- Crucially, these variables support `Functor` as well as `fmapEither`.
--
-- Intended for qualified import.
--
-- > import StateModel.Lockstep.GVar (GVar, Operation(..), InterpretOp(..))
-- > import StateModel.Lockstep.GVar qualified as GVar
module StateModel.Lockstep.GVar (
    GVar -- opaque
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
import Data.Bifunctor
import Data.Either (isRight)
import Data.Functor.Identity
import Data.Kind
import Data.Typeable

import Test.QuickCheck.StateModel (Var(..), LookUp, Any(..))

import StateModel.Lockstep.EnvF (EnvF)
import StateModel.Lockstep.EnvF qualified as EnvF

{-------------------------------------------------------------------------------
  Main type
-------------------------------------------------------------------------------}

data GVar :: (Type -> Type -> Type) -> Type -> Type where
  GVar :: Typeable x => Var x -> op x y -> GVar op y

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

class Operation (op :: Type -> Type -> Type) where
  opIdentity  :: op a a

class Operation op => InterpretOp op (f :: Type -> Type) where
  interpretOp :: op a b -> f a -> Either String (f b)

{-------------------------------------------------------------------------------
  Example (but useful) 'Operation' example

  NOTE: We do not give a general "composition" constructor as this would make
  it more difficult to give a meaningful Eq instance.
-------------------------------------------------------------------------------}

data Op e a b where
  OpId    :: Op e a a
  OpRight :: Op e a (Either e c) -> Op e a c

deriving instance Show (Op e a b)
deriving instance Eq   (Op e a b)

instance Operation (Op e) where
  opIdentity = OpId

instance Show e => InterpretOp (Op e) Identity where
  interpretOp = \op -> fmap Identity . go op . runIdentity
    where
      go :: Op e a b -> a -> Either String b
      go OpId         = Right
      go (OpRight op) = first show <=< go op

{-------------------------------------------------------------------------------
  Construction
-------------------------------------------------------------------------------}

fromVar :: Operation op => Typeable a => Var a -> GVar op a
fromVar var = GVar var opIdentity

map :: (forall x. op x a -> op x b) -> GVar op a -> GVar op b
map f (GVar var op) = GVar var (f op)

{-------------------------------------------------------------------------------
  Interaction with 'Env' and 'EnvF'
-------------------------------------------------------------------------------}

lookUpEnv :: InterpretOp op Identity => LookUp -> GVar op a -> Either String a
lookUpEnv lookUp (GVar var op) =
    fmap runIdentity $ interpretOp op (Identity (lookUp var))

lookUpEnvF ::
      (Typeable f, InterpretOp op f)
   => GVar op a -> EnvF f -> Either String (f a)
lookUpEnvF (GVar var op) env =
    case EnvF.lookup var env of
      Nothing  -> Left $ "Variable " ++ show var ++ " not in the environment"
      Just val -> interpretOp op val

definedInEnvF ::
     (Typeable f, InterpretOp op f)
  => EnvF f -> Any (GVar op) -> Bool
definedInEnvF _    (Error _)  = False
definedInEnvF envF (Some var) = isRight $ lookUpEnvF var envF