{-# LANGUAGE TypeInType, MultiParamTypeClasses, FunctionalDependencies,
             FlexibleInstances, UndecidableInstances,
             GeneralizedNewtypeDeriving, TypeFamilies,
             ScopedTypeVariables, TypeApplications, FlexibleContexts,
             RankNTypes, TupleSections, StandaloneDeriving, DeriveTraversable #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Stitch.Control.Monad.HReader where

import Text.Parsec.Prim
import Control.Monad.Reader

import Data.Kind

-- These orphan instances are necessary for the ParsecT instance below.
-- I have no idea why they aren't defined in Parsec.
deriving instance Foldable Consumed
deriving instance Traversable Consumed

-- | Classifies a reader monad where a local computation can
-- change the type of the environment
class Monad m => MonadHReader r1 m | m -> r1 where
  -- | Update the environment to a new type
  type SetEnv r2 m :: Type -> Type

  -- | Compute with a local environment, possibly of a different
  -- type than the outer environment
  hlocal :: (r1 -> r2) -> (Monad (SetEnv r2 m) => SetEnv r2 m a) -> m a

instance Monad m => MonadHReader r1 (ReaderT r1 m) where
  type SetEnv r2 (ReaderT r1 m) = ReaderT r2 m
  hlocal f action = ReaderT $ runReaderT action . f

instance MonadHReader r1 m => MonadHReader r1 (ParsecT s u m) where
  type SetEnv r2 (ParsecT s u m) = ParsecT s u (SetEnv r2 m)
  hlocal f action = mkPT $ \s ->
    hlocal f $ traverse (fmap return) =<< runParsecT action s

-- A more complete treatment would have instances for other monad transformer types
