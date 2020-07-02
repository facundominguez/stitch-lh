{-# LANGUAGE PolyKinds, GADTs, RankNTypes, QuantifiedConstraints #-}

-- Support for existentials

module Language.Stitch.Data.Exists (
    Ex(..), packEx, unpackEx, mapEx
  , SingEx(..), packSingEx, unpackSingEx
  ) where

import Language.Stitch.Data.Singletons
import Data.Kind

import Control.Arrow ( first )

-- | Pack a type whose last index is to be existentially bound
data Ex :: (k -> Type) -> Type where
  Ex :: a i -> Ex a

instance (forall i. Read (a i)) => Read (Ex a) where
  readsPrec prec s = fmap (first Ex) $ readsPrec prec s

instance (forall i. Show (a i)) => Show (Ex a) where
  show (Ex x) = show x

-- | Pack an existential
packEx :: a i -> Ex a
packEx = Ex

-- | Unpack an existential (CPS-style)
unpackEx :: Ex a -> (forall i. a i -> r) -> r
unpackEx (Ex x) k = k x

-- | Map a function over the packed existential
mapEx :: (forall i. a i -> b i) -> Ex a -> Ex b
mapEx f (Ex x) = Ex (f x)

-- | Like 'Ex', but stores a singleton describing the
-- existentially bound index
data SingEx :: (k -> Type) -> Type where
  SingEx :: Sing i -> a i -> SingEx a

-- | Pack an existential with an explicit singleton
packSingEx :: Sing i -> a i -> SingEx a
packSingEx = SingEx

-- | Unpack an existential with an explicit singleton (CPS-style)
unpackSingEx :: SingEx a -> (forall i. Sing i -> a i -> r) -> r
unpackSingEx (SingEx s x) k = k s x
