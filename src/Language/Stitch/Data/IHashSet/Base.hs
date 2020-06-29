{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

------------------------------------------------------------------------
-- A set of /hashable/ values.  A set cannot contain duplicate items.
-- A 'HashSet' makes no guarantees as to the order of its elements.
--
-- The implementation is based on /hash array mapped trie/.  A
-- 'HashSet' is often faster than other tree-based set types,
-- especially when value comparison is expensive, as in the case of
-- strings.
--
-- Many operations have a average-case complexity of /O(log n)/.  The
-- implementation uses a large base (i.e. 16) so in practice these
-- operations are constant time.

module Language.Stitch.Data.IHashSet.Base
    (
      IHashSet

    -- * Construction
    , empty
    , singleton

    -- * Combine
    , union
    , unions

    -- * Basic interface
    , null
    , size
    , member
    , insert
    , delete

    -- * Transformations
    , map

      -- * Difference and intersection
    , difference
    , intersection

    -- * Folds
    , foldl'
    , foldr

    -- * Filter
    , filter

    -- * Conversions

    -- ** Lists
    , toList
    , fromList

    -- * HashMaps
    , toMap
    , fromMap

    -- Exported from Data.HashMap.{Strict, Lazy}
    , keysSet
    ) where

import Language.Stitch.Data.IHashMap.Base (IHashMap, foldrWithKey, equalKeys)
import Data.Hashable (Hashable(..))
import GHC.Exts (build)
import Prelude hiding (filter, foldr, map, null)
import qualified Language.Stitch.Data.IHashMap.Base as H
import qualified Data.List as List
import Data.Typeable (Typeable)
import Control.DeepSeq (NFData(..))
import Text.Read

import qualified GHC.Exts as Exts

import Data.Functor.Const
import Data.Type.Equality

import Language.Stitch.Data.IHashable
import Language.Stitch.Data.Exists

-- | A set of values.  A set cannot contain duplicate values.
newtype IHashSet a = IHashSet {
      asMap :: IHashMap a (Const ())
    } deriving (Typeable)

type role IHashSet nominal

instance (forall i. NFData (a i)) => NFData (IHashSet a) where
  rnf = rnf . asMap
  {-# INLINE rnf #-}

instance (TestEquality a) => Eq (IHashSet a) where
    IHashSet a == IHashSet b = equalKeys a b
    {-# INLINE (==) #-}

instance (IHashable a, TestEquality a) => Semigroup (IHashSet a) where
    (<>) = union
    {-# INLINE (<>) #-}

instance (IHashable a, TestEquality a) => Monoid (IHashSet a) where
    mempty = empty
    {-# INLINE mempty #-}
    mappend = (<>)
    {-# INLINE mappend #-}

instance (TestEquality a, IHashable a, forall i. Read (a i)) => Read (IHashSet a) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault

instance (forall i. Show (a i)) => Show (IHashSet a) where
  showsPrec d m = showParen (d > 10) $
    showString "fromList " . shows (toList m)

instance (IHashable a) => Hashable (IHashSet a) where
    hashWithSalt salt = hashWithSalt salt . asMap

-- | /O(1)/ Construct an empty set.
empty :: IHashSet a
empty = IHashSet H.empty

-- | /O(1)/ Construct a set with a single element.
singleton :: IHashable a => a i -> IHashSet a
singleton a = IHashSet (H.singleton a (Const ()))
{-# INLINABLE singleton #-}

-- | /O(1)/ Convert to the equivalent 'HashMap'.
toMap :: IHashSet a -> IHashMap a (Const ())
toMap = asMap

-- | /O(1)/ Convert from the equivalent 'HashMap'.
fromMap :: IHashMap a (Const ()) -> IHashSet a
fromMap = IHashSet

-- | /O(n)/ Produce a 'IHashSet' of all the keys in the given 'HashMap'.
--
-- @since 0.2.10.0
keysSet :: IHashMap k a -> IHashSet k
keysSet m = fromMap (H.map (const (Const ())) m)

-- | /O(n+m)/ Construct a set containing all elements from both sets.
--
-- To obtain good performance, the smaller set must be presented as
-- the first argument.
union :: (TestEquality a, IHashable a) => IHashSet a -> IHashSet a -> IHashSet a
union s1 s2 = IHashSet $ H.union (asMap s1) (asMap s2)
{-# INLINE union #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: (TestEquality a, IHashable a) => [IHashSet a] -> IHashSet a
unions = List.foldl' union empty
{-# INLINE unions #-}

-- | /O(1)/ Return 'True' if this set is empty, 'False' otherwise.
null :: IHashSet a -> Bool
null = H.null . asMap
{-# INLINE null #-}

-- | /O(n)/ Return the number of elements in this set.
size :: IHashSet a -> Int
size = H.size . asMap
{-# INLINE size #-}

-- | /O(log n)/ Return 'True' if the given value is present in this
-- set, 'False' otherwise.
member :: (TestEquality a, IHashable a) => a i -> IHashSet a -> Bool
member a s = case H.lookup a (asMap s) of
               Just _ -> True
               _      -> False
{-# INLINABLE member #-}

-- | /O(log n)/ Add the specified value to this set.
insert :: (TestEquality a, IHashable a) => a i -> IHashSet a -> IHashSet a
insert a = IHashSet . H.insert a (Const ()) . asMap
{-# INLINABLE insert #-}

-- | /O(log n)/ Remove the specified value from this set if
-- present.
delete :: (TestEquality a, IHashable a) => a i -> IHashSet a -> IHashSet a
delete a = IHashSet . H.delete a . asMap
{-# INLINABLE delete #-}

-- | /O(n)/ Transform this set by applying a function to every value.
-- The resulting set may be smaller than the source.
map :: (IHashable b, TestEquality b) => (forall i. a i -> b i) -> IHashSet a -> IHashSet b
map f = fromList . List.map (mapEx f) . toList
{-# INLINE map #-}

-- | /O(n)/ Difference of two sets. Return elements of the first set
-- not existing in the second.
difference :: (TestEquality a, IHashable a) => IHashSet a -> IHashSet a -> IHashSet a
difference (IHashSet a) (IHashSet b) = IHashSet (H.difference a b)
{-# INLINABLE difference #-}

-- | /O(n)/ Intersection of two sets. Return elements present in both
-- the first set and the second.
intersection :: (TestEquality a, IHashable a) => IHashSet a -> IHashSet a -> IHashSet a
intersection (IHashSet a) (IHashSet b) = IHashSet (H.intersection a b)
{-# INLINABLE intersection #-}

-- | /O(n)/ Reduce this set by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before before using the result in the next
-- application.  This function is strict in the starting value.
foldl' :: forall a b. (forall i. a -> b i -> a) -> a -> IHashSet b -> a
foldl' f z0 = H.foldlWithKey' g z0 . asMap
  where g z k _ = f z k
{-# INLINE foldl' #-}

-- | /O(n)/ Reduce this set by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (forall i. b i -> a -> a) -> a -> IHashSet b -> a
foldr f z0 = foldrWithKey g z0 . asMap
  where g k _ z = f k z
{-# INLINE foldr #-}

-- | /O(n)/ Filter this set by retaining only elements satisfying a
-- predicate.
filter :: (forall i. a i -> Bool) -> IHashSet a -> IHashSet a
filter p = IHashSet . H.filterWithKey q . asMap
  where q k _ = p k
{-# INLINE filter #-}

-- | /O(n)/ Return a list of this set's elements.  The list is
-- produced lazily.
toList :: IHashSet a -> [Ex a]
toList t = build (\ c z -> foldrWithKey (\k _ -> c (Ex k)) z (asMap t))
{-# INLINE toList #-}

-- | /O(n*min(W, n))/ Construct a set from a list of elements.
fromList :: (TestEquality a, IHashable a) => [Ex a] -> IHashSet a
fromList = IHashSet . List.foldl' (\ m (Ex k) -> H.insert k (Const ()) m) H.empty
{-# INLINE fromList #-}

instance (TestEquality a, IHashable a) => Exts.IsList (IHashSet a) where
    type Item (IHashSet a) = Ex a
    fromList = fromList
    toList   = toList
