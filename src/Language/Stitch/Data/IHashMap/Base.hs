-- As adapted from unordered-containers
-- https://github.com/tibbe/unordered-containers

{-# LANGUAGE BangPatterns, DeriveDataTypeable, MagicHash #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fno-full-laziness -funbox-strict-fields #-}

module Language.Stitch.Data.IHashMap.Base
    (
      IHashMap(..)
    , IHashable(..)
    , Leaf(..)

      -- * Construction
    , empty
    , singleton

      -- * Basic interface
    , null
    , size
    , member
    , lookup
    , lookupDefault
    , (!)
    , insert
    , insertWith
    , unsafeInsert
    , delete
    , adjust
    , update
    , alter
    , alterF

      -- * Combine
      -- ** Union
    , union
    , unionWith
    , unionWithKey
    , unions

      -- * Transformations
    , map
    , mapWithKey
    , traverseWithKey

      -- * Difference and intersection
    , difference
    , differenceWith
    , intersection
    , intersectionWith
    , intersectionWithKey

      -- * Folds
    , foldl'
    , foldlWithKey'
    , foldr
    , foldrWithKey

      -- * Filter
    , mapMaybe
    , mapMaybeWithKey
    , filter
    , filterWithKey

      -- * Conversions
    , keys
    , elems

      -- ** Lists
    , toList
    , fromList
    , fromListWith

      -- Internals used by the strict version
    , Hash
    , Bitmap
    , bitmapIndexedOrFull
    , collision
    , hash
    , mask
    , index
    , bitsPerSubkey
    , fullNodeMask
    , sparseIndex
    , two
    , unionArrayBy
    , update16
    , update16M
    , update16With'
    , updateOrConcatWith
    , updateOrConcatWithKey
    , filterMapAux
    , equalKeys
    , lookupRecordCollision
    , LookupRes(..)
    , insert'
    , delete'
    , lookup'
    , insertNewKey
    , insertKeyExists
    , deleteKeyExists
    , insertModifying
    , ptrEq
    , adjust#
    ) where

import Control.DeepSeq ( NFData(rnf) )
import Control.Monad.ST (ST)
import Data.Bits ((.&.), (.|.), complement, popCount)
import qualified Data.List as L
import GHC.Exts ((==#), build, reallyUnsafePtrEquality#)
import Prelude hiding (filter, foldr, lookup, map, null, pred)
import Text.Read hiding (step)

import qualified Language.Stitch.Data.IHashMap.Array as A
import qualified Data.Hashable as H
import Data.Hashable (Hashable)
import Control.Monad.ST (runST)
import Language.Stitch.Data.IHashMap.UnsafeShift (unsafeShiftL, unsafeShiftR)
import Language.Stitch.Data.IHashMap.List (isPermutationBy)
import Data.Typeable (Typeable)

import GHC.Exts (isTrue#)
import qualified GHC.Exts as Exts

import GHC.Exts (TYPE, Int (..), Int#)

import Data.Functor.Identity (Identity (..))
import Control.Applicative (Const (..))
import Data.Coerce (coerce)

import Data.Type.Equality ( (:~:)(..), TestEquality(..) )
import Language.Stitch.Data.Exists
import Language.Stitch.Data.IHashable

-- | Convenience function.  Compute a hash value for the given value.
hash :: IHashable k => k a -> Hash
hash = fromIntegral . ihash

-- | Conveniently test uninformative equality
eq :: TestEquality a => a i1 -> a i2 -> Bool
eq x y = case testEquality x y of Just _  -> True
                                  Nothing -> False
infix 4 `eq`
{-# INLINE eq #-}

data Leaf k v = forall i. L !(k i) (v i)

instance (TestEquality k, TestEquality v) => Eq (Leaf k v) where
  L k1 v1 == L k2 v2
    | Just _ <- testEquality k1 k2
    , Just _ <- testEquality v1 v2
    = True

    | otherwise
    = False

instance (forall i. NFData (k i), forall i. NFData (v i)) => NFData (Leaf k v) where
  rnf (L k v) = rnf k `seq` rnf v

deriving instance (forall i. Read (k i), forall i. Read (v i)) => Read (Leaf k v)
deriving instance (forall i. Show (k i), forall i. Show (v i)) => Show (Leaf k v)

-- Invariant: The length of the 1st argument to 'Full' is
-- 2^bitsPerSubkey

-- | A map from keys to values.  A map cannot contain duplicate keys;
-- each key can map to at most one value.
data IHashMap k v
    = Empty
    | BitmapIndexed !Bitmap !(A.Array (IHashMap k v))
    | Leaf !Hash !(Leaf k v)
    | Full !(A.Array (IHashMap k v))
    | Collision !Hash !(A.Array (Leaf k v))
      deriving (Typeable)

type role IHashMap nominal representational

instance (forall i. NFData (k i), forall i. NFData (v i)) => NFData (IHashMap k v) where
  rnf Empty                 = ()
  rnf (BitmapIndexed _ ary) = rnf ary
  rnf (Leaf _ l)            = rnf l
  rnf (Full ary)            = rnf ary
  rnf (Collision _ ary)     = rnf ary

instance (TestEquality k, IHashable k) => Semigroup (IHashMap k v) where
  (<>) = union
  {-# INLINE (<>) #-}

instance (TestEquality k, IHashable k) => Monoid (IHashMap k v) where
  mempty = empty
  {-# INLINE mempty #-}
  mappend = (<>)
  {-# INLINE mappend #-}


type Hash   = Word
type Bitmap = Word
type Shift  = Int

instance (TestEquality k, IHashable k, forall i. Read (k i), forall i. Read (e i))
          => Read (IHashMap k e) where
  readPrec = parens $ prec 10 $ do
    Ident "fromList" <- lexP
    xs <- readPrec
    return (fromList xs)

  readListPrec = readListPrecDefault

instance (forall i. Show (k i), forall i. Show (v i)) => Show (IHashMap k v) where
  showsPrec d m = showParen (d > 10) $
    showString "fromList " . shows (toList m)

instance (TestEquality k, TestEquality v) => Eq (IHashMap k v) where
    t1 == t2 = go (toList' t1 []) (toList' t2 [])
      where
        -- If the two trees are the same, then their lists of 'Leaf's and
        -- 'Collision's read from left to right should be the same (modulo the
        -- order of elements in 'Collision').

        go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
          | k1 == k2 &&
            leafEq l1 l2
          = go tl1 tl2
        go (Collision k1 ary1 : tl1) (Collision k2 ary2 : tl2)
          | k1 == k2 &&
            A.length ary1 == A.length ary2 &&
            isPermutationBy leafEq (A.toList ary1) (A.toList ary2)
          = go tl1 tl2
        go [] [] = True
        go _  _  = False

        leafEq (L k v) (L k' v') = eq k k' && eq v v'

-- Same as 'equal' but doesn't compare the values.
equalKeys :: TestEquality k => IHashMap k v -> IHashMap k v' -> Bool
equalKeys t1 t2 = go (toList' t1 []) (toList' t2 [])
  where
    go (Leaf k1 l1 : tl1) (Leaf k2 l2 : tl2)
      | k1 == k2 && leafEq l1 l2
      = go tl1 tl2
    go (Collision k1 ary1 : tl1) (Collision k2 ary2 : tl2)
      | k1 == k2 && A.length ary1 == A.length ary2 &&
        isPermutationBy leafEq (A.toList ary1) (A.toList ary2)
      = go tl1 tl2
    go [] [] = True
    go _  _  = False

    leafEq (L k _) (L k' _) = eq k k'

instance (IHashable k, IHashable v) => Hashable (IHashMap k v) where
    hashWithSalt salt hm = go salt (toList' hm [])
      where
        go :: Int -> [IHashMap k v] -> Int
        go s [] = s
        go s (Leaf _ l : tl)
          = s `hashLeafWithSalt` l `go` tl
        -- For collisions we hashmix hash value
        -- and then array of values' hashes sorted
        go s (Collision h a : tl)
          = (s `H.hashWithSalt` h) `hashCollisionWithSalt` a `go` tl
        go s (_ : tl) = s `go` tl

        hashLeafWithSalt :: Int -> Leaf k v -> Int
        hashLeafWithSalt s (L k v) = s `ihashWithSalt` k `ihashWithSalt` v

        hashCollisionWithSalt :: Int -> A.Array (Leaf k v) -> Int
        hashCollisionWithSalt s
          = L.foldl' H.hashWithSalt s . arrayHashesSorted s

        arrayHashesSorted :: Int -> A.Array (Leaf k v) -> [Int]
        arrayHashesSorted s = L.sort . L.map (hashLeafWithSalt s) . A.toList

  -- Helper to get 'Leaf's and 'Collision's as a list.
toList' :: IHashMap k v -> [IHashMap k v] -> [IHashMap k v]
toList' (BitmapIndexed _ ary) a = A.foldr toList' a ary
toList' (Full ary)            a = A.foldr toList' a ary
toList' l@(Leaf _ _)          a = l : a
toList' c@(Collision _ _)     a = c : a
toList' Empty                 a = a

-- Helper function to detect 'Leaf's and 'Collision's.
isLeafOrCollision :: IHashMap k v -> Bool
isLeafOrCollision (Leaf _ _)      = True
isLeafOrCollision (Collision _ _) = True
isLeafOrCollision _               = False

------------------------------------------------------------------------
-- * Construction

-- | /O(1)/ Construct an empty map.
empty :: IHashMap k v
empty = Empty

-- | /O(1)/ Construct a map with a single element.
singleton :: (IHashable k) => k i -> v i -> IHashMap k v
singleton k v = Leaf (hash k) (L k v)

------------------------------------------------------------------------
-- * Basic interface

-- | /O(1)/ Return 'True' if this map is empty, 'False' otherwise.
null :: IHashMap k v -> Bool
null Empty = True
null _   = False

-- | /O(n)/ Return the number of key-value mappings in this map.
size :: IHashMap k v -> Int
size t = go t 0
  where
    go Empty                !n = n
    go (Leaf _ _)            n = n + 1
    go (BitmapIndexed _ ary) n = A.foldl' (flip go) n ary
    go (Full ary)            n = A.foldl' (flip go) n ary
    go (Collision _ ary)     n = n + A.length ary

-- | /O(log n)/ Return 'True' if the specified key is present in the
-- map, 'False' otherwise.
member :: (TestEquality k, IHashable k) => k i -> IHashMap k a -> Bool
member k m = case lookup k m of
    Nothing -> False
    Just _  -> True
{-# INLINABLE member #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or 'Nothing' if this map contains no mapping for the key.
lookup :: (TestEquality k, IHashable k) => k i -> IHashMap k v -> Maybe (v i)
-- GHC does not yet perform a worker-wrapper transformation on
-- unboxed sums automatically. That seems likely to happen at some
-- point (possibly as early as GHC 8.6) but for now we do it manually.
lookup k m = case lookup# k m of
  (# (# #) | #) -> Nothing
  (# | a #) -> Just a
{-# INLINE lookup #-}

lookup# :: (TestEquality k, IHashable k) => k i -> IHashMap k v -> (# (# #) | v i #)
lookup# k m = lookupCont (\_ -> (# (# #) | #)) (\v _i -> (# | v #)) (hash k) k m
{-# INLINABLE lookup# #-}

-- | lookup' is a version of lookup that takes the hash separately.
-- It is used to implement alterF.
lookup' :: TestEquality k => Hash -> k i -> IHashMap k v -> Maybe (v i)
-- GHC does not yet perform a worker-wrapper transformation on
-- unboxed sums automatically. That seems likely to happen at some
-- point (possibly as early as GHC 8.6) but for now we do it manually.
-- lookup' would probably prefer to be implemented in terms of its own
-- lookup'#, but it's not important enough and we don't want too much
-- code.
lookup' h k m = case lookupRecordCollision# h k m of
  (# (# #) | #) -> Nothing
  (# | (# a, _i #) #) -> Just a
{-# INLINE lookup' #-}

-- The result of a lookup, keeping track of if a hash collision occured.
-- If a collision did not occur then it will have the Int value (-1).
data LookupRes a = Absent | Present a !Int

-- Internal helper for lookup. This version takes the precomputed hash so
-- that functions that make multiple calls to lookup and related functions
-- (insert, delete) only need to calculate the hash once.
--
-- It is used by 'alterF' so that hash computation and key comparison only needs
-- to be performed once. With this information you can use the more optimized
-- versions of insert ('insertNewKey', 'insertKeyExists') and delete
-- ('deleteKeyExists')
--
-- Outcomes:
--   Key not in map           => Absent
--   Key in map, no collision => Present v (-1)
--   Key in map, collision    => Present v position
lookupRecordCollision :: TestEquality k => Hash -> k i -> IHashMap k v -> LookupRes (v i)
lookupRecordCollision h k m = case lookupRecordCollision# h k m of
  (# (# #) | #) -> Absent
  (# | (# a, i #) #) -> Present a (I# i) -- GHC will eliminate the I#
{-# INLINE lookupRecordCollision #-}

-- Why do we produce an Int# instead of an Int? Unfortunately, GHC is not
-- yet any good at unboxing things *inside* products, let alone sums. That
-- may be changing in GHC 8.6 or so (there is some work in progress), but
-- for now we use Int# explicitly here. We don't need to push the Int#
-- into lookupCont because inlining takes care of that.
lookupRecordCollision# :: TestEquality k => Hash -> k i -> IHashMap k v -> (# (# #) | (# v i, Int# #) #)
lookupRecordCollision# h k m =
    lookupCont (\_ -> (# (# #) | #)) (\v (I# i) -> (# | (# v, i #) #)) h k m
-- INLINABLE to specialize to the Eq instance.
{-# INLINABLE lookupRecordCollision# #-}

-- A two-continuation version of lookupRecordCollision. This lets us
-- share source code between lookup and lookupRecordCollision without
-- risking any performance degradation.
--
-- The absent continuation has type @((# #) -> r)@ instead of just @r@
-- so we can be representation-polymorphic in the result type. Since
-- this whole thing is always inlined, we don't have to worry about
-- any extra CPS overhead.
lookupCont ::
  forall rep (r :: TYPE rep) k v i.
     TestEquality k
  => ((# #) -> r)    -- Absent continuation
  -> (v i -> Int -> r) -- Present continuation
  -> Hash -- The hash of the key
  -> k i -> IHashMap k v -> r
lookupCont absent present !h0 !k0 !m0 = go h0 k0 0 m0
  where
    go :: TestEquality k => Hash -> k i -> Int -> IHashMap k v -> r
    go !_ !_ !_ Empty = absent (# #)
    go h k _ (Leaf hx (L kx x))
        | h == hx
        , Just Refl <- testEquality k kx = present x (-1)
        | otherwise                      = absent (# #)
    go h k s (BitmapIndexed b v)
        | b .&. m == 0 = absent (# #)
        | otherwise    =
            go h k (s+bitsPerSubkey) (A.index v (sparseIndex b m))
      where m = mask h s
    go h k s (Full v) =
      go h k (s+bitsPerSubkey) (A.index v (index h s))
    go h k _ (Collision hx v)
        | h == hx   = lookupInArrayCont absent present k v
        | otherwise = absent (# #)
{-# INLINE lookupCont #-}

-- | /O(log n)/ Return the value to which the specified key is mapped,
-- or the default value if this map contains no mapping for the key.
lookupDefault :: (TestEquality k, IHashable k)
              => v i         -- ^ Default value to return.
              -> k i -> IHashMap k v -> v i
lookupDefault def k t = case lookup k t of
    Just v -> v
    _      -> def
{-# INLINABLE lookupDefault #-}

-- | /O(log n)/ Return the value to which the specified key is mapped.
-- Calls 'error' if this map contains no mapping for the key.
(!) :: (TestEquality k, IHashable k) => IHashMap k v -> k i -> v i
(!) m k = case lookup k m of
    Just v  -> v
    Nothing -> error "Data.IHashMap.Base.(!): key not found"
{-# INLINABLE (!) #-}

infixl 9 !

-- | Create a 'Collision' value with two 'Leaf' values.
collision :: Hash -> Leaf k v -> Leaf k v -> IHashMap k v
collision h e1 e2 =
    let v = A.run $ do mary <- A.new 2 e1
                       A.write mary 1 e2
                       return mary
    in Collision h v
{-# INLINE collision #-}

-- | Create a 'BitmapIndexed' or 'Full' node.
bitmapIndexedOrFull :: Bitmap -> A.Array (IHashMap k v) -> IHashMap k v
bitmapIndexedOrFull b ary
    | b == fullNodeMask = Full ary
    | otherwise         = BitmapIndexed b ary
{-# INLINE bitmapIndexedOrFull #-}

-- | /O(log n)/ Associate the specified value with the specified
-- key in this map.  If this map previously contained a mapping for
-- the key, the old value is replaced.
insert :: (TestEquality k, IHashable k) => k i -> v i -> IHashMap k v -> IHashMap k v
insert k v m = insert' (hash k) k v m
{-# INLINABLE insert #-}

insert' :: TestEquality k => Hash -> k i -> v i -> IHashMap k v -> IHashMap k v
insert' h0 k0 v0 m0 = go h0 k0 v0 0 m0
  where
    go !h !k x !_ Empty = Leaf h (L k x)
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = case testEquality ky k of
                    Just Refl -> if x `ptrEq` y
                                 then t
                                 else Leaf h (L k x)
                    Nothing   -> collision h l (L k x)
        | otherwise = runST (two s h k x hy ky y)
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $! Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.index ary i
                !st' = go h k x (s+bitsPerSubkey) st
            in if st' `ptrEq` st
               then t
               else BitmapIndexed b (A.update ary i st')
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) =
        let !st  = A.index ary i
            !st' = go h k x (s+bitsPerSubkey) st
        in if st' `ptrEq` st
            then t
            else Full (update16 ary i st')
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = Collision h (updateOrSnocWith const k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE insert' #-}

-- Insert optimized for the case when we know the key is not in the map.
--
-- It is only valid to call this when the key does not exist in the map.
--
-- We can skip:
--  - the key equality check on a Leaf
--  - check for its existence in the array for a hash collision
insertNewKey :: Hash -> k i -> v i -> IHashMap k v -> IHashMap k v
insertNewKey !h0 !k0 x0 !m0 = go h0 k0 x0 0 m0
  where
    go !h !k x !_ Empty = Leaf h (L k x)
    go h k x s (Leaf hy l@(L ky y))
      | hy == h = collision h l (L k x)
      | otherwise = runST (two s h k x hy ky y)
    go h k x s (BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $! Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.index ary i
                !st' = go h k x (s+bitsPerSubkey) st
            in BitmapIndexed b (A.update ary i st')
      where m = mask h s
            i = sparseIndex b m
    go h k x s (Full ary) =
        let !st  = A.index ary i
            !st' = go h k x (s+bitsPerSubkey) st
        in Full (update16 ary i st')
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = Collision h (snocNewLeaf (L k x) v)
        | otherwise =
            go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
      where
        snocNewLeaf :: Leaf k v -> A.Array (Leaf k v) -> A.Array (Leaf k v)
        snocNewLeaf leaf ary = A.run $ do
          let n = A.length ary
          mary <- A.new_ (n + 1)
          A.copy ary 0 mary 0 n
          A.write mary n leaf
          return mary
{-# NOINLINE insertNewKey #-}


-- Insert optimized for the case when we know the key is in the map.
--
-- It is only valid to call this when the key exists in the map and you know the
-- hash collision position if there was one. This information can be obtained
-- from 'lookupRecordCollision'. If there is no collision pass (-1) as collPos
-- (first argument).
--
-- We can skip the key equality check on a Leaf because we know the leaf must be
-- for this key.
insertKeyExists :: Int -> Hash -> k i -> v i -> IHashMap k v -> IHashMap k v
insertKeyExists !collPos0 !h0 !k0 x0 !m0 = go collPos0 h0 k0 x0 0 m0
  where
    go !_collPos !h !k x !_s (Leaf _hy _kx)
        = Leaf h (L k x)
    go collPos h k x s (BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $ Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st  = A.index ary i
                !st' = go collPos h k x (s+bitsPerSubkey) st
            in BitmapIndexed b (A.update ary i st')
      where m = mask h s
            i = sparseIndex b m
    go collPos h k x s (Full ary) =
        let !st  = A.index ary i
            !st' = go collPos h k x (s+bitsPerSubkey) st
        in Full (update16 ary i st')
      where i = index h s
    go collPos h k x _s (Collision _hy v)
        | collPos >= 0 = Collision h (setAtPosition collPos k x v)
        | otherwise = Empty -- error "Internal error: go {collPos negative}"
    go _ _ _ _ _ Empty = Empty -- error "Internal error: go Empty"

{-# NOINLINE insertKeyExists #-}

-- Replace the ith Leaf with Leaf k v.
--
-- This does not check that @i@ is within bounds of the array.
setAtPosition :: Int -> k i -> v i -> A.Array (Leaf k v) -> A.Array (Leaf k v)
setAtPosition i k x ary = A.update ary i (L k x)
{-# INLINE setAtPosition #-}


-- | In-place update version of insert
unsafeInsert :: (TestEquality k, IHashable k) => k i -> v i -> IHashMap k v -> IHashMap k v
unsafeInsert k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go !h !k x !_ Empty = return $! Leaf h (L k x)
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = case testEquality ky k of
                      Just Refl -> if x `ptrEq` y
                                   then return t
                                   else return $! Leaf h (L k x)
                      Nothing   -> return $! collision h l (L k x)
        | otherwise = two s h k x hy ky y
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexM ary i
            st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdateM ary i st'
            return t
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.indexM ary i
        st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdateM ary i st'
        return t
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = return $! Collision h (updateOrSnocWith const k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE unsafeInsert #-}

-- | Create a map from two key-value pairs which hashes don't collide.
two :: Shift -> Hash -> k i1 -> v i1 -> Hash -> k i2 -> v i2 -> ST s (IHashMap k v)
two = go
  where
    go s h1 k1 v1 h2 k2 v2
        | bp1 == bp2 = do
            st <- go (s+bitsPerSubkey) h1 k1 v1 h2 k2 v2
            ary <- A.singletonM st
            return $! BitmapIndexed bp1 ary
        | otherwise  = do
            mary <- A.new 2 $ Leaf h1 (L k1 v1)
            A.write mary idx2 $ Leaf h2 (L k2 v2)
            ary <- A.unsafeFreeze mary
            return $! BitmapIndexed (bp1 .|. bp2) ary
      where
        bp1  = mask h1 s
        bp2  = mask h2 s
        idx2 | index h1 s < index h2 s = 1
             | otherwise               = 0
{-# INLINE two #-}

-- | /O(log n)/ Associate the value with the key in this map.  If
-- this map previously contained a mapping for the key, the old value
-- is replaced by the result of applying the given function to the new
-- and old value.  Example:
--
-- > insertWith f k v map
-- >   where f new old = new + old
insertWith :: (TestEquality k, IHashable k) => (v i -> v i -> v i) -> k i -> v i -> IHashMap k v
            -> IHashMap k v
-- We're not going to worry about allocating a function closure
-- to pass to insertModifying. See comments at 'adjust'.
insertWith f k new m = insertModifying new (\old -> (# f new old #)) k m
{-# INLINE insertWith #-}

-- | @insertModifying@ is a lot like insertWith; we use it to implement alterF.
-- It takes a value to insert when the key is absent and a function
-- to apply to calculate a new value when the key is present. Thanks
-- to the unboxed unary tuple, we avoid introducing any unnecessary
-- thunks in the tree.
insertModifying :: (TestEquality k, IHashable k) => v i -> (v i -> (# v i #)) -> k i -> IHashMap k v
            -> IHashMap k v
insertModifying x f k0 m0 = go h0 k0 0 m0
  where
    !h0 = hash k0
    go !h !k !_ Empty = Leaf h (L k x)
    go h k s t@(Leaf hy l@(L ky y))
        | hy == h = case testEquality ky k of
                    Just Refl -> case f y of
                                   (# v' #) | ptrEq y v' -> t
                                            | otherwise -> Leaf h (L k (v'))
                    Nothing   -> collision h l (L k x)
        | otherwise = runST (two s h k x hy ky y)
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let ary' = A.insert ary i $! Leaf h (L k x)
            in bitmapIndexedOrFull (b .|. m) ary'
        | otherwise =
            let !st   = A.index ary i
                !st'  = go h k (s+bitsPerSubkey) st
                ary'  = A.update ary i $! st'
            in if ptrEq st st'
               then t
               else BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s t@(Full ary) =
        let !st   = A.index ary i
            !st'  = go h k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in if ptrEq st st'
           then t
           else Full ary'
      where i = index h s
    go h k s t@(Collision hy v)
        | h == hy   =
            let !v' = insertModifyingArr x f k v
            in if A.unsafeSameArray v v'
               then t
               else Collision h v'
        | otherwise = go h k s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE insertModifying #-}

-- Like insertModifying for arrays; used to implement insertModifying
insertModifyingArr :: TestEquality k => v i -> (v i -> (# v i #)) -> k i -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
insertModifyingArr x f k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n = A.run $ do
            -- Not found, append to the end.
            mary <- A.new_ (n + 1)
            A.copy ary 0 mary 0 n
            A.write mary n (L k x)
            return mary
        | otherwise = case A.index ary i of
            (L kx y) | Just Refl <- testEquality k kx
                         -> case f y of
                                      (# y' #) -> if ptrEq y y'
                                                  then ary
                                                  else A.update ary i (L k y')
                     | otherwise -> go k ary (i+1) n
{-# INLINE insertModifyingArr #-}

-- | In-place update version of insertWith
unsafeInsertWith :: forall k v i. (TestEquality k, IHashable k)
                 => (v i -> v i -> v i) -> k i -> v i -> IHashMap k v
                 -> IHashMap k v
unsafeInsertWith f k0 v0 m0 = runST (go h0 k0 v0 0 m0)
  where
    h0 = hash k0
    go :: Hash -> k i -> v i -> Shift -> IHashMap k v -> ST s (IHashMap k v)
    go !h !k x !_ Empty = return $! Leaf h (L k x)
    go h k x s (Leaf hy l@(L ky y))
        | hy == h = case testEquality ky k of
                      Just Refl -> return $! Leaf h (L k (f x y))
                      Nothing   -> return $! collision h l (L k x)
        | otherwise = two s h k x hy ky y
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 = do
            ary' <- A.insertM ary i $! Leaf h (L k x)
            return $! bitmapIndexedOrFull (b .|. m) ary'
        | otherwise = do
            st <- A.indexM ary i
            st' <- go h k x (s+bitsPerSubkey) st
            A.unsafeUpdateM ary i st'
            return t
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) = do
        st <- A.indexM ary i
        st' <- go h k x (s+bitsPerSubkey) st
        A.unsafeUpdateM ary i st'
        return t
      where i = index h s
    go h k x s t@(Collision hy v)
        | h == hy   = return $! Collision h (updateOrSnocWith f k x v)
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE unsafeInsertWith #-}

-- | /O(log n)/ Remove the mapping for the specified key from this map
-- if present.
delete :: (TestEquality k, IHashable k) => k i -> IHashMap k v -> IHashMap k v
delete k m = delete' (hash k) k m
{-# INLINABLE delete #-}

delete' :: TestEquality k => Hash -> k i -> IHashMap k v -> IHashMap k v
delete' h0 k0 m0 = go h0 k0 0 m0
  where
    go !_ !_ !_ Empty = Empty
    go h k _ t@(Leaf hy (L ky _))
        | hy == h && ky `eq` k = Empty
        | otherwise            = t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise =
            let !st = A.index ary i
                !st' = go h k (s+bitsPerSubkey) st
            in if st' `ptrEq` st
                then t
                else case st' of
                Empty | A.length ary == 1 -> Empty
                      | A.length ary == 2 ->
                          case (i, A.index ary 0, A.index ary 1) of
                          (0, _, l) | isLeafOrCollision l -> l
                          (1, l, _) | isLeafOrCollision l -> l
                          _                               -> bIndexed
                      | otherwise -> bIndexed
                    where
                      bIndexed = BitmapIndexed (b .&. complement m) (A.delete ary i)
                l | isLeafOrCollision l && A.length ary == 1 -> l
                _ -> BitmapIndexed b (A.update ary i st')
      where m = mask h s
            i = sparseIndex b m
    go h k s t@(Full ary) =
        let !st   = A.index ary i
            !st' = go h k (s+bitsPerSubkey) st
        in if st' `ptrEq` st
            then t
            else case st' of
            Empty ->
                let ary' = A.delete ary i
                    bm   = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                in BitmapIndexed bm ary'
            _ -> Full (A.update ary i st')
      where i = index h s
    go h k _ t@(Collision hy v)
        | h == hy = case indexOf k v of
            Just i
                | A.length v == 2 ->
                    if i == 0
                    then Leaf h (A.index v 1)
                    else Leaf h (A.index v 0)
                | otherwise -> Collision h (A.delete v i)
            Nothing -> t
        | otherwise = t
{-# INLINABLE delete' #-}

-- | Delete optimized for the case when we know the key is in the map.
--
-- It is only valid to call this when the key exists in the map and you know the
-- hash collision position if there was one. This information can be obtained
-- from 'lookupRecordCollision'. If there is no collision pass (-1) as collPos.
--
-- We can skip:
--  - the key equality check on the leaf, if we reach a leaf it must be the key
deleteKeyExists :: Int -> Hash -> k i -> IHashMap k v -> IHashMap k v
deleteKeyExists !collPos0 !h0 !k0 !m0 = go collPos0 h0 k0 0 m0
  where
    go :: Int -> Hash -> k i -> Int -> IHashMap k v -> IHashMap k v
    go !_collPos !_h !_k !_s (Leaf _ _) = Empty
    go collPos h k s (BitmapIndexed b ary) =
            let !st = A.index ary i
                !st' = go collPos h k (s+bitsPerSubkey) st
            in case st' of
                Empty | A.length ary == 1 -> Empty
                      | A.length ary == 2 ->
                          case (i, A.index ary 0, A.index ary 1) of
                          (0, _, l) | isLeafOrCollision l -> l
                          (1, l, _) | isLeafOrCollision l -> l
                          _                               -> bIndexed
                      | otherwise -> bIndexed
                    where
                      bIndexed = BitmapIndexed (b .&. complement m) (A.delete ary i)
                l | isLeafOrCollision l && A.length ary == 1 -> l
                _ -> BitmapIndexed b (A.update ary i st')
      where m = mask h s
            i = sparseIndex b m
    go collPos h k s (Full ary) =
        let !st   = A.index ary i
            !st' = go collPos h k (s+bitsPerSubkey) st
        in case st' of
            Empty ->
                let ary' = A.delete ary i
                    bm   = fullNodeMask .&. complement (1 `unsafeShiftL` i)
                in BitmapIndexed bm ary'
            _ -> Full (A.update ary i st')
      where i = index h s
    go collPos h _ _ (Collision _hy v)
      | A.length v == 2
      = if collPos == 0
        then Leaf h (A.index v 1)
        else Leaf h (A.index v 0)
      | otherwise = Collision h (A.delete v collPos)
    go !_ !_ !_ !_ Empty = Empty -- error "Internal error: deleteKeyExists empty"
{-# NOINLINE deleteKeyExists #-}

-- | /O(log n)/ Adjust the value tied to a given key in this map only
-- if it is present. Otherwise, leave the map alone.
adjust :: (TestEquality k, IHashable k) => (v i -> v i) -> k i -> IHashMap k v -> IHashMap k v
-- This operation really likes to leak memory, so using this
-- indirect implementation shouldn't hurt much. Furthermore, it allows
-- GHC to avoid a leak when the function is lazy. In particular,
--
--     adjust (const x) k m
-- ==> adjust# (\v -> (# const x v #)) k m
-- ==> adjust# (\_ -> (# x #)) k m
adjust f k m = adjust# (\v -> (# f v #)) k m
{-# INLINE adjust #-}

-- | Much like 'adjust', but not inherently leaky.
adjust# :: (TestEquality k, IHashable k) => (v i -> (# v i #)) -> k i -> IHashMap k v -> IHashMap k v
adjust# f k0 m0 = go h0 k0 0 m0
  where
    h0 = hash k0
    go !_ !_ !_ Empty = Empty
    go h k _ t@(Leaf hy (L ky y))
        | hy == h
        , Just Refl <- testEquality ky k
        = case f y of
            (# y' #) | ptrEq y y' -> t
                     | otherwise -> Leaf h (L k y')
        | otherwise          = t
    go h k s t@(BitmapIndexed b ary)
        | b .&. m == 0 = t
        | otherwise = let !st   = A.index ary i
                          !st'  = go h k (s+bitsPerSubkey) st
                          ary' = A.update ary i $! st'
                      in if ptrEq st st'
                         then t
                         else BitmapIndexed b ary'
      where m = mask h s
            i = sparseIndex b m
    go h k s t@(Full ary) =
        let i    = index h s
            !st   = A.index ary i
            !st'  = go h k (s+bitsPerSubkey) st
            ary' = update16 ary i $! st'
        in if ptrEq st st'
           then t
           else Full ary'
    go h k _ t@(Collision hy v)
        | h == hy   = let !v' = updateWith# f k v
                      in if A.unsafeSameArray v v'
                         then t
                         else Collision h v'
        | otherwise = t
{-# INLINABLE adjust# #-}

-- | /O(log n)/  The expression (@'update' f k map@) updates the value @x@ at @k@,
-- (if it is in the map). If (f k x) is @'Nothing', the element is deleted.
-- If it is (@'Just' y), the key k is bound to the new value y.
update :: (TestEquality k, IHashable k) => (a i -> Maybe (a i)) -> k i -> IHashMap k a -> IHashMap k a
update f = alter (>>= f)
{-# INLINABLE update #-}


-- | /O(log n)/  The expression (@'alter' f k map@) alters the value @x@ at @k@, or
-- absence thereof. @alter@ can be used to insert, delete, or update a value in a
-- map. In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: (TestEquality k, IHashable k) => (Maybe (v i) -> Maybe (v i)) -> k i -> IHashMap k v -> IHashMap k v
-- TODO(m-renaud): Consider using specialized insert and delete for alter.
alter f k m =
  case f (lookup k m) of
    Nothing -> delete k m
    Just v  -> insert k v m
{-# INLINABLE alter #-}

-- | /O(log n)/  The expression (@'alterF' f k map@) alters the value @x@ at
-- @k@, or absence thereof. @alterF@ can be used to insert, delete, or update
-- a value in a map.
--
-- Note: 'alterF' is a flipped version of the 'at' combinator from
-- <https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-At.html#v:at Control.Lens.At>.
--
-- @since 0.2.9
alterF :: (Functor f, TestEquality k, IHashable k)
       => (Maybe (v i) -> f (Maybe (v i))) -> k i -> IHashMap k v -> f (IHashMap k v)
-- We only calculate the hash once, but unless this is rewritten
-- by rules we may test for key equality multiple times.
-- We force the value of the map for consistency with the rewritten
-- version; otherwise someone could tell the difference using a lazy
-- @f@ and a functor that is similar to Const but not actually Const.
alterF f = \ !k !m ->
  let
    !h = hash k
    mv = lookup' h k m
  in (<$> f mv) $ \fres ->
    case fres of
      Nothing -> delete' h k m
      Just v' -> insert' h k v' m

-- We unconditionally rewrite alterF in RULES, but we expose an
-- unfolding just in case it's used in some way that prevents the
-- rule from firing.
{-# INLINABLE [0] alterF #-}

-- This is just a bottom value. See the comment on the "alterFWeird"
-- rule.
test_bottom :: a
test_bottom = error "Data.IHashMap.alterF internal error: hit test_bottom"

-- We use this as an error result in RULES to ensure we don't get
-- any useless CallStack nonsense.
bogus# :: (# #) -> (# a #)
bogus# _ = error "Data.IHashMap.alterF internal error: hit bogus#"

{-# RULES
-- We probe the behavior of @f@ by applying it to Nothing and to
-- Just test_bottom. Based on the results, and how they relate to
-- each other, we choose the best implementation.

"alterFWeird" forall f. alterF f =
   alterFWeird (f Nothing) (f (Just test_bottom)) f

-- This rule covers situations where alterF is used to simply insert or
-- delete in some functor (most likely via Control.Lens.At). We recognize here
-- (through the repeated @x@ on the LHS) that
--
-- @f Nothing = f (Just bottom)@,
--
-- which guarantees that @f@ doesn't care what its argument is, so
-- we don't have to either.
"alterFconstant" forall (f :: Maybe (a i) -> f (Maybe (a i))) x.
  alterFWeird x x f = \ !k !m ->
    fmap (\case {Nothing -> delete k m; Just a -> insert k a m}) x

-- This rule handles the case where 'alterF' is used to do 'insertWith'-like
-- things. Whenever possible, GHC will get rid of the Maybe nonsense for us.
-- We delay this rule to stage 1 so alterFconstant has a chance to fire.
"alterFinsertWith" [1] forall (f :: Maybe (a i) -> Identity (Maybe (a i))) x y.
  alterFWeird (coerce (Just x)) (coerce (Just y)) f =
    coerce (insertModifying x (\mold -> case runIdentity (f (Just mold)) of
                                            Nothing -> bogus# (# #)
                                            Just new -> (# new #)))

-- Handle the case where someone uses 'alterF' instead of 'adjust'. This
-- rule is kind of picky; it will only work if the function doesn't
-- do anything between case matching on the Maybe and producing a result.
"alterFadjust" forall (f :: Maybe (a i) -> Identity (Maybe (a i))) _y.
  alterFWeird (coerce Nothing) (coerce (Just _y)) f =
    coerce (adjust# (\x -> case runIdentity (f (Just x)) of
                               Just x' -> (# x' #)
                               Nothing -> bogus# (# #)))

-- The simple specialization to Const; in this case we can look up
-- the key without caring what position it's in. This is only a tiny
-- optimization.
"alterFlookup" forall _ign1 _ign2 (f :: Maybe (a i) -> Const r (Maybe (a i))).
  alterFWeird _ign1 _ign2 f = \ !k !m -> Const (getConst (f (lookup k m)))
 #-}

-- This is a very unsafe version of alterF used for RULES. When calling
-- alterFWeird x y f, the following *must* hold:
--
-- x = f Nothing
-- y = f (Just _|_)
--
-- Failure to abide by these laws will make demons come out of your nose.
alterFWeird
       :: (Functor f, TestEquality k, IHashable k)
       => f (Maybe (v i))
       -> f (Maybe (v i))
       -> (Maybe (v i) -> f (Maybe (v i))) -> k i -> IHashMap k v -> f (IHashMap k v)
alterFWeird _ _ f = alterFEager f
{-# INLINE [0] alterFWeird #-}

-- | This is the default version of alterF that we use in most non-trivial
-- cases. It's called "eager" because it looks up the given key in the map
-- eagerly, whether or not the given function requires that information.
alterFEager :: (Functor f, TestEquality k, IHashable k)
       => (Maybe (v i) -> f (Maybe (v i))) -> k i -> IHashMap k v -> f (IHashMap k v)
alterFEager f !k m = (<$> f mv) $ \fres ->
  case fres of

    ------------------------------
    -- Delete the key from the map.
    Nothing -> case lookupRes of

      -- Key did not exist in the map to begin with, no-op
      Absent -> m

      -- Key did exist
      Present _ collPos -> deleteKeyExists collPos h k m

    ------------------------------
    -- Update value
    Just v' -> case lookupRes of

      -- Key did not exist before, insert v' under a new key
      Absent -> insertNewKey h k v' m

      -- Key existed before
      Present v collPos ->
        if v `ptrEq` v'
        -- If the value is identical, no-op
        then m
        -- If the value changed, update the value.
        else insertKeyExists collPos h k v' m

  where !h = hash k
        !lookupRes = lookupRecordCollision h k m
        !mv = case lookupRes of
           Absent -> Nothing
           Present v _ -> Just v
{-# INLINABLE alterFEager #-}


------------------------------------------------------------------------
-- * Combine

-- | /O(n+m)/ The union of two maps. If a key occurs in both maps, the
-- mapping from the first will be the mapping in the result.
union :: (TestEquality k, IHashable k) => IHashMap k v -> IHashMap k v -> IHashMap k v
union = unionWith const
{-# INLINABLE union #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWith :: (TestEquality k, IHashable k) => (forall i. v i -> v i -> v i) -> IHashMap k v -> IHashMap k v
          -> IHashMap k v
unionWith f = unionWithKey (const f)
{-# INLINE unionWith #-}

-- | /O(n+m)/ The union of two maps.  If a key occurs in both maps,
-- the provided function (first argument) will be used to compute the
-- result.
unionWithKey :: (TestEquality k, IHashable k) => (forall i. k i -> v i -> v i -> v i) -> IHashMap k v -> IHashMap k v
          -> IHashMap k v
unionWithKey f = go 0
  where
    -- empty vs. anything
    go !_ t1 Empty = t1
    go _ Empty t2 = t2
    -- leaf vs. leaf
    go s t1@(Leaf h1 l1@(L k1 v1)) t2@(Leaf h2 l2@(L k2 v2))
        | h1 == h2  = case testEquality k1 k2 of
                      Just Refl -> Leaf h1 (L k1 (f k1 v1 v2))
                      Nothing   -> collision h1 l1 l2
        | otherwise = goDifferentHash s h1 h2 t1 t2
    go s t1@(Leaf h1 (L k1 v1)) t2@(Collision h2 ls2)
        | h1 == h2  = Collision h1 (updateOrSnocWithKey f k1 v1 ls2)
        | otherwise = goDifferentHash s h1 h2 t1 t2
    go s t1@(Collision h1 ls1) t2@(Leaf h2 (L k2 v2))
        | h1 == h2  = Collision h1 (updateOrSnocWithKey (flip . f) k2 v2 ls1)
        | otherwise = goDifferentHash s h1 h2 t1 t2
    go s t1@(Collision h1 ls1) t2@(Collision h2 ls2)
        | h1 == h2  = Collision h1 (updateOrConcatWithKey f ls1 ls2)
        | otherwise = goDifferentHash s h1 h2 t1 t2
    -- branch vs. branch
    go s (BitmapIndexed b1 ary1) (BitmapIndexed b2 ary2) =
        let b'   = b1 .|. b2
            ary' = unionArrayBy (go (s+bitsPerSubkey)) b1 b2 ary1 ary2
        in bitmapIndexedOrFull b' ary'
    go s (BitmapIndexed b1 ary1) (Full ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) b1 fullNodeMask ary1 ary2
        in Full ary'
    go s (Full ary1) (BitmapIndexed b2 ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) fullNodeMask b2 ary1 ary2
        in Full ary'
    go s (Full ary1) (Full ary2) =
        let ary' = unionArrayBy (go (s+bitsPerSubkey)) fullNodeMask fullNodeMask
                   ary1 ary2
        in Full ary'
    -- leaf vs. branch
    go s (BitmapIndexed b1 ary1) t2
        | b1 .&. m2 == 0 = let ary' = A.insert ary1 i t2
                               b'   = b1 .|. m2
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateWith' ary1 i $ \st1 ->
                                   go (s+bitsPerSubkey) st1 t2
                           in BitmapIndexed b1 ary'
        where
          h2 = leafHashCode t2
          m2 = mask h2 s
          i = sparseIndex b1 m2
    go s t1 (BitmapIndexed b2 ary2)
        | b2 .&. m1 == 0 = let ary' = A.insert ary2 i $! t1
                               b'   = b2 .|. m1
                           in bitmapIndexedOrFull b' ary'
        | otherwise      = let ary' = A.updateWith' ary2 i $ \st2 ->
                                   go (s+bitsPerSubkey) t1 st2
                           in BitmapIndexed b2 ary'
      where
        h1 = leafHashCode t1
        m1 = mask h1 s
        i = sparseIndex b2 m1
    go s (Full ary1) t2 =
        let h2   = leafHashCode t2
            i    = index h2 s
            ary' = update16With' ary1 i $ \st1 -> go (s+bitsPerSubkey) st1 t2
        in Full ary'
    go s t1 (Full ary2) =
        let h1   = leafHashCode t1
            i    = index h1 s
            ary' = update16With' ary2 i $ \st2 -> go (s+bitsPerSubkey) t1 st2
        in Full ary'

    leafHashCode (Leaf h _) = h
    leafHashCode (Collision h _) = h
    leafHashCode _ = error "leafHashCode"

    goDifferentHash s h1 h2 t1 t2
        | m1 == m2  = BitmapIndexed m1 (A.singleton $! go (s+bitsPerSubkey) t1 t2)
        | m1 <  m2  = BitmapIndexed (m1 .|. m2) (A.pair t1 t2)
        | otherwise = BitmapIndexed (m1 .|. m2) (A.pair t2 t1)
      where
        m1 = mask h1 s
        m2 = mask h2 s
{-# INLINE unionWithKey #-}

-- | Strict in the result of @f@.
unionArrayBy :: (a -> a -> a) -> Bitmap -> Bitmap -> A.Array a -> A.Array a
             -> A.Array a
unionArrayBy f b1 b2 ary1 ary2 = A.run $ do
    let b' = b1 .|. b2
    mary <- A.new_ (popCount b')
    -- iterate over nonzero bits of b1 .|. b2
    -- it would be nice if we could shift m by more than 1 each time
    let ba = b1 .&. b2
        go !i !i1 !i2 !m
            | m > b'        = return ()
            | b' .&. m == 0 = go i i1 i2 (m `unsafeShiftL` 1)
            | ba .&. m /= 0 = do
                A.write mary i $! f (A.index ary1 i1) (A.index ary2 i2)
                go (i+1) (i1+1) (i2+1) (m `unsafeShiftL` 1)
            | b1 .&. m /= 0 = do
                A.write mary i =<< A.indexM ary1 i1
                go (i+1) (i1+1) (i2  ) (m `unsafeShiftL` 1)
            | otherwise     = do
                A.write mary i =<< A.indexM ary2 i2
                go (i+1) (i1  ) (i2+1) (m `unsafeShiftL` 1)
    go 0 0 0 (b' .&. negate b') -- XXX: b' must be non-zero
    return mary
    -- TODO: For the case where b1 .&. b2 == b1, i.e. when one is a
    -- subset of the other, we could use a slightly simpler algorithm,
    -- where we copy one array, and then update.
{-# INLINE unionArrayBy #-}

-- TODO: Figure out the time complexity of 'unions'.

-- | Construct a set containing all elements from a list of sets.
unions :: (TestEquality k, IHashable k) => [IHashMap k v] -> IHashMap k v
unions = L.foldl' union empty
{-# INLINE unions #-}

------------------------------------------------------------------------
-- * Transformations

-- | /O(n)/ Transform this map by applying a function to every value.
mapWithKey :: (forall i. k i -> v1 i -> v2 i) -> IHashMap k v1 -> IHashMap k v2
mapWithKey f = go
  where
    go Empty = Empty
    go (Leaf h (L k v)) = Leaf h $ L k (f k v)
    go (BitmapIndexed b ary) = BitmapIndexed b $ A.map' go ary
    go (Full ary) = Full $ A.map' go ary
    go (Collision h ary) = Collision h $
                           A.map' (\ (L k v) -> L k (f k v)) ary
{-# INLINE mapWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value.
map :: (forall i. v1 i -> v2 i) -> IHashMap k v1 -> IHashMap k v2
map f = mapWithKey (const f)
{-# INLINE map #-}

-- TODO: We should be able to use mutation to create the new
-- 'IHashMap'.

-- | /O(n)/ Transform this map by accumulating an Applicative result
-- from every value.
traverseWithKey :: Applicative f => (forall i. k i -> v1 i -> f (v2 i)) -> IHashMap k v1
                -> f (IHashMap k v2)
traverseWithKey f = go
  where
    go Empty                 = pure Empty
    go (Leaf h (L k v))      = Leaf h . L k <$> f k v
    go (BitmapIndexed b ary) = BitmapIndexed b <$> A.traverse go ary
    go (Full ary)            = Full <$> A.traverse go ary
    go (Collision h ary)     =
        Collision h <$> A.traverse (\ (L k v) -> L k <$> f k v) ary
{-# INLINE traverseWithKey #-}

------------------------------------------------------------------------
-- * Difference and intersection

-- | /O(n*log m)/ Difference of two maps. Return elements of the first map
-- not existing in the second.
difference :: forall k v w.
              (TestEquality k, IHashable k) => IHashMap k v -> IHashMap k w -> IHashMap k v
difference a b = foldlWithKey' go empty a
  where
    go :: IHashMap k v -> k i -> v i -> IHashMap k v
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 _       -> m
{-# INLINABLE difference #-}

-- | /O(n*log m)/ Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the values of these keys.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
differenceWith :: forall k v w. (TestEquality k, IHashable k) => (forall i. v i -> w i -> Maybe (v i)) -> IHashMap k v -> IHashMap k w -> IHashMap k v
differenceWith f a b = foldlWithKey' go empty a
  where
    go :: IHashMap k v -> k i -> v i -> IHashMap k v
    go m k v = case lookup k b of
                 Nothing -> insert k v m
                 Just w  -> maybe m (\y -> insert k y m) (f v w)
{-# INLINABLE differenceWith #-}

-- | /O(n*log m)/ Intersection of two maps. Return elements of the first
-- map for keys existing in the second.
intersection :: forall k v w. (TestEquality k, IHashable k) => IHashMap k v -> IHashMap k w -> IHashMap k v
intersection a b = foldlWithKey' go empty a
  where
    go :: IHashMap k v -> k i -> v i -> IHashMap k v
    go m k v = case lookup k b of
                 Just _ -> insert k v m
                 _      -> m
{-# INLINABLE intersection #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWith :: forall k v1 v2 v3. (TestEquality k, IHashable k) => (forall i. v1 i -> v2 i -> v3 i) -> IHashMap k v1
                 -> IHashMap k v2 -> IHashMap k v3
intersectionWith f a b = foldlWithKey' go empty a
  where
    go :: IHashMap k v3 -> k i -> v1 i -> IHashMap k v3
    go m k v = case lookup k b of
                 Just w -> insert k (f v w) m
                 _      -> m
{-# INLINABLE intersectionWith #-}

-- | /O(n+m)/ Intersection of two maps. If a key occurs in both maps
-- the provided function is used to combine the values from the two
-- maps.
intersectionWithKey :: forall k v1 v2 v3. (TestEquality k, IHashable k) => (forall i. k i -> v1 i -> v2 i -> v3 i)
                    -> IHashMap k v1 -> IHashMap k v2 -> IHashMap k v3
intersectionWithKey f a b = foldlWithKey' go empty a
  where
    go :: IHashMap k v3 -> k i -> v1 i -> IHashMap k v3
    go m k v = case lookup k b of
                 Just w -> insert k (f k v w) m
                 _      -> m
{-# INLINABLE intersectionWithKey #-}

------------------------------------------------------------------------
-- * Folds

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before using the result in the next application.
-- This function is strict in the starting value.
foldl' :: (forall i. a -> v i -> a) -> a -> IHashMap k v -> a
foldl' f = foldlWithKey' (\ z _ v -> f z v)
{-# INLINE foldl' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- left-identity of the operator).  Each application of the operator
-- is evaluated before using the result in the next application.
-- This function is strict in the starting value.
foldlWithKey' :: (forall i. a -> k i -> v i -> a) -> a -> IHashMap k v -> a
foldlWithKey' f = go
  where
    go !z Empty                = z
    go z (Leaf _ (L k v))      = f z k v
    go z (BitmapIndexed _ ary) = A.foldl' go z ary
    go z (Full ary)            = A.foldl' go z ary
    go z (Collision _ ary)     = A.foldl' (\ z' (L k v) -> f z' k v) z ary
{-# INLINE foldlWithKey' #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldr :: (forall i. v i -> a -> a) -> a -> IHashMap k v -> a
foldr f = foldrWithKey (const f)
{-# INLINE foldr #-}

-- | /O(n)/ Reduce this map by applying a binary operator to all
-- elements, using the given starting value (typically the
-- right-identity of the operator).
foldrWithKey :: (forall i. k i -> v i -> a -> a) -> a -> IHashMap k v -> a
foldrWithKey f = go
  where
    go z Empty                 = z
    go z (Leaf _ (L k v))      = f k v z
    go z (BitmapIndexed _ ary) = A.foldr (flip go) z ary
    go z (Full ary)            = A.foldr (flip go) z ary
    go z (Collision _ ary)     = A.foldr (\ (L k v) z' -> f k v z') z ary
{-# INLINE foldrWithKey #-}

------------------------------------------------------------------------
-- * Filter

-- | Create a new array of the @n@ first elements of @mary@.
trim :: A.MArray s a -> Int -> ST s (A.Array a)
trim mary n = do
    mary2 <- A.new_ n
    A.copyM mary 0 mary2 0 n
    A.unsafeFreeze mary2
{-# INLINE trim #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybeWithKey :: (forall i. k i -> v1 i -> Maybe (v2 i)) -> IHashMap k v1 -> IHashMap k v2
mapMaybeWithKey f = filterMapAux onLeaf onColl
  where onLeaf (Leaf h (L k v)) | Just v' <- f k v = Just (Leaf h (L k v'))
        onLeaf _ = Nothing

        onColl (L k v) | Just v' <- f k v = Just (L k v')
                       | otherwise = Nothing
{-# INLINE mapMaybeWithKey #-}

-- | /O(n)/ Transform this map by applying a function to every value
--   and retaining only some of them.
mapMaybe :: (forall i. v1 i -> Maybe (v2 i)) -> IHashMap k v1 -> IHashMap k v2
mapMaybe f = mapMaybeWithKey (const f)
{-# INLINE mapMaybe #-}

-- | /O(n)/ Filter this map by retaining only elements satisfying a
-- predicate.
filterWithKey :: forall k v. (forall i. k i -> v i -> Bool) -> IHashMap k v -> IHashMap k v
filterWithKey pred = filterMapAux onLeaf onColl
  where onLeaf t@(Leaf _ (L k v)) | pred k v = Just t
        onLeaf _ = Nothing

        onColl el@(L k v) | pred k v = Just el
        onColl _ = Nothing
{-# INLINE filterWithKey #-}


-- | Common implementation for 'filterWithKey' and 'mapMaybeWithKey',
--   allowing the former to former to reuse terms.
filterMapAux :: forall k v1 v2
              . (IHashMap k v1 -> Maybe (IHashMap k v2))
             -> (Leaf k v1 -> Maybe (Leaf k v2))
             -> IHashMap k v1
             -> IHashMap k v2
filterMapAux onLeaf onColl = go
  where
    go Empty = Empty
    go t@Leaf{}
        | Just t' <- onLeaf t = t'
        | otherwise = Empty
    go (BitmapIndexed b ary) = filterA ary b
    go (Full ary) = filterA ary fullNodeMask
    go (Collision h ary) = filterC ary h

    filterA ary0 b0 =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary b0 0 0 1 n
      where
        step :: A.Array (IHashMap k v1) -> A.MArray s (IHashMap k v2)
             -> Bitmap -> Int -> Int -> Bitmap -> Int
             -> ST s (IHashMap k v2)
        step !ary !mary !b i !j !bi n
            | i >= n = case j of
                0 -> return Empty
                1 -> do
                    ch <- A.read mary 0
                    case ch of
                      t | isLeafOrCollision t -> return t
                      _                       -> BitmapIndexed b <$> trim mary 1
                _ -> do
                    ary2 <- trim mary j
                    return $! if j == maxChildren
                              then Full ary2
                              else BitmapIndexed b ary2
            | bi .&. b == 0 = step ary mary b i j (bi `unsafeShiftL` 1) n
            | otherwise = case go (A.index ary i) of
                Empty -> step ary mary (b .&. complement bi) (i+1) j
                         (bi `unsafeShiftL` 1) n
                t     -> do A.write mary j t
                            step ary mary b (i+1) (j+1) (bi `unsafeShiftL` 1) n

    filterC ary0 h =
        let !n = A.length ary0
        in runST $ do
            mary <- A.new_ n
            step ary0 mary 0 0 n
      where
        step :: A.Array (Leaf k v1) -> A.MArray s (Leaf k v2)
             -> Int -> Int -> Int
             -> ST s (IHashMap k v2)
        step !ary !mary i !j n
            | i >= n    = case j of
                0 -> return Empty
                1 -> do l <- A.read mary 0
                        return $! Leaf h l
                _ | i == j -> do ary2 <- A.unsafeFreeze mary
                                 return $! Collision h ary2
                  | otherwise -> do ary2 <- trim mary j
                                    return $! Collision h ary2
            | Just el <- onColl (A.index ary i)
                = A.write mary j el >> step ary mary (i+1) (j+1) n
            | otherwise = step ary mary (i+1) j n
{-# INLINE filterMapAux #-}

-- | /O(n)/ Filter this map by retaining only elements which values
-- satisfy a predicate.
filter :: (forall i. v i -> Bool) -> IHashMap k v -> IHashMap k v
filter p = filterWithKey (\_ v -> p v)
{-# INLINE filter #-}

------------------------------------------------------------------------
-- * Conversions

-- TODO: Improve fusion rules by modelled them after the Prelude ones
-- on lists.

-- | /O(n)/ Return a list of this map's keys.  The list is produced
-- lazily.
keys :: IHashMap k v -> [Ex k]
keys = L.map (\(L k _) -> packEx k) . toList
{-# INLINE keys #-}

-- | /O(n)/ Return a list of this map's values.  The list is produced
-- lazily.
elems :: IHashMap k v -> [Ex v]
elems = L.map (\(L _ v) -> packEx v) . toList
{-# INLINE elems #-}

------------------------------------------------------------------------
-- ** Lists

-- | /O(n)/ Return a list of this map's elements.  The list is
-- produced lazily. The order of its elements is unspecified.
toList :: IHashMap k v -> [Leaf k v]
toList t = build (\ c z -> foldrWithKey (\k v -> c (L k v)) z t)
{-# INLINE toList #-}

-- | /O(n)/ Construct a map with the supplied mappings.  If the list
-- contains duplicate mappings, the later mappings take precedence.
fromList :: (TestEquality k, IHashable k) => [Leaf k v] -> IHashMap k v
fromList = L.foldl' (\ m (L k v) -> unsafeInsert k v m) empty
{-# INLINABLE fromList #-}

-- | /O(n*log n)/ Construct a map from a list of elements.  Uses
-- the provided function to merge duplicate entries.
fromListWith :: (TestEquality k, IHashable k) => (forall i. v i -> v i -> v i) -> [Leaf k v] -> IHashMap k v
fromListWith f = L.foldl' (\ m (L k v) -> unsafeInsertWith f k v m) empty
{-# INLINE fromListWith #-}

------------------------------------------------------------------------
-- Array operations

-- | /O(n)/ Look up the value associated with the given key in an
-- array.
lookupInArrayCont ::
  forall rep (r :: TYPE rep) k v i.
  TestEquality k => ((# #) -> r) -> (v i -> Int -> r) -> k i -> A.Array (Leaf k v) -> r
lookupInArrayCont absent present k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go :: TestEquality k => k i -> A.Array (Leaf k v) -> Int -> Int -> r
    go !k !ary !i !n
        | i >= n    = absent (# #)
        | otherwise = case A.index ary i of
            (L kx v)
                | Just Refl <- testEquality k kx -> present v i
                | otherwise                      -> go k ary (i+1) n
{-# INLINE lookupInArrayCont #-}

-- | /O(n)/ Lookup the value associated with the given key in this
-- array.  Returns 'Nothing' if the key wasn't found.
indexOf :: TestEquality k => k i -> A.Array (Leaf k v) -> Maybe Int
indexOf k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = Nothing
        | otherwise = case A.index ary i of
            (L kx _)
                | k `eq` kx -> Just i
                | otherwise -> go k ary (i+1) n
{-# INLINABLE indexOf #-}

updateWith# :: TestEquality k => (v i -> (# v i #)) -> k i -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateWith# f k0 ary0 = go k0 ary0 0 (A.length ary0)
  where
    go !k !ary !i !n
        | i >= n    = ary
        | otherwise = case A.index ary i of
            (L kx y) | Just Refl <- testEquality k kx -> case f y of
                          (# y' #)
                             | ptrEq y y' -> ary
                             | otherwise -> A.update ary i (L k y')
                     | otherwise -> go k ary (i+1) n
{-# INLINABLE updateWith# #-}

updateOrSnocWith :: TestEquality k => (v i -> v i -> v i) -> k i -> v i -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWith f = updateOrSnocWithKey (const f)
{-# INLINABLE updateOrSnocWith #-}

updateOrSnocWithKey :: TestEquality k => (k i -> v i -> v i -> v i) -> k i -> v i -> A.Array (Leaf k v)
                 -> A.Array (Leaf k v)
updateOrSnocWithKey f k0 v0 ary0 = go k0 v0 ary0 0 (A.length ary0)
  where
    go !k v !ary !i !n
        | i >= n = A.run $ do
            -- Not found, append to the end.
            mary <- A.new_ (n + 1)
            A.copy ary 0 mary 0 n
            A.write mary n (L k v)
            return mary
        | otherwise = case A.index ary i of
            (L kx y) | Just Refl <- testEquality k kx -> A.update ary i (L k (f k v y))
                     | otherwise                      -> go k v ary (i+1) n
{-# INLINABLE updateOrSnocWithKey #-}

updateOrConcatWith :: TestEquality k => (forall i. v i -> v i -> v i) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWith f = updateOrConcatWithKey (const f)
{-# INLINABLE updateOrConcatWith #-}

updateOrConcatWithKey :: TestEquality k => (forall i. k i -> v i -> v i -> v i) -> A.Array (Leaf k v) -> A.Array (Leaf k v) -> A.Array (Leaf k v)
updateOrConcatWithKey f ary1 ary2 = A.run $ do
    -- first: look up the position of each element of ary2 in ary1
    let indices = A.map (\(L k _) -> indexOf k ary1) ary2
    -- that tells us how large the overlap is:
    -- count number of Nothing constructors
    let nOnly2 = A.foldl' (\n -> maybe (n+1) (const n)) 0 indices
    let n1 = A.length ary1
    let n2 = A.length ary2
    -- copy over all elements from ary1
    mary <- A.new_ (n1 + nOnly2)
    A.copy ary1 0 mary 0 n1
    -- append or update all elements from ary2
    let go !iEnd !i2
          | i2 >= n2 = return ()
          | otherwise = case A.index indices i2 of
               Just i1 -> do -- key occurs in both arrays, store combination in position i1
                             L k1 v1 <- A.indexM ary1 i1
                             L k2 v2 <- A.indexM ary2 i2
                              -- RAE: This next line is a waste of time.
                              -- But we need it to prove to GHC that the indices
                              -- line up. It can be avoided only by lots of
                              -- pyrotechnics, including an index array type
                             Just Refl <- return (testEquality k1 k2)
                             A.write mary i1 (L k1 (f k1 v1 v2))
                             go iEnd (i2+1)
               Nothing -> do -- key is only in ary2, append to end
                             A.write mary iEnd =<< A.indexM ary2 i2
                             go (iEnd+1) (i2+1)
    go n1 0
    return mary
{-# INLINABLE updateOrConcatWithKey #-}

------------------------------------------------------------------------
-- Manually unrolled loops

-- | /O(n)/ Update the element at the given position in this array.
update16 :: A.Array e -> Int -> e -> A.Array e
update16 ary idx b = runST (update16M ary idx b)
{-# INLINE update16 #-}

-- | /O(n)/ Update the element at the given position in this array.
update16M :: A.Array e -> Int -> e -> ST s (A.Array e)
update16M ary idx b = do
    mary <- clone16 ary
    A.write mary idx b
    A.unsafeFreeze mary
{-# INLINE update16M #-}

-- | /O(n)/ Update the element at the given position in this array, by applying a function to it.
update16With' :: A.Array e -> Int -> (e -> e) -> A.Array e
update16With' ary idx f = update16 ary idx $! f (A.index ary idx)
{-# INLINE update16With' #-}

-- | Unsafely clone an array of 16 elements.  The length of the input
-- array is not checked.
clone16 :: A.Array e -> ST s (A.MArray s e)
clone16 ary =
    A.thaw ary 0 16

------------------------------------------------------------------------
-- Bit twiddling

bitsPerSubkey :: Int
bitsPerSubkey = 4

maxChildren :: Int
maxChildren = fromIntegral $ 1 `unsafeShiftL` bitsPerSubkey

subkeyMask :: Bitmap
subkeyMask = 1 `unsafeShiftL` bitsPerSubkey - 1

sparseIndex :: Bitmap -> Bitmap -> Int
sparseIndex b m = popCount (b .&. (m - 1))

mask :: Word -> Shift -> Bitmap
mask w s = 1 `unsafeShiftL` index w s
{-# INLINE mask #-}

-- | Mask out the 'bitsPerSubkey' bits used for indexing at this level
-- of the tree.
index :: Hash -> Shift -> Int
index w s = fromIntegral $ (unsafeShiftR w s) .&. subkeyMask
{-# INLINE index #-}

-- | A bitmask with the 'bitsPerSubkey' least significant bits set.
fullNodeMask :: Bitmap
fullNodeMask = complement (complement 0 `unsafeShiftL` maxChildren)
{-# INLINE fullNodeMask #-}

-- | Check if two the two arguments are the same value.  N.B. This
-- function might give false negatives (due to GC moving objects.)
ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y ==# 1#)
{-# INLINE ptrEq #-}

------------------------------------------------------------------------
-- IsList instance
instance (TestEquality k, IHashable k) => Exts.IsList (IHashMap k v) where
    type Item (IHashMap k v) = Leaf k v
    fromList = fromList
    toList   = toList
