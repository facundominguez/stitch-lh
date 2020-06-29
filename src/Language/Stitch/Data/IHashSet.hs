{-# LANGUAGE Safe #-}

-- Adapted by Richard Eisenberg

------------------------------------------------------------------------
-- |
-- Module      :  Data.HashSet
-- Copyright   :  2011 Bryan O'Sullivan
-- License     :  BSD-style
-- Maintainer  :  johan.tibell@gmail.com
-- Stability   :  provisional
-- Portability :  portable
--
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

module Language.Stitch.Data.IHashSet
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
    ) where

import Language.Stitch.Data.IHashSet.Base
import Prelude ()
