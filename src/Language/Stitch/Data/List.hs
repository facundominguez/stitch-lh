{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Data.List
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- An interface of lists that can be used in reflected definitions
-- with LH
--
----------------------------------------------------------------------------

module Language.Stitch.Data.List where

import Language.Stitch.Data.Nat
import Prelude hiding (length)


-- XXX: Using a custom List instead of [a] avoids LH error: unknown function/constant smt_set_sng
data List a = Cons a (List a) | Nil

{-@
inline empty
empty :: { xs : List a | length xs = 0 }
@-}
empty :: List a
empty = Nil

{-@
inline cons
cons :: a -> xs : List a -> { ys : List a | length ys = 1 + length xs }
@-}
cons :: a -> List a -> List a
cons a b = Cons a b

{-@
reflect elemAt
elemAt :: n : Nat -> { xs : List a | length xs > n } -> a
@-}
elemAt :: Nat -> List a -> a
elemAt 0 (Cons x _) = x
elemAt i (Cons _ xs) = elemAt (i-1) xs

{-@
reflect deleteAt
deleteAt
  :: n : Nat
  -> { xs : List a | length xs > n }
  -> { ys : List a | length xs = length ys + 1}
@-}
deleteAt :: Nat -> List a -> List a
deleteAt 0 (Cons _ xs) = xs
deleteAt i (Cons x xs) = Cons x (deleteAt (i-1) xs)

{-@
measure length
length :: xs : List a -> Nat
@-}
length :: List a -> Nat
length Nil = 0
length (Cons _ xs) = 1 + length xs
