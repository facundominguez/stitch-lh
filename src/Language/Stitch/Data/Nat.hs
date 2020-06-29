{-# LANGUAGE TypeInType, TypeOperators, TypeFamilies, MultiParamTypeClasses,
             FlexibleInstances, UndecidableInstances #-}

module Language.Stitch.Data.Nat where

data Nat = Zero | Succ Nat
  deriving Show

type family n + m where
  Zero   + m = m
  Succ n + m = Succ (n + m)
