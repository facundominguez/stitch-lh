{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Language.Stitch.Data.Nat where

{-@ type Nat = { v : Int | v >= 0 } @-}
type Nat = Int
