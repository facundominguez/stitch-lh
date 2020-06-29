{-# LANGUAGE TypeInType, GADTs, StandaloneDeriving, TypeOperators,
             TypeFamilies, UndecidableInstances #-}

module Language.Stitch.Data.Fin where

import Language.Stitch.Data.Nat
import Data.Kind

data Fin :: Nat -> Type where
  FZ :: Fin (Succ n)
  FS :: Fin n -> Fin (Succ n)

deriving instance Show (Fin n)

finToInt :: Fin n -> Int
finToInt FZ = 0
finToInt (FS n) = 1 + finToInt n
