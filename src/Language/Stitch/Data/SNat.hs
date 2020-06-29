{-# LANGUAGE GADTs #-}

module Language.Stitch.Data.SNat where

import Language.Stitch.Data.Fin
import Language.Stitch.Data.Singletons
import Language.Stitch.Data.Nat

minus :: Sing n -> Fin n -> Nat
minus (SSucc n) (FS v) = n `minus` v
minus n         FZ     = fromSing n
