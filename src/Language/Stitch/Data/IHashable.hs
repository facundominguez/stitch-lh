-- A polykinded IHashable class
-- Based on the hashable package, by Johan Tibell

{-# LANGUAGE PolyKinds #-}

module Language.Stitch.Data.IHashable where

import Data.Hashable
import Data.Proxy
import Data.Functor.Const

class IHashable t where
    -- | Lift a hashing function through the type constructor.
    ihashWithSalt :: Int -> t a -> Int

    ihash :: t a -> Int
    ihash = ihashWithSalt defaultSalt
      where
        -- from hashable package
        defaultSalt = -2578643520546668380  -- 0xdc36d1615b7400a4

instance IHashable Proxy where
  ihashWithSalt = hashWithSalt
  ihash = hash

instance Hashable a => IHashable (Const a) where
  ihashWithSalt s (Const x) = hashWithSalt s x
  ihash (Const x) = hash x
