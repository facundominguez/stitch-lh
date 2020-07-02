{-# LANGUAGE PolyKinds, DataKinds, GADTs, TypeOperators, TypeFamilies,
             StandaloneDeriving, ExplicitForAll #-}

module Language.Stitch.Data.Vec where

import Language.Stitch.Data.Nat
import Data.Kind
import Language.Stitch.Data.Fin

import Data.Type.Equality

data Vec :: Type -> Nat -> Type where
  VNil :: Vec a Zero
  (:>) :: a -> Vec a n -> Vec a (Succ n)
infixr 5 :>

deriving instance Show a => Show (Vec a n)

(!!!) :: Vec a n -> Fin n -> a
-- RAE: Oy. Need to reverse order b/c of laziness
vec !!! fin = case (fin, vec) of
  (FZ,   x :> _)  -> x
  (FS n, _ :> xs) -> xs !!! n

type family (v :: Vec a n) !!! (fin :: Fin n) :: a where
  (x :> _) !!!  FZ       = x
  (_ :> xs) !!! (FS fin) = xs !!! fin

elemIndex :: Eq a => a -> Vec a n -> Maybe (Fin n)
elemIndex _ VNil = Nothing
elemIndex x (y :> ys)
  | x == y    = Just FZ
  | otherwise = FS <$> elemIndex x ys

type family (v1 :: Vec a n) +++ (v2 :: Vec a m) :: Vec a (n + m) where
  (_ :: Vec a Zero) +++ v2 = v2
  (x :> xs)         +++ v2 = x :> (xs +++ v2)
infixr 5 +++

--------------------------------------------------------

-- | @Length xs@ is a runtime witness for how long a vector @xs@ is.
-- @LZ :: Length xs@ says that @xs@ is empty.
-- @LS len :: Length xs@ tells you that @xs@ has one more element
-- than @len@ says.
-- A term of type @Length xs@ also serves as a proxy for @xs@.
data Length :: forall a n. Vec a n -> Type where
  LZ :: Length VNil
  LS :: Length xs -> Length (x :> xs)

deriving instance Show (Length xs)

--------------------------------------------------------

-- | @Elem xs x@ is evidence that @x@ is in the vector @xs@.
-- @EZ :: Elem xs x@ is evidence that @x@ is the first element of @xs@.
-- @ES ev :: Elem xs x@ is evidence that @x@ is one position later in
-- @xs@ than is indicated in @ev@
data Elem :: forall a n. Vec a n -> a -> Type where
  EZ :: Elem (x :> xs) x
  ES :: Elem xs x -> Elem (y :> xs) x

deriving instance Show (Elem xs x)

-- | Informative equality on Elems
eqElem :: Elem xs x1 -> Elem xs x2 -> Maybe (x1 :~: x2)
eqElem EZ EZ           = Just Refl
eqElem (ES e1) (ES e2) = eqElem e1 e2
eqElem _       _       = Nothing

instance TestEquality (Elem xs) where
  testEquality = eqElem

-- | Convert an 'Elem' to a proper de Bruijn index
elemToInt :: Elem ctx ty -> Int
elemToInt EZ     = 0
elemToInt (ES e) = 1 + elemToInt e

-- | Convert an 'Elem' to a 'Fin'
elemToFin :: Elem (ctx :: Vec a n) x -> Fin n
elemToFin EZ     = FZ
elemToFin (ES e) = FS (elemToFin e)

-- | Weaken an 'Elem' to work against a larger vector.
weakenElem :: Length prefix -> Elem xs x -> Elem (prefix +++ xs) x
weakenElem LZ       e = e
weakenElem (LS len) e = ES (weakenElem len e)

-- | Strengthen an 'Elem' to work with a suffix of a vector. Fails when
-- the element in question ('x') occurs in the 'prefix'.
strengthenElem :: Length prefix -> Elem (prefix +++ xs) x -> Maybe (Elem xs x)
strengthenElem LZ       e      = Just e
strengthenElem (LS _)   EZ     = Nothing
strengthenElem (LS len) (ES e) = strengthenElem len e
