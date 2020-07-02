{-# LANGUAGE GADTs, RankNTypes, PolyKinds, TypeOperators, TypeApplications,
             TypeFamilies #-}

module Language.Stitch.Scratch where

import Language.Stitch.Data.Vec
import Data.Kind
import Language.Stitch.Data.Nat

import Language.Stitch.Type
import Language.Stitch.Exp

data FSnocVec :: forall a m. (forall n. Vec a (Succ n) -> Type) -> Vec a m -> Type where
  FNil :: forall (b :: forall n. Vec a (Succ n) -> Type). FSnocVec b VNil
  (:<:) :: forall (b :: forall n. Vec a (Succ n) -> Type) x xs. FSnocVec b xs -> b (x :> xs) -> FSnocVec b (x :> xs)
infixl 5 :<:

-- (Exp [] ty1, Exp [ty1] ty2, Exp [ty2:ty1] ty3, Exp [ty3:ty2:ty1] ty4, ..., Exp tys{n-1} tyn)

type family VTail (v :: Vec a (Succ n)) :: Vec a n where
  VTail (_ :> xs) = xs

type family VHead (v :: Vec a (Succ n)) :: a where
  VHead (x :> _) = x

newtype Exp' (tys :: Ctx (Succ n)) = Exp' (Exp (VTail tys) (VHead tys))

example :: FSnocVec Exp' ((Int -> Int) :> Bool :> Int :> VNil)
example = FNil :<: Exp' (IntE 5) :<: Exp' (BoolE False) :<: Exp' (Lam (typeRep @Int) (Var (ES (ES EZ))))

data Lets :: forall n. Ctx n -> Type where
  LNil :: Lets VNil
  (:<<:) :: Lets ctx -> Exp ctx ty -> Lets (ty :> ctx)
infixl 5 :<<:

ex2 :: Lets ((Int -> Int) :> Bool :> Int :> VNil)
ex2 = LNil :<<: IntE 5 :<<: BoolE False :<<: Lam (typeRep @Int) (Var (ES (ES EZ)))
