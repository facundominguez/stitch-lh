{-# LANGUAGE GADTs, TypeOperators, TypeFamilies, PolyKinds,
             ScopedTypeVariables, UndecidableInstances, UndecidableSuperClasses,
             FlexibleInstances, StandaloneDeriving, PatternSynonyms,
             ViewPatterns, TypeApplications, TypeFamilyDependencies,
             ConstraintKinds, DataKinds #-}
{-# OPTIONS_GHC -Wno-orphans #-}  -- {I,}Hashable instance for Elem

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Exp
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@richarde.dev)
-- Stability   :  experimental
--
-- The Exp GADT. Stitch expressions encoded in an 'Exp' value are
-- *always* well-typed.
--
----------------------------------------------------------------------------

module Language.Stitch.Exp (
  Ctx, KnownLength,
  Exp(..),
  eqExp, eqExpB, exprType
  ) where

import Language.Stitch.Type
import Language.Stitch.Pretty
import Language.Stitch.Op
import Language.Stitch.Util

import Language.Stitch.Data.Vec
import Language.Stitch.Data.Singletons

import Data.Type.Equality
import Language.Stitch.Data.IHashable
import Data.Hashable
import Data.Kind

import Text.PrettyPrint.ANSI.Leijen

-- | A context is just a vector of types
type Ctx n = Vec Ty n

-- | Convenient constraint synonym
type KnownLength (ctx :: Ctx n) = SingI n

-- | @Exp ctx ty@ is a well-typed expression of type @ty@ in context
-- @ctx@. Note that a context is a list of types, where a type's index
-- in the list indicates the de Bruijn index of the associated term-level
-- variable.
data Exp :: forall n. Ctx n -> Ty -> Type where
  Var   :: Elem ctx ty -> Exp ctx ty
  Lam   :: STy arg -> Exp (arg :> ctx) res -> Exp ctx (arg :-> res)
  App   :: Exp ctx (arg :-> res) -> Exp ctx arg -> Exp ctx res
  Let   :: Exp ctx rhs_ty -> Exp (rhs_ty :> ctx) body_ty -> Exp ctx body_ty
  Arith :: Exp ctx TInt -> ArithOp ty -> Exp ctx TInt -> Exp ctx ty
  Cond  :: Exp ctx TBool -> Exp ctx ty -> Exp ctx ty -> Exp ctx ty
  Fix   :: Exp ctx (ty :-> ty) -> Exp ctx ty
  IntE  :: Int -> Exp ctx TInt
  BoolE :: Bool -> Exp ctx TBool

deriving instance Show (Exp ctx ty)

----------------------------------------------------
-- | Informative equality on expressions
eqExp :: Exp ctx ty1 -> Exp ctx ty2 -> Maybe (ty1 :~: ty2)
eqExp = go
  where
    go :: Exp ctx ty1 -> Exp ctx ty2 -> Maybe (ty1 :~: ty2)
    go (Var v1) (Var v2) = eqElem v1 v2
    go (Lam t1 b1) (Lam t2 b2) = do Refl <- testEquality t1 t2
                                    Refl <- go b1 b2
                                    return Refl
    go (App f1 a1) (App f2 a2) = do Refl <- go f1 f2
                                    Refl <- go a1 a2
                                    return Refl
    go (Let e1 b1) (Let e2 b2) = do Refl <- go e1 e2
                                    Refl <- go b1 b2
                                    return Refl
    go (Arith l1 op1 r1) (Arith l2 op2 r2) = do Refl <- go l1 l2
                                                Refl <- eqArithOp op1 op2
                                                Refl <- go r1 r2
                                                return Refl
    go (Cond c1 t1 f1) (Cond c2 t2 f2) = do Refl <- go c1 c2
                                            Refl <- go t1 t2
                                            Refl <- go f1 f2
                                            return Refl
    go (Fix b1) (Fix b2) = do Refl <- go b1 b2
                              return Refl
    go (IntE i1) (IntE i2) | i1 == i2  = Just Refl
                           | otherwise = Nothing
    go (BoolE b1) (BoolE b2) | b1 == b2  = Just Refl
                             | otherwise = Nothing

    go _ _ = Nothing

instance TestEquality (Exp ctx) where
  testEquality = eqExp

instance KnownLength ctx => Hashable (Exp ctx ty) where
  hashWithSalt s = go
    where
      go (Var e)          = hashDeBruijn s e sing
      go (Lam ty body)    = s `hashWithSalt` ty
                              `hashWithSalt` body
      go (App e1 e2)      = s `hashWithSalt` e1
                              `hashWithSalt` e2
      go (Let e1 e2)      = s `hashWithSalt` e1
                              `hashWithSalt` e2
      go (Arith e1 op e2) = s `hashWithSalt` e1
                              `hashWithSalt` op
                              `hashWithSalt` e2
      go (Cond c t f)     = s `hashWithSalt` c
                              `hashWithSalt` t
                              `hashWithSalt` f
      go (Fix body)       = s `hashWithSalt` body
      go (IntE n)         = s `hashWithSalt` n
      go (BoolE b)        = s `hashWithSalt` b

instance KnownLength ctx => IHashable (Exp ctx) where
  ihashWithSalt = hashWithSalt
  ihash = hash

instance KnownLength ctx => Hashable (Elem ctx ty) where
  hashWithSalt s v = hashDeBruijn s v sing

instance KnownLength ctx => IHashable (Elem ctx) where
  ihashWithSalt = hashWithSalt
  ihash = hash

-- | The identity of a de Bruijn index comes from the difference between the size
-- of the context and the value of the index. We use this when hashing so that,
-- say, (#2 #3) is recognized as the same expression as the body of λ.(#3 #4).
hashDeBruijn :: forall n (x :: Ty) (xs :: Ctx n). Int -> Elem xs x -> SNat n -> Int
hashDeBruijn salt EZ     size_ctx         = hashWithSalt salt (snatToInt size_ctx)
hashDeBruijn salt (ES e) (SSucc size_ctx) = hashDeBruijn salt e size_ctx

-- | Equality on expressions, needed for testing.
eqExpB :: Exp ctx ty1 -> Exp ctx ty2 -> Bool
-- Cannot be defined in terms of eqExp because the contexts might be different
eqExpB (Var e1)        (Var e2)        = elemToInt e1 == elemToInt e2
eqExpB (Lam ty1 body1) (Lam ty2 body2) | Just Refl <- ty1 `testEquality` ty2
                                       = body1 `eqExpB` body2
                                       | otherwise
                                       = False
eqExpB (App e1a e1b)   (App e2a e2b)   = e1a `eqExpB` e2a && e1b `eqExpB` e2b
eqExpB (Arith e1a op1 e1b) (Arith e2a op2 e2b)
  = e1a `eqExpB` e2a && op1 `eqArithOpB` op2 && e1b `eqExpB` e2b
eqExpB (Cond e1a e1b e1c) (Cond e2a e2b e2c)
  = e1a `eqExpB` e2a && e1b `eqExpB` e2b && e1c `eqExpB` e2c
eqExpB (IntE i1)     (IntE i2)     = i1 == i2
eqExpB (BoolE b1)    (BoolE b2)    = b1 == b2
eqExpB _             _             = False

----------------------------------------------------
-- | Extract the type of an expression
exprType :: SVec ctx -> Exp ctx ty -> STy ty
exprType ctx (Var v) = go v ctx
  where
    go :: forall a n (v :: Vec a n) (x :: a). Elem v x -> SVec v -> Sing x
    go EZ     (h :%> _) = h
    go (ES e) (_ :%> t) = go e t
exprType ctx (Lam arg_ty body) = arg_ty ::-> exprType (arg_ty :%> ctx) body
exprType ctx (App fun _)       = extractResType $ exprType ctx fun
exprType ctx (Let e1 e2)       = exprType (exprType ctx e1 :%> ctx) e2
exprType _   (Arith _ op _)    = arithType op
exprType ctx (Cond _ e1 _)     = exprType ctx e1
exprType ctx (Fix body)        = extractResType $ exprType ctx body
exprType _   (IntE _)          = sing
exprType _   (BoolE _)         = sing

----------------------------------------------------
-- Pretty-printing

instance Pretty (Exp VNil ty) where
  pretty = prettyExp topPrec

instance forall n (ctx :: Ctx n) ty. SingI n => PrettyExp (Exp ctx ty) where
  type NumBoundVars (Exp (ctx :: Ctx n) ty) = n
  prettyExp = pretty_exp

pretty_exp :: SingI n => Prec -> Exp (ctx :: Ctx n) ty -> Doc
pretty_exp _    (Var n)          = prettyVar (elemToFin n)
pretty_exp prec (Lam ty body)    = prettyLam prec ty body
pretty_exp prec (App e1 e2)      = prettyApp prec e1 e2
pretty_exp prec (Let e1 e2)      = prettyLet prec e1 e2
pretty_exp prec (Arith e1 op e2) = prettyArith prec e1 op e2
pretty_exp prec (Cond e1 e2 e3)  = prettyIf prec e1 e2 e3
pretty_exp prec (Fix e)          = prettyFix prec e
pretty_exp _    (IntE n)         = int n
pretty_exp _    (BoolE True)     = text "true"
pretty_exp _    (BoolE False)    = text "false"
