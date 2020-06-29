{-# LANGUAGE ScopedTypeVariables, TypeInType, TypeOperators,
             TypeFamilies, GADTs, StandaloneDeriving, RankNTypes,
             LambdaCase, EmptyCase, TypeApplications #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Shift
-- Copyright   :  (C) 2015 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Richard Eisenberg (rae@cs.brynmawr.edu)
-- Stability   :  experimental
--
-- de Bruijn shifting
--
----------------------------------------------------------------------------

module Language.Stitch.Shift (
    Shiftable(..), shift, unshift, uncheckedUnshift
  ) where

import Language.Stitch.Exp
import Language.Stitch.Type

import Language.Stitch.Data.Vec
import Data.Kind ( Type )

import Unsafe.Coerce

class Shiftable (a :: forall n. Ctx n -> Ty -> Type) where
  -- | Shift all de Bruijn indices to accommodate a new context prefix
  shifts   :: Length prefix -> a ctx ty -> a (prefix +++ ctx) ty

  -- | Shift a closed term into a context with bound variables; this
  -- can often be more efficient than the general case
  shifts0  :: a VNil ty -> a prefix ty

  -- | Lower de Bruijn indices if possible; fails if an index is too low
  unshifts :: Length prefix -> a (prefix +++ ctx) ty -> Maybe (a ctx ty)

-- | Convenient abbreviation for the common case of shifting by only one index
shift :: forall (a :: forall n. Ctx n -> Ty -> Type) ctx t ty.
         Shiftable a => a ctx ty -> a (t :> ctx) ty
shift = shifts (LS LZ)

-- | Convenient synonym for the common case of unshifting by only one level.
unshift :: forall (a :: forall n. Ctx n -> Ty -> Type) ctx t ty.
           Shiftable a => a (t :> ctx) ty -> Maybe (a ctx ty)
unshift = unshifts (LS LZ)

-- | Unshift, but assert that this succeeds
uncheckedUnshift :: forall (a :: forall n. Ctx n -> Ty -> Type) ctx t ty.
                    Shiftable a => a (t :> ctx) ty -> a ctx ty
uncheckedUnshift e = case unshift e of
  Just e' -> e'
  Nothing -> error "uncheckedUnshift failure"

instance Shiftable Exp where
  shifts    = shiftsExp
  shifts0   = shifts0Exp
  unshifts  = unshiftsExp

instance Shiftable Elem where
  shifts    = weakenElem
  shifts0   = \case {}
  unshifts  = strengthenElem

-- | Convert an expression typed in one context to one typed in a larger
-- context. Operationally, this amounts to de Bruijn index shifting.
-- As a proposition, this is the weakening lemma.
shiftsExp :: forall prefix ctx ty. Length prefix -> Exp ctx ty -> Exp (prefix +++ ctx) ty
shiftsExp prefix = go LZ
  where
    go :: Length (locals :: Ctx n) -> Exp (locals +++ ctx) ty0 -> Exp (locals +++ prefix +++ ctx) ty0
    go len (Var v)          = Var (shifts_var len v)
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    shifts_var :: Length (locals :: Ctx n)
               -> Elem (locals +++ ctx) ty0
               -> Elem (locals +++ prefix +++ ctx) ty0
    shifts_var LZ     v      = weakenElem prefix v
    shifts_var (LS _) EZ     = EZ
    shifts_var (LS l) (ES e) = ES (shifts_var l e)

-- | If an expression is closed, we actually have no work to do. Unfortunately,
-- we cannot convince GHC of this fact, and so we have to recur out to the leaves
-- to fix the types.
shifts0Exp :: forall prefix ty. Exp VNil ty -> Exp prefix ty
shifts0Exp = go LZ
  where
    go :: Length (locals :: Ctx n) -> Exp locals ty0 -> Exp (locals +++ prefix) ty0
    go len (Var v)          = Var (shifts0_var v len)
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    shifts0_var :: Elem locals ty0 -> Length (locals :: Ctx n) -> Elem (locals +++ prefix) ty0
    shifts0_var EZ     _        = EZ
    shifts0_var (ES v) (LS len) = ES (shifts0_var v len)

-- Because shifts0Exp provably does nothing, let's just short-circuit it:
{-# NOINLINE shifts0Exp #-}
{-# RULES "shifts0Exp" shifts0Exp = unsafeCoerce #-}

-- | Unshift an expression. This is essentially a strengthening lemma, which fails
-- precisely when de Bruijn index of a free variable to be unshifted is too low.
unshiftsExp :: forall prefix ctx ty.
           Length prefix -> Exp (prefix +++ ctx) ty -> Maybe (Exp ctx ty)
unshiftsExp prefix = go LZ
  where
    go :: forall num_locals (locals :: Ctx num_locals) ty.
          Length locals
       -> Exp (locals +++ prefix +++ ctx) ty
       -> Maybe (Exp (locals +++ ctx) ty)
    go len (Var v)          = Var <$> unshift_var len v
    go len (Lam ty body)    = Lam ty <$> go (LS len) body
    go len (App e1 e2)      = App <$> go len e1 <*> go len e2
    go len (Let e1 e2)      = Let <$> go len e1 <*> go (LS len) e2
    go len (Arith e1 op e2) = Arith <$> go len e1 <*> pure op <*> go len e2
    go len (Cond e1 e2 e3)  = Cond <$> go len e1 <*> go len e2 <*> go len e3
    go len (Fix e)          = Fix <$> go len e
    go _   (IntE n)         = pure (IntE n)
    go _   (BoolE b)        = pure (BoolE b)

    unshift_var :: forall num_locals (locals :: Ctx num_locals) ty.
                   Length locals
                -> Elem (locals +++ prefix +++ ctx) ty
                -> Maybe (Elem (locals +++ ctx) ty)
    unshift_var LZ       v      = strengthenElem prefix v
    unshift_var (LS _)   EZ     = pure EZ
    unshift_var (LS len) (ES v) = ES <$> unshift_var len v
