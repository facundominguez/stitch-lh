{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--exact-data-cons" @-}
-- ple is necessary to reason about the evaluation of checkBindings
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Check
-- Copyright   :  (C) 2015 Richard Eisenberg
--                (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- The stitch typechecker.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Check where

-- XXX: If we don't import Data.Set, LH fails with: Unbound symbol Set_mem
import qualified Data.Set as Set
import Language.Stitch.LH.Data.List (List(..))
import qualified Language.Stitch.LH.Data.List as List
import Language.Stitch.LH.Data.Map (Map)
import qualified Language.Stitch.LH.Data.Map as Map
import Language.Stitch.LH.Data.Nat as Nat
import Language.Stitch.LH.Type
import Language.Stitch.LH.Op
import Language.Stitch.LH.Pretty
import Language.Stitch.LH.Unchecked
import Text.PrettyPrint.ANSI.Leijen


{-@
type VarsSmallerThanExp N = { e : Exp | numFreeVarsExp e <= N }
type SaneBindings exp CTX = { e : exp | checkBindings CTX e }
type WellTypedExp CTX = SaneBindings (VarsSmallerThanExp (List.length CTX)) CTX
predicate WellTyped E CTX = checkBindings CTX E && numFreeVarsExp E <= (List.length CTX)
type FunExp = { e : Exp | isFunTy (exprType e) }
type ExpT T = { e : Exp | T = exprType e }
data Exp
  = Var Ty Nat
  | Lam Ty Exp
  | App (e1 :: FunExp) (ExpT (funArgTy (exprType e1)))
  | Let Exp Exp
  | Arith (ExpT TInt) ArithOp (ExpT TInt)
  | Cond (ExpT TBool) (a :: Exp) (ExpT (exprType a))
  | Fix ({ e:FunExp | funArgTy (exprType e) = funResTy (exprType e) })
  | IntE Int
  | BoolE Bool
@-}

-- | Checked expression
data Exp
  = Var Ty Nat
  | Lam Ty Exp
  | App Exp Exp
  | Let Exp Exp
  | Arith Exp ArithOp Exp
  | Cond Exp Exp Exp
  | Fix Exp
  | IntE Int
  | BoolE Bool
  deriving Show

-- An expression paired with the bound for the valid
-- variable indices
{-@ data ScopedExp = ScopedExp (n :: NumVarsInScope) (VarsSmallerThanExp n) @-}
data ScopedExp = ScopedExp NumVarsInScope Exp

instance Pretty ScopedExp where
  pretty (ScopedExp n e) = pretty (ScopedUExp n (uncheckExp e))

{-@ uncheckExp :: e:Exp -> { uexp:UExp | numFreeVarsExp e = numFreeVars uexp } @-}
uncheckExp :: Exp -> UExp
uncheckExp = \case
  Var _ i -> UVar i
  Lam ty e -> ULam ty (uncheckExp e)
  App e1 e2 -> UApp (uncheckExp e1) (uncheckExp e2)
  Let e1 e2 -> ULet (uncheckExp e1) (uncheckExp e2)
  Arith e1 op e2 -> UArith (uncheckExp e1) op (uncheckExp e2)
  Cond e1 e2 e3 -> UCond (uncheckExp e1) (uncheckExp e2) (uncheckExp e3)
  Fix e -> UFix (uncheckExp e)
  IntE i -> UIntE i
  BoolE b -> UBoolE b

{-@ measure exprType @-}
exprType :: Exp -> Ty
exprType (Var ty _) = ty
exprType (Lam ty e) = TFun ty (exprType e)
exprType (App e1 _) = funResTy (exprType e1)
exprType (Let _ e2) = exprType e2
exprType (Arith _ op _) = arithType op
exprType (Cond _ e2 _) = exprType e2
exprType (Fix e) = funResTy (exprType e)
exprType (IntE _) = TInt
exprType (BoolE _) = TBool

-- | Check that all occurrences of a variable have the given type
{-@ reflect checkBindings @-}
{-@ checkBindings :: ctx : List Ty -> VarsSmallerThanExp (List.length ctx) -> Bool @-}
checkBindings :: List Ty -> Exp -> Bool
checkBindings ctx (Var vty i) = List.elemAt i ctx == vty
checkBindings ctx (Lam t e) = checkBindings (Cons t ctx) e
checkBindings ctx (App e1 e2) = checkBindings ctx e1 && checkBindings ctx e2
checkBindings ctx (Let e1 e2) = checkBindings ctx e1 && checkBindings (Cons (exprType e1) ctx) e2
checkBindings ctx (Arith e1 _ e2) = checkBindings ctx e1 && checkBindings ctx e2
checkBindings ctx (Cond e1 e2 e3) = checkBindings ctx e1 && checkBindings ctx e2 && checkBindings ctx e3
checkBindings ctx (Fix e) = checkBindings ctx e
checkBindings _ (IntE _) = True
checkBindings _ (BoolE _) = True

{-@
assume aClosedExpIsValidInAnyContext
  :: ctx : List Ty
  -> e : WellTypedExp Nil
  -> { er : WellTypedExp ctx | e = er }
@-}
aClosedExpIsValidInAnyContext :: List Ty -> Exp -> Exp
aClosedExpIsValidInAnyContext _ e = e

{-@
measure numFreeVarsExp
numFreeVarsExp :: Exp -> Nat
@-}
numFreeVarsExp :: Exp -> Nat
numFreeVarsExp (Var _ v) = v + 1
numFreeVarsExp (Lam _ body) = Nat.minus (numFreeVarsExp body) 1
numFreeVarsExp (App e1 e2) = Nat.max (numFreeVarsExp e1) (numFreeVarsExp e2)
numFreeVarsExp (Let e1 e2) =
    Nat.max (numFreeVarsExp e1) (Nat.minus (numFreeVarsExp e2) 1)
numFreeVarsExp (Arith e1 _ e2) = Nat.max (numFreeVarsExp e1) (numFreeVarsExp e2)
numFreeVarsExp (Cond e1 e2 e3) =
    Nat.max (Nat.max (numFreeVarsExp e1) (numFreeVarsExp e2)) (numFreeVarsExp e3)
numFreeVarsExp (Fix body) = numFreeVarsExp body
numFreeVarsExp (IntE _) = 0
numFreeVarsExp (BoolE _) = 0

{-@
check
  :: Globals
  -> VarsSmallerThan UExp 0
  -> (e : WellTypedExp Nil -> { t: Ty | exprType e = t } -> Either TyError b)
  -> Either TyError b
@-}
check :: Globals -> UExp -> (Exp -> Ty -> Either TyError b) -> Either TyError b
check globals = go Nil
  where
    {-@
      go :: ts : List Ty
         -> VarsSmallerThan UExp (List.length ts)
         -> (e1 : WellTypedExp ts -> { t: Ty | exprType e1 = t } -> Either TyError b)
         -> Either TyError b
      @-}
    go :: List Ty -> UExp -> (Exp -> Ty -> Either TyError b) -> Either TyError b
    go ctx ue f = case ue of
      UVar i -> let ty = List.elemAt i ctx
                 in f (Var ty i) ty

      UGlobal name -> case lookupGlobal name globals of
        Just (TypedExp e t) -> f (aClosedExpIsValidInAnyContext ctx e) t
        Nothing -> Left (OutOfScopeGlobal name)

      -- XXX: Using $ here causes liquid haskell to crash
      ULam ty body -> go (Cons ty ctx) body (\r rty -> f (Lam ty r) (TFun ty rty))

      UApp e1 e2 ->
          go ctx e1 (\te1 ty1 -> go ctx e2 (\te2 ty2 -> case ty1 of
            TFun farg_ty res_ty ->
              if farg_ty == ty2 then
                f (App te1 te2) res_ty
              else
                Left $ TypeMismatch
                  (ScopedUExp (List.length ctx) e2)
                  farg_ty
                  ty2
                  (ScopedUExp (List.length ctx) (UApp e1 e2))
            ty -> Left (NotAFunction (ScopedUExp (List.length ctx) e1) ty)
          ))

      ULet e1 e2 ->
        go ctx e1 (\te1 ty1 -> go (Cons ty1 ctx) e2 (\te2 ty2 ->
          f (Let te1 te2) ty2
        ))

      UArith e1 op e2 ->
        go ctx e1 (\te1 ty1 -> go ctx e2 (\te2 ty2 ->
          if ty1 == TInt then
            if ty2 == TInt then
              f (Arith te1 op te2) (arithType op)
            else
              Left $ TypeMismatch
                (ScopedUExp (List.length ctx) e2)
                TInt
                ty2
                (ScopedUExp (List.length ctx) (UArith e1 op e2))
          else
            Left $ TypeMismatch
              (ScopedUExp (List.length ctx) e1)
              TInt
              ty1
              (ScopedUExp (List.length ctx) (UArith e1 op e2))
        ))

      UCond e1 e2 e3 ->
        go ctx e1 (\te1 ty1 -> go ctx e2 (\te2 ty2 -> go ctx e3 (\te3 ty3 ->
          if ty1 == TBool then
            if ty2 == ty3 then
              f (Cond te1 te2 te3) ty2
            else
              Left $ TypeMismatch
                (ScopedUExp (List.length ctx) e3)
                ty2
                ty3
                (ScopedUExp (List.length ctx) (UCond e1 e2 e3))
          else
            Left $ TypeMismatch
              (ScopedUExp (List.length ctx) e1)
              TBool
              ty1
              (ScopedUExp (List.length ctx) (UCond e1 e2 e3))
        )))

      UFix e -> go ctx e (\te1 ty1 -> case ty1 of
          TFun arg_ty res_ty ->
            if arg_ty == res_ty then
              f (Fix te1) res_ty
            else
              Left $ TypeMismatch
                (ScopedUExp (List.length ctx) e)
                (TFun arg_ty arg_ty)
                (TFun arg_ty res_ty)
                (ScopedUExp (List.length ctx) (UFix e))
          ty -> Left (NotAFunction (ScopedUExp (List.length ctx) e) ty)
        )

      UIntE i -> f (IntE i) TInt

      UBoolE b -> f (BoolE b) TBool

data TyError
  = OutOfScopeGlobal String
  | NotAFunction ScopedUExp Ty
  | TypeMismatch ScopedUExp Ty Ty ScopedUExp -- expression expected_type actual_type context
  deriving Show

instance Pretty TyError where
  pretty = \case
    OutOfScopeGlobal name ->
      text "Global variable not in scope:" <+> squotes (text name)
    NotAFunction e ty ->
      text "Expected a function instead of" <+>
      squotes (prettyTypedExp e ty)
    TypeMismatch e expected actual ctx ->
      text "Found" <+> squotes (prettyTypedExp e expected) <$$>
      text "but expected type" <+> squotes (pretty actual) <$$>
      inTheExpression ctx

prettyTypedExp :: ScopedUExp -> Ty -> Doc
prettyTypedExp e ty = pretty e <+> text ":" <+> pretty ty

inTheExpression :: ScopedUExp -> Doc
inTheExpression e = text "in the expression" <+> squotes (pretty e)


{-@
data TypedExp = TypedExp (e :: WellTypedExp Nil) {t:Ty | exprType e = t}
@-}
data TypedExp = TypedExp Exp Ty

{-@ measure typedExpType @-}
typedExpType :: TypedExp -> Ty
typedExpType (TypedExp _ ty) = ty

-- | The global variable environment maps variables to
-- expressions
-- XXX: Using newtype causes LH to crash.
data Globals = Globals (Map String TypedExp)

-- | An empty global variable environment
emptyGlobals :: Globals
emptyGlobals = Globals Map.empty

-- | Extend a 'Globals' with a new binding
{-@ extendGlobals :: String -> TypedExp -> Globals -> Globals @-}
extendGlobals :: String -> TypedExp -> Globals -> Globals
extendGlobals var e (Globals globals)
  -- XXX: Using $ causes LH to fail here
  = Globals (Map.insert var e globals)

-- | Lookup a global variable. Fails with 'throwError' if the variable
-- is not bound.
lookupGlobal
  :: String -> Globals -> Maybe TypedExp
lookupGlobal var (Globals globals) = Map.lookup var globals
