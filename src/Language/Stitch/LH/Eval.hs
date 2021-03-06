{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.LH.Eval
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Stitch expression evaluators for checked expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.LH.Eval where

-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))
import Language.Stitch.LH.Data.List (List(..))
import qualified Language.Stitch.LH.Data.List as List
-- XXX: Needed to avoid missing symbols in LH
import qualified Language.Stitch.LH.Data.Map as Map
import Language.Stitch.LH.Data.Nat
import Language.Stitch.LH.Check
import Language.Stitch.LH.Op
import Language.Stitch.LH.Type

import Text.PrettyPrint.ANSI.Leijen

------------------------------------------------
-- Evaluation

{-@
type ValueT T = { v:Value | valueType v = T }
data Value
       = VInt Int
       | VBool Bool
       | VFun (vfun_e :: FunExp)
              (   { v:Value | funArgTy (exprType vfun_e) = valueType v }
               -> { vr:Value | funResTy (exprType vfun_e) = valueType vr }
              )
@-}
data Value = VInt Int | VBool Bool | VFun Exp (Value -> Value)

instance Pretty Value where
  pretty = \case
    VInt i -> int i
    VBool True -> text "true"
    VBool False -> text "false"
    VFun e _ -> pretty (ScopedExp (numFreeVarsExp e) e)

{-@
// XXX: If using measure, LH fails with: elaborate makeKnowledge failed on
reflect mapValueType
mapValueType
  :: vs:List Value
  -> { ts:List Ty
     | List.length ts = List.length vs
     }
@-}
mapValueType :: List Value -> List Ty
mapValueType Nil = Nil
mapValueType (Cons x xs) = Cons (valueType x) (mapValueType xs)

{-@ measure valueType @-}
valueType :: Value -> Ty
valueType VInt{} = TInt
valueType VBool{} = TBool
valueType (VFun e _) = exprType e

-- | Evaluate an expression, using big-step semantics.
{-@
eval
  :: e : WellTypedExp Nil
  -> { v:Value | valueType v = exprType e }
@-}
eval :: Exp -> Value
eval = evalWithCtx Nil

{-@
evalWithCtx :: ctx:List Value -> e:WellTypedExp (mapValueType ctx) -> ValueT (exprType e)
@-}
evalWithCtx :: List Value -> Exp -> Value
evalWithCtx ctx e0 = case e0 of
    Var _ i ->
      List.elemAt i (ctx ? mapValueTypeLength_prop ctx) ? elemAtThroughMapValueType_prop i ctx

    -- TODO: omitting funArgTyLam_prop here gives a non-obvious message.
    -- Think about techiniques to arrive quickly at the missing assumption.
    Lam ty_arg e -> VFun e0 ((\v -> evalWithCtx (Cons (v ? funArgTyLam_prop ty_arg e) ctx) e) ? funResTy_lam_prop ty_arg e)

    App e1 e2 -> case evalWithCtx ctx e1 of
      VFun _ f -> f (evalWithCtx ctx e2)

    Let e1 e2 -> evalWithCtx (Cons (evalWithCtx ctx e1) ctx) e2

    Arith e1 op e2 -> evalArithOp op (evalWithCtx ctx e1) (evalWithCtx ctx e2)

    Cond e1 e2 e3 -> case evalWithCtx ctx e1 of
      VBool True -> evalWithCtx ctx e2
      VBool False -> evalWithCtx ctx e3

    Fix e -> case evalWithCtx ctx e of
      VFun _ f -> valueFix (exprType e0) f

    IntE i -> VInt i

    BoolE b -> VBool b

{-@
valueFix :: t:Ty -> (ValueT t -> ValueT t) -> ValueT t
lazy valueFix
@-}
valueFix :: Ty -> (Value -> Value) -> Value
valueFix t f = f (valueFix t f)

{-@
evalArithOp :: op:ArithOp -> ValueT TInt -> ValueT TInt -> ValueT (arithType op)
@-}
evalArithOp :: ArithOp -> Value -> Value -> Value
evalArithOp = \case
  Plus -> evalIntOp (+)
  Minus -> evalIntOp (-)
  Times -> evalIntOp (*)
  Divide -> evalIntOp unsafeDiv
  Mod -> evalIntOp unsafeMod
  Less -> evalBoolOp (<)
  LessE -> evalBoolOp (<=)
  Greater -> evalBoolOp (>)
  GreaterE -> evalBoolOp (>=)
  Equals -> evalBoolOp (==)

{-@
evalIntOp :: (Int -> Int -> Int) -> ValueT TInt -> ValueT TInt -> ValueT TInt
@-}
evalIntOp :: (Int -> Int -> Int) -> Value -> Value -> Value
evalIntOp f (VInt i0) (VInt i1) = VInt (f i0 i1)

{-@
evalBoolOp :: (Int -> Int -> Bool) -> ValueT TInt -> ValueT TInt -> ValueT TBool
@-}
evalBoolOp :: (Int -> Int -> Bool) -> Value -> Value -> Value
evalBoolOp f (VInt i0) (VInt i1) = VBool (f i0 i1)

{-@ ignore unsafeDiv @-}
unsafeDiv :: Int -> Int -> Int
unsafeDiv = div
{-@ ignore unsafeMod @-}
unsafeMod :: Int -> Int -> Int
unsafeMod = mod


{-@
mapValueTypeLength_prop
  :: ctx:List Value -> { List.length (mapValueType ctx) = List.length ctx }
@-}
mapValueTypeLength_prop :: List Value -> Proof
mapValueTypeLength_prop ctx =
  List.length (mapValueType ctx)
  ===
  List.length ctx
  ***
  QED


-- TODO: why isn't funArgTyLam_prop obvious to LH?
{-@
funArgTyLam_prop
  :: ty : Ty
  -> e : Exp
  -> { funArgTy (exprType (Lam ty e)) = ty }
@-}
funArgTyLam_prop :: Ty -> Exp -> Proof
funArgTyLam_prop _ _ = ()

{-@
elemAtThroughMapValueType_prop
  :: i:Nat
  -> ctx : { List Value | i < List.length ctx }
  -> { List.elemAt i (mapValueType ctx) = valueType (List.elemAt i ctx) }
@-}
elemAtThroughMapValueType_prop :: Nat -> List Value -> Proof
elemAtThroughMapValueType_prop 0 ctx@(Cons _ _) =
  List.elemAt 0 (mapValueType ctx)
  ===
  valueType (List.elemAt 0 ctx)
  ***
  QED
elemAtThroughMapValueType_prop i ctx@(Cons _ ctxs) =
  List.elemAt i (mapValueType ctx)
  ===
  List.elemAt (i - 1) (mapValueType ctxs)
  ===
  (valueType (List.elemAt (i - 1) ctxs) ? elemAtThroughMapValueType_prop (i - 1) ctxs)
  ===
  valueType (List.elemAt i ctx)
  ***
  QED

{-@
funResTy_lam_prop
  :: ty:Ty -> e:Exp -> { funResTy (exprType (Lam ty e)) = exprType e }
@-}
funResTy_lam_prop :: Ty -> Exp -> Proof
funResTy_lam_prop ty e =
  funResTy (exprType (Lam ty e) ? isFunTy_lam_prop ty e)
  ===
  exprType e
  ***
  QED

{-@
isFunTy_lam_prop :: ty:Ty -> e:Exp -> { isFunTy (exprType (Lam ty e)) }
@-}
isFunTy_lam_prop :: Ty -> Exp -> Proof
isFunTy_lam_prop ty e =
  isFunTy (exprType (Lam ty e))
  ===
  isFunTy (TFun ty (exprType e))
  ===
  True
  ***
  QED
