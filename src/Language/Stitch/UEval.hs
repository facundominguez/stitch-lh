{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple" @-}

module Language.Stitch.UEval where

import qualified Data.Map (Map)
-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators (Proof, (==.), (===), (***), QED(..), (?))
import Language.Stitch.Data.List (List(..))
import qualified Language.Stitch.Data.List as List
import qualified Language.Stitch.Data.Map as Map
import Language.Stitch.Data.Nat
import Language.Stitch.Infer
import Language.Stitch.Op
import Language.Stitch.Type
import Language.Stitch.Unchecked

import Text.PrettyPrint.ANSI.Leijen

------------------------------------------------
-- Evaluation


-- XXX: If we don't include maybeJoin here LH fails with:
-- Unbound symbol is$GHC.Maybe.Just
{-@ reflect _maybeJoin @-}
_maybeJoin :: Maybe (Maybe a) -> Maybe a
_maybeJoin m = case m of
  Nothing -> Nothing
  Just Nothing -> Nothing
  Just (Just a) -> Just a

{-@
type ValueT T = { v:Value | valueType v = T }
data Value
       = VInt Int
       | VBool Bool
       | VFun (globals :: UGlobals)
              (ctx :: List Ty)
              (vfun_e :: { vfun_e:VarsSmallerThan UExp (List.length ctx)
                         | hasAType globals ctx vfun_e && isFunTy (uexpType globals ctx vfun_e)
                         }
              )
              (   { v:Value | funArgTy (uexpType globals ctx vfun_e) = valueType v }
               -> { vr:Value | funResTy (uexpType globals ctx vfun_e) = valueType vr }
              )
@-}
data Value = VInt Int | VBool Bool | VFun UGlobals (List Ty) UExp (Value -> Value)



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
valueType (VFun globals ctx e _) = uexpType globals ctx e

{-@
valueAt
  :: i : Nat
  -> vs : { vs:List Value | i < List.length vs }
  -> t : { t:Ty | t = List.elemAt i (mapValueType vs) }
  -> { v:Value | t = valueType v && v = List.elemAt i vs }
@-}
valueAt :: Nat -> List Value -> Ty -> Value
valueAt 0 (Cons x _) _ = x
valueAt n (Cons _ xs) t = valueAt (n-1) xs t

-- | Evaluate an expression, using big-step semantics.
{-@
eval
  :: te : TypedExp
  -> { v:Value | valueType v = typedExpType te }
@-}
eval :: TypedExp -> Value
eval (TypedExp globals e _ty) = go globals Nil e

{-@ go
      :: globals : UGlobals
      -> ctx : List Value
      -> e : { e:VarsSmallerThan UExp (List.length ctx) | hasAType globals (mapValueType ctx) e }
      -> { v:Value | hasInferredTypeWithCtx globals (mapValueType ctx) e (valueType v) }
@-}
go :: UGlobals -> List Value -> UExp -> Value
go globals ctx e0 = case e0 of
    UVar i ->
      List.elemAt i (ctx ? mapValueTypeLength_prop ctx) ? elemAtThroughMapValueType_prop i ctx

    UGlobal name -> case lookupUGlobals name globals of
      -- Given that the input expression is well typed,
      -- the Nothing case is impossible
      Just (TypedExp ge e _ty) -> go ge Nil e

--    ULam ty_arg e ->
--      VFun globals (mapValueType ctx) e0 (\v -> go globals (Cons v ctx) e) ? funResTy_lam_prop globals (mapValueType ctx) ty_arg e

--    UApp e1 e2 -> case go globals ctx e1 of
--      VFun _ _ _ f -> f (go globals ctx e2)


    -- Evaluating the expression would require inferring types
    -- again for e1 or e2
    -- UApp e1 e2 -> ... 



{-@
mapValueTypeLength_prop
  :: ctx:List Value -> { List.length (mapValueType ctx) = List.length ctx }
@-}
mapValueTypeLength_prop :: List Value -> Proof
mapValueTypeLength_prop ctx =
  List.length (mapValueType ctx)
  ==.
  List.length ctx
  ***
  QED

{-@
elemAtThroughMapValueType_prop
  :: i:Nat
  -> ctx : { ctx:List Value | i < List.length ctx }
  -> { List.elemAt i (mapValueType ctx) = valueType (List.elemAt i ctx) }
@-}
elemAtThroughMapValueType_prop :: Nat -> List Value -> Proof
elemAtThroughMapValueType_prop 0 ctx@(Cons _ _) =
  List.elemAt 0 (mapValueType ctx)
  ==.
  valueType (List.elemAt 0 ctx)
  ***
  QED
elemAtThroughMapValueType_prop i ctx@(Cons _ ctxs) =
  List.elemAt i (mapValueType ctx)
  ==.
  valueType (List.elemAt i ctx) ? elemAtThroughMapValueType_prop (i - 1) ctxs
  ***
  QED

{-@
hasAType_lam_prop
  :: globals:UGlobals
  -> ctx:List Ty
  -> ty:Ty
  -> e: { e:VarsSmallerThan UExp (List.length (Cons ty ctx))
        | hasAType globals ctx (ULam ty e)
        }
  -> { hasAType globals (Cons ty ctx) e }
@-}
hasAType_lam_prop :: UGlobals -> List Ty -> Ty -> UExp -> Proof
hasAType_lam_prop globals ctx ty e =
  hasAType globals ctx (ULam ty e)
  ===
  (case inferUExpTypeWithCtx globals ctx (ULam ty e) of
    Success _ -> True
    Error _ -> False
  )
  ===
  hasAType globals (Cons ty ctx) e
  ***
  QED

{-@
funResTy_lam_prop
  :: globals:UGlobals
  -> ctx:List Ty
  -> ty:Ty
  -> e: { e:VarsSmallerThan UExp (List.length (Cons ty ctx))
        | hasAType globals ctx (ULam ty e)
        }
  -> { hasAType globals (Cons ty ctx) e &&
       funResTy (uexpType globals ctx (ULam ty e)) = uexpType globals (Cons ty ctx) e
     }
@-}
funResTy_lam_prop :: UGlobals -> List Ty -> Ty -> UExp -> Proof
funResTy_lam_prop globals ctx ty e =
  funResTy (uexpType globals ctx (ULam ty e)) -- ? isFunTy_lam_prop globals ctx ty e)
  ===
  funResTy (case inferUExpTypeWithCtx globals ctx (ULam ty e) of
    Success t -> t
  )
  ===
  funResTy (
        case inferUExpTypeWithCtx globals (List.cons ty ctx) e of
          Success r -> TFun ty r
  )
  ===
  uexpType globals (Cons ty ctx) e
  ***
  QED

{-@
isFunTy_lam_prop
  :: globals:UGlobals
  -> ctx:List Ty
  -> ty:Ty
  -> { e:VarsSmallerThan UExp (List.length (Cons ty ctx)) | hasAType globals ctx (ULam ty e) }
  -> { isFunTy (uexpType globals ctx (ULam ty e)) }
@-}
isFunTy_lam_prop :: UGlobals -> List Ty -> Ty -> UExp -> Proof
isFunTy_lam_prop globals ctx ty e =
  isFunTy (uexpType globals ctx (ULam ty e))
  ==.
  True
  ***
  QED
