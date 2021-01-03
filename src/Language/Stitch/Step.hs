{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Step
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- Stitch expression evaluators for checked expressions.
--
----------------------------------------------------------------------------

module Language.Stitch.Step where

-- XXX: Needed to avoid missing symbols in LH
import qualified Data.Set as Set
import Language.Haskell.Liquid.ProofCombinators (Proof, (===), (***), QED(..), (?))
import Language.Stitch.Data.List (List(..))
import qualified Language.Stitch.Data.List as List
-- XXX: Needed to avoid missing symbols in LH
import qualified Language.Stitch.Data.Map as Map
import Language.Stitch.Data.Nat
import Language.Stitch.Check
import Language.Stitch.Eval
import Language.Stitch.Op
import Language.Stitch.Type

import Text.PrettyPrint.ANSI.Leijen


{-@
subst
  :: es:WellTypedExp Nil
  -> e1:WellTypedExp (Cons (exprType es) Nil)
  -> { er:WellTypedExp Nil | exprType e1 == exprType er }
@-}
subst :: Exp -> Exp -> Exp
subst es = substIndex (Cons (exprType es) Nil) 0 es

{-@
substIndex
  :: ctx:List Ty
  -> i:Nat
  -> es: { es:WellTypedExp Nil | exprType es = List.elemAt i ctx }
  -> e1:WellTypedExp ctx
  -> { er:WellTypedExp ctx | exprType e1 == exprType er }
@-}
substIndex :: List Ty -> Nat -> Exp -> Exp -> Exp
substIndex ctx i es e0 = case e0 of
    Var _ v ->
      if v == i then
        aClosedExpIsValidInAnyContext (List.deleteAt i ctx) es
      else
        e0
--    Lam ty e1 -> Lam ty (substIndex (Cons ty ctx) (i + 1) es e1)

{-

j = i => checkBindings ctx (Var ty i) = checkBindings (List.deleteAt j ctx) (Var ty i)


Nil e
List.deleteAt 0 (Cons x Nil) ==
:: List Ty -> Exp -> Bool
@-}

{-
{-@
step
  :: e:WellTypedExp Nil
  -> Either (ValueT (exprType e))
            ({ r:WellTypedExp Nil | exprType e = exprType r })
@-}
step :: Exp -> Either Value Exp
step = stepWithCtx Nil

{-@
stepWithCtx
  :: ctx:List Value
  -> e:WellTypedExp (mapValueType ctx)
  -> Either (ValueT (exprType e))
            ({ r:WellTypedExp (mapValueType ctx) | exprType e = exprType r })
@-}
stepWithCtx :: List Value -> Exp -> Either Value Exp
stepWithCtx ctx e0 = case e0 of
    Var{} -> Left (evalWithCtx ctx e0)
    Lam{} -> Left (evalWithCtx ctx e0)
    App e1 e2 -> case stepWithCtx ctx e1 of
      Right e1' -> Right (App e1' e2)
      Left (VFun _ f) -> case stepWithCtx ctx e2 of
        Right e2' -> Right (App e1 e2')
        Left v -> Left (f v)
--    Let e1 e2 -> case stepWithCtx ctx e1 of
--      Right e1' -> Right (Let e1' e2)
--      Left v1 -> stepWithCtx (Cons v1 ctx) e2
    Arith e1 op e2 -> case stepWithCtx ctx e1 of
      Right e1' -> Right (Arith e1' op e2)
      Left v1 -> case stepWithCtx ctx e2 of
        Right e2' -> Right (Arith e1 op e2')
        Left v2 -> Left (evalArithOp op v1 v2)
    Cond e1 e2 e3 -> case stepWithCtx ctx e1 of
      Right e1' -> Right (Cond e1' e2 e3)
      Left v1 -> case stepWithCtx ctx e2 of
        Right e2' -> Right (Cond e1 e2' e3)
        Left v2 -> case stepWithCtx ctx e3 of
          Right e3' -> Right (Cond e1 e2 e3')
          Left v2 -> 
          Left (evalArithOp op v1 v2)





checkBindings (mapValueType ctx) (Var vty i)
==>
List.elemAt i (mapValueType ctx) = vty
==>


numFreeVarsExp (Var _ i) <= List.length (mapValueType ctx)
==>
i + 1 <= List.length (mapValueType ctx)
==>
i < List.length (mapValueType ctx)
==>
i < List.length ctx


eval :: Exp VNil t -> ValuePair t
eval (Var v)          = impossibleVar v
eval e@(Lam _ body)   = ValuePair e $ \ arg -> subst arg body
eval (App e1 e2)      = eval (apply (eval e1) (eval e2))
eval (Let e1 e2)      = eval (subst (expr $ eval e1) e2)
eval (Arith e1 op e2) = eval (arith (val $ eval e1) op (val $ eval e2))
eval (Cond e1 e2 e3)  = eval (cond (val $ eval e1) e2 e3)
eval (Fix e)          = eval (unfix (eval e))
eval e@(IntE n)       = ValuePair e n
eval e@(BoolE b)      = ValuePair e b

-}
{-

-- | Substitute the first expression into the second. As a proposition,
-- this is the substitution lemma.
subst :: forall ctx s t.
         Exp ctx s -> Exp (s :> ctx) t -> Exp ctx t
subst e = go LZ
  where
    go :: Length (locals :: Ctx n) -> Exp (locals +++ s :> ctx) t0 -> Exp (locals +++ ctx) t0
    go len (Var v)          = subst_var len v
    go len (Lam ty body)    = Lam ty (go (LS len) body)
    go len (App e1 e2)      = App (go len e1) (go len e2)
    go len (Let e1 e2)      = Let (go len e1) (go (LS len) e2)
    go len (Arith e1 op e2) = Arith (go len e1) op (go len e2)
    go len (Cond e1 e2 e3)  = Cond (go len e1) (go len e2) (go len e3)
    go len (Fix e)          = Fix (go len e)
    go _   (IntE n)         = IntE n
    go _   (BoolE b)        = BoolE b

    subst_var :: Length (locals :: Ctx n) -> Elem (locals +++ s :> ctx) t0
              -> Exp (locals +++ ctx) t0
    subst_var LZ       EZ     = e
    subst_var LZ       (ES v) = Var v
    subst_var (LS _)   EZ     = Var EZ
    subst_var (LS len) (ES v) = shift (subst_var len v)

-- | Given a lambda and an expression, beta-reduce.
apply :: ValuePair (arg :-> res) -> ValuePair arg -> Exp VNil res
apply fun arg = val fun (expr arg)

-- | Apply an arithmetic operator to two values.
arith :: Int -> ArithOp ty -> Int -> Exp VNil ty
arith n1 Plus     n2 = IntE $ n1 + n2
arith n1 Minus    n2 = IntE $ n1 - n2
arith n1 Times    n2 = IntE $ n1 * n2
arith n1 Divide   n2 = IntE $ n1 `div` n2
arith n1 Mod      n2 = IntE $ n1 `mod` n2
arith n1 Less     n2 = BoolE $ n1 < n2
arith n1 LessE    n2 = BoolE $ n1 <= n2
arith n1 Greater  n2 = BoolE $ n1 > n2
arith n1 GreaterE n2 = BoolE $ n1 >= n2
arith n1 Equals   n2 = BoolE $ n1 == n2

-- | Conditionally choose between two expressions
cond :: Bool -> Exp VNil t -> Exp VNil t -> Exp VNil t
cond True  e _ = e
cond False _ e = e

-- | Unroll a `fix` one level
unfix :: ValuePair (ty :-> ty) -> Exp VNil ty
unfix (ValuePair { expr = elam, val = vlam })
  = vlam (Fix elam)

-- | A well-typed variable in an empty context is impossible.
impossibleVar :: Elem VNil x -> a
impossibleVar = \case {}

-------------------------------------------------
-- Values

-- | Well-typed closed values.
type family Value t where
  Value TInt      = Int
  Value TBool     = Bool
  Value (a :-> b) = Exp VNil a -> Exp VNil b

-- | Store a value in both expression form and value form.
-- The duplication avoids conversions later without losing the
-- tagless aspect of values. Note that the 'ValuePair' constructor
-- should not considered a value tag; this type could be inlined into
-- an unboxed tuple with the same semantics; the only loss would
-- be syntactic cleanliness.
data ValuePair :: Ty -> Type where
  ValuePair :: { expr :: Exp VNil ty
               , val  :: Value ty
               } -> ValuePair ty

instance Pretty (ValuePair ty) where
  pretty = pretty . expr

------------------------------------------------
-- Evaluation

-- | Evaluate an expression, using big-step semantics.
eval :: Exp VNil t -> ValuePair t
eval (Var v)          = impossibleVar v
eval e@(Lam _ body)   = ValuePair e $ \ arg -> subst arg body
eval (App e1 e2)      = eval (apply (eval e1) (eval e2))
eval (Let e1 e2)      = eval (subst (expr $ eval e1) e2)
eval (Arith e1 op e2) = eval (arith (val $ eval e1) op (val $ eval e2))
eval (Cond e1 e2 e3)  = eval (cond (val $ eval e1) e2 e3)
eval (Fix e)          = eval (unfix (eval e))
eval e@(IntE n)       = ValuePair e n
eval e@(BoolE b)      = ValuePair e b

-- | The result of stepping is either a reduction or the detection
-- of a value.
data StepResult :: Ty -> Type where
  Step  :: Exp VNil ty -> StepResult ty
  Value :: ValuePair ty -> StepResult ty

-- | Step an expression, either to another expression or to a value.
step :: Exp VNil ty -> StepResult ty
step (Var v)          = impossibleVar v
step e@(Lam _ body)   = Value (ValuePair e $ \ arg -> subst arg body)
step (App e1 e2)      = case step e1 of
                          Step e1'      -> Step (App e1' e2)
                          Value lam_val ->
                            case step e2 of
                              Step e2'      -> Step (App (expr lam_val) e2')
                              Value arg_val -> Step (apply lam_val arg_val)
step (Let e1 e2)      = case step e1 of
                          Step e1' -> Step (Let e1' e2)
                          Value e1 -> Step (subst (expr e1) e2)
step (Arith e1 op e2) = case step e1 of
                          Step e1' -> Step (Arith e1' op e2)
                          Value v1 -> case step e2 of
                            Step e2' -> Step (Arith (expr v1) op e2')
                            Value v2 -> Step (arith (val v1) op (val v2))
step (Cond e1 e2 e3)  = case step e1 of
                          Step e1' -> Step (Cond e1' e2 e3)
                          Value v1 -> Step (cond (val v1) e2 e3)
step (Fix e)          = case step e of
                          Step e' -> Step (Fix e')
                          Value v -> Step (unfix v)
step e@(IntE n)       = Value (ValuePair e n)
step e@(BoolE b)      = Value (ValuePair e b)
-}
