{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell -Wno-incomplete-patterns #-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--ple" @-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Stitch.Infer
-- Copyright   :  (C) 2021 Facundo Domínguez
-- License     :  BSD-style (see LICENSE)
-- Stability   :  experimental
--
-- The stitch typechecker.
--
----------------------------------------------------------------------------

module Language.Stitch.Infer where

-- XXX: If we don't import Data.Set, LH fails with: Unbound symbol Set_mem
import qualified Data.Set as Set
import Language.Stitch.Data.Map (Map)
import Language.Stitch.Data.List (List(..))
import qualified Language.Stitch.Data.List as List
import qualified Language.Stitch.Data.Map as Map
import Language.Stitch.Type
import Language.Stitch.Op
import Language.Stitch.Unchecked
import Text.PrettyPrint.ANSI.Leijen


data TyError
  = OutOfScopeGlobal String
  | NotAFunction ScopedUExp Ty
  | TypeMismatch ScopedUExp Ty Ty ScopedUExp -- expression expected_type actual_type context
  deriving Eq

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

-- XXX: If we don't include maybeJoin here LH fails with:
-- Unbound symbol is$GHC.Maybe.Nothing
{-@ reflect _maybeJoin @-}
_maybeJoin :: Maybe (Maybe a) -> Maybe a
_maybeJoin m = case m of
  Nothing -> Nothing
  Just Nothing -> Nothing
  Just (Just a) -> Just a

{-@
reflect hasAType
hasAType
  :: UGlobals
  -> ctx:List Ty
  -> VarsSmallerThan UExp (List.length ctx)
  -> Bool
@-}
hasAType :: UGlobals -> List Ty -> UExp -> Bool
hasAType globals ctx e = case inferUExpTypeWithCtx globals ctx e of
  Success _ -> True
  Error _ -> False

{-@
reflect uexpType
uexpType
  :: globals:UGlobals
  -> ctx:List Ty
  -> { e:VarsSmallerThan UExp (List.length ctx) | hasAType globals ctx e }
  -> { t:Ty | hasInferredTypeWithCtx globals ctx e t }
@-}
uexpType :: UGlobals -> List Ty -> UExp -> Ty
uexpType globals ctx e = case inferUExpTypeWithCtx globals ctx e of
  Success t -> t

{-@
reflect inferUExpType
inferUExpType :: UGlobals -> VarsSmallerThan UExp 0 -> InferResult
@-}
inferUExpType :: UGlobals -> UExp -> InferResult
inferUExpType globals e = inferUExpTypeWithCtx globals Nil e

-- | This is isomorphic to @Either TyError Ty@. Using @Either@ makes LH
-- fail when trying to reflect type inference.
data InferResult = Error TyError | Success Ty
  deriving Eq

{-@
reflect hasInferredType
hasInferredType :: UGlobals -> VarsSmallerThan UExp 0 -> Ty -> Bool
@-}
hasInferredType :: UGlobals -> UExp -> Ty -> Bool
hasInferredType g = hasInferredTypeWithCtx g Nil

{-@
reflect hasInferredTypeWithCtx
hasInferredTypeWithCtx
  :: UGlobals -> ctx:List Ty -> VarsSmallerThan UExp (List.length ctx) -> Ty -> Bool
@-}
hasInferredTypeWithCtx :: UGlobals -> List Ty -> UExp -> Ty -> Bool
hasInferredTypeWithCtx g ctx e ty = inferUExpTypeWithCtx g ctx e == Success ty

{-@
reflect inferUExpTypeWithCtx
// XXX: The refined type prevents us from forgetting to add types to the
// context when introducing a lambda, but it doesn't prevent us from
// adding a type to the context more than once.
inferUExpTypeWithCtx
  :: UGlobals -> ts : List Ty -> e : VarsSmallerThan UExp (List.length ts) -> InferResult
@-}
inferUExpTypeWithCtx :: UGlobals -> List Ty -> UExp -> InferResult
inferUExpTypeWithCtx globals ctx = \case
      UVar i -> Success (List.elemAt i ctx)

      UGlobal name ->
        case lookupUGlobals name globals of
          Just (TypedExp _ _ ty) -> Success ty
          Nothing -> Error (OutOfScopeGlobal name)

      ULam ty body ->
        case inferUExpTypeWithCtx globals (List.cons ty ctx) body of
          Error err -> Error err
          Success r -> Success (TFun ty r)

      UApp e1 e2 ->
        case inferUExpTypeWithCtx globals ctx e1 of { Error err -> Error err; Success ty1 ->
        case inferUExpTypeWithCtx globals ctx e2 of { Error err -> Error err; Success ty2 ->
        case ty1 of
          TFun farg_ty res_ty ->
            if farg_ty == ty2 then
              Success res_ty
            else
              Error $ TypeMismatch
                (ScopedUExp (List.length ctx) e2)
                farg_ty
                ty2
                (ScopedUExp (List.length ctx) (UApp e1 e2))
          ty -> Error (NotAFunction (ScopedUExp (List.length ctx) e1) ty)
        }}

      ULet e1 e2 -> do
        case inferUExpTypeWithCtx globals ctx e1 of
          Error err -> Error err
          Success ty -> inferUExpTypeWithCtx globals (List.cons ty ctx) e2

      UArith e1 op e2 ->
        case inferUExpTypeWithCtx globals ctx e1 of { Error err -> Error err; Success ty1 ->
        case inferUExpTypeWithCtx globals ctx e2 of { Error err -> Error err; Success ty2 ->
        if ty1 == TInt then
          if ty2 == TInt then
            Success (arithType op)
          else
            Error $ TypeMismatch
              (ScopedUExp (List.length ctx) e2)
              TInt
              ty2
              (ScopedUExp (List.length ctx) (UArith e1 op e2))
        else
          Error $ TypeMismatch
            (ScopedUExp (List.length ctx) e1)
            TInt
            ty1
            (ScopedUExp (List.length ctx) (UArith e1 op e2))
        }}

      UCond e1 e2 e3 ->
        case inferUExpTypeWithCtx globals ctx e1 of { Error err -> Error err; Success ty1 ->
        case inferUExpTypeWithCtx globals ctx e2 of { Error err -> Error err; Success ty2 ->
        case inferUExpTypeWithCtx globals ctx e3 of { Error err -> Error err; Success ty3 ->
        if ty1 == TBool then
          if ty2 == ty3 then
            Success ty2
          else
            Error $ TypeMismatch
              (ScopedUExp (List.length ctx) e3)
              ty2
              ty3
              (ScopedUExp (List.length ctx) (UCond e1 e2 e3))
        else
          Error $ TypeMismatch
            (ScopedUExp (List.length ctx) e1)
            TBool
            ty1
            (ScopedUExp (List.length ctx) (UCond e1 e2 e3))
        }}}

      UFix e -> case inferUExpTypeWithCtx globals ctx e of
        Error err -> Error err
        Success (TFun arg_ty res_ty) ->
          if arg_ty == res_ty then
            Success res_ty
          else
            Error $ TypeMismatch
              (ScopedUExp (List.length ctx) e)
              (TFun arg_ty arg_ty)
              (TFun arg_ty res_ty)
              (ScopedUExp (List.length ctx) (UFix e))
        Success ty ->
          Error (NotAFunction (ScopedUExp (List.length ctx) e) ty)

      UIntE _ -> Success TInt

      UBoolE _ -> Success TBool

-- XXX: LH can't reflect _bindEither
{-
reflect _bindEither
@-}
_bindEither :: Either a b -> (b -> Either a c) -> Either a c
_bindEither (Right b) f = f b
_bindEither (Left a) _ = Left a


{-@
data TypedExp =
       TypedExp (g :: UGlobals) (e :: VarsSmallerThan UExp 0) { ty:Ty | hasInferredType g e ty }
@-}
data TypedExp = TypedExp UGlobals UExp Ty

{-@ measure typedExpType @-}
typedExpType :: TypedExp -> Ty
typedExpType (TypedExp _ _ ty) = ty

-- XXX: LH fails to reflect inferUExpTypeWithCtx if we make UGlobals a type synonym
-- instead: The types for the wrapper and worker data constructors cannot be merged
-- XXX: Using newtype in Haskell and data in LH silently ignores the refinement.

-- | The global variable environment maps variables to
-- expressions
newtype UGlobals = UGlobals (Map String TypedExp)

-- | An empty global variable environment
emptyUGlobals :: UGlobals
emptyUGlobals = UGlobals Map.empty

-- | Extend a 'UGlobals' with a new binding
{-@ extendUGlobals :: String -> TypedExp -> UGlobals -> UGlobals @-}
extendUGlobals :: String -> TypedExp -> UGlobals -> UGlobals
extendUGlobals var e (UGlobals globals)
  -- XXX: Using $ causes LH to fail here
  = UGlobals (Map.insert var e globals)

-- | Lookup a global variable.
{-@
reflect lookupUGlobals
lookupUGlobals :: String -> UGlobals -> Maybe TypedExp
@-}
lookupUGlobals :: String -> UGlobals -> Maybe TypedExp
lookupUGlobals var (UGlobals g) = Map.lookup var g
