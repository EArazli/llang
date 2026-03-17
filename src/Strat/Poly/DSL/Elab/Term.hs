{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.DSL.Elab.Term
  ( provisionalCtorSort
  , resolveTyVarMode
  , resolveTyVarDecl
  , mkTypeMetaVar
  , ownerModeForTypeMeta
  , elabTmDeclVar
  , elabParamDecls
  , buildTypeTemplateBinders
  , elabContext
  , elabContextWithTables
  , elabObjExpr
  , elabObjExprInScope
  , elabObjExprWithTables
  , elabObjExprWithTablesInScope
  , elabObjExprWithTablesImplicitMetas
  , elabObjExprWithTablesImplicitMetasInScope
  , elabObjExprInferOwner
  , elabObjExprInferOwnerInScope
  , elabObjExprInferOwnerWithTables
  , elabObjExprInferOwnerWithTablesInScope
  , elabTmTerm
  , elabTmTermInScope
  , elabTmTermWithTables
  , elabTmTermWithTablesInScope
  , lookupTmFunByNameInTables
  , lookupTmFunAnyInTables
  , elabInputShapes
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import Strat.Frontend.Env (emptyEnv)
import Strat.Poly.DSL.AST (RawBinderArg(..), RawInputShape, RawPolyContext, RawPolyObjExpr)
import Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabDiagExprWithInScope
  , unifyBoundary
  )
import Strat.Poly.DSL.Elab.TermBase hiding
  ( elabContext
  , elabContextWithTables
  , elabObjExpr
  , elabObjExprInScope
  , elabObjExprWithTables
  , elabObjExprWithTablesInScope
  , elabObjExprWithTablesImplicitMetas
  , elabObjExprWithTablesImplicitMetasInScope
  , elabObjExprInferOwner
  , elabObjExprInferOwnerInScope
  , elabObjExprInferOwnerWithTables
  , elabObjExprInferOwnerWithTablesInScope
  , elabInputShapes
  , elabTmTerm
  , elabTmTermInScope
  , elabTmTermWithTables
  , elabTmTermWithTablesInScope
  )
import qualified Strat.Poly.DSL.Elab.TermBase as Base
import Strat.Poly.Doctrine
  ( BinderSig(..)
  , CtorTables
  , Doctrine
  , InputShape
  , deriveCtorTablesForElab
  , doctrineElabTypeTheoryFromTables
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (Context, Obj, TermDiagram, TmVar)
import Strat.Poly.Term.AST (TermBinderArg(..))

elabContext
  :: Doctrine
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyContext
  -> Either Text Context
elabContext doc expectedMode tyVars tmVars tmBound ctx = do
  ctorTables <- deriveCtorTablesForElab doc
  elabContextWithTables doc ctorTables expectedMode tyVars tmVars tmBound ctx

elabContextWithTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyContext
  -> Either Text Context
elabContextWithTables doc ctorTables expectedMode tyVars tmVars tmBound =
  Base.elabContextWithTablesBy
    (termBinderArgElaborator M.empty doc ctorTables tyVars tmVars)
    doc
    ctorTables
    expectedMode
    tyVars
    tmVars
    tmBound

elabObjExpr
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExpr = elabObjExprInScope M.empty

elabObjExprInScope
  :: M.Map Text Obj
  -> Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInScope typeScope doc tyVars tmVars tmBound expectedOwnerMode expr = do
  ctorTables <- deriveCtorTablesForElab doc
  elabObjExprWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expectedOwnerMode expr

elabObjExprWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTables = elabObjExprWithTablesInScope M.empty

elabObjExprWithTablesInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expectedOwnerMode =
  Base.elabObjExprWithTablesInScopeBy
    (termBinderArgElaborator typeScope doc ctorTables tyVars tmVars)
    typeScope
    doc
    ctorTables
    tyVars
    tmVars
    tmBound
    expectedOwnerMode

elabObjExprWithTablesImplicitMetas
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTablesImplicitMetas = elabObjExprWithTablesImplicitMetasInScope M.empty

elabObjExprWithTablesImplicitMetasInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> ModeName
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprWithTablesImplicitMetasInScope typeScope doc ctorTables tyVars tmVars tmBound expectedOwnerMode =
  Base.elabObjExprWithTablesImplicitMetasInScopeBy
    (termBinderArgElaborator typeScope doc ctorTables tyVars tmVars)
    typeScope
    doc
    ctorTables
    tyVars
    tmVars
    tmBound
    expectedOwnerMode

elabObjExprInferOwner
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwner = elabObjExprInferOwnerInScope M.empty

elabObjExprInferOwnerInScope
  :: M.Map Text Obj
  -> Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerInScope typeScope doc tyVars tmVars tmBound expr = do
  ctorTables <- deriveCtorTablesForElab doc
  elabObjExprInferOwnerWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound expr

elabObjExprInferOwnerWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerWithTables = elabObjExprInferOwnerWithTablesInScope M.empty

elabObjExprInferOwnerWithTablesInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> RawPolyObjExpr
  -> Either Text Obj
elabObjExprInferOwnerWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound =
  Base.elabObjExprInferOwnerWithTablesInScopeBy
    (termBinderArgElaborator typeScope doc ctorTables tyVars tmVars)
    typeScope
    doc
    ctorTables
    tyVars
    tmVars
    tmBound

elabInputShapes
  :: Doctrine
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> [RawInputShape]
  -> Either Text [InputShape]
elabInputShapes doc mode tyVars tmVars shapes = do
  ctorTables <- deriveCtorTablesForElab doc
  Base.elabInputShapesBy
    (termBinderArgElaborator M.empty doc ctorTables tyVars tmVars)
    doc
    mode
    tyVars
    tmVars
    shapes

elabTmTerm
  :: Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTerm = elabTmTermInScope M.empty

elabTmTermInScope
  :: M.Map Text Obj
  -> Doctrine
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermInScope typeScope doc tyVars tmVars tmBound mExpected raw = do
  ctorTables <- deriveCtorTablesForElab doc
  elabTmTermWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound mExpected raw

elabTmTermWithTables
  :: Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermWithTables = elabTmTermWithTablesInScope M.empty

elabTmTermWithTablesInScope
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> M.Map Text (Int, Obj)
  -> Maybe Obj
  -> RawPolyObjExpr
  -> Either Text TermDiagram
elabTmTermWithTablesInScope typeScope doc ctorTables tyVars tmVars tmBound mExpected raw =
  Base.elabTmTermWithTablesInScopeBy
    (termBinderArgElaborator typeScope doc ctorTables tyVars tmVars)
    typeScope
    doc
    ctorTables
    tyVars
    tmVars
    tmBound
    mExpected
    raw

termBinderArgElaborator
  :: M.Map Text Obj
  -> Doctrine
  -> CtorTables
  -> [TmVar]
  -> [TmVar]
  -> ModeName
  -> [BinderSig]
  -> [RawBinderArg]
  -> Either Text [TermBinderArg]
termBinderArgElaborator typeScope doc ctorTables tyVars tmVars mode slots rawArgs =
  case (slots, rawArgs) of
    ([], []) -> Right []
    ([], _) -> Left "term head does not accept binder arguments"
    (_:_, []) -> Left "missing term head binder arguments"
    _ | length slots /= length rawArgs ->
          Left "term head binder arity mismatch"
    _ ->
          mapM elabOne (zip slots rawArgs)
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars

    elabOne (slot, rawArg) =
      case rawArg of
        RBAMeta _ ->
          Left "term head binder arguments do not support binder metavariables"
        RBAExpr exprArg -> do
          ttDoc <- doctrineElabTypeTheoryFromTables doc ctorTables
          (diagArg, _) <-
            elabDiagExprWithInScope
              M.empty
              typeScope
              emptyEnv
              doc
              mode
              (bsTmCtx slot)
              tyVars
              tmVars
              M.empty
              BMNoMeta
              False
              False
              exprArg
          TBABody <$> unifyBoundary ttDoc rigidTy rigidTm (bsDom slot) (bsCod slot) diagArg
