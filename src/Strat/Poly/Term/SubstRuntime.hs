{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.SubstRuntime
  ( runtimeTermSubstOps
  , applySubstObj
  , applySubstTm
  , applySubstTmInCtx
  , applySubstDiagram
  , applySubstCtx
  , normalizeSubst
  , composeSubst
  ) where

import Data.Text (Text)
import Strat.Poly.Graph (Diagram)
import Strat.Poly.Obj (Context, Obj, TermDiagram)
import Strat.Poly.Subst
  ( Subst
  , TermSubstOps
  , applySubstCtxWith
  , applySubstDiagramWith
  , applySubstObjWith
  , applySubstTmInCtxWith
  , applySubstTmWith
  , composeSubstWith
  , normalizeSubstWith
  )
import Strat.Poly.Term.DefEqCore
  ( normalizeObjDeepWithCtx
  , normalizeTermDiagram
  )
import Strat.Poly.TermExpr
  ( mkTermSubstOps
  , structuralConvEnv
  )
import Strat.Poly.TypeTheory (TypeTheory)

runtimeTermSubstOps :: TypeTheory -> TermSubstOps
runtimeTermSubstOps tt =
  mkTermSubstOps
    tt
    (structuralConvEnv tt)
    (normalizeObjDeepWithCtx tt)
    (normalizeTermDiagram tt)

applySubstObj :: TypeTheory -> Subst -> Obj -> Either Text Obj
applySubstObj tt =
  applySubstObjWith (runtimeTermSubstOps tt) tt

applySubstTm :: TypeTheory -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTm tt =
  applySubstTmWith (runtimeTermSubstOps tt) tt

applySubstTmInCtx :: TypeTheory -> [Obj] -> Subst -> Obj -> TermDiagram -> Either Text TermDiagram
applySubstTmInCtx tt =
  applySubstTmInCtxWith (runtimeTermSubstOps tt) tt

applySubstDiagram :: TypeTheory -> Subst -> Diagram -> Either Text Diagram
applySubstDiagram tt =
  applySubstDiagramWith (runtimeTermSubstOps tt) tt

applySubstCtx :: TypeTheory -> Subst -> Context -> Either Text Context
applySubstCtx tt =
  applySubstCtxWith (runtimeTermSubstOps tt) tt

normalizeSubst :: TypeTheory -> Subst -> Either Text Subst
normalizeSubst tt =
  normalizeSubstWith (runtimeTermSubstOps tt) tt

composeSubst :: TypeTheory -> Subst -> Subst -> Either Text Subst
composeSubst tt =
  composeSubstWith (runtimeTermSubstOps tt) tt
