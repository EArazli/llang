{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjNormalize
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeObjDeep
  , normalizeObjDeepWithMapper
  , normalizeObjDeepWithCtx
  , normalizeObjDeepWithCtxWithMapper
  , normalizeCodeTermDeepWithCtx
  , normalizeCodeTermDeepWithCtxWithMapper
  , normalizeTermDiagram
  , normalizeTermDiagramWithMapper
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  , termToDiagram
  , termToDiagramWithMapper
  , diagramToTerm
  , validateTermDiagram
  ) where

import Data.Text (Text)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.Graph (Diagram, dMode)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (CodeTerm, Obj, TermDiagram)
import Strat.Poly.Rewrite (rewriteOnceRawWithMapper, rulesForMode)
import qualified Strat.Poly.Term.DefEqCore as Core
import qualified Strat.Poly.Term.NormalizeCommon as Common
import Strat.Poly.Term.NBE.Normalize (normalizeDiagramDefEqWithStep)
import Strat.Poly.Term.RuleDiagram (SpliceMapper, sameModeSpliceMapper)
import Strat.Poly.TermExpr (TermExpr)
import Strat.Poly.TypeTheory (TypeTheory)


checkObjWellFormed :: TypeTheory -> Obj -> Either Text ()
checkObjWellFormed tt =
  Common.checkObjWellFormedUsing normalizeTermDiagramWithMapper tt

checkCodeWellFormed :: TypeTheory -> ModeName -> CodeTerm -> Either Text ()
checkCodeWellFormed tt =
  Common.checkCodeWellFormedUsing normalizeTermDiagramWithMapper tt

normalizeObjDeep :: TypeTheory -> Obj -> Either Text Obj
normalizeObjDeep tt =
  Common.normalizeObjDeepUsing normalizeTermDiagramWithMapper tt

normalizeObjDeepWithMapper :: TypeTheory -> SpliceMapper -> Obj -> Either Text Obj
normalizeObjDeepWithMapper tt =
  Common.normalizeObjDeepWithMapperUsing normalizeTermDiagramWithMapper tt

normalizeObjDeepWithCtx :: TypeTheory -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtx tt =
  Common.normalizeObjDeepWithCtxUsing normalizeTermDiagramWithMapper tt

normalizeObjDeepWithCtxWithMapper :: TypeTheory -> SpliceMapper -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtxWithMapper tt =
  Common.normalizeObjDeepWithCtxWithMapperUsing normalizeTermDiagramWithMapper tt

normalizeCodeTermDeepWithCtx
  :: TypeTheory
  -> [Obj]
  -> ModeName
  -> CodeTerm
  -> Either Text CodeTerm
normalizeCodeTermDeepWithCtx tt =
  Common.normalizeCodeTermDeepWithCtxUsing normalizeTermDiagramWithMapper tt

normalizeCodeTermDeepWithCtxWithMapper
  :: TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> ModeName
  -> CodeTerm
  -> Either Text CodeTerm
normalizeCodeTermDeepWithCtxWithMapper tt =
  Common.normalizeCodeTermDeepWithCtxWithMapperUsing normalizeTermDiagramWithMapper tt

termExprToDiagramChecked
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramChecked tt =
  Common.termExprToDiagramCheckedUsing normalizeTermDiagramWithMapper tt

diagramToTermExprChecked
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprChecked tt =
  Common.diagramToTermExprCheckedUsing normalizeTermDiagramWithMapper tt

termToDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text Diagram
termToDiagram tt =
  Common.termToDiagramUsing normalizeTermDiagramWithMapper tt

termToDiagramWithMapper
  :: TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text Diagram
termToDiagramWithMapper tt =
  Common.termToDiagramWithMapperUsing normalizeTermDiagramWithMapper tt

diagramToTerm
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
diagramToTerm tt =
  Common.diagramToTermUsing normalizeTermDiagramWithMapper tt

validateTermDiagram :: Diagram -> Either Text ()
validateTermDiagram =
  Common.validateTermDiagram

normalizeTermDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagram tt =
  normalizeTermDiagramWithMapper tt (sameModeSpliceMapper "defeq")

normalizeTermDiagramWithMapper
  :: TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagramWithMapper tt spliceMapper tmCtx expectedSort term =
  Core.normalizeTermDiagramWithMapperUsing normalizeRound tt spliceMapper tmCtx expectedSort term
  where
    -- Chosen long-term boundary: public defeq is one normalization path, but
    -- structural computational rules still act as a diagram-level shell around
    -- the term semantic core rather than as first-class NbE semantic values.
    normalizeObjTopWithMapper =
      Common.normalizeObjDeepWithCtxWithMapperUsing normalizeTermDiagramWithMapper tt spliceMapper

    objEq tmCtx' a b = do
      aN <- normalizeObjTopWithMapper tmCtx' a
      bN <- normalizeObjTopWithMapper tmCtx' b
      pure (aN == bN)

    structuralStep current =
      let structuralRules = rulesForMode UseOnlyComputationalLR tt (dMode current)
       in if null structuralRules
            then Right Nothing
            else rewriteOnceRawWithMapper objEq tt spliceMapper structuralRules current

    normalizeRound fragment tt' conv tmCtx' expectedSort' src =
      normalizeDiagramDefEqWithStep fragment tt' conv tmCtx' expectedSort' structuralStep src
