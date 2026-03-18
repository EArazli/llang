{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DefEq
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeTermDiagram
  , normalizeTermDiagramWithMapper
  , normalizeObjDeep
  , normalizeObjDeepWithMapper
  , normalizeObjDeepWithCtx
  , normalizeObjDeepWithCtxWithMapper
  , normalizeCodeTermDeepWithCtx
  , normalizeCodeTermDeepWithCtxWithMapper
  , termToDiagram
  , termToDiagramWithMapper
  , validateTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  , defEqObj
  , defEqObjWithMapper
  , defEqTermDiagram
  , defEqTermDiagramWithMapper
  , defEqRuleTermDiagram
  , defEqRuleTermDiagramWithMapper
  ) where

import Data.Text (Text)
import Strat.Poly.Obj (Obj, TermDiagram(..))
import Strat.Poly.Term.RuleDiagram (SpliceMapper, sameModeSpliceMapper)
import Strat.Poly.Term.Compat (SharedTermDiagramContext(..), sharedTermDiagramContext)
import Strat.Poly.ObjNormalize
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeTermDiagram
  , normalizeTermDiagramWithMapper
  , normalizeObjDeep
  , normalizeObjDeepWithMapper
  , normalizeObjDeepWithCtx
  , normalizeObjDeepWithCtxWithMapper
  , normalizeCodeTermDeepWithCtx
  , normalizeCodeTermDeepWithCtxWithMapper
  , termToDiagram
  , termToDiagramWithMapper
  , validateTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  )
import Strat.Poly.Term.NBE.Normalize (normalizeRuleDiagramDefEq)
import Strat.Poly.TermExpr (mkNormalizingConvEnv)
import Strat.Poly.TypeTheory (TypeTheory, defFragmentForMode)


defEqObj :: TypeTheory -> [Obj] -> Obj -> Obj -> Either Text Bool
defEqObj tt =
  defEqObjWithMapper tt (sameModeSpliceMapper "defeq")

defEqObjWithMapper :: TypeTheory -> SpliceMapper -> [Obj] -> Obj -> Obj -> Either Text Bool
defEqObjWithMapper tt spliceMapper tmCtx a b = do
  if a == b
    then Right True
    else do
      aN <- normalizeObjDeepWithCtxWithMapper tt spliceMapper tmCtx a
      bN <- normalizeObjDeepWithCtxWithMapper tt spliceMapper tmCtx b
      pure (aN == bN)

defEqTermDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> TermDiagram
  -> Either Text Bool
defEqTermDiagram tt =
  defEqTermDiagramWithMapper tt (sameModeSpliceMapper "defeq")

defEqTermDiagramWithMapper
  :: TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> TermDiagram
  -> Either Text Bool
defEqTermDiagramWithMapper tt spliceMapper tmCtx expectedSort a b = do
  aN <- normalizeTermDiagramWithMapper tt spliceMapper tmCtx expectedSort a
  bN <- normalizeTermDiagramWithMapper tt spliceMapper tmCtx expectedSort b
  pure (aN == bN)

defEqRuleTermDiagram
  :: TypeTheory
  -> [Obj]
  -> TermDiagram
  -> TermDiagram
  -> Either Text Bool
defEqRuleTermDiagram tt =
  defEqRuleTermDiagramWithMapper tt (sameModeSpliceMapper "defeq")

defEqRuleTermDiagramWithMapper
  :: TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> TermDiagram
  -> TermDiagram
  -> Either Text Bool
defEqRuleTermDiagramWithMapper tt spliceMapper tmCtx lhs rhs = do
  ctx <- sharedTermDiagramContext "defeqRuleTermDiagram" lhs rhs
  fragment <-
    case defFragmentForMode tt (stdcMode ctx) of
      Just one -> Right one
      Nothing -> Left "defeqRuleTermDiagram: missing definitional fragment for mode"
  let conv = mkNormalizingConvEnv tt spliceMapper (normalizeObjDeepWithCtxWithMapper tt spliceMapper)
  lhsN <- normalizeRuleDiagramDefEq fragment tt conv tmCtx (stdcBoundarySorts ctx) (stdcExpectedSort ctx) (unTerm lhs)
  rhsN <- normalizeRuleDiagramDefEq fragment tt conv tmCtx (stdcBoundarySorts ctx) (stdcExpectedSort ctx) (unTerm rhs)
  pure (lhsN == rhsN)
