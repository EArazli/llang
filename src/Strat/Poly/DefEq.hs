{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DefEq
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeTermDiagram
  , normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeCodeTermDeepWithCtx
  , termToDiagram
  , validateTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  , defEqObj
  , defEqTermDiagram
  ) where

import Data.Text (Text)
import Strat.Poly.Obj (Obj, TermDiagram)
import Strat.Poly.ObjNormalize
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeTermDiagram
  , normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeCodeTermDeepWithCtx
  , termToDiagram
  , validateTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  )
import Strat.Poly.TypeTheory (TypeTheory)


defEqObj :: TypeTheory -> [Obj] -> Obj -> Obj -> Either Text Bool
defEqObj tt tmCtx a b = do
  aN <- normalizeObjDeepWithCtx tt tmCtx a
  bN <- normalizeObjDeepWithCtx tt tmCtx b
  pure (aN == bN)

defEqTermDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> TermDiagram
  -> Either Text Bool
defEqTermDiagram tt tmCtx expectedSort a b = do
  aN <- normalizeTermDiagram tt tmCtx expectedSort a
  bN <- normalizeTermDiagram tt tmCtx expectedSort b
  pure (aN == bN)
