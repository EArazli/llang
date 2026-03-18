{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.DefEqCore
  ( normalizeObjDeepWithCtx
  , normalizeObjDeepWithCtxWithMapper
  , normalizeTermDiagram
  , normalizeTermDiagramWithMapper
  , normalizeTermDiagramWithMapperUsing
  , termToDiagram
  , termToDiagramWithMapper
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Graph
  ( Diagram(..)
  , validateLiteralEdges
  , weakenDiagramTmCtxToModePrefix
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (Obj, TermDiagram(..), objOwnerMode)
import qualified Strat.Poly.Term.NormalizeCommon as Common
import Strat.Poly.Term.NBE.Normalize (normalizeDiagramDefEq)
import Strat.Poly.Term.RuleDiagram (SpliceMapper, sameModeSpliceMapper)
import Strat.Poly.TermExpr (TermConvEnv, mkNormalizingConvEnv)
import Strat.Poly.TypeTheory (DefFragment, TypeTheory, defFragmentForMode)

normalizeObjDeepWithCtx :: TypeTheory -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtx tt =
  Common.normalizeObjDeepWithCtxUsing normalizeTermDiagramWithMapper tt

normalizeObjDeepWithCtxWithMapper :: TypeTheory -> SpliceMapper -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtxWithMapper tt =
  Common.normalizeObjDeepWithCtxWithMapperUsing normalizeTermDiagramWithMapper tt

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
normalizeTermDiagramWithMapper tt spliceMapper tmCtx expectedSort term = do
  normalizeTermDiagramWithMapperUsing normalizeDiagramDefEq tt spliceMapper tmCtx expectedSort term

normalizeTermDiagramWithMapperUsing
  :: (DefFragment -> TypeTheory -> TermConvEnv -> [Obj] -> Obj -> Diagram -> Either Text TermDiagram)
  -> TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagramWithMapperUsing normalizeRound tt spliceMapper tmCtx expectedSort term = do
  expectedSort' <- wrap "normalize-sort" (normalizeObjDeepWithCtxWithMapper tt spliceMapper tmCtx expectedSort)
  src <- wrap "widen-tmctx" (weakenDiagramTmCtxToModePrefix tmCtx (unTerm term))
  let mode = objOwnerMode expectedSort'
  fragment <-
    case defFragmentForMode tt mode of
      Just one -> Right one
      Nothing -> Left "normalizeTermDiagram: missing definitional fragment for mode"
  let conv = mkNormalizingConvEnv tt spliceMapper (normalizeObjDeepWithCtxWithMapper tt spliceMapper)
  wrap "validate-literals" (validateLiteralEdges tt src)
  out <- wrap "defeq-round" (normalizeRound fragment tt conv tmCtx expectedSort' src)
  let outGraph = unTerm out
  wrap "validate-literals" (validateLiteralEdges tt outGraph)
  pure out
  where
    wrap stage =
      mapLeft
        ( \err ->
            "normalizeTermDiagram[mode="
              <> renderMode (objOwnerMode expectedSort)
              <> ", expectedSort="
              <> T.pack (show expectedSort)
              <> ", tmCtxSize="
              <> T.pack (show (length tmCtx))
              <> ", inArity="
              <> T.pack (show (length (dIn (unTerm term))))
              <> ", outArity="
              <> T.pack (show (length (dOut (unTerm term))))
              <> ", stage="
              <> stage
              <> "]: "
              <> err
        )

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

renderMode :: ModeName -> Text
renderMode = T.pack . show

mapLeft :: (e -> e') -> Either e a -> Either e' a
mapLeft f ea =
  case ea of
    Left err -> Left (f err)
    Right a -> Right a
