{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjNormalize
  ( normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  , termToDiagram
  , diagramToTerm
  , validateTermDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , diagramPortObj
  , weakenDiagramTmCtxTo
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj
  ( TermDiagram(..)
  , ObjArg(..)
  , Obj(..)
  , objMode
  , normalizeObjExpr
  )
import Strat.Poly.TypeTheory
  ( TypeParamSig(..)
  , TypeTheory(..)
  , lookupTmFunSig
  )
import Strat.Poly.TermExpr
  ( TermExpr
  , TermConvEnv(..)
  , diagramToTermExprWith
  , diagramGraphToTermExprUnchecked
  , termExprToDiagramWith
  , validateTermGraph
  )
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)


normalizeObjDeep :: TypeTheory -> Obj -> Either Text Obj
normalizeObjDeep tt = normalizeObjDeepWithCtx tt []

normalizeObjDeepWithCtx :: TypeTheory -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtx tt tmCtx ty = do
  ty' <- go ty
  normalizeObjExpr (ttModes tt) ty'
  where
    go expr =
      case expr of
        OVar _ -> Right expr
        OMod me inner -> OMod me <$> go inner
        OCon ref args ->
          case M.lookup ref (ttObjParams tt) of
            Just params ->
              if length params /= length args
                then Left "normalizeObjDeep: type constructor arity mismatch"
                else OCon ref <$> mapM normalizeArg (zip params args)
            Nothing ->
              if null args
                then Right (OCon ref [])
                else Left "normalizeObjDeep: unknown type constructor"

    normalizeArg (TPS_Ty _, OAObj tyArg) = OAObj <$> go tyArg
    normalizeArg (TPS_Tm sortTy, OATm tm) = do
      sortTy' <- go sortTy
      tm' <- normalizeTermDiagram tt tmCtx sortTy' tm
      Right (OATm tm')
    normalizeArg (TPS_Ty _, OATm _) =
      Left "normalizeObjDeep: expected type argument"
    normalizeArg (TPS_Tm _, OAObj _) =
      Left "normalizeObjDeep: expected term argument"

normalizeTermDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagram tt tmCtx expectedSort term = do
  expectedSort' <- wrap "normalize-sort" (normalizeObjDeepWithCtx tt tmCtx expectedSort)
  src <- wrap "term-to-diagram" (termToDiagram tt tmCtx expectedSort' term)
  trs <- wrap "trs-lookup" (termTRSForMode tt (objMode expectedSort'))
  expr0 <- wrap "diagram-to-termexpr" (diagramGraphToTermExprUnchecked src)
  let expr = normalizeTermExpr trs expr0
  out <- wrap "termexpr-to-diagram" (termExprToDiagramChecked tt tmCtx expectedSort' expr)
  let outGraph = unTerm out
  wrap "validate-output-graph" (validateTermGraph outGraph)
  wrap "check-output-sort" (ensureOutputSort tt tmCtx expectedSort' outGraph)
  -- Normalize output graph layout by a deterministic structural roundtrip.
  exprCanon <- wrap "roundtrip-diagram-to-termexpr" (diagramGraphToTermExprUnchecked outGraph)
  wrap "roundtrip-termexpr-to-diagram" (termExprToDiagramChecked tt tmCtx expectedSort' exprCanon)
  where
    wrap stage =
      mapLeft
        ( \err ->
            "normalizeTermDiagram[mode="
              <> renderMode (objMode expectedSort)
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
termToDiagram tt tmCtx expectedSort (TermDiagram term0) = do
  expectedSort' <- wrap "normalize-sort" (normalizeObjDeepWithCtx tt tmCtx expectedSort)
  term <- wrap "weaken-tmctx" (weakenDiagramTmCtxTo tmCtx term0)
  wrap "validate-term-graph" (validateTermGraph term)
  if dMode term == objMode expectedSort'
    then Right ()
    else wrapFail "mode-mismatch" "term mode differs from expected sort mode"
  wrap "check-output-sort" (ensureOutputSort tt tmCtx expectedSort' term)
  pure term
  where
    wrap stage =
      mapLeft
        ( \err ->
            "termToDiagram[mode="
              <> renderMode (objMode expectedSort)
              <> ", expectedSort="
              <> T.pack (show expectedSort)
              <> ", tmCtxSize="
              <> T.pack (show (length tmCtx))
              <> ", inArity="
              <> T.pack (show (length (dIn term0)))
              <> ", outArity="
              <> T.pack (show (length (dOut term0)))
              <> ", stage="
              <> stage
              <> "]: "
              <> err
        )
    wrapFail stage msg =
      Left
        ( "termToDiagram[mode="
            <> renderMode (objMode expectedSort)
            <> ", expectedSort="
            <> T.pack (show expectedSort)
            <> ", tmCtxSize="
            <> T.pack (show (length tmCtx))
            <> ", inArity="
            <> T.pack (show (length (dIn term0)))
            <> ", outArity="
            <> T.pack (show (length (dOut term0)))
            <> ", stage="
            <> stage
            <> "]: "
            <> msg
        )

diagramToTerm
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
diagramToTerm tt tmCtx expectedSort term0 = do
  expectedSort' <- normalizeObjDeepWithCtx tt tmCtx expectedSort
  let term = term0 { dTmCtx = tmCtx }
  validateTermGraph term
  if dMode term == objMode expectedSort'
    then Right ()
    else Left "diagramToTerm: mode mismatch"
  ensureOutputSort tt tmCtx expectedSort' term
  pure (TermDiagram term)

validateTermDiagram :: Diagram -> Either Text ()
validateTermDiagram = validateTermGraph

ensureOutputSort :: TypeTheory -> [Obj] -> Obj -> Diagram -> Either Text ()
ensureOutputSort tt tmCtx expectedSort term = do
  out <- requireSingleOut term
  outSort <-
    case diagramPortObj term out of
      Nothing -> Left "termToDiagram: missing output port type"
      Just ty -> normalizeObjDeepWithCtx tt tmCtx ty
  expectedSort' <- normalizeObjDeepWithCtx tt tmCtx expectedSort
  if outSort == expectedSort'
    then Right ()
    else Left "termToDiagram: output sort mismatch"

requireSingleOut :: Diagram -> Either Text PortId
requireSingleOut term =
  case dOut term of
    [pid] -> Right pid
    _ -> Left "termToDiagram: term diagram must have exactly one output"

termTRSForMode :: TypeTheory -> ModeName -> Either Text TRS
termTRSForMode tt mode =
  case M.lookup mode (ttTmTRS tt) of
    Nothing -> Right (mkTRS mode [])
    Just trs -> Right trs

termExprToDiagramChecked
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramChecked tt tmCtx expectedSort tm =
  termExprToDiagramWith (checkedConvEnv tt) tmCtx expectedSort tm

diagramToTermExprChecked
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprChecked tt tmCtx expectedSort tm =
  diagramToTermExprWith (checkedConvEnv tt) tmCtx expectedSort tm

checkedConvEnv :: TypeTheory -> TermConvEnv
checkedConvEnv tt =
  TermConvEnv
    { tcLookupSig = \mode f -> lookupTmFunSig tt mode f
    , tcSortEq = \tmCtx tyA tyB -> do
        tyA' <- normalizeObjDeepWithCtx tt tmCtx tyA
        tyB' <- normalizeObjDeepWithCtx tt tmCtx tyB
        pure (tyA' == tyB')
    }

renderMode :: ModeName -> Text
renderMode mode =
  T.pack (show mode)

mapLeft :: (e -> f) -> Either e a -> Either f a
mapLeft f mv =
  case mv of
    Left err -> Left (f err)
    Right v -> Right v
