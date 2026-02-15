{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeNormalize
  ( normalizeTypeDeep
  , normalizeTypeDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  , diagramToTerm
  , validateTermDiagram
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , diagramPortType
  )
import Strat.Poly.ModeTheory (ModeName, composeMod, normalizeModExpr, meSrc, mePath)
import Strat.Poly.TypeExpr
  ( TermDiagram(..)
  , TypeArg(..)
  , TypeExpr(..)
  , typeMode
  )
import Strat.Poly.TypeTheory
  ( TypeParamSig(..)
  , TypeTheory(..)
  )
import Strat.Poly.TermExpr
  ( diagramGraphToTermExprUnchecked
  , termExprToDiagramUnchecked
  , validateTermGraph
  )
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import Strat.Poly.Term.RewriteCompile (compileTermRules)
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)


normalizeTypeDeep :: TypeTheory -> TypeExpr -> Either Text TypeExpr
normalizeTypeDeep tt = normalizeTypeDeepWithCtx tt []

normalizeTypeDeepWithCtx :: TypeTheory -> [TypeExpr] -> TypeExpr -> Either Text TypeExpr
normalizeTypeDeepWithCtx tt tmCtx ty = do
  ty' <- go ty
  normalizeTypeExpr0 ty'
  where
    go expr =
      case expr of
        TVar _ -> Right expr
        TMod me inner -> TMod me <$> go inner
        TCon ref args ->
          case M.lookup ref (ttTypeParams tt) of
            Just params ->
              if length params /= length args
                then Left "normalizeTypeDeep: type constructor arity mismatch"
                else TCon ref <$> mapM normalizeArg (zip params args)
            Nothing ->
              if null args
                then Right (TCon ref [])
                else Left "normalizeTypeDeep: unknown type constructor"

    normalizeArg (TPS_Ty _, TAType tyArg) = TAType <$> go tyArg
    normalizeArg (TPS_Tm sortTy, TATm tm) = do
      sortTy' <- go sortTy
      tm' <- normalizeTermDiagram tt tmCtx sortTy' tm
      Right (TATm tm')
    normalizeArg (TPS_Ty _, TATm _) =
      Left "normalizeTypeDeep: expected type argument"
    normalizeArg (TPS_Tm _, TAType _) =
      Left "normalizeTypeDeep: expected term argument"

    normalizeTypeExpr0 expr =
      case expr of
        TVar _ -> Right expr
        TCon ref args -> do
          args' <- mapM normalizeArg0 args
          Right (TCon ref args')
        TMod me inner0 -> do
          inner <- normalizeTypeExpr0 inner0
          (meComposed, innerBase) <-
            case inner of
              TMod me2 inner2 -> do
                me' <- composeMod0 me2 me
                Right (me', inner2)
              _ -> Right (me, inner)
          if typeMode innerBase /= meSrc meComposed
            then Left "normalizeTypeExpr: modality source does not match inner type mode"
            else do
              let meNorm = normalizeModExpr0 meComposed
              if null (mePath meNorm)
                then Right innerBase
                else Right (TMod meNorm innerBase)

    normalizeArg0 arg =
      case arg of
        TAType innerTy -> TAType <$> normalizeTypeExpr0 innerTy
        TATm tm -> Right (TATm tm)

    composeMod0 = composeMod (ttModes tt)
    normalizeModExpr0 = normalizeModExpr (ttModes tt)

normalizeTermDiagram
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagram tt tmCtx expectedSort term = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  src <- termToDiagram tt tmCtx expectedSort' term
  trs <- termTRSForMode tt (typeMode expectedSort')
  expr0 <- diagramGraphToTermExprUnchecked src
  let expr = normalizeTermExpr trs expr0
  out <- termExprToDiagramUnchecked tt tmCtx expectedSort' expr
  let outGraph = unTerm out
  validateTermGraph outGraph
  ensureOutputSort tt tmCtx expectedSort' outGraph
  -- Normalize output graph layout by a deterministic structural roundtrip.
  exprCanon <- diagramGraphToTermExprUnchecked outGraph
  termExprToDiagramUnchecked tt tmCtx expectedSort' exprCanon

termToDiagram
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text Diagram
termToDiagram tt tmCtx expectedSort (TermDiagram term0) = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  let term = term0 { dTmCtx = tmCtx }
  validateTermGraph term
  if dMode term == typeMode expectedSort'
    then Right ()
    else Left "termToDiagram: mode mismatch"
  ensureOutputSort tt tmCtx expectedSort' term
  pure term

diagramToTerm
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> Diagram
  -> Either Text TermDiagram
diagramToTerm tt tmCtx expectedSort term0 = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  let term = term0 { dTmCtx = tmCtx }
  validateTermGraph term
  if dMode term == typeMode expectedSort'
    then Right ()
    else Left "diagramToTerm: mode mismatch"
  ensureOutputSort tt tmCtx expectedSort' term
  pure (TermDiagram term)

validateTermDiagram :: Diagram -> Either Text ()
validateTermDiagram = validateTermGraph

ensureOutputSort :: TypeTheory -> [TypeExpr] -> TypeExpr -> Diagram -> Either Text ()
ensureOutputSort tt tmCtx expectedSort term = do
  out <- requireSingleOut term
  outSort <-
    case diagramPortType term out of
      Nothing -> Left "termToDiagram: missing output port type"
      Just ty -> normalizeTypeDeepWithCtx tt tmCtx ty
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
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
  case M.lookup mode (ttTmRules tt) of
    Nothing -> Right (mkTRS mode [])
    Just _ -> compileTermRules tt mode
