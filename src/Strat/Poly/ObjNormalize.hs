{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjNormalize
  ( normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeCodeTermDeepWithCtx
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
  , validateDiagram
  , weakenDiagramTmCtxTo
  )
import Strat.Poly.ModeTheory (ModeName, meSrc, meTgt)
import Strat.Poly.ObjClassifier (modeUniverseObj, modeClassifierMode)
import Strat.Poly.Obj
  ( TermDiagram(..)
  , CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , ObjName(..)
  , ObjRef(..)
  , objOwnerMode
  , normalizeObjExpr
  )
import Strat.Poly.TypeTheory
  ( DefFragment(..)
  , TypeParamSig(..)
  , TypeTheory(..)
  , defFragmentForMode
  , termTRSForMode
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
import Strat.Poly.Term.NBE.Normalize (normalizeDiagramNBE)


normalizeObjDeep :: TypeTheory -> Obj -> Either Text Obj
normalizeObjDeep tt = normalizeObjDeepWithCtx tt []

normalizeCodeTermDeepWithCtx
  :: TypeTheory
  -> [Obj]
  -> ModeName
  -> CodeTerm
  -> Either Text CodeTerm
normalizeCodeTermDeepWithCtx tt tmCtx owner code =
  case code of
    CTMeta _ -> Right code
    CTCon ref args ->
      case M.lookup ref (ttObjParams tt) of
        Just params ->
          if length params /= length args
            then Left "normalizeCodeTermDeepWithCtx: type constructor arity mismatch"
            else do
              args' <- mapM normalizeArgBySig (zip params args)
              Right (CTCon ref args')
        Nothing ->
          if not (ttStrictCtorLookup tt)
            then
              if M.null (ttObjParams tt)
                then do
                  -- modeOnlyTypeTheory intentionally omits constructor signatures; normalize structurally.
                  args' <- mapM normalizeUnknownArg args
                  Right (CTCon ref args')
                else
                  if null args
                    then Right code
                    else unknownCtor ref
            else
              if M.null (ttObjParams tt) || not ownerRequiresCtorLookup
                then do
                  -- modeOnlyTypeTheory intentionally omits constructor signatures; normalize structurally.
                  args' <- mapM normalizeUnknownArg args
                  Right (CTCon ref args')
                else
                  if null args && isOpaqueNullary ref
                    then Right code
                    else unknownCtor ref
    CTMod me innerCode -> do
      if meTgt me /= owner
        then Left "normalizeCodeTermDeepWithCtx: modality target does not match object owner mode"
        else Right ()
      inner' <- normalizeCodeTermDeepWithCtx tt tmCtx (meSrc me) innerCode
      merged <- normalizeObjExpr (ttModes tt) Obj { objOwnerMode = owner, objCode = CTMod me inner' }
      pure (objCode merged)
    CTLift me innerCode -> do
      if meTgt me /= modeClassifierMode (ttModes tt) owner
        then Left "normalizeCodeTermDeepWithCtx: CTLift requires lift target == classifier(owner mode)"
        else Right ()
      inner' <- normalizeCodeTermDeepWithCtx tt tmCtx (meSrc me) innerCode
      merged <- normalizeObjExpr (ttModes tt) Obj { objOwnerMode = owner, objCode = CTLift me inner' }
      pure (objCode merged)
  where
    normalizeArgBySig (TPS_Ty _, CAObj tyArg) =
      CAObj <$> normalizeObjDeepWithCtx tt tmCtx tyArg
    normalizeArgBySig (TPS_Tm sortTy, CATm tm) = do
      sortTy' <- normalizeObjDeepWithCtx tt tmCtx sortTy
      tm' <- normalizeTermDiagram tt tmCtx sortTy' tm
      Right (CATm tm')
    normalizeArgBySig (TPS_Ty _, CATm _) =
      Left "normalizeCodeTermDeepWithCtx: expected type argument"
    normalizeArgBySig (TPS_Tm _, CAObj _) =
      Left "normalizeCodeTermDeepWithCtx: expected term argument"

    normalizeUnknownArg arg =
      case arg of
        CAObj tyArg -> CAObj <$> normalizeObjDeepWithCtx tt tmCtx tyArg
        CATm tm -> Right (CATm tm)

    ownerRequiresCtorLookup =
      case modeUniverseObj (ttModes tt) owner of
        Just universe ->
          case objCode universe of
            CTMeta _ -> False
            _ -> True
        Nothing -> False

    renderRef ref = T.pack (show ref)
    renderModeName m = T.pack (show m)

    isOpaqueNullary ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

    unknownCtor ref =
      Left
        ( "normalizeCodeTermDeepWithCtx: unknown type constructor "
            <> renderRef ref
            <> " (owner mode "
            <> renderModeName owner
            <> "); available refs: "
            <> renderAvailableRefs
        )

    renderAvailableRefs =
      let refs = M.keys (ttObjParams tt)
       in if null refs
            then "(none)"
            else T.intercalate ", " (map renderRef refs)

normalizeObjDeepWithCtx :: TypeTheory -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtx tt tmCtx ty = do
  code' <- normalizeCodeTermDeepWithCtx tt tmCtx (objOwnerMode ty) (objCode ty)
  normalizeObjExpr (ttModes tt) ty { objCode = code' }

normalizeTermDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagram tt tmCtx expectedSort term = do
  expectedSort' <- wrap "normalize-sort" (normalizeObjDeepWithCtx tt tmCtx expectedSort)
  src <- wrap "term-to-diagram" (termToDiagram tt tmCtx expectedSort' term)
  let mode = objOwnerMode expectedSort'
  case defFragmentForMode tt mode of
    Just DefFragmentNBE { dfNBE = cfg } -> do
      out <- wrap "nbe-normalize" (normalizeDiagramNBE cfg tt nbeSortEq tmCtx expectedSort' src)
      let outGraph = unTerm out
      wrap "validate-output-graph" (validateDiagram outGraph)
      wrap "check-output-sort" (ensureOutputSort tt tmCtx expectedSort' outGraph)
      pure out
    _ -> do
      let trs = termTRSForMode tt mode
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
    nbeSortEq sortCtx tyA tyB = do
      tyA' <- normalizeObjDeepWithCtx tt sortCtx tyA
      tyB' <- normalizeObjDeepWithCtx tt sortCtx tyB
      pure (tyA' == tyB')

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
termToDiagram tt tmCtx expectedSort (TermDiagram term0) = do
  expectedSort' <- wrap "normalize-sort" (normalizeObjDeepWithCtx tt tmCtx expectedSort)
  term <- wrap "weaken-tmctx" (weakenDiagramTmCtxTo tmCtx term0)
  case defFragmentForMode tt (objOwnerMode expectedSort') of
    Just DefFragmentNBE {} -> wrap "validate-diagram" (validateDiagram term)
    _ -> wrap "validate-term-graph" (validateTermGraph term)
  if dMode term == objOwnerMode expectedSort'
    then Right ()
    else wrapFail "mode-mismatch" "term mode differs from expected sort mode"
  wrap "check-output-sort" (ensureOutputSort tt tmCtx expectedSort' term)
  pure term
  where
    wrap stage =
      mapLeft
        ( \err ->
            "termToDiagram[mode="
              <> renderMode (objOwnerMode expectedSort)
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
            <> renderMode (objOwnerMode expectedSort)
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
  case defFragmentForMode tt (objOwnerMode expectedSort') of
    Just DefFragmentNBE {} -> validateDiagram term
    _ -> validateTermGraph term
  if dMode term == objOwnerMode expectedSort'
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
