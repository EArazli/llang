{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjNormalize
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeObjDeep
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
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Control.Monad (unless)
import Strat.Poly.Literal (literalKind)
import Strat.Poly.Graph
  ( Diagram(..)
  , EdgePayload(..)
  , PortId
  , diagramPortObj
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , setPortLabel
  , unPortId
  , validateDiagram
  , validateLiteralEdges
  , weakenDiagramTmCtxTo
  )
import Strat.Poly.ModeTheory (ModeName, meSrc, meTgt)
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Names (GenName)
import Strat.Poly.Obj
  ( TermDiagram(..)
  , CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , ObjName(..)
  , ObjRef(..)
  , TmVar(..)
  , objOwnerMode
  , defaultMetaArgs
  , modeCtxGlobals
  , normalizeCodeTerm
  , normalizeObjExpr
  )
import Strat.Poly.TypeTheory
  ( DefFragment(..)
  , TmHeadSig(..)
  , TypeParamSig(..)
  , TypeTheory(..)
  , defFragmentForMode
  , literalKindForObj
  , termTRSForMode
  , lookupTmHeadSig
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , TermConvEnv(..)
  , termExprToDiagramWith
  , diagramGraphToTermExprWith
  , validateTermGraph
  )
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import Strat.Poly.Term.NBE.Normalize (normalizeDiagramNBE)


normalizeObjDeep :: TypeTheory -> Obj -> Either Text Obj
normalizeObjDeep tt = normalizeObjDeepWithCtx tt []

checkObjWellFormed :: TypeTheory -> Obj -> Either Text ()
checkObjWellFormed tt obj = do
  let owner = objOwnerMode obj
  let codeMode = modeClassifierMode (ttModes tt) owner
  checkCodeWellFormed tt codeMode (objCode obj)
  case objCode obj of
    CTCon ref _ -> do
      let ownerTable = M.findWithDefault S.empty owner (ttUniverseCtors tt)
      unless
        (S.member (orName ref) ownerTable)
        (Left "checkObjWellFormed: top-level constructor is not eligible for owner mode")
    _ -> Right ()

checkCodeWellFormed :: TypeTheory -> ModeName -> CodeTerm -> Either Text ()
checkCodeWellFormed tt codeMode code =
  case code of
    CTMeta _ -> Right ()
    CTCon ref args -> do
      unless
        (orMode ref == codeMode || isOpaqueMetaSort ref)
        (Left "checkCodeWellFormed: constructor mode does not match current code mode")
      case M.lookup (orName ref) sigTable of
        Just params -> do
          unless
            (length params == length args)
            (Left "checkCodeWellFormed: constructor arity mismatch")
          mapM_ checkArgBySig (zip params args)
        Nothing ->
          if ttStrictCtorLookup tt
            then Left "checkCodeWellFormed: unknown constructor"
            else mapM_ checkArgUnknown args
    CTLift me inner -> do
      if meTgt me == codeMode
        then checkCodeWellFormed tt (meSrc me) inner
        else Left "checkCodeWellFormed: lift target does not match current code mode"
  where
    sigTable = M.findWithDefault M.empty codeMode (ttCtorSigs tt)

    checkArgBySig (TPS_Ty expectedOwner, arg) =
      case arg of
        CAObj innerObj -> do
          unless
            (objOwnerMode innerObj == expectedOwner)
            (Left "checkCodeWellFormed: type argument owner mode mismatch")
          checkObjWellFormed tt innerObj
        CATm _ ->
          Left "checkCodeWellFormed: expected type argument"
    checkArgBySig (TPS_Tm _, arg) =
      case arg of
        CAObj _ ->
          Left "checkCodeWellFormed: expected term argument"
        CATm _ ->
          Right ()

    checkArgUnknown arg =
      case arg of
        CAObj innerObj -> checkObjWellFormed tt innerObj
        CATm _ -> Right ()

    isOpaqueMetaSort ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

normalizeCodeTermDeepWithCtx
  :: TypeTheory
  -> [Obj]
  -> ModeName -- code mode
  -> CodeTerm
  -> Either Text CodeTerm
normalizeCodeTermDeepWithCtx tt tmCtx codeMode code =
  case code of
    CTMeta _ -> Right code
    CTCon ref args -> do
      if orMode ref == codeMode || isOpaqueMetaSort ref
        then Right ()
        else Left "normalizeCodeTermDeepWithCtx: constructor mode does not match current code mode"
      case M.lookup (orName ref) sigTable of
        Just params ->
          if length params /= length args
            then Left "normalizeCodeTermDeepWithCtx: type constructor arity mismatch"
            else do
              args' <- mapM normalizeArgBySig (zip params args)
              Right (CTCon ref args')
        Nothing ->
          if not (ttStrictCtorLookup tt)
            then
              if M.null sigTable
                then do
                  -- modeOnlyTypeTheory intentionally omits constructor signatures; normalize structurally.
                  args' <- mapM normalizeUnknownArg args
                  Right (CTCon ref args')
                else
                  if null args
                    then Right code
                    else unknownCtor ref
            else
              if M.null sigTable
                then do
                  -- modeOnlyTypeTheory intentionally omits constructor signatures; normalize structurally.
                  args' <- mapM normalizeUnknownArg args
                  Right (CTCon ref args')
                else
                  if null args && isOpaqueNullary ref
                    then Right code
                    else unknownCtor ref
    CTLift me innerCode -> do
      if meTgt me == codeMode
        then Right ()
        else Left "normalizeCodeTermDeepWithCtx: modality target does not match current code mode"
      inner' <- normalizeCodeTermDeepWithCtx tt tmCtx (meSrc me) innerCode
      normalizeCodeTerm (ttModes tt) (CTLift me inner')
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

    renderRef ref = T.pack (show ref)
    renderModeName m = T.pack (show m)

    isOpaqueNullary ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

    isOpaqueMetaSort ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

    unknownCtor ref =
      Left
        ( "normalizeCodeTermDeepWithCtx: unknown type constructor "
            <> renderRef ref
            <> " (code mode "
            <> renderModeName codeMode
            <> "); available refs: "
            <> renderAvailableRefs
        )

    renderAvailableRefs =
      let refs = [ ObjRef codeMode name | name <- M.keys sigTable ]
       in if null refs
            then "(none)"
            else T.intercalate ", " (map renderRef refs)

    sigTable = M.findWithDefault M.empty codeMode (ttCtorSigs tt)

normalizeObjDeepWithCtx :: TypeTheory -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtx tt tmCtx ty = do
  let codeMode = modeClassifierMode (ttModes tt) (objOwnerMode ty)
  code' <- normalizeCodeTermDeepWithCtx tt tmCtx codeMode (objCode ty)
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
      wrap "validate-literals" (validateLiteralEdges tt outGraph)
      wrap "check-output-sort" (ensureOutputSort tt tmCtx expectedSort' outGraph)
      pure out
    _ -> do
      let trs = termTRSForMode tt mode
      expr0 <-
        wrap
          "diagram-to-termexpr"
          (diagramGraphToTermExprChecked tt tmCtx expectedSort' src)
      let expr = normalizeTermExpr trs expr0
      out <- wrap "termexpr-to-diagram" (termExprToDiagramChecked tt tmCtx expectedSort' expr)
      let outGraph = unTerm out
      wrap "validate-output-graph" (validateTermGraph outGraph)
      wrap "validate-literals" (validateLiteralEdges tt outGraph)
      wrap "check-output-sort" (ensureOutputSort tt tmCtx expectedSort' outGraph)
      -- Normalize output graph layout by a deterministic structural roundtrip.
      exprCanon <-
        wrap
          "roundtrip-diagram-to-termexpr"
          (diagramGraphToTermExprChecked tt tmCtx expectedSort' outGraph)
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
    Just DefFragmentNBE {} -> do
      wrap "validate-diagram" (validateDiagram term)
      wrap "validate-literals" (validateLiteralEdges tt term)
    _ -> do
      _ <- wrap "validate-term-graph" (diagramGraphToTermExprChecked tt tmCtx expectedSort' term)
      wrap "validate-literals" (validateLiteralEdges tt term)
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
    Just DefFragmentNBE {} -> validateDiagram term *> validateLiteralEdges tt term
    _ -> do
      _ <- diagramGraphToTermExprChecked tt tmCtx expectedSort' term
      validateLiteralEdges tt term
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
termExprToDiagramChecked tt tmCtx expectedSort tm = do
  out <- termExprToDiagramWith tt (checkedConvEnv tt) tmCtx expectedSort tm
  validateLiteralEdges tt (unTerm out)
  pure out

diagramToTermExprChecked
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprChecked tt tmCtx expectedSort tm =
  diagramGraphToTermExprChecked tt tmCtx expectedSort (unTerm tm)

diagramGraphToTermExprChecked
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExprChecked tt tmCtx expectedSort diag = do
  expr <- diagramGraphToTermExprWith tt (checkedConvEnv tt) tmCtx expectedSort diag
  _ <- termExprToDiagramChecked tt tmCtx expectedSort expr
  pure expr

checkedConvEnv :: TypeTheory -> TermConvEnv
checkedConvEnv tt =
  TermConvEnv
    { tcLookupSig = \mode f -> lookupTmHeadSig tt mode f
    , tcSortEq = \tmCtx tyA tyB -> do
        tyA' <- normalizeObjDeepWithCtx tt tmCtx tyA
        tyB' <- normalizeObjDeepWithCtx tt tmCtx tyB
        pure (tyA' == tyB')
    , tcNormalizeSort = normalizeObjDeepWithCtx tt
    , tcLiteralKindForSort = \tmCtx sortTy -> do
        sortTy' <- normalizeObjDeepWithCtx tt tmCtx sortTy
        pure (literalKindForObj tt sortTy')
    }

renderMode :: ModeName -> Text
renderMode mode =
  T.pack (show mode)

mapLeft :: (e -> f) -> Either e a -> Either f a
mapLeft f mv =
  case mv of
    Left err -> Left (f err)
    Right v -> Right v
