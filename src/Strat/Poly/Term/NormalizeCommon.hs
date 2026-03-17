{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.NormalizeCommon
  ( TermNormalizer
  , checkObjWellFormedUsing
  , checkCodeWellFormedUsing
  , normalizeObjDeepUsing
  , normalizeObjDeepWithMapperUsing
  , normalizeObjDeepWithCtxUsing
  , normalizeObjDeepWithCtxWithMapperUsing
  , normalizeCodeTermDeepWithCtxUsing
  , normalizeCodeTermDeepWithCtxWithMapperUsing
  , termToDiagramUsing
  , termToDiagramWithMapperUsing
  , diagramToTermUsing
  , validateTermDiagram
  , termExprToDiagramCheckedUsing
  , diagramToTermExprCheckedUsing
  ) where

import Control.Monad (foldM, unless)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , diagramPortObj
  , validateLiteralEdges
  , weakenDiagramTmCtxToModePrefix
  )
import Strat.Poly.ModeTheory (ModeName, meSrc, meTgt)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , ObjName(..)
  , ObjRef(..)
  , TermDiagram(..)
  , TmVar(..)
  , normalizeCodeTerm
  , normalizeObjExpr
  , objOwnerMode
  , tmVarOwner
  )
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Subst (bindHeadSubst)
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Strat.Poly.Term.NBE.Normalize
  ( validateDiagramDefEq
  )
import Strat.Poly.Term.RuleDiagram (SpliceMapper, sameModeSpliceMapper)
import Strat.Poly.TermExpr
  ( TermConvEnv
  , TermExpr
  , applyHeadSubstObj
  , diagramGraphToTermExprWith
  , mkNormalizingConvEnv
  , normalizeTermDiagramStructurally
  , structuralConvEnv
  , termExprToDiagramWith
  , validateTermGraph
  )
import Strat.Poly.TypeTheory
  ( GenArgSig(..)
  , TypeTheory(..)
  , defFragmentForMode
  , lookupGenArgSig
  )

type TermNormalizer =
  TypeTheory -> SpliceMapper -> [Obj] -> Obj -> TermDiagram -> Either Text TermDiagram

checkObjWellFormedUsing :: TermNormalizer -> TypeTheory -> Obj -> Either Text ()
checkObjWellFormedUsing normalizeTerm tt obj = do
  let owner = objOwnerMode obj
  let codeMode = modeClassifierMode (ttModes tt) owner
  checkCodeWellFormedUsing normalizeTerm tt codeMode (objCode obj)
  case objCode obj of
    CTCon ref _ -> do
      let ownerTable = M.findWithDefault S.empty owner (ttUniverseCtors tt)
      unless
        (S.member (orName ref) ownerTable)
        (Left "checkObjWellFormed: top-level constructor is not eligible for owner mode")
    _ -> Right ()

checkCodeWellFormedUsing :: TermNormalizer -> TypeTheory -> ModeName -> CodeTerm -> Either Text ()
checkCodeWellFormedUsing normalizeTerm tt codeMode code =
  case code of
    CTMeta _ -> Right ()
    CTCon ref args -> do
      unless
        (orMode ref == codeMode || isOpaqueMetaSort ref)
        (Left "checkCodeWellFormed: constructor mode does not match current code mode")
      case lookupCodeHeadParams tt codeMode (orName ref) of
        Just params -> do
          unless
            (length params == length args)
            (Left "checkCodeWellFormed: constructor arity mismatch")
          _ <- foldM checkArgBySig M.empty (zip params args)
          Right ()
        Nothing ->
          if ttStrictCtorLookup tt
            then Left "checkCodeWellFormed: unknown constructor"
            else mapM_ checkArgUnknown args
    CTLift me inner -> do
      if meTgt me == codeMode
        then checkCodeWellFormedUsing normalizeTerm tt (meSrc me) inner
        else Left "checkCodeWellFormed: lift target does not match current code mode"
  where
    checkArgBySig substAcc (param, arg) =
      case (param, arg) of
        (GP_Ty v, CAObj innerObj) -> do
          let expectedOwner = tmVarOwner v
          unless
            (objOwnerMode innerObj == expectedOwner)
            (Left "checkCodeWellFormed: type argument owner mode mismatch")
          checkObjWellFormedUsing normalizeTerm tt innerObj
          bindHeadSubst v (CAObj innerObj) substAcc
        (GP_Ty _, CATm _) ->
          Left "checkCodeWellFormed: expected type argument"
        (GP_Tm v, CATm tmArg) -> do
          let tmCtx = dTmCtx (unTerm tmArg)
          expectedSort <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx substAcc (tmvSort v)
          _ <- termToDiagramUsing normalizeTerm tt tmCtx expectedSort tmArg
          bindHeadSubst v (CATm tmArg) substAcc
        (GP_Tm _, CAObj _) ->
          Left "checkCodeWellFormed: expected term argument"

    checkArgUnknown arg =
      case arg of
        CAObj innerObj -> checkObjWellFormedUsing normalizeTerm tt innerObj
        CATm _ -> Right ()

    isOpaqueMetaSort ref =
      case orName ref of
        ObjName "__obj_meta_sort" -> True
        _ -> False

normalizeObjDeepUsing :: TermNormalizer -> TypeTheory -> Obj -> Either Text Obj
normalizeObjDeepUsing normalizeTerm tt =
  normalizeObjDeepWithCtxUsing normalizeTerm tt []

normalizeObjDeepWithMapperUsing :: TermNormalizer -> TypeTheory -> SpliceMapper -> Obj -> Either Text Obj
normalizeObjDeepWithMapperUsing normalizeTerm tt spliceMapper =
  normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper []

normalizeObjDeepWithCtxUsing :: TermNormalizer -> TypeTheory -> [Obj] -> Obj -> Either Text Obj
normalizeObjDeepWithCtxUsing normalizeTerm tt =
  normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt (sameModeSpliceMapper "defeq")

normalizeObjDeepWithCtxWithMapperUsing
  :: TermNormalizer
  -> TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> Obj
  -> Either Text Obj
normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx ty = do
  let codeMode = modeClassifierMode (ttModes tt) (objOwnerMode ty)
  code' <- normalizeCodeTermDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx codeMode (objCode ty)
  normalizeObjExpr (ttModes tt) ty { objCode = code' }

normalizeCodeTermDeepWithCtxUsing
  :: TermNormalizer
  -> TypeTheory
  -> [Obj]
  -> ModeName
  -> CodeTerm
  -> Either Text CodeTerm
normalizeCodeTermDeepWithCtxUsing normalizeTerm tt =
  normalizeCodeTermDeepWithCtxWithMapperUsing normalizeTerm tt (sameModeSpliceMapper "defeq")

normalizeCodeTermDeepWithCtxWithMapperUsing
  :: TermNormalizer
  -> TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> ModeName
  -> CodeTerm
  -> Either Text CodeTerm
normalizeCodeTermDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx codeMode code =
  case code of
    CTMeta _ -> Right code
    CTCon ref args -> do
      if orMode ref == codeMode || isOpaqueMetaSort ref
        then Right ()
        else Left "normalizeCodeTermDeepWithCtx: constructor mode does not match current code mode"
      case lookupCodeHeadParams tt codeMode (orName ref) of
        Just params ->
          if length params /= length args
            then Left "normalizeCodeTermDeepWithCtx: type constructor arity mismatch"
            else do
              (args', _) <- foldM normalizeArgBySig ([], M.empty) (zip params args)
              Right (CTCon ref args')
        Nothing ->
          if not (ttStrictCtorLookup tt)
            then
              if M.null sigTable
                then do
                  args' <- mapM normalizeUnknownArg args
                  Right (CTCon ref args')
                else
                  if null args
                    then Right code
                    else unknownCtor ref
            else
              if M.null sigTable
                then do
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
      inner' <- normalizeCodeTermDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx (meSrc me) innerCode
      normalizeCodeTerm (ttModes tt) (CTLift me inner')
  where
    normalizeArgBySig (acc, substAcc) (param, arg) =
      case (param, arg) of
        (GP_Ty v, CAObj tyArg) -> do
          tyArg' <- normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx tyArg
          subst' <- bindHeadSubst v (CAObj tyArg') substAcc
          Right (acc <> [CAObj tyArg'], subst')
        (GP_Tm v, CATm tm) -> do
          sortTy' <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx substAcc (tmvSort v)
          tm' <-
            case normalizeTerm tt spliceMapper tmCtx sortTy' tm of
              Right out -> Right out
              Left _ ->
                normalizeTermDiagramStructurally
                  tt
                  (structuralConvEnv tt)
                  (dTmCtx (unTerm tm))
                  tm
          subst' <- bindHeadSubst v (CATm tm') substAcc
          Right (acc <> [CATm tm'], subst')
        (GP_Ty _, CATm _) ->
          Left "normalizeCodeTermDeepWithCtx: expected type argument"
        (GP_Tm _, CAObj _) ->
          Left "normalizeCodeTermDeepWithCtx: expected term argument"

    normalizeUnknownArg arg =
      case arg of
        CAObj tyArg -> CAObj <$> normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx tyArg
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
      let refs = [ObjRef codeMode name | name <- M.keys sigTable]
       in if null refs
            then "(none)"
            else T.intercalate ", " (map renderRef refs)

    sigTable = M.findWithDefault M.empty codeMode (ttCtorSigs tt)

termToDiagramUsing
  :: TermNormalizer
  -> TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text Diagram
termToDiagramUsing normalizeTerm tt =
  termToDiagramWithMapperUsing normalizeTerm tt (sameModeSpliceMapper "defeq")

termToDiagramWithMapperUsing
  :: TermNormalizer
  -> TypeTheory
  -> SpliceMapper
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text Diagram
termToDiagramWithMapperUsing normalizeTerm tt spliceMapper tmCtx expectedSort (TermDiagram term0) = do
  expectedSort' <- wrap "normalize-sort" (normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx expectedSort)
  term <- wrap "widen-tmctx" (weakenDiagramTmCtxToModePrefix tmCtx term0)
  fragment <-
    case defFragmentForMode tt (objOwnerMode expectedSort') of
      Just one -> Right one
      Nothing -> Left "termToDiagram: missing definitional fragment for mode"
  wrap "validate-diagram" (validateDiagramDefEq fragment tt (checkedConvEnvWithMapperUsing normalizeTerm tt spliceMapper) tmCtx expectedSort' term)
  wrap "validate-literals" (validateLiteralEdges tt term)
  if dMode term == objOwnerMode expectedSort'
    then Right ()
    else wrapFail "mode-mismatch" "term mode differs from expected sort mode"
  wrap "check-output-sort" (ensureOutputSort normalizeTerm tt spliceMapper tmCtx expectedSort' term)
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

diagramToTermUsing
  :: TermNormalizer
  -> TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
diagramToTermUsing normalizeTerm tt tmCtx expectedSort term0 = do
  expectedSort' <- normalizeObjDeepWithCtxUsing normalizeTerm tt tmCtx expectedSort
  let term = term0 { dTmCtx = tmCtx }
  fragment <-
    case defFragmentForMode tt (objOwnerMode expectedSort') of
      Just one -> Right one
      Nothing -> Left "diagramToTerm: missing definitional fragment for mode"
  validateDiagramDefEq fragment tt (checkedConvEnvUsing normalizeTerm tt) tmCtx expectedSort' term
  validateLiteralEdges tt term
  if dMode term == objOwnerMode expectedSort'
    then Right ()
    else Left "diagramToTerm: mode mismatch"
  ensureOutputSort normalizeTerm tt (sameModeSpliceMapper "defeq") tmCtx expectedSort' term
  pure (TermDiagram term)

validateTermDiagram :: Diagram -> Either Text ()
validateTermDiagram = validateTermGraph

termExprToDiagramCheckedUsing
  :: TermNormalizer
  -> TypeTheory
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramCheckedUsing normalizeTerm tt tmCtx expectedSort tm = do
  out <- termExprToDiagramWith tt (checkedConvEnvUsing normalizeTerm tt) tmCtx expectedSort tm
  validateLiteralEdges tt (unTerm out)
  pure out

diagramToTermExprCheckedUsing
  :: TermNormalizer
  -> TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprCheckedUsing normalizeTerm tt tmCtx expectedSort tm =
  diagramGraphToTermExprCheckedUsing normalizeTerm tt tmCtx expectedSort (unTerm tm)

diagramGraphToTermExprCheckedUsing
  :: TermNormalizer
  -> TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExprCheckedUsing normalizeTerm tt tmCtx expectedSort diag = do
  expr <- diagramGraphToTermExprWith tt (checkedConvEnvUsing normalizeTerm tt) tmCtx expectedSort diag
  _ <- termExprToDiagramCheckedUsing normalizeTerm tt tmCtx expectedSort expr
  pure expr

checkedConvEnvUsing :: TermNormalizer -> TypeTheory -> TermConvEnv
checkedConvEnvUsing normalizeTerm tt =
  checkedConvEnvWithMapperUsing normalizeTerm tt (sameModeSpliceMapper "defeq")

checkedConvEnvWithMapperUsing :: TermNormalizer -> TypeTheory -> SpliceMapper -> TermConvEnv
checkedConvEnvWithMapperUsing normalizeTerm tt spliceMapper =
  mkNormalizingConvEnv
    tt
    spliceMapper
    (normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper)

ensureOutputSort :: TermNormalizer -> TypeTheory -> SpliceMapper -> [Obj] -> Obj -> Diagram -> Either Text ()
ensureOutputSort normalizeTerm tt spliceMapper tmCtx expectedSort term = do
  out <- requireSingleOut term
  outSort <-
    case diagramPortObj term out of
      Nothing -> Left "termToDiagram: missing output port type"
      Just ty -> normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx ty
  expectedSort' <- normalizeObjDeepWithCtxWithMapperUsing normalizeTerm tt spliceMapper tmCtx expectedSort
  if outSort == expectedSort'
    then Right ()
    else Left "termToDiagram: output sort mismatch"

requireSingleOut :: Diagram -> Either Text PortId
requireSingleOut term =
  case dOut term of
    [pid] -> Right pid
    _ -> Left "termToDiagram: term diagram must have exactly one output"

lookupCodeHeadParams :: TypeTheory -> ModeName -> ObjName -> Maybe [GenParam]
lookupCodeHeadParams tt codeMode name =
  case M.lookup name (M.findWithDefault M.empty codeMode (ttCtorSigs tt)) of
    Just sig -> Just (csParams sig)
    Nothing ->
      case lookupGenArgSig tt codeMode (objNameToGenName name) of
        Just sig -> Just (gasParams sig)
        Nothing -> Nothing
  where
    objNameToGenName (ObjName text) = GenName text

renderMode :: ModeName -> Text
renderMode mode =
  T.pack (show mode)

mapLeft :: (e -> f) -> Either e a -> Either f a
mapLeft f mv =
  case mv of
    Left err -> Left (f err)
    Right v -> Right v
