{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.TermExpr
  ( TermExpr(..)
  , TermBinderArg(..)
  , pattern TMGen
  , TermConvEnv(..)
  , mkNormalizingConvEnv
  , ResolvedHeadArgs(..)
  , termExprToDiagramWith
  , termExprToDiagram
  , diagramToTermExprWith
  , diagramToTermExpr
  , diagramGraphToTermExprWith
  , diagramGraphToTermExpr
  , diagramGraphToRuleExprWith
  , diagramGraphToRuleExpr
  , structuralConvEnv
  , resolveHeadArgsExpr
  , resolvedHeadFlatArgs
  , mkTermSubstOps
  , termSubstOps
  , applyHeadSubstObj
  , instantiateHostBoundObj
  , instantiateHostBoundCtx
  , instantiateMetaBody
  , normalizeCtxStructurally
  , normalizeCtxStructurallyWithPrefix
  , normalizeDiagramStructurally
  , normalizeTermDiagramStructurally
  , requireHeadSig
  , validateTermGraph
  , validateRuleGraph
  , validateDefEqGraph
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  ) where

import Control.Monad (foldM, forM, when)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Alpha (freshenTmHeadSigAgainstWithMaps)
import Strat.Poly.DiagramBuild
  ( allocPorts
  , emitGenNode
  , finalizeSingleOutputDiagram
  , emitLiteralNode
  , emitMetaNode
  )
import Strat.Poly.Graph
  ( BinderArg(..)
  , Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , canonDiagramRaw
  , diagramPortObj
  , emptyDiagram
  , validateDiagram
  , weakenDiagramTmCtxToModePrefix
  )
import Strat.Poly.Literal (LiteralKind, literalKind)
import Strat.Poly.ModeTheory (ModeName, meSrc)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , TermDiagram(..)
  , TmVar(..)
  , freeVarsObj
  , modeCtxGlobals
  , normalizeObjExpr
  , objOwnerMode
  )
import Strat.Poly.Subst (TermSubstOps(..), applySubstObjWith, bindHeadSubst, mkSubst)
import Strat.Poly.Tele (GenParam(..))
import Strat.Poly.Term.AST
  ( TermHeadArg(..)
  , TermBinderArg(..)
  , TermExpr(..)
  , boundGlobalsExpr
  , freeTmVarsExpr
  , isPureMetaExpr
  , maxTmScopeExpr
  , pattern TMGen
  )
import Strat.Poly.Term.GraphRead (TermPortReader(..), readTermOutput)
import Strat.Poly.Term.RuleDiagram (SpliceMapper, sameModeSpliceMapper)
import Strat.Poly.Term.Scope
  ( hostBoundGlobalsExpr
  , hostMaxTmScopeExpr
  , instantiateMetaBodyWith
  )
import Strat.Poly.TypeTheory
  ( BinderSig(..)
  , TmHeadSig(..)
  , TypeTheory(..)
  , literalKindForObj
  , lookupTmHeadSig
  )

data TermGraphPolicy
  = StrictTermGraph
  | RuleTermGraph
  | DefEqTermGraph

data TermConvEnv = TermConvEnv
  { tcLookupSig :: ModeName -> GenName -> Maybe TmHeadSig
  , tcSortEq :: [Obj] -> Obj -> Obj -> Either Text Bool
  , tcNormalizeSort :: [Obj] -> Obj -> Either Text Obj
  , tcLiteralKindForSort :: [Obj] -> Obj -> Either Text (Maybe LiteralKind)
  , tcSpliceMapper :: SpliceMapper
  }

type HeadSubst = M.Map TmVar CodeArg

data ResolvedHeadArgs = ResolvedHeadArgs
  { rhaSig :: TmHeadSig
  , rhaStoredCodeArgs :: [CodeArg]
  , rhaStoredExprArgs :: [TermHeadArg]
  , rhaInputs :: [(Obj, TermExpr)]
  , rhaBinderExprArgs :: [TermBinderArg]
  }

resolvedHeadFlatArgs :: ResolvedHeadArgs -> [TermHeadArg]
resolvedHeadFlatArgs resolved =
  rhaStoredExprArgs resolved <> map (THATm . snd) (rhaInputs resolved)

resolvedHeadExpr :: GenName -> ResolvedHeadArgs -> TermExpr
resolvedHeadExpr f resolved =
  TMHead f (resolvedHeadFlatArgs resolved) (rhaBinderExprArgs resolved)

termSubstOps :: TypeTheory -> TermConvEnv -> TermSubstOps
termSubstOps tt convEnv =
  mkTermSubstOps
    tt
    convEnv
    (tcNormalizeSort convEnv)
    (\_ _ tm -> normalizeTermDiagramStructurally tt convEnv (dTmCtx (unTerm tm)) tm)
    (diagramToTermExprWith tt convEnv)
    (termExprToDiagramWith tt convEnv)

mkTermSubstOps
  :: TypeTheory
  -> TermConvEnv
  -> ([Obj] -> Obj -> Either Text Obj)
  -> ([Obj] -> Obj -> TermDiagram -> Either Text TermDiagram)
  -> ([Obj] -> Obj -> TermDiagram -> Either Text TermExpr)
  -> ([Obj] -> Obj -> TermExpr -> Either Text TermDiagram)
  -> TermSubstOps
mkTermSubstOps tt convEnv normalizeObj normalizeTerm diagramToExpr exprToDiagram =
  TermSubstOps
    { tsoNormalizeObj = normalizeObj
    , tsoNormalizeTermDiagram = normalizeTerm
    , tsoDiagramToTermExpr = diagramToExpr
    , tsoTermExprToDiagram = exprToDiagram
    , tsoNormalizeCtx = normalizeCtxStructurally tt convEnv
    , tsoRequireHeadSig = requireHeadSig convEnv
    , tsoResolveHeadArgs =
        \tmCtx currentSort f flatArgs binderArgs -> do
          resolved <- resolveHeadArgsExpr tt convEnv tmCtx M.empty currentSort f flatArgs binderArgs
          Right (resolvedHeadFlatArgs resolved, rhaBinderExprArgs resolved)
    , tsoApplyHeadSubstObj = \tmCtx headSubst obj -> applyHeadSubstObj tt convEnv tmCtx headSubst obj
    , tsoInstantiateMetaBody = instantiateMetaBody
    }

termExprToDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagram tt =
  termExprToDiagramWith tt (structuralConvEnv tt)

termExprToDiagramWith
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramWith tt convEnv tmCtx expectedSort tm = do
  expectedSort' <- tcNormalizeSort convEnv tmCtx expectedSort
  let mode = objOwnerMode expectedSort'
  needed <- requiredModePrefixLen tmCtx mode tm
  let tmCtx' = tmCtxModePrefix tmCtx mode needed
  let modeInputsAll = modeCtxEntries tmCtx' mode
  let modeInputs = modeInputsAll
  let (inPorts, d0) = allocPorts (map snd modeInputs) (emptyDiagram mode tmCtx')
  let base = d0 { dIn = inPorts, dOut = [] }
  (root, d1) <- go modeInputs modeInputsAll inPorts base expectedSort' tm
  out <- finalizeSingleOutputDiagram inPorts root d1
  validateTermGraph out
  pure (TermDiagram out)
  where
    go modeInputs modeInputsAll inPorts diag currentSort currentTm =
      case currentTm of
        TMMeta v metaArgs -> do
          vSort <- tcNormalizeSort convEnv tmCtx (tmvSort v)
          ok <- tcSortEq convEnv tmCtx vSort currentSort
          if ok
            then Right ()
            else
              Left
                ( "termExprToDiagram: metavariable sort mismatch for "
                    <> tmvName v
                    <> " (expected "
                    <> T.pack (show currentSort)
                    <> ", got "
                    <> T.pack (show vSort)
                    <> ")"
                )
          if length metaArgs == tmvScope v
            then Right ()
            else
              Left
                ( "termExprToDiagram: metavariable spine arity mismatch for "
                    <> tmvName v
                    <> " (expected "
                    <> T.pack (show (tmvScope v))
                    <> ", got "
                    <> T.pack (show (length metaArgs))
                    <> ")"
                )
          if tmvScope v <= length modeInputsAll
            then Right ()
            else Left "termExprToDiagram: metavariable scope exceeds mode-local context"
          argPorts <- mapM (lookupMetaInput modeInputs inPorts) metaArgs
          let v' = v { tmvSort = vSort }
          emitMetaNode vSort v' argPorts diag
        TMBound i ->
          case lookupBound modeInputs inPorts i of
            Nothing -> Left "termExprToDiagram: bound term variable out of scope or wrong mode"
            Just (pid, sortTy) -> do
              ensureSortEq "termExprToDiagram: bound term variable sort mismatch" sortTy currentSort
              pure (pid, diag)
        TMHead f flatArgs binderArgs -> do
          resolved <- resolveHeadArgsExpr tt convEnv tmCtx M.empty currentSort f flatArgs binderArgs
          (argPorts, d1) <-
            foldM
              (\(ports, dAcc) (argSort, argTm) -> do
                (argPort, dNext) <- go modeInputs modeInputsAll inPorts dAcc argSort argTm
                pure (ports <> [argPort], dNext))
              ([], diag)
              (rhaInputs resolved)
          let binderPayloads = map binderArgPayload (rhaBinderExprArgs resolved)
          emitGenNode currentSort f (rhaStoredCodeArgs resolved) binderPayloads argPorts d1
        TMSplice _ _ _ ->
          Left "termExprToDiagram: splice terms are only supported in trusted rewrite rules"
        TMLit lit -> do
          ensureLiteralSort currentSort lit
          emitLiteralNode currentSort lit diag

    lookupMetaInput modeInputs inPorts globalTm =
      case elemIndex' globalTm (map fst modeInputs) of
        Nothing ->
          Left
            ( "termExprToDiagram: metavariable argument index "
                <> T.pack (show globalTm)
                <> " not in mode-local context"
            )
        Just localIx ->
          case nth' inPorts localIx of
            Nothing -> Left "termExprToDiagram: internal metavariable input mapping failure"
            Just pid -> Right pid

    ensureSortEq err lhs rhs = do
      ok <- tcSortEq convEnv tmCtx lhs rhs
      if ok then Right () else Left err

    ensureLiteralSort sortTy lit = do
      mKind <- tcLiteralKindForSort convEnv tmCtx sortTy
      case mKind of
        Just kind
          | kind == literalKind lit -> Right ()
          | otherwise -> Left "termExprToDiagram: literal kind does not match expected sort"
        Nothing -> Left "termExprToDiagram: expected sort does not admit literals"

    binderArgPayload (TBABody inner) = BAConcrete inner
    binderArgPayload (TBAHole _) =
      error "termExprToDiagram: binder holes should be rejected before payload encoding"

diagramToTermExprWith
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprWith tt convEnv tmCtx expectedSort (TermDiagram diag) =
  diagramGraphToTermExprWith tt convEnv tmCtx expectedSort diag

diagramToTermExpr
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExpr tt =
  diagramToTermExprWith tt (structuralConvEnv tt)

diagramGraphToTermExpr
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExpr tt =
  diagramGraphToTermExprWith tt (structuralConvEnv tt)

diagramGraphToRuleExpr
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToRuleExpr tt =
  diagramGraphToRuleExprWith tt (structuralConvEnv tt)

diagramGraphToTermExprWith
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExprWith tt convEnv tmCtx expectedSort diag = do
  diagramGraphToExprWithPolicy StrictTermGraph tt convEnv tmCtx expectedSort diag

diagramGraphToRuleExprWith
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToRuleExprWith tt convEnv tmCtx expectedSort diag =
  diagramGraphToExprWithPolicy RuleTermGraph tt convEnv tmCtx expectedSort diag

diagramGraphToExprWithPolicy
  :: TermGraphPolicy
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToExprWithPolicy policy tt convEnv tmCtx expectedSort diag = do
  validateGraphWithPolicy policy diag
  expectedSort' <- tcNormalizeSort convEnv tmCtx expectedSort
  let mode = objOwnerMode expectedSort'
  if dMode diag == mode
    then Right ()
    else Left "diagramToTermExpr: mode mismatch"
  validateBoundaryMapping
  case dOut diag of
    [outPort] -> do
      outTy <-
        case diagramPortObj diag outPort of
          Nothing -> Left "diagramToTermExpr: missing output port type"
          Just ty -> Right ty
      outOk <- tcSortEq convEnv tmCtx outTy expectedSort'
      if outOk
        then Right ()
        else
          Left
            ( "diagramToTermExpr: output sort mismatch (expected "
                <> T.pack (show expectedSort')
                <> ", got "
                <> T.pack (show outTy)
                <> ")"
            )
      diagramGraphToExprCore policy tt convEnv tmCtx diag expectedSort'
    _ -> Left "diagramToTermExpr: term diagram must have exactly one output"
  where
    modeInputs = modeCtxEntries tmCtx (dMode diag)
    nIn = length (dIn diag)

    validateBoundaryMapping = do
      if nIn <= length modeInputs
        then Right ()
        else Left "diagramToTermExpr: boundary input prefix exceeds mode-local context"
      mapM_ checkBoundaryType (zip [0 :: Int ..] (dIn diag))

    checkBoundaryType (localPos, pid) = do
      expectedTy <-
        case nth' modeInputs localPos of
          Nothing -> Left "diagramToTermExpr: missing expected boundary input sort"
          Just (_, ty) -> Right ty
      actualTy <-
        case diagramPortObj diag pid of
          Nothing -> Left "diagramToTermExpr: missing boundary input sort"
          Just ty -> Right ty
      ok <- tcSortEq convEnv tmCtx actualTy expectedTy
      if ok
        then Right ()
        else
          Left
            ( "diagramToTermExpr: boundary input sort mismatch at local position "
                <> T.pack (show localPos)
                <> " (expected "
                <> T.pack (show expectedTy)
                <> ", got "
                <> T.pack (show actualTy)
                <> ")"
            )

diagramGraphToExprCore
  :: TermGraphPolicy
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Diagram
  -> Obj
  -> Either Text TermExpr
diagramGraphToExprCore policy tt convEnv tmCtx diag expectedSort = do
  validateGraphWithPolicy policy diag
  readTermOutput reader diag expectedSort
  where
    modeInputs = modeCtxEntries tmCtx (dMode diag)
    nIn = length (dIn diag)
    localToGlobal = map fst (take nIn modeInputs)
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    reader =
      TermPortReader
        { tprBoundaryLookup = \pid -> M.lookup pid inMap
        , tprOnBoundary = \currentSort local pid -> do
            sortTy <- requirePortType pid
            ensureSortEq
              ( "diagramToTermExpr: boundary input sort mismatch at local position "
                  <> T.pack (show local)
                  <> " (expected "
                  <> T.pack (show currentSort)
                  <> ", got "
                  <> T.pack (show sortTy)
                  <> ")"
              )
              sortTy
              currentSort
            case nth' localToGlobal local of
              Nothing -> Left "diagramToTermExpr: invalid boundary input mapping"
              Just globalTm -> Right (TMBound globalTm)
        , tprOnEdge = \recur currentSort pid producer ->
            case ePayload producer of
              PGen gen args bargs -> do
                sig0 <- requireHeadSigByShape gen args (length (eIns producer)) (length bargs)
                let used = S.unions (map freeVarsObj (currentSort : tmCtx))
                let (sig, _, _) = freshenTmHeadSigAgainstWithMaps used sig0
                (storedArgs, substAfterParams) <- rebuildStoredArgs sig args
                inputArgs <- rebuildInputs recur substAfterParams (zip (thsInputs sig) (eIns producer))
                binderArgs <- rebuildBinderArgs substAfterParams (zip (thsBinders sig) bargs)
                resSort0 <- applyHeadSubstObj tt convEnv tmCtx substAfterParams (thsRes sig)
                resSort <- tcNormalizeSort convEnv tmCtx resSort0
                ensureSortEq "diagramToTermExpr: term head result sort mismatch" resSort currentSort
                Right (TMHead gen (storedArgs <> inputArgs) binderArgs)
              PTmMeta v -> do
                vSort <- tcNormalizeSort convEnv tmCtx (tmvSort v)
                ensureSortEq "diagramToTermExpr: metavariable sort mismatch" vSort currentSort
                metaArgs <- mapM boundaryInputGlobal (eIns producer)
                Right (TMMeta v metaArgs)
              PTmLit lit -> do
                sortTy <- requirePortType pid
                ensureSortEq "diagramToTermExpr: literal node output sort mismatch" sortTy currentSort
                mKind <- tcLiteralKindForSort convEnv tmCtx currentSort
                case mKind of
                  Just kind
                    | kind == literalKind lit -> Right (TMLit lit)
                    | otherwise -> Left "diagramToTermExpr: literal kind does not match output sort"
                  Nothing ->
                    Left
                      ( "diagramToTermExpr: literal node output sort does not admit literals: "
                          <> T.pack (show currentSort)
                      )
              PSplice hole me ->
                case policy of
                  StrictTermGraph ->
                    Left "diagramToTermExpr: splice nodes are not supported in TermExpr"
                  RuleTermGraph ->
                    case eOuts producer of
                      [outPid]
                        | outPid == pid -> do
                            args <-
                              mapM
                                ( \inputPid -> do
                                    inputSort <- requirePortType inputPid
                                    recur inputSort inputPid
                                )
                                (eIns producer)
                            Right (TMSplice hole me args)
                      _ ->
                        Left "diagramToTermExpr: splice node must have exactly one output in a term rule"
                  DefEqTermGraph ->
                    case eOuts producer of
                      [outPid]
                        | outPid == pid -> do
                            args <-
                              mapM
                                ( \inputPid -> do
                                    inputSort <- requirePortType inputPid
                                    recur inputSort inputPid
                                )
                                (eIns producer)
                            Right (TMSplice hole me args)
                      _ ->
                        Left "diagramToTermExpr: splice node must have exactly one output in a term rule"
              _ ->
                Left "diagramToTermExpr: non-term payload in term diagram"
        , tprSingleOutputErr = "diagramToTermExpr: term diagram must have exactly one output"
        , tprCycleErr = "diagramToTermExpr: cycle detected in term diagram"
        , tprMissingProducerErr = "diagramToTermExpr: missing producer"
        }

    boundaryInputGlobal pid =
      case M.lookup pid inMap of
        Nothing ->
          Left "diagramToTermExpr: PTmMeta inputs must connect to boundary inputs"
        Just local ->
          case nth' localToGlobal local of
            Nothing -> Left "diagramToTermExpr: invalid boundary input mapping"
            Just globalTm -> Right globalTm

    requirePortType pid =
      case diagramPortObj diag pid of
        Nothing -> Left "diagramToTermExpr: missing port type"
        Just ty -> Right ty

    ensureSortEq err lhs rhs = do
      ok <- tcSortEq convEnv tmCtx lhs rhs
      if ok then Right () else Left err

    requireHeadSigByShape gen args inputArity binderArity =
      case tcLookupSig convEnv (dMode diag) gen of
        Nothing -> Left "diagramToTermExpr: unknown term head"
        Just sig0
          | length (thsParams sig0) /= length args ->
              Left "diagramToTermExpr: stored argument arity mismatch"
          | length (thsBinders sig0) /= binderArity ->
              Left "diagramToTermExpr: term head binder arity mismatch"
          | length (thsInputs sig0) /= inputArity ->
              Left "diagramToTermExpr: term head input arity mismatch"
          | otherwise ->
              Right sig0

    rebuildStoredArgs sig args =
      foldM
        stepStoredArg
        ([], M.empty)
        (zip (thsParams sig) args)

    stepStoredArg (acc, substAcc) (param, arg) =
      case (param, arg) of
        (GP_Ty v, CAObj obj) -> do
          obj' <- tcNormalizeSort convEnv tmCtx obj
          subst' <- bindHeadSubst v (CAObj obj') substAcc
          pure (acc <> [THAObj obj'], subst')
        (GP_Ty _, CATm _) ->
          Left "diagramToTermExpr: expected object-valued stored arg"
        (GP_Tm v, CATm tmArg) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAcc (tmvSort v)
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          storedTmCtx <- normalizeCtxStructurally tt convEnv (dTmCtx (unTerm tmArg))
          expr <- diagramToTermExprWith tt convEnv storedTmCtx expectedArgSort tmArg
          tmArg' <- termExprToDiagramWith tt convEnv tmCtx expectedArgSort expr
          subst' <- bindHeadSubst v (CATm tmArg') substAcc
          pure (acc <> [THATm expr], subst')
        (GP_Tm _, CAObj _) ->
          Left "diagramToTermExpr: expected term-valued stored arg"

    rebuildInputs recur substAfterParams inputs =
      foldM
        (\acc (argSort, inputPid) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAfterParams argSort
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          argExpr <- recur expectedArgSort inputPid
          pure (acc <> [THATm argExpr]))
        []
        inputs

    rebuildBinderArgs substAfterParams binders =
      foldM
        (\acc (slot0, barg) -> do
          slot <- instantiateBinderSig tt convEnv tmCtx substAfterParams slot0
          innerExpr <- rebuildBinderArg slot barg
          pure (acc <> [innerExpr]))
        []
        binders

    rebuildBinderArg slot barg =
      case barg of
        BAConcrete inner0 -> do
          inner <- normalizeDiagramStructurally tt convEnv inner0
          validateConcreteBinderArg slot inner
          Right (TBABody inner)
        BAMeta hole ->
          case policy of
            StrictTermGraph ->
              Left "diagramToTermExpr: binder metavariables are not supported in TermExpr"
            RuleTermGraph ->
              Right (TBAHole hole)
            DefEqTermGraph ->
              Right (TBAHole hole)

validateTermGraph :: Diagram -> Either Text ()
validateTermGraph =
  validateGraphWithPolicy StrictTermGraph

validateRuleGraph :: Diagram -> Either Text ()
validateRuleGraph =
  validateGraphWithPolicy RuleTermGraph

validateDefEqGraph :: Diagram -> Either Text ()
validateDefEqGraph =
  validateGraphPayloadsWithPolicy DefEqTermGraph

validateGraphWithPolicy :: TermGraphPolicy -> Diagram -> Either Text ()
validateGraphWithPolicy policy diag = do
  validateDiagram diag
  case dOut diag of
    [_] -> Right ()
    _ -> Left "validateTermDiagram: term diagram must have exactly one output"
  let modeInputs0 = modeCtxEntries (dTmCtx diag) (dMode diag)
  let nIn = length (dIn diag)
  if nIn <= length modeInputs0
    then Right ()
    else Left "validateTermDiagram: boundary input prefix exceeds mode-local context"
  mapM_ (checkBoundaryType modeInputs0) (zip [0 :: Int ..] (dIn diag))
  validateGraphPayloadsWithPolicy policy diag
  pure ()
  where
    checkBoundaryType modeInputs0 (localPos, pid) = do
      expectedTy <-
        case nth' modeInputs0 localPos of
          Nothing -> Left "validateTermDiagram: missing expected boundary input sort"
          Just (_, ty) -> Right ty
      actualTy <-
        case diagramPortObj diag pid of
          Nothing -> Left "validateTermDiagram: missing boundary input sort"
          Just ty -> Right ty
      if actualTy == expectedTy
        then Right ()
        else Left "validateTermDiagram: boundary input sort mismatch"

validateGraphPayloadsWithPolicy :: TermGraphPolicy -> Diagram -> Either Text ()
validateGraphPayloadsWithPolicy policy diag = do
  validateDiagram diag
  case dOut diag of
    [_] -> Right ()
    _ -> Left "validateTermDiagram: term diagram must have exactly one output"
  mapM_ checkEdge (IM.elems (dEdges diag))
  pure ()
  where
    checkEdge edge =
      case ePayload edge of
        PGen _ args bargs -> do
          mapM_ checkCodeArg args
          mapM_ checkBinderArg bargs
        PSplice _ _ ->
          case policy of
            StrictTermGraph ->
              Left "validateTermDiagram: splice nodes are not allowed in checked term diagrams"
            RuleTermGraph ->
              case eOuts edge of
                [_] -> Right ()
                _ -> Left "validateTermDiagram: splice nodes in term rules must have exactly one output"
            DefEqTermGraph ->
              case eOuts edge of
                [_] -> Right ()
                _ -> Left "validateTermDiagram: splice nodes in definitional term diagrams must have exactly one output"
        PTmMeta _ ->
          if all (`elem` dIn diag) (eIns edge)
            then Right ()
            else Left "validateTermDiagram: PTmMeta inputs must be boundary ports"
        PTmLit _ ->
          case (eIns edge, eOuts edge) of
            ([], [_]) -> Right ()
            _ -> Left "validateTermDiagram: PTmLit must have no inputs and exactly one output"
        PInternalDrop -> Right ()
        _ ->
          case policy of
            StrictTermGraph ->
              Left "validateTermDiagram: only PGen/PTmMeta/PTmLit/PInternalDrop are allowed in term diagrams"
            RuleTermGraph ->
              Left "validateTermDiagram: only PGen/PSplice/PTmMeta/PTmLit/PInternalDrop are allowed in term rules"
            DefEqTermGraph ->
              Right ()

    checkCodeArg arg =
      case arg of
        CAObj _ -> Right ()
        CATm (TermDiagram inner) -> validateGraphPayloadsWithPolicy policy inner

    checkBinderArg barg =
      case barg of
        BAConcrete inner -> validateGraphPayloadsWithPolicy policy inner
        BAMeta _ ->
          case policy of
            StrictTermGraph ->
              Left "validateTermDiagram: binder metavariables are not allowed in checked term diagrams"
            RuleTermGraph ->
              Right ()
            DefEqTermGraph ->
              Right ()

requiredModePrefixLen :: [Obj] -> ModeName -> TermExpr -> Either Text Int
requiredModePrefixLen tmCtx mode tm = do
  let modeInputsAll = modeCtxEntries tmCtx mode
  let globals = map fst modeInputsAll
  let neededScope = hostMaxTmScopeExpr tm
  let boundGlobals = S.toList (hostBoundGlobalsExpr tm)
  boundPositions <-
    forM
      boundGlobals
      ( \globalTm ->
          case elemIndex' globalTm globals of
            Nothing ->
              Left
                ( "termExprToDiagram: bound variable index "
                    <> T.pack (show globalTm)
                    <> " not in mode-local context (wrong mode or out of scope)"
                )
            Just localPos ->
              Right localPos
      )
  let neededBound =
        case boundPositions of
          [] -> 0
          _ -> 1 + maximum boundPositions
  let needed = max neededScope neededBound
  when
    (needed > length modeInputsAll)
    (Left "termExprToDiagram: required prefix exceeds available bound vars of this mode")
  pure needed

lookupBound :: [(Int, Obj)] -> [PortId] -> Int -> Maybe (PortId, Obj)
lookupBound modeInputs inPorts idx = do
  local <- elemIndex' idx (map fst modeInputs)
  pid <- nth' inPorts local
  (_, sortTy) <- nth' modeInputs local
  pure (pid, sortTy)

modeCtxEntries :: [Obj] -> ModeName -> [(Int, Obj)]
modeCtxEntries tmCtx mode =
  [ (i, ty)
  | i <- modeCtxGlobals tmCtx mode
  , Just ty <- [nth' tmCtx i]
  ]

tmCtxModePrefix :: [Obj] -> ModeName -> Int -> [Obj]
tmCtxModePrefix tmCtx mode needed =
  case take needed (modeCtxGlobals tmCtx mode) of
    [] -> []
    globals ->
      let cutoff = maximum globals
       in take (cutoff + 1) tmCtx

structuralConvEnv :: TypeTheory -> TermConvEnv
structuralConvEnv tt =
  convEnv
  where
    convEnv = mkNormalizingConvEnv tt (sameModeSpliceMapper "term") (normalizeSortStructurally tt convEnv)

mkNormalizingConvEnv
  :: TypeTheory
  -> SpliceMapper
  -> ([Obj] -> Obj -> Either Text Obj)
  -> TermConvEnv
mkNormalizingConvEnv tt spliceMapper normalizeSort =
  TermConvEnv
    { tcLookupSig = \mode f -> lookupTmHeadSig tt mode f
    , tcSortEq = \tmCtx a b -> do
        a' <- normalizeSort tmCtx a
        b' <- normalizeSort tmCtx b
        pure (a' == b')
    , tcNormalizeSort = normalizeSort
    , tcLiteralKindForSort = \tmCtx sortTy -> do
        sortTy' <- normalizeSort tmCtx sortTy
        pure (literalKindForObj tt sortTy')
    , tcSpliceMapper = spliceMapper
    }

normalizeSortStructurally
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Either Text Obj
normalizeSortStructurally tt convEnv tmCtx obj =
  case objCode obj of
    CTMeta _ ->
      normalizeObjExpr (ttModes tt) obj
    CTCon ref args -> do
      args' <- mapM normalizeArg args
      normalizeObjExpr (ttModes tt) obj { objCode = CTCon ref args' }
    CTLift me inner -> do
      inner' <- normalizeSortStructurally tt convEnv tmCtx (Obj (meSrc me) inner)
      normalizeObjExpr (ttModes tt) obj { objCode = CTLift me (objCode inner') }
  where
    normalizeArg arg =
      case arg of
        CAObj innerObj ->
          CAObj <$> normalizeSortStructurally tt convEnv tmCtx innerObj
        CATm tmArg -> do
          CATm <$> normalizeTermDiagramStructurally tt convEnv (dTmCtx (unTerm tmArg)) tmArg

normalizeCtxStructurally
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Either Text [Obj]
normalizeCtxStructurally tt convEnv =
  normalizeCtxStructurallyWithPrefix tt convEnv []

normalizeCtxStructurallyWithPrefix
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> [Obj]
  -> Either Text [Obj]
normalizeCtxStructurallyWithPrefix tt convEnv prefix =
  go prefix
  where
    go _ [] = Right []
    go ctxAcc (ty : rest) = do
      ty' <- normalizeSortStructurally tt convEnv ctxAcc ty
      rest' <- go (ctxAcc <> [ty']) rest
      pure (ty' : rest')

normalizeDiagramStructurally
  :: TypeTheory
  -> TermConvEnv
  -> Diagram
  -> Either Text Diagram
normalizeDiagramStructurally tt convEnv =
  goDiag
  where
    goDiag diag = do
      dTmCtx' <- normalizeCtxStructurally tt convEnv (dTmCtx diag)
      edges' <- IM.traverseWithKey (\_ edge -> normalizeEdge dTmCtx' edge) (dEdges diag)
      portObj' <- IM.traverseWithKey (\_ ty -> normalizeSortStructurally tt convEnv dTmCtx' ty) (dPortObj diag)
      pure diag { dTmCtx = dTmCtx', dPortObj = portObj', dEdges = edges' }

    normalizeEdge tmCtx edge = do
      payload' <- normalizePayload tmCtx (ePayload edge)
      pure edge { ePayload = payload' }

    normalizePayload tmCtx payload =
      case payload of
        PGen g args bargs -> do
          args' <- traverse (normalizeCodeArg tmCtx) args
          bargs' <- traverse normalizeBinderArg bargs
          pure (PGen g args' bargs')
        PBox name inner ->
          PBox name <$> goDiag inner
        PFeedback inner ->
          PFeedback <$> goDiag inner
        PTmMeta v -> do
          sort' <- normalizeSortStructurally tt convEnv tmCtx (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        other ->
          pure other

    normalizeCodeArg tmCtx arg =
      case arg of
        CAObj innerObj ->
          CAObj <$> normalizeSortStructurally tt convEnv tmCtx innerObj
        CATm innerTm ->
          CATm <$> normalizeTermDiagramStructurally tt convEnv (dTmCtx (unTerm innerTm)) innerTm

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner ->
          BAConcrete <$> goDiag inner
        BAMeta x ->
          pure (BAMeta x)

normalizeTermDiagramStructurally
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagramStructurally tt convEnv tmCtx0 (TermDiagram diag) = do
  tmCtx <- normalizeCtxStructurally tt convEnv tmCtx0
  diag' <- normalizeDiagramStructurally tt convEnv diag
  diag'' <- weakenDiagramTmCtxToModePrefix tmCtx diag'
  portObj' <- IM.traverseWithKey (\_ ty -> normalizeSortStructurally tt convEnv tmCtx ty) (dPortObj diag'')
  canon <- canonDiagramRaw diag'' { dTmCtx = tmCtx, dPortObj = portObj' }
  pure (TermDiagram canon)

requireHeadSig :: TermConvEnv -> [Obj] -> Obj -> GenName -> [TermHeadArg] -> [TermBinderArg] -> Either Text TmHeadSig
requireHeadSig convEnv tmCtx sortTy f args bargs = do
  sortTy' <- tcNormalizeSort convEnv tmCtx sortTy
  sig <-
    case tcLookupSig convEnv (objOwnerMode sortTy') f of
      Nothing -> Left "termExprToDiagram: unknown term head"
      Just s -> Right s
  if length args /= length (thsParams sig) + length (thsInputs sig)
    then Left "termExprToDiagram: term head arity mismatch"
    else Right ()
  if length bargs /= length (thsBinders sig)
    then Left "termExprToDiagram: term head binder arity mismatch"
    else Right ()
  pure sig

resolveHeadArgsExpr
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> HeadSubst
  -> Obj
  -> GenName
  -> [TermHeadArg]
  -> [TermBinderArg]
  -> Either Text ResolvedHeadArgs
resolveHeadArgsExpr tt convEnv tmCtx outerSubst currentSort f flatArgs binderArgs = do
  sig0 <- requireHeadSig convEnv tmCtx currentSort f flatArgs binderArgs
  let used = M.keysSet outerSubst
  let (sig, _, _) = freshenTmHeadSigAgainstWithMaps used sig0
  let (paramArgs, inputArgs) = splitAt (length (thsParams sig)) flatArgs
  (storedCodeRev, storedExprRev, substAfterParams) <-
    foldM
      stepParam
      ([], [], outerSubst)
      (zip (thsParams sig) paramArgs)
  inputsRev <-
    foldM
      (stepInput substAfterParams)
      []
      (zip (thsInputs sig) inputArgs)
  binderArgsRev <-
    foldM
      (stepBinder substAfterParams)
      []
      (zip (thsBinders sig) binderArgs)
  resSort0 <- applyHeadSubstObj tt convEnv tmCtx substAfterParams (thsRes sig)
  resSort <- tcNormalizeSort convEnv tmCtx resSort0
  ok <- tcSortEq convEnv tmCtx resSort currentSort
  if ok
    then
      pure
        ResolvedHeadArgs
          { rhaSig = sig
          , rhaStoredCodeArgs = reverse storedCodeRev
          , rhaStoredExprArgs = reverse storedExprRev
          , rhaInputs = reverse inputsRev
          , rhaBinderExprArgs = reverse binderArgsRev
          }
    else
      Left
        ( "termExprToDiagram: term head result sort mismatch (inferred "
            <> T.pack (show resSort)
            <> ", expected "
            <> T.pack (show currentSort)
            <> ")"
        )
  where

    stepParam (codeAcc, exprAcc, substAcc) (param, arg) =
      case (param, arg) of
        (GP_Ty v, THAObj obj) -> do
          obj' <- tcNormalizeSort convEnv tmCtx obj
          subst' <- bindHeadSubst v (CAObj obj') substAcc
          pure (CAObj obj' : codeAcc, THAObj obj' : exprAcc, subst')
        (GP_Ty _, THATm _) ->
          Left "termExprToDiagram: expected object-valued parameter argument"
        (GP_Tm v, THATm tmArg) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAcc (tmvSort v)
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          tmArg' <- rewriteHeadExpr tt convEnv tmCtx substAcc expectedArgSort tmArg
          tmDiag <-
            case termExprToDiagramWith tt convEnv tmCtx expectedArgSort tmArg' of
              Left err -> Left ("resolveHeadArgsExpr: parameter elaboration failed: " <> err)
              Right tmDiag -> Right tmDiag
          subst' <- bindHeadSubst v (CATm tmDiag) substAcc
          pure (CATm tmDiag : codeAcc, THATm tmArg' : exprAcc, subst')
        (GP_Tm _, THAObj _) ->
          Left "termExprToDiagram: expected term-valued parameter argument"

    stepInput substAfterParams acc (argSort, arg) = do
      argTm <-
        case arg of
          THATm tmArg -> Right tmArg
          THAObj _ -> Left "termExprToDiagram: expected term input argument"
      expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAfterParams argSort
      expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
      argTm' <- rewriteHeadExpr tt convEnv tmCtx substAfterParams expectedArgSort argTm
      _ <-
        case termExprToDiagramWith tt convEnv tmCtx expectedArgSort argTm' of
          Left err -> Left ("resolveHeadArgsExpr: input elaboration failed: " <> err)
          Right tmDiag -> Right tmDiag
      pure ((expectedArgSort, argTm') : acc)

    stepBinder substAfterParams acc (slot0, barg) = do
      slot <- instantiateBinderSig tt convEnv tmCtx substAfterParams slot0
      barg' <- rewriteBinderArg tt convEnv slot barg
      pure (barg' : acc)

instantiateBinderSig
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> HeadSubst
  -> BinderSig
  -> Either Text BinderSig
instantiateBinderSig tt convEnv tmCtx headSubst binder = do
  tmCtx0 <- mapM (applyHeadSubstObj tt convEnv tmCtx headSubst) (bsTmCtx binder)
  tmCtx' <- normalizeCtxStructurally tt convEnv tmCtx0
  dom0 <- mapM (applyHeadSubstObj tt convEnv tmCtx' headSubst) (bsDom binder)
  dom' <- normalizeCtxStructurallyWithPrefix tt convEnv tmCtx' dom0
  cod0 <- mapM (applyHeadSubstObj tt convEnv tmCtx' headSubst) (bsCod binder)
  cod' <- normalizeCtxStructurallyWithPrefix tt convEnv tmCtx' cod0
  pure binder { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

rewriteBinderArg
  :: TypeTheory
  -> TermConvEnv
  -> BinderSig
  -> TermBinderArg
  -> Either Text TermBinderArg
rewriteBinderArg tt convEnv slot barg =
  case barg of
    TBABody inner0 -> do
      inner <- normalizeDiagramStructurally tt convEnv inner0
      validateConcreteBinderArg slot inner
      pure (TBABody inner)
    TBAHole _ ->
      Left "termExprToDiagram: binder holes are only supported in trusted rewrite rules"

validateConcreteBinderArg :: BinderSig -> Diagram -> Either Text ()
validateConcreteBinderArg slot inner = do
  validateDiagram inner
  if dTmCtx inner == bsTmCtx slot
    then Right ()
    else Left "termExprToDiagram: binder argument term-context mismatch"
  dom <- diagramBoundaryTypes inner (dIn inner)
  cod <- diagramBoundaryTypes inner (dOut inner)
  if dom == bsDom slot && cod == bsCod slot
    then Right ()
    else Left "termExprToDiagram: binder argument boundary mismatch"

diagramBoundaryTypes :: Diagram -> [PortId] -> Either Text [Obj]
diagramBoundaryTypes diag =
  mapM
    ( \pid ->
        case diagramPortObj diag pid of
          Just ty -> Right ty
          Nothing -> Left "termExprToDiagram: missing binder boundary sort"
    )

rewriteHeadExpr
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> HeadSubst
  -> Obj
  -> TermExpr
  -> Either Text TermExpr
rewriteHeadExpr tt convEnv tmCtx subst currentSort expr =
  case expr of
    TMBound i -> do
      boundSort <-
        case nth' tmCtx i of
          Nothing -> Left "termExprToDiagram: bound term variable out of scope"
          Just sortTy -> tcNormalizeSort convEnv tmCtx sortTy
      ok <- tcSortEq convEnv tmCtx boundSort currentSort
      if ok
        then Right expr
        else Left "termExprToDiagram: bound term variable sort mismatch"
    TMMeta v args ->
      case M.lookup v subst of
        Nothing -> do
          vSort0 <- applyHeadSubstObj tt convEnv tmCtx subst (tmvSort v)
          vSort <- tcNormalizeSort convEnv tmCtx vSort0
          ok <- tcSortEq convEnv tmCtx vSort currentSort
          if ok
            then Right (TMMeta (v { tmvSort = vSort }) args)
            else
              Left
                ( "termExprToDiagram: metavariable sort mismatch for "
                    <> tmvName v
                    <> " (expected "
                    <> T.pack (show currentSort)
                    <> ", got "
                    <> T.pack (show vSort)
                    <> ")"
                )
        Just (CAObj _) ->
          Left "termExprToDiagram: expected term-valued substitution for term metavariable"
        Just (CATm tmSub) -> do
          body <- diagramToTermExprWith tt convEnv tmCtx currentSort tmSub
          body' <- instantiateMetaBody tmCtx v args body
          rewriteHeadExpr tt convEnv tmCtx (M.delete v subst) currentSort body'
    TMHead f flatArgs binderArgs -> do
      resolved <- resolveHeadArgsExpr tt convEnv tmCtx subst currentSort f flatArgs binderArgs
      pure (resolvedHeadExpr f resolved)
    TMSplice _ _ _ ->
      Left "termExprToDiagram: splice terms are only supported in trusted rewrite rules"
    TMLit lit -> do
      sortTy <- tcNormalizeSort convEnv tmCtx currentSort
      case literalKindForObj tt sortTy of
        Just kind
          | kind == literalKind lit -> Right expr
          | otherwise -> Left "termExprToDiagram: literal kind does not match expected sort"
        Nothing -> Left "termExprToDiagram: expected sort does not admit literals"

applyHeadSubstObj
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> HeadSubst
  -> Obj
  -> Either Text Obj
applyHeadSubstObj tt convEnv _tmCtx subst ty = do
  subst' <- mkSubst (M.toList subst)
  applySubstObjWith (termSubstOps tt convEnv) tt subst' ty


instantiateMetaBody
  :: [Obj]
  -> TmVar
  -> [Int]
  -> TermExpr
  -> Either Text TermExpr
instantiateMetaBody =
  instantiateMetaBodyWith "termExprToDiagram"

instantiateHostBoundObj
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> M.Map Int TermDiagram
  -> Obj
  -> Either Text Obj
instantiateHostBoundObj tt convEnv tmCtx diagSubst obj = do
  exprSubst <- M.fromList <$> mapM diagramToExpr (M.toList diagSubst)
  instantiateObj exprSubst obj
  where
    diagramToExpr (i, tm) = do
      sortTy <- hostSubstTermDiagramOutputSort "instantiateHostBoundObj" (unTerm tm)
      expr <- diagramToTermExprWith tt convEnv tmCtx sortTy tm
      pure (i, expr)

    instantiateObj exprSubst obj0 =
      fmap (\code' -> obj0 { objCode = code' }) (instantiateCode exprSubst (objCode obj0))

    instantiateCode exprSubst code =
      case code of
        CTMeta _ -> Right code
        CTCon ref args ->
          CTCon ref <$> mapM (instantiateArg exprSubst) args
        CTLift me inner ->
          CTLift me <$> instantiateCode exprSubst inner

    instantiateArg exprSubst arg =
      case arg of
        CAObj inner ->
          CAObj <$> instantiateObj exprSubst inner
        CATm tm -> do
          sortTy <- hostSubstTermDiagramOutputSort "instantiateHostBoundObj" (unTerm tm)
          expr <- diagramToTermExprWith tt convEnv tmCtx sortTy tm
          expr' <- instantiateExpr exprSubst expr
          CATm <$> termExprToDiagramWith tt convEnv tmCtx sortTy expr'

    instantiateExpr exprSubst tm =
      case tm of
        TMBound i ->
          Right (M.findWithDefault (TMBound i) i exprSubst)
        TMMeta v args ->
          TMMeta v <$> mapM (instantiateMetaArg exprSubst) args
        TMHead f args bargs -> do
          args' <- mapM (instantiateHeadArg exprSubst) args
          pure (TMHead f args' bargs)
        TMSplice hole me args ->
          TMSplice hole me <$> mapM (instantiateExpr exprSubst) args
        TMLit lit ->
          Right (TMLit lit)

    instantiateHeadArg exprSubst arg =
      case arg of
        THAObj inner ->
          THAObj <$> instantiateObj exprSubst inner
        THATm inner ->
          THATm <$> instantiateExpr exprSubst inner

    instantiateMetaArg exprSubst i =
      case M.lookup i exprSubst of
        Nothing ->
          Right i
        Just (TMBound j) ->
          Right j
        Just _ ->
          Left "instantiateHostBoundObj: cannot substitute a non-variable term into a metavariable spine"

instantiateHostBoundCtx
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> M.Map Int TermDiagram
  -> [Obj]
  -> Either Text [Obj]
instantiateHostBoundCtx tt convEnv tmCtx diagSubst =
  mapM (instantiateHostBoundObj tt convEnv tmCtx diagSubst)

hostSubstTermDiagramOutputSort :: Text -> Diagram -> Either Text Obj
hostSubstTermDiagramOutputSort label diag =
  case dOut diag of
    [pid] ->
      case diagramPortObj diag pid of
        Just ty -> Right ty
        Nothing -> Left (label <> ": missing output sort")
    _ -> Left (label <> ": term diagram must have exactly one output")

elemIndex' :: Eq a => a -> [a] -> Maybe Int
elemIndex' x xs = go 0 xs
  where
    go _ [] = Nothing
    go i (y:ys)
      | x == y = Just i
      | otherwise = go (i + 1) ys

nth' :: [a] -> Int -> Maybe a
nth' xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
