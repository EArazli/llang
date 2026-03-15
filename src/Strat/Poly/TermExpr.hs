{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TermExpr
  ( TermExpr(..)
  , TermConvEnv(..)
  , ResolvedHeadArgs(..)
  , termExprToDiagramWith
  , termExprToDiagram
  , diagramToTermExprWith
  , diagramToTermExpr
  , diagramGraphToTermExprWith
  , diagramGraphToTermExpr
  , structuralConvEnv
  , resolveHeadArgsExpr
  , resolvedHeadFlatArgs
  , applyHeadSubstObj
  , instantiateMetaBody
  , normalizeCtxStructurally
  , normalizeTermDiagramStructurally
  , validateTermGraph
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
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , addEdgePayload
  , canonDiagramRaw
  , diagramPortObj
  , emptyDiagram
  , freshPort
  , unEdgeId
  , unPortId
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
  , defaultMetaArgs
  , freeVarsObj
  , modeCtxGlobals
  , normalizeObjExpr
  , objOwnerMode
  )
import Strat.Poly.Subst (TermSubstOps(..), applySubstObjWith, bindHeadSubst, mkSubst)
import Strat.Poly.Tele (GenParam(..))
import Strat.Poly.Term.AST
  ( TermHeadArg(..)
  , TermExpr(..)
  , boundGlobalsExpr
  , freeTmVarsExpr
  , isPureMetaExpr
  , maxTmScopeExpr
  )
import Strat.Poly.TypeTheory
  ( TmHeadSig(..)
  , TypeTheory(..)
  , literalKindForObj
  , lookupTmHeadSig
  )
import Strat.Poly.Traversal (traverseDiagram)

data TermConvEnv = TermConvEnv
  { tcLookupSig :: ModeName -> GenName -> Maybe TmHeadSig
  , tcSortEq :: [Obj] -> Obj -> Obj -> Either Text Bool
  , tcNormalizeSort :: [Obj] -> Obj -> Either Text Obj
  , tcLiteralKindForSort :: [Obj] -> Obj -> Either Text (Maybe LiteralKind)
  }

type HeadSubst = M.Map TmVar CodeArg

data ResolvedHeadArgs = ResolvedHeadArgs
  { rhaSig :: TmHeadSig
  , rhaStoredCodeArgs :: [CodeArg]
  , rhaStoredExprArgs :: [TermHeadArg]
  , rhaInputs :: [(Obj, TermExpr)]
  }

resolvedHeadFlatArgs :: ResolvedHeadArgs -> [TermHeadArg]
resolvedHeadFlatArgs resolved =
  rhaStoredExprArgs resolved <> map (THATm . snd) (rhaInputs resolved)

termSubstOps :: TypeTheory -> TermConvEnv -> TermSubstOps
termSubstOps tt convEnv =
  TermSubstOps
    { tsoNormalizeObj = tcNormalizeSort convEnv
    , tsoNormalizeTermDiagram = \_ _ tm -> normalizeTermDiagramStructurally tt convEnv (dTmCtx (unTerm tm)) tm
    , tsoDiagramToTermExpr = diagramToTermExprWith tt convEnv
    , tsoTermExprToDiagram = termExprToDiagramWith tt convEnv
    , tsoNormalizeCtx = normalizeCtxStructurally tt convEnv
    , tsoRequireHeadSig = \tmCtx currentSort f flatArgs -> requireHeadSig convEnv tmCtx currentSort f flatArgs
    , tsoResolveHeadFlatArgs =
        \tmCtx currentSort f flatArgs ->
          resolvedHeadFlatArgs <$> resolveHeadArgsExpr tt convEnv tmCtx M.empty currentSort f flatArgs
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
  let withOut = d1 { dOut = [root] }
  out <- saturateUnusedPrefixInputs withOut
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
          let (outPort, d1) = freshPort vSort diag
          d2 <- addEdgePayload (PTmMeta v') argPorts [outPort] d1
          pure (outPort, d2)
        TMBound i ->
          case lookupBound modeInputs inPorts i of
            Nothing -> Left "termExprToDiagram: bound term variable out of scope or wrong mode"
            Just (pid, sortTy) -> do
              ensureSortEq "termExprToDiagram: bound term variable sort mismatch" sortTy currentSort
              pure (pid, diag)
        TMGen f flatArgs -> do
          resolved <- resolveHeadArgsExpr tt convEnv tmCtx M.empty currentSort f flatArgs
          (argPorts, d1) <-
            foldM
              (\(ports, dAcc) (argSort, argTm) -> do
                (argPort, dNext) <- go modeInputs modeInputsAll inPorts dAcc argSort argTm
                pure (ports <> [argPort], dNext))
              ([], diag)
              (rhaInputs resolved)
          let (outPort, d2) = freshPort currentSort d1
          d3 <- addEdgePayload (PGen f (rhaStoredCodeArgs resolved) []) argPorts [outPort] d2
          pure (outPort, d3)
        TMLit lit -> do
          ensureLiteralSort currentSort lit
          let (outPort, d1) = freshPort currentSort diag
          d2 <- addEdgePayload (PTmLit lit) [] [outPort] d1
          pure (outPort, d2)

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

diagramGraphToTermExprWith
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExprWith tt convEnv tmCtx expectedSort diag = do
  validateTermGraph diag
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
      diagramGraphToTermExprCore tt convEnv tmCtx diag expectedSort'
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

diagramGraphToTermExprCore
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Diagram
  -> Obj
  -> Either Text TermExpr
diagramGraphToTermExprCore tt convEnv tmCtx diag expectedSort = do
  validateTermGraph diag
  case dOut diag of
    [outPort] -> termAt S.empty expectedSort outPort
    _ -> Left "diagramToTermExpr: term diagram must have exactly one output"
  where
    modeInputs = modeCtxEntries tmCtx (dMode diag)
    nIn = length (dIn diag)
    localToGlobal = map fst (take nIn modeInputs)
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    termAt seen currentSort pid =
      case M.lookup pid inMap of
        Just local -> do
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
        Nothing ->
          if pid `S.member` seen
            then Left "diagramToTermExpr: cycle detected in term diagram"
            else do
              producer <-
                case IM.lookup (unPortId pid) (dProd diag) of
                  Just (Just eid) ->
                    case IM.lookup (unEdgeId eid) (dEdges diag) of
                      Nothing -> Left "diagramToTermExpr: producer edge missing"
                      Just edge -> Right edge
                  _ -> Left "diagramToTermExpr: missing producer"
              case ePayload producer of
                PGen gen args bargs
                  | null bargs -> do
                      sig0 <- requireHeadSigByArity gen args (length (eIns producer))
                      let used = S.unions (map freeVarsObj (currentSort : tmCtx))
                      let (sig, _, _) = freshenTmHeadSigAgainstWithMaps used sig0
                      (storedArgs, substAfterParams) <- rebuildStoredArgs sig args
                      inputArgs <- rebuildInputs (S.insert pid seen) substAfterParams (zip (thsInputs sig) (eIns producer))
                      resSort0 <- applyHeadSubstObj tt convEnv tmCtx substAfterParams (thsRes sig)
                      resSort <- tcNormalizeSort convEnv tmCtx resSort0
                      ensureSortEq "diagramToTermExpr: term head result sort mismatch" resSort currentSort
                      Right (TMGen gen (storedArgs <> inputArgs))
                  | otherwise ->
                      Left "diagramToTermExpr: generator term node must not carry binder args"
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
                _ ->
                  Left "diagramToTermExpr: non-term payload in term diagram"

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

    requireHeadSigByArity gen args inputArity =
      case tcLookupSig convEnv (dMode diag) gen of
        Nothing -> Left "diagramToTermExpr: unknown term head"
        Just sig0
          | length (thsParams sig0) /= length args ->
              Left "diagramToTermExpr: stored argument arity mismatch"
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

    rebuildInputs seen substAfterParams inputs =
      foldM
        (\acc (argSort, inputPid) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAfterParams argSort
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          argExpr <- termAt seen expectedArgSort inputPid
          pure (acc <> [THATm argExpr]))
        []
        inputs

validateTermGraph :: Diagram -> Either Text ()
validateTermGraph diag = do
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
  mapM_ checkEdge (IM.elems (dEdges diag))
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

    checkEdge edge =
      case ePayload edge of
        PGen _ _args bargs ->
          if null bargs
            then Right ()
            else Left "validateTermDiagram: term generator nodes cannot have binder args"
        PTmMeta _ ->
          if all (`elem` dIn diag) (eIns edge)
            then Right ()
            else Left "validateTermDiagram: PTmMeta inputs must be boundary ports"
        PTmLit _ ->
          case (eIns edge, eOuts edge) of
            ([], [_]) -> Right ()
            _ -> Left "validateTermDiagram: PTmLit must have no inputs and exactly one output"
        PInternalDrop -> Right ()
        _ -> Left "validateTermDiagram: only PGen/PTmMeta/PTmLit/PInternalDrop are allowed in term diagrams"

requiredModePrefixLen :: [Obj] -> ModeName -> TermExpr -> Either Text Int
requiredModePrefixLen tmCtx mode tm = do
  let modeInputsAll = modeCtxEntries tmCtx mode
  let globals = map fst modeInputsAll
  let neededScope = maxTmScopeExpr tm
  let boundGlobals = S.toList (boundGlobalsExpr tm)
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

allocPorts :: [Obj] -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (restPorts, diag2) = allocPorts rest diag1
   in (pid : restPorts, diag2)

saturateUnusedPrefixInputs :: Diagram -> Either Text Diagram
saturateUnusedPrefixInputs diag =
  foldM ensureConsumed diag (dIn diag)
  where
    ensureConsumed d pid =
      let isBoundaryOutput = pid `elem` dOut d
       in case IM.lookup (unPortId pid) (dCons d) of
            Just Nothing
              | isBoundaryOutput -> Right d
              | otherwise -> addEdgePayload PInternalDrop [pid] [] d
            _ -> Right d

structuralConvEnv :: TypeTheory -> TermConvEnv
structuralConvEnv tt =
  convEnv
  where
    convEnv =
      TermConvEnv
        { tcLookupSig = \mode f -> lookupTmHeadSig tt mode f
        , tcSortEq = \tmCtx a b -> do
            a' <- normalizeSortStructurally tt convEnv tmCtx a
            b' <- normalizeSortStructurally tt convEnv tmCtx b
            pure (a' == b')
        , tcNormalizeSort = normalizeSortStructurally tt convEnv
        , tcLiteralKindForSort = \tmCtx sortTy -> do
            sortTy' <- normalizeSortStructurally tt convEnv tmCtx sortTy
            pure (literalKindForObj tt sortTy')
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
  go []
  where
    go _ [] = Right []
    go ctxAcc (ty : rest) = do
      ty' <- normalizeSortStructurally tt convEnv ctxAcc ty
      rest' <- go (ctxAcc <> [ty']) rest
      pure (ty' : rest')

normalizeTermDiagramStructurally
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagramStructurally tt convEnv tmCtx0 (TermDiagram diag) = do
  tmCtx <- normalizeCtxStructurally tt convEnv tmCtx0
  diag' <- normalizeDiagramLocal diag
  diag'' <- weakenDiagramTmCtxToModePrefix tmCtx diag'
  portObj' <- IM.traverseWithKey (\_ ty -> normalizeSortStructurally tt convEnv tmCtx ty) (dPortObj diag'')
  canon <- canonDiagramRaw diag'' { dTmCtx = tmCtx, dPortObj = portObj' }
  pure (TermDiagram canon)
  where
    normalizeDiagramLocal =
      traverseDiagram onDiag pure pure pure

    onDiag d = do
      dTmCtx' <- normalizeCtxStructurally tt convEnv (dTmCtx d)
      edges' <- IM.traverseWithKey (\_ edge -> normalizeEdge dTmCtx' edge) (dEdges d)
      portObj' <- IM.traverseWithKey (\_ ty -> normalizeSortStructurally tt convEnv dTmCtx' ty) (dPortObj d)
      pure d { dTmCtx = dTmCtx', dPortObj = portObj', dEdges = edges' }

    normalizeEdge tmCtx edge = do
      payload' <- normalizePayload tmCtx (ePayload edge)
      pure edge { ePayload = payload' }

    normalizePayload tmCtx payload =
      case payload of
        PGen g args bargs -> do
          args' <- traverse (normalizeCodeArg tmCtx) args
          pure (PGen g args' bargs)
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
          Right (CATm innerTm)

requireHeadSig :: TermConvEnv -> [Obj] -> Obj -> GenName -> [TermHeadArg] -> Either Text TmHeadSig
requireHeadSig convEnv tmCtx sortTy f args = do
  sortTy' <- tcNormalizeSort convEnv tmCtx sortTy
  sig <-
    case tcLookupSig convEnv (objOwnerMode sortTy') f of
      Nothing -> Left "termExprToDiagram: unknown term head"
      Just s -> Right s
  if length args /= length (thsParams sig) + length (thsInputs sig)
    then Left "termExprToDiagram: term head arity mismatch"
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
  -> Either Text ResolvedHeadArgs
resolveHeadArgsExpr tt convEnv tmCtx outerSubst currentSort f flatArgs = do
  sig0 <- requireHeadSig convEnv tmCtx currentSort f flatArgs
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
          }
    else Left "termExprToDiagram: term head result sort mismatch"
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
    TMGen f flatArgs -> do
      resolved <- resolveHeadArgsExpr tt convEnv tmCtx subst currentSort f flatArgs
      pure (TMGen f (resolvedHeadFlatArgs resolved))
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
instantiateMetaBody tmCtx v spine body = do
  let formal = defaultMetaArgs tmCtx v
      scope = tmvScope v
  if length formal == scope
    then Right ()
    else Left "termExprToDiagram: default-meta spine arity does not match scope"
  if length spine == scope
    then Right ()
    else
      Left
        ( "termExprToDiagram: occurrence spine arity mismatch for "
            <> tmvName v
            <> " (expected "
            <> T.pack (show scope)
            <> ", got "
            <> T.pack (show (length spine))
            <> ")"
        )
  let ren = M.fromList (zip formal spine)
  pure (renameTermGlobalsPartial ren body)

renameTermGlobalsPartial :: M.Map Int Int -> TermExpr -> TermExpr
renameTermGlobalsPartial ren tm =
  case tm of
    TMBound i -> TMBound (M.findWithDefault i i ren)
    TMMeta v args -> TMMeta v (map (\i -> M.findWithDefault i i ren) args)
    TMGen f args -> TMGen f (map renameHeadArg args)
    TMLit lit -> TMLit lit
  where
    renameHeadArg arg =
      case arg of
        THAObj obj -> THAObj obj
        THATm tm0 -> THATm (renameTermGlobalsPartial ren tm0)

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
