{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TermExpr
  ( TermExpr(..)
  , TermConvEnv(..)
  , termExprToDiagramWith
  , termExprToDiagram
  , diagramToTermExprWith
  , diagramToTermExpr
  , diagramGraphToTermExprWith
  , diagramGraphToTermExpr
  , validateTermGraph
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  ) where

import Control.Monad (foldM, forM, when)
import Data.List (elemIndex)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Term.AST
  ( TermExpr(..)
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  )
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , diagramPortObj
  , validateDiagram
  , unPortId
  , unEdgeId
  , setPortLabel
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( TermDiagram(..)
  , TmVar(..)
  , Obj(..)
  , objOwnerMode
  , modeCtxGlobals
  )
import Strat.Poly.TypeTheory
  ( TmFunSig(..)
  , TypeTheory
  , lookupTmFunSig
  )

data TermConvEnv = TermConvEnv
  { tcLookupSig :: ModeName -> GenName -> Maybe TmFunSig
  , tcSortEq :: [Obj] -> Obj -> Obj -> Either Text Bool
  }

termExprToDiagram
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagram tt =
  termExprToDiagramWith (structuralConvEnv tt)

termExprToDiagramWith
  :: TermConvEnv
  -> [Obj]
  -> Obj
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramWith convEnv tmCtx expectedSort tm = do
  let mode = objOwnerMode expectedSort
  let modeInputsAll = modeCtxEntries tmCtx mode
  needed <- requiredModePrefixLen tmCtx mode tm
  let modeInputs = take needed modeInputsAll
  let (inPorts, d0) = allocPorts (map snd modeInputs) (emptyDiagram mode tmCtx)
  d1 <- annotateInputs modeInputs inPorts d0
  let base = d1 { dIn = inPorts, dOut = [] }
  (root, d2) <- go modeInputs modeInputsAll inPorts base expectedSort tm
  let withOut = d2 { dOut = [root] }
  out <- saturateUnusedPrefixInputs withOut
  validateTermGraph out
  pure (TermDiagram out)
  where
    go modeInputs modeInputsAll inPorts diag currentSort currentTm =
      case currentTm of
        TMMeta v metaArgs -> do
          let vSort = tmvSort v
          ensureSortEq "termExprToDiagram: metavariable sort mismatch" vSort currentSort
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
            Just (pid, sortTy) ->
              do
                ensureSortEq "termExprToDiagram: bound term variable sort mismatch" sortTy currentSort
                pure (pid, diag)
        TMFun f args -> do
          sig <- requireFunSig convEnv tmCtx currentSort f args
          (argPorts, d1) <- foldM step ([], diag) (zip (tfsArgs sig) args)
          let (outPort, d2) = freshPort currentSort d1
          d3 <- addEdgePayload (PGen f M.empty []) argPorts [outPort] d2
          pure (outPort, d3)
      where
        step (ports, dAcc) (argSort, argTm) = do
          (argPort, dNext) <- go modeInputs modeInputsAll inPorts dAcc argSort argTm
          pure (ports <> [argPort], dNext)

    lookupMetaInput modeInputs inPorts globalTm =
      case elemIndex globalTm (map fst modeInputs) of
        Nothing ->
          Left
            ( "termExprToDiagram: metavariable argument index "
                <> T.pack (show globalTm)
                <> " not in mode-local context"
            )
        Just localIx ->
          case nth inPorts localIx of
            Nothing -> Left "termExprToDiagram: internal metavariable input mapping failure"
            Just pid -> Right pid

    annotateInputs modeInputs inPorts diag =
      foldM step diag (zip modeInputs inPorts)
      where
        step d ((globalTm, _), pid) =
          setPortLabel pid ("tmctx:" <> T.pack (show globalTm)) d

    ensureSortEq err lhs rhs = do
      ok <- tcSortEq convEnv tmCtx lhs rhs
      if ok
        then Right ()
        else Left err

diagramToTermExprWith
  :: TermConvEnv
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprWith convEnv tmCtx expectedSort (TermDiagram diag) =
  diagramGraphToTermExprWith convEnv tmCtx expectedSort diag

diagramToTermExpr
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExpr tt =
  diagramToTermExprWith (structuralConvEnv tt)

diagramGraphToTermExpr
  :: TypeTheory
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExpr tt =
  diagramGraphToTermExprWith (structuralConvEnv tt)

diagramGraphToTermExprWith
  :: TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExprWith convEnv tmCtx expectedSort diag = do
  validateTermGraph diag
  let mode = objOwnerMode expectedSort
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
      outOk <- tcSortEq convEnv tmCtx outTy expectedSort
      if outOk
        then Right ()
        else Left "diagramToTermExpr: output sort mismatch"
      diagramGraphToTermExprCore diag
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
        case nth modeInputs localPos of
          Nothing -> Left "diagramToTermExpr: missing expected boundary input sort"
          Just (_, ty) -> Right ty
      actualTy <-
        case diagramPortObj diag pid of
          Nothing -> Left "diagramToTermExpr: missing boundary input sort"
          Just ty -> Right ty
      ok <- tcSortEq convEnv tmCtx actualTy expectedTy
      if ok
        then Right ()
        else Left "diagramToTermExpr: boundary input sort mismatch"

diagramGraphToTermExprCore
  :: Diagram
  -> Either Text TermExpr
diagramGraphToTermExprCore diag = do
  validateTermGraph diag
  case dOut diag of
    [outPort] -> termAt S.empty outPort
    _ -> Left "diagramToTermExpr: term diagram must have exactly one output"
  where
    modeInputs = modeCtxEntries (dTmCtx diag) (dMode diag)
    nIn = length (dIn diag)
    localToGlobal = map fst (take nIn modeInputs)
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    termAt seen pid =
      case M.lookup pid inMap of
        Just local ->
          case nth localToGlobal local of
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
                PGen gen attrs bargs
                  | M.null attrs && null bargs -> do
                      args <- mapM (termAt (S.insert pid seen)) (eIns producer)
                      Right (TMFun gen args)
                  | otherwise ->
                      Left "diagramToTermExpr: generator term node must not carry attrs or binder args"
                PTmMeta v ->
                  do
                    metaArgs <- mapM boundaryInputGlobal (eIns producer)
                    Right (TMMeta v metaArgs)
                _ ->
                  Left "diagramToTermExpr: non-term payload in term diagram"
    boundaryInputGlobal pid =
      case M.lookup pid inMap of
        Nothing ->
          Left "diagramToTermExpr: PTmMeta inputs must connect to boundary inputs"
        Just local ->
          case nth localToGlobal local of
            Nothing -> Left "diagramToTermExpr: invalid boundary input mapping"
            Just globalTm -> Right globalTm
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
        case nth modeInputs0 localPos of
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
        PGen _ attrs bargs ->
          if M.null attrs && null bargs
            then Right ()
            else Left "validateTermDiagram: term generator nodes cannot have attrs or binder args"
        PTmMeta _ ->
          if all (`elem` dIn diag) (eIns edge)
            then Right ()
            else Left "validateTermDiagram: PTmMeta inputs must be boundary ports"
        PInternalDrop -> Right ()
        _ -> Left "validateTermDiagram: only PGen/PTmMeta/PInternalDrop are allowed in term diagrams"

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
          case elemIndex globalTm globals of
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
  local <- elemIndex idx (map fst modeInputs)
  pid <- nth inPorts local
  (_, sortTy) <- nth modeInputs local
  pure (pid, sortTy)

modeCtxEntries :: [Obj] -> ModeName -> [(Int, Obj)]
modeCtxEntries tmCtx mode =
  [ (i, ty)
  | i <- modeCtxGlobals tmCtx mode
  , Just ty <- [nth tmCtx i]
  ]

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
              | otherwise ->
                  addEdgePayload PInternalDrop [pid] [] d
            _ -> Right d

structuralConvEnv :: TypeTheory -> TermConvEnv
structuralConvEnv tt =
  TermConvEnv
    { tcLookupSig = \mode f -> lookupTmFunSig tt mode f
    , tcSortEq = \_ a b -> Right (a == b)
    }

requireFunSig :: TermConvEnv -> [Obj] -> Obj -> GenName -> [TermExpr] -> Either Text TmFunSig
requireFunSig convEnv tmCtx sortTy f args = do
  sig <-
    case tcLookupSig convEnv (objOwnerMode sortTy) f of
      Nothing -> Left "termExprToDiagram: unknown term function"
      Just s -> Right s
  if length (tfsArgs sig) /= length args
    then Left "termExprToDiagram: term function arity mismatch"
    else Right ()
  ok <- tcSortEq convEnv tmCtx (tfsRes sig) sortTy
  if ok
    then Right sig
    else Left "termExprToDiagram: term function result sort mismatch"

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
