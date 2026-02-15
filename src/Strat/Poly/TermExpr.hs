{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TermExpr
  ( TermExpr(..)
  , TermConvEnv(..)
  , termExprToDiagramWith
  , termExprToDiagram
  , termExprToDiagramUnchecked
  , diagramToTermExprWith
  , diagramToTermExpr
  , diagramGraphToTermExprWith
  , diagramGraphToTermExpr
  , diagramGraphToTermExprUnchecked
  , validateTermGraph
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  , sameTmMetaId
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
  , sameTmMetaId
  )
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId(..)
  , addEdgePayload
  , emptyDiagram
  , freshPort
  , diagramPortType
  , validateDiagram
  , unPortId
  , unEdgeId
  , setPortLabel
  )
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr
  ( TermDiagram(..)
  , TmFunName(..)
  , TmVar(..)
  , TypeExpr(..)
  , typeMode
  )
import Strat.Poly.TypeTheory
  ( TmFunSig(..)
  , TypeTheory
  , lookupTmFunSig
  )

data TermConvEnv = TermConvEnv
  { tcLookupSig :: ModeName -> TmFunName -> Maybe TmFunSig
  , tcSortEq :: [TypeExpr] -> TypeExpr -> TypeExpr -> Either Text Bool
  }

termExprToDiagram
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagram tt =
  termExprToDiagramWith (uncheckedConvEnv tt)

termExprToDiagramUnchecked
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramUnchecked tt =
  termExprToDiagramWith (uncheckedConvEnv tt)

termExprToDiagramWith
  :: TermConvEnv
  -> [TypeExpr]
  -> TypeExpr
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagramWith convEnv tmCtx expectedSort tm = do
  let mode = typeMode expectedSort
  let modeInputsAll = modeCtx tmCtx mode
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
        TMVar v -> do
          let vSort = tmvSort v
          ensureSortEq "termExprToDiagramUnchecked: metavariable sort mismatch" vSort currentSort
          if tmvScope v <= length modeInputsAll
            then Right ()
            else Left "termExprToDiagramUnchecked: metavariable scope exceeds mode-local context"
          let v' = v { tmvSort = vSort }
          let (outPort, d1) = freshPort vSort diag
          d2 <- addEdgePayload (PTmMeta v') (take (tmvScope v') inPorts) [outPort] d1
          pure (outPort, d2)
        TMBound i ->
          case lookupBound modeInputs inPorts i of
            Nothing -> Left "termExprToDiagramUnchecked: bound term variable out of scope or wrong mode"
            Just (pid, sortTy) ->
              do
                ensureSortEq "termExprToDiagramUnchecked: bound term variable sort mismatch" sortTy currentSort
                pure (pid, diag)
        TMFun f args -> do
          sig <- requireFunSig convEnv tmCtx currentSort f args
          (argPorts, d1) <- foldM step ([], diag) (zip (tfsArgs sig) args)
          let (outPort, d2) = freshPort currentSort d1
          let TmFunName fname = f
          d3 <- addEdgePayload (PGen (GenName fname) M.empty []) argPorts [outPort] d2
          pure (outPort, d3)
      where
        step (ports, dAcc) (argSort, argTm) = do
          (argPort, dNext) <- go modeInputs modeInputsAll inPorts dAcc argSort argTm
          pure (ports <> [argPort], dNext)

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
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExprWith convEnv tmCtx expectedSort (TermDiagram diag) =
  diagramGraphToTermExprWith convEnv tmCtx expectedSort diag

diagramToTermExpr
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExpr tt =
  diagramToTermExprWith (uncheckedConvEnv tt)

diagramGraphToTermExpr
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExpr tt =
  diagramGraphToTermExprWith (uncheckedConvEnv tt)

diagramGraphToTermExprWith
  :: TermConvEnv
  -> [TypeExpr]
  -> TypeExpr
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExprWith convEnv tmCtx expectedSort diag = do
  validateTermGraph diag
  let mode = typeMode expectedSort
  if dMode diag == mode
    then Right ()
    else Left "diagramToTermExpr: mode mismatch"
  validateBoundaryMapping
  case dOut diag of
    [outPort] -> do
      outTy <-
        case diagramPortType diag outPort of
          Nothing -> Left "diagramToTermExpr: missing output port type"
          Just ty -> Right ty
      outOk <- tcSortEq convEnv tmCtx outTy expectedSort
      if outOk
        then Right ()
        else Left "diagramToTermExpr: output sort mismatch"
      diagramGraphToTermExprUnchecked diag
    _ -> Left "diagramToTermExpr: term diagram must have exactly one output"
  where
    modeInputs = modeCtx tmCtx (dMode diag)
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
        case diagramPortType diag pid of
          Nothing -> Left "diagramToTermExpr: missing boundary input sort"
          Just ty -> Right ty
      ok <- tcSortEq convEnv tmCtx actualTy expectedTy
      if ok
        then Right ()
        else Left "diagramToTermExpr: boundary input sort mismatch"

diagramGraphToTermExprUnchecked
  :: Diagram
  -> Either Text TermExpr
diagramGraphToTermExprUnchecked diag = do
  validateTermGraph diag
  case dOut diag of
    [outPort] -> termAt S.empty outPort
    _ -> Left "diagramToTermExprUnchecked: term diagram must have exactly one output"
  where
    modeInputs = modeCtx (dTmCtx diag) (dMode diag)
    nIn = length (dIn diag)
    localToGlobal = map fst (take nIn modeInputs)
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    termAt seen pid =
      case M.lookup pid inMap of
        Just local ->
          case nth localToGlobal local of
            Nothing -> Left "diagramToTermExprUnchecked: invalid boundary input mapping"
            Just globalTm -> Right (TMBound globalTm)
        Nothing ->
          if pid `S.member` seen
            then Left "diagramToTermExprUnchecked: cycle detected in term diagram"
            else do
              producer <-
                case IM.lookup (unPortId pid) (dProd diag) of
                  Just (Just eid) ->
                    case IM.lookup (unEdgeId eid) (dEdges diag) of
                      Nothing -> Left "diagramToTermExprUnchecked: producer edge missing"
                      Just edge -> Right edge
                  _ -> Left "diagramToTermExprUnchecked: missing producer"
              case ePayload producer of
                PGen (GenName gName) attrs bargs
                  | M.null attrs && null bargs -> do
                      args <- mapM (termAt (S.insert pid seen)) (eIns producer)
                      Right (TMFun (TmFunName gName) args)
                  | otherwise ->
                      Left "diagramToTermExprUnchecked: generator term node must not carry attrs or binder args"
                PTmMeta v ->
                  if eIns producer == take (tmvScope v) (dIn diag)
                    then Right (TMVar v)
                    else Left "diagramToTermExprUnchecked: PTmMeta inputs do not match canonical scope prefix"
                _ ->
                  Left "diagramToTermExprUnchecked: non-term payload in term diagram"
validateTermGraph :: Diagram -> Either Text ()
validateTermGraph diag = do
  validateDiagram diag
  case dOut diag of
    [_] -> Right ()
    _ -> Left "validateTermDiagram: term diagram must have exactly one output"
  let modeInputs0 = modeCtx (dTmCtx diag) (dMode diag)
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
        case diagramPortType diag pid of
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
        PTmMeta _ -> Right ()
        PInternalDrop -> Right ()
        _ -> Left "validateTermDiagram: only PGen/PTmMeta/PInternalDrop are allowed in term diagrams"

modeCtx :: [TypeExpr] -> ModeName -> [(Int, TypeExpr)]
modeCtx tele mode =
  [ (i, ty)
  | (i, ty) <- zip [0 :: Int ..] tele
  , typeMode ty == mode
  ]

requiredModePrefixLen :: [TypeExpr] -> ModeName -> TermExpr -> Either Text Int
requiredModePrefixLen tmCtx mode tm = do
  let modeInputsAll = modeCtx tmCtx mode
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

lookupBound :: [(Int, TypeExpr)] -> [PortId] -> Int -> Maybe (PortId, TypeExpr)
lookupBound modeInputs inPorts idx = do
  local <- elemIndex idx (map fst modeInputs)
  pid <- nth inPorts local
  (_, sortTy) <- nth modeInputs local
  pure (pid, sortTy)

allocPorts :: [TypeExpr] -> Diagram -> ([PortId], Diagram)
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

uncheckedConvEnv :: TypeTheory -> TermConvEnv
uncheckedConvEnv tt =
  TermConvEnv
    { tcLookupSig = \mode f -> lookupTmFunSig tt mode f
    , tcSortEq = \_ a b -> Right (a == b)
    }

requireFunSig :: TermConvEnv -> [TypeExpr] -> TypeExpr -> TmFunName -> [TermExpr] -> Either Text TmFunSig
requireFunSig convEnv tmCtx sortTy f args = do
  sig <-
    case tcLookupSig convEnv (typeMode sortTy) f of
      Nothing -> Left "termExprToDiagramUnchecked: unknown term function"
      Just s -> Right s
  if length (tfsArgs sig) /= length args
    then Left "termExprToDiagramUnchecked: term function arity mismatch"
    else Right ()
  ok <- tcSortEq convEnv tmCtx (tfsRes sig) sortTy
  if ok
    then Right sig
    else Left "termExprToDiagramUnchecked: term function result sort mismatch"

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
