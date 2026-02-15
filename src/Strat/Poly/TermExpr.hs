{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TermExpr
  ( TermExpr(..)
  , termExprToDiagram
  , diagramToTermExpr
  , diagramGraphToTermExpr
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
import {-# SOURCE #-} Strat.Poly.TypeNormalize (normalizeTypeDeepWithCtx)
import Strat.Poly.TypeTheory
  ( TmFunSig(..)
  , TypeTheory
  , lookupTmFunSig
  )


data TermExpr
  = TMVar TmVar
  | TMBound Int
  | TMFun TmFunName [TermExpr]
  deriving (Eq, Ord, Show)

termExprToDiagram
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermExpr
  -> Either Text TermDiagram
termExprToDiagram tt tmCtx expectedSort tm = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  let mode = typeMode expectedSort'
  let modeInputsAll = modeCtx tmCtx mode
  needed <- requiredModePrefixLen tmCtx mode tm
  let modeInputs = take needed modeInputsAll
  let (inPorts, d0) = allocPorts (map snd modeInputs) (emptyDiagram mode tmCtx)
  d1 <- annotateInputs modeInputs inPorts d0
  let base = d1 { dIn = inPorts, dOut = [] }
  (root, d2) <- go modeInputs modeInputsAll inPorts base expectedSort' tm
  let withOut = d2 { dOut = [root] }
  out <- saturateUnusedPrefixInputs withOut
  validateTermGraph out
  pure (TermDiagram out)
  where
    go modeInputs modeInputsAll inPorts diag currentSort currentTm =
      case currentTm of
        TMVar v -> do
          let vSortRaw = tmvSort v
          vSort <- normalizeTypeDeepWithCtx tt tmCtx vSortRaw
          same <- sortsDefEq tt tmCtx currentSort vSort
          if same
            then Right ()
            else Left "termExprToDiagram: metavariable sort mismatch"
          if tmvScope v <= length modeInputsAll
            then Right ()
            else Left "termExprToDiagram: metavariable scope exceeds mode-local context"
          let v' = v { tmvSort = vSort }
          let (outPort, d1) = freshPort vSort diag
          d2 <- addEdgePayload (PTmMeta v') (take (tmvScope v') inPorts) [outPort] d1
          pure (outPort, d2)
        TMBound i ->
          case lookupBound modeInputs inPorts i of
            Nothing -> Left "termExprToDiagram: bound term variable out of scope or wrong mode"
            Just (pid, sortTy) -> do
              same <- sortsDefEq tt tmCtx currentSort sortTy
              if same
                then pure (pid, diag)
                else Left "termExprToDiagram: bound term variable sort mismatch"
        TMFun f args -> do
          sig <- requireFunSig tt tmCtx currentSort f args
          (argPorts, d1) <- foldM step ([], diag) (zip (tfsArgs sig) args)
          let (outPort, d2) = freshPort currentSort d1
          let TmFunName fname = f
          d3 <- addEdgePayload (PGen (GenName fname) M.empty []) argPorts [outPort] d2
          pure (outPort, d3)
      where
        step (ports, dAcc) (argSort, argTm) = do
          argSort' <- normalizeTypeDeepWithCtx tt tmCtx argSort
          (argPort, dNext) <- go modeInputs modeInputsAll inPorts dAcc argSort' argTm
          pure (ports <> [argPort], dNext)

    annotateInputs modeInputs inPorts diag =
      foldM step diag (zip modeInputs inPorts)
      where
        step d ((globalTm, _), pid) =
          setPortLabel pid ("tmctx:" <> T.pack (show globalTm)) d

diagramToTermExpr
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text TermExpr
diagramToTermExpr tt tmCtx expectedSort (TermDiagram diag) =
  diagramGraphToTermExpr tt tmCtx expectedSort diag

diagramGraphToTermExpr
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> Diagram
  -> Either Text TermExpr
diagramGraphToTermExpr tt tmCtx expectedSort diag = do
  validateTermGraph diag
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  let mode = typeMode expectedSort'
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
      same <- sortsDefEq tt tmCtx outTy expectedSort'
      if same
        then Right ()
        else Left "diagramToTermExpr: output sort mismatch"
      termAt S.empty inMap outPort
    _ -> Left "diagramToTermExpr: term diagram must have exactly one output"
  where
    modeInputs = modeCtx tmCtx (dMode diag)
    nIn = length (dIn diag)
    localToGlobal = map fst (take nIn modeInputs)
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])
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
      if actualTy == expectedTy
        then Right ()
        else Left "diagramToTermExpr: boundary input sort mismatch"

    termAt seen inMap0 pid =
      case M.lookup pid inMap0 of
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
                PGen (GenName gName) attrs bargs
                  | M.null attrs && null bargs -> do
                      args <- mapM (termAt (S.insert pid seen) inMap0) (eIns producer)
                      Right (TMFun (TmFunName gName) args)
                  | otherwise ->
                      Left "diagramToTermExpr: generator term node must not carry attrs or binder args"
                PTmMeta v ->
                  if eIns producer == take (tmvScope v) (dIn diag)
                    then Right (TMVar v)
                    else Left "diagramToTermExpr: PTmMeta inputs do not match canonical scope prefix"
                _ ->
                  Left "diagramToTermExpr: non-term payload in term diagram"
freeTmVarsExpr :: TermExpr -> S.Set TmVar
freeTmVarsExpr tm =
  case tm of
    TMVar v -> S.singleton v
    TMBound _ -> S.empty
    TMFun _ args -> S.unions (map freeTmVarsExpr args)

boundGlobalsExpr :: TermExpr -> S.Set Int
boundGlobalsExpr tm =
  case tm of
    TMVar _ -> S.empty
    TMBound i -> S.singleton i
    TMFun _ args -> S.unions (map boundGlobalsExpr args)

maxTmScopeExpr :: TermExpr -> Int
maxTmScopeExpr tm =
  case tm of
    TMVar v -> tmvScope v
    TMBound _ -> 0
    TMFun _ args -> maximum (0 : map maxTmScopeExpr args)

isPureMetaExpr :: TermExpr -> Bool
isPureMetaExpr tm =
  case tm of
    TMVar _ -> True
    TMBound _ -> False
    TMFun _ _ -> False

sameTmMetaId :: TmVar -> TmVar -> Bool
sameTmMetaId a b = tmvName a == tmvName b && tmvScope a == tmvScope b

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

sortsDefEq :: TypeTheory -> [TypeExpr] -> TypeExpr -> TypeExpr -> Either Text Bool
sortsDefEq tt tmCtx lhs rhs = do
  lhs' <- normalizeTypeDeepWithCtx tt tmCtx lhs
  rhs' <- normalizeTypeDeepWithCtx tt tmCtx rhs
  pure (lhs' == rhs')

requireFunSig :: TypeTheory -> [TypeExpr] -> TypeExpr -> TmFunName -> [TermExpr] -> Either Text TmFunSig
requireFunSig tt tmCtx sortTy f args = do
  sortTy' <- normalizeTypeDeepWithCtx tt tmCtx sortTy
  sig <-
    case lookupTmFunSig tt (typeMode sortTy') f of
      Nothing -> Left "termExprToDiagram: unknown term function"
      Just s -> Right s
  if length (tfsArgs sig) /= length args
    then Left "termExprToDiagram: term function arity mismatch"
    else Right ()
  sameSort <- sortsDefEq tt tmCtx (tfsRes sig) sortTy'
  if sameSort
    then Right sig
    else Left "termExprToDiagram: term function result sort mismatch"

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
