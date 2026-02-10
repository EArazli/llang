{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Rewrite
  ( RewriteRule(..)
  , rewriteOnce
  , rewriteAll
  , rulesFromPolicy
  , rulesFromDoctrine
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Match
import Strat.Poly.TypeExpr (TyVar, TypeExpr)
import Strat.Poly.Cell2
import Strat.Poly.UnifyTy (emptySubst)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (Orientation(..), RuleClass(..))
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory (ModeTheory)


data RewriteRule = RewriteRule
  { rrName   :: Text
  , rrLHS    :: Diagram
  , rrRHS    :: Diagram
  , rrTyVars :: [TyVar]
  } deriving (Eq, Show)

rewriteOnce :: ModeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnce mt rules diag = do
  rejectSplice "rewriteOnce" diag
  top <- rewriteOnceTop mt UseAllOriented rules diag
  case top of
    Just _ -> pure top
    Nothing -> rewriteOnceNested mt rules diag

rewriteOnceTop :: ModeTheory -> RewritePolicy -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceTop mt _policy rules diag = go rules
  where
    go [] = Right Nothing
    go (r:rs) = do
      if dMode (rrLHS r) /= dMode diag
        then go rs
        else do
          rejectSplice "rewrite rule lhs" (rrLHS r)
          matches <- findAllMatchesWithTyVars mt (S.fromList (rrTyVars r)) (rrLHS r) diag
          tryMatches matches
      where
        tryMatches [] = go rs
        tryMatches (m:ms) =
          case applyMatch mt r m diag of
            Left _ -> tryMatches ms
            Right d -> do
              canon <- renumberDiagram d
              pure (Just canon)

rewriteOnceNested :: ModeTheory -> [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceNested mt rules diag =
  go (IM.toAscList (dEdges diag))
  where
    go [] = Right Nothing
    go ((edgeKey, edge):rest) =
      case ePayload edge of
        PSplice _ -> Left "rewriteOnce: splice nodes are not allowed in evaluation terms"
        PBox name inner -> do
          innerRes <- rewriteOnce mt rules inner
          case innerRes of
            Nothing -> go rest
            Just inner' -> do
              let edge' = edge { ePayload = PBox name inner' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              canon <- renumberDiagram diag'
              pure (Just canon)
        PGen gen attrs bargs -> do
          bargRes <- rewriteOnceBinderArgs bargs
          case bargRes of
            Nothing -> go rest
            Just bargs' -> do
              let edge' = edge { ePayload = PGen gen attrs bargs' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              canon <- renumberDiagram diag'
              pure (Just canon)

    rewriteOnceBinderArgs [] = Right Nothing
    rewriteOnceBinderArgs (b:bs) =
      case b of
        BAMeta _ -> rewriteOnceBinderArgs bs
        BAConcrete inner -> do
          res <- rewriteOnce mt rules inner
          case res of
            Just inner' -> Right (Just (BAConcrete inner' : bs))
            Nothing -> do
              rest <- rewriteOnceBinderArgs bs
              pure (fmap (b :) rest)

rewriteAll :: ModeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAll mt cap rules diag = do
  rejectSplice "rewriteAll" diag
  top <- rewriteAllTop mt rules diag
  inner <- rewriteAllNested mt cap rules diag
  pure (take cap (top <> inner))
  where
    rewriteAllTop mt' rules' diag' = go [] rules'
      where
        go acc [] = Right acc
        go acc (r:rs) = do
          if dMode (rrLHS r) /= dMode diag'
            then go acc rs
            else do
              matches <- findAllMatchesWithTyVars mt' (S.fromList (rrTyVars r)) (rrLHS r) diag'
              applied <- foldl collect (Right []) matches
              canon <- mapM renumberDiagram applied
              go (acc <> canon) rs
          where
            collect acc m =
              case acc of
                Left err -> Left err
                Right ds ->
                  case applyMatch mt' r m diag' of
                    Left _ -> Right ds
                    Right d -> Right (ds <> [d])

rewriteAllNested :: ModeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAllNested mt cap rules diag = do
  let edges = IM.toAscList (dEdges diag)
  fmap concat (mapM (rewriteInEdge mt cap rules diag) edges)

rewriteInEdge :: ModeTheory -> Int -> [RewriteRule] -> Diagram -> (Int, Edge) -> Either Text [Diagram]
rewriteInEdge mt cap rules diag (edgeKey, edge) =
  case ePayload edge of
    PSplice _ -> Left "rewriteAll: splice nodes are not allowed in evaluation terms"
    PBox name inner -> do
      innerRes <- rewriteAll mt cap rules inner
      mapM
        (\d -> do
          let edge' = edge { ePayload = PBox name d }
          let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
          renumberDiagram diag')
        innerRes
    PGen gen attrs bargs -> do
      bargsRes <- rewriteAllBinderArgs mt cap rules bargs
      mapM
        (\bargs' -> do
          let edge' = edge { ePayload = PGen gen attrs bargs' }
          let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
          renumberDiagram diag')
        bargsRes

rewriteAllBinderArgs :: ModeTheory -> Int -> [RewriteRule] -> [BinderArg] -> Either Text [[BinderArg]]
rewriteAllBinderArgs _ _ _ [] = Right []
rewriteAllBinderArgs mt cap rules args =
  fmap concat (mapM rewriteAt [0 .. length args - 1])
  where
    rewriteAt i =
      case splitAt i args of
        (pre, BAConcrete inner : post) -> do
          res <- rewriteAll mt cap rules inner
          pure [pre <> [BAConcrete inner'] <> post | inner' <- res]
        _ -> Right []

applyMatch :: ModeTheory -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatch mt rule match host = do
  rejectSplice "rewrite host" host
  -- Normalize host boundary types before gluing so mergePorts compares
  -- canonicalized types (e.g. after modality equations).
  let hostNorm = applySubstDiagram mt emptySubst host
  let lhs = rrLHS rule
  let rhs0 = applyAttrSubstDiagram (mAttrSubst match) (applySubstDiagram mt (mTySubst match) (rrRHS rule))
  rhs1 <- instantiateBinderMetas (mBinderSub match) rhs0
  rhs <- expandSplices (mBinderSub match) rhs1
  host1 <- deleteMatchedEdges hostNorm (M.elems (mEdgeMap match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPortMap match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  host3 <- insertDiagram host2 rhsShift
  let lhsBoundary = dIn lhs <> dOut lhs
  let rhsBoundary = dIn rhsShift <> dOut rhsShift
  if length lhsBoundary /= length rhsBoundary
    then Left "rewriteOnce: boundary length mismatch"
    else do
      (host4, _) <- foldl step (Right (host3, M.empty)) (zip lhsBoundary rhsBoundary)
      validateDiagram host4
      pure host4
  where
    step acc (lhsPort, rhsPort) = do
      (diag, seen) <- acc
      hostPort <-
        case M.lookup lhsPort (mPortMap match) of
          Nothing -> Left "rewriteOnce: missing boundary port mapping"
          Just p -> Right p
      case M.lookup rhsPort seen of
        Nothing -> do
          diag' <- mergePorts diag hostPort rhsPort
          pure (diag', M.insert rhsPort hostPort seen)
        Just hostPort' -> do
          diag' <- mergePorts diag hostPort' hostPort
          pure (diag', seen)

instantiateBinderMetas :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
instantiateBinderMetas binderSub diag =
  fmap (\edges' -> diag { dEdges = edges' }) (traverseEdges (dEdges diag))
  where
    traverseEdges edges =
      fmap IM.fromList
        (mapM
          (\(k, edge) -> do
            payload' <- traversePayload (ePayload edge)
            pure (k, edge { ePayload = payload' }))
          (IM.toList edges))

    traversePayload payload =
      case payload of
        PBox name inner -> PBox name <$> instantiateBinderMetas binderSub inner
        PSplice x -> Right (PSplice x)
        PGen gen attrs bargs -> do
          bargs' <- mapM traverseBinderArg bargs
          Right (PGen gen attrs bargs')

    traverseBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> instantiateBinderMetas binderSub inner
        BAMeta x ->
          case M.lookup x binderSub of
            Nothing -> Left "rewriteOnce: RHS uses uncaptured binder meta"
            Just captured -> Right (BAConcrete captured)

expandSplices :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
expandSplices binderSub diag0 = do
  diag1 <- recurseEdges diag0
  expandTop diag1
  where
    recurseEdges diag = do
      edges' <-
        fmap IM.fromList
          (mapM
            (\(k, edge) -> do
              payload' <- recursePayload (ePayload edge)
              pure (k, edge { ePayload = payload' }))
            (IM.toList (dEdges diag)))
      pure diag { dEdges = edges' }

    recursePayload payload =
      case payload of
        PBox name inner -> PBox name <$> expandSplices binderSub inner
        PSplice x -> Right (PSplice x)
        PGen gen attrs bargs -> do
          bargs' <- mapM recurseBinderArg bargs
          Right (PGen gen attrs bargs')

    recurseBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> expandSplices binderSub inner
        BAMeta x -> Right (BAMeta x)

    expandTop diag =
      case findSpliceEdge diag of
        Nothing -> Right diag
        Just (edgeKey, edge, x) -> do
          captured <-
            case M.lookup x binderSub of
              Nothing -> Left "rewriteOnce: splice uses uncaptured binder meta"
              Just d -> Right d
          if dIxCtx captured /= dIxCtx diag
            then Left "rewriteOnce: splice index-context mismatch"
            else Right ()
          domSplice <- mapM (requirePortType diag) (eIns edge)
          codSplice <- mapM (requirePortType diag) (eOuts edge)
          domCaptured <- mapM (requirePortType captured) (dIn captured)
          codCaptured <- mapM (requirePortType captured) (dOut captured)
          if domSplice /= domCaptured || codSplice /= codCaptured
            then Left "rewriteOnce: splice boundary mismatch"
            else Right ()
          diagNoEdge <- deleteEdgeKeepPorts diag edgeKey edge
          let capturedShift = shiftDiagram (dNextPort diagNoEdge) (dNextEdge diagNoEdge) captured
          diagInserted <- insertDiagram diagNoEdge capturedShift
          let splicePairs = zip (eIns edge) (dIn capturedShift) <> zip (eOuts edge) (dOut capturedShift)
          (diagMerged, _) <- foldl mergePair (Right (diagInserted, M.empty)) splicePairs
          validateDiagram diagMerged
          expandTop diagMerged

    mergePair acc (hostPort, capturedPort) = do
      (d, seen) <- acc
      case M.lookup capturedPort seen of
        Nothing -> do
          d' <- mergePorts d hostPort capturedPort
          pure (d', M.insert capturedPort hostPort seen)
        Just mappedHostPort -> do
          d' <- mergePorts d mappedHostPort hostPort
          pure (d', seen)

findSpliceEdge :: Diagram -> Maybe (Int, Edge, BinderMetaVar)
findSpliceEdge diag =
  case
    [ (k, edge, x)
    | (k, edge) <- IM.toAscList (dEdges diag)
    , PSplice x <- [ePayload edge]
    ]
    of
      [] -> Nothing
      (x:_) -> Just x

deleteEdgeKeepPorts :: Diagram -> Int -> Edge -> Either Text Diagram
deleteEdgeKeepPorts diag edgeKey edge = do
  let diag1 = diag { dEdges = IM.delete edgeKey (dEdges diag) }
  let diag2 = clearConsumers diag1 (eIns edge)
  let diag3 = clearProducers diag2 (eOuts edge)
  pure diag3
  where
    clearConsumers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
       in d { dCons = foldl clearOne (dCons d) ports }

    clearProducers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
       in d { dProd = foldl clearOne (dProd d) ports }

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "rewriteOnce: missing port type"
    Just ty -> Right ty

internalPorts :: Diagram -> [PortId]
internalPorts diag =
  let allPorts = S.fromList (diagramPortIds diag)
      boundary = S.fromList (dIn diag <> dOut diag)
   in S.toList (S.difference allPorts boundary)

deleteMatchedEdges :: Diagram -> [EdgeId] -> Either Text Diagram
deleteMatchedEdges diag edgeIds = foldl step (Right diag) edgeIds
  where
    step acc eid = do
      d <- acc
      case IM.lookup (edgeKey eid) (dEdges d) of
        Nothing -> Left "rewriteOnce: missing edge"
        Just edge -> do
          let d1 = d { dEdges = IM.delete (edgeKey eid) (dEdges d) }
          let d2 = clearConsumers d1 (eIns edge)
          let d3 = clearProducers d2 (eOuts edge)
          pure d3

    edgeKey (EdgeId k) = k

    clearConsumers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
       in d { dCons = foldl clearOne (dCons d) ports }

    clearProducers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
       in d { dProd = foldl clearOne (dProd d) ports }

deleteMatchedPorts :: Diagram -> [PortId] -> M.Map PortId PortId -> Either Text Diagram
deleteMatchedPorts diag ports portMap = foldl step (Right diag) ports
  where
    step acc p = do
      d <- acc
      case M.lookup p portMap of
        Nothing -> Left "rewriteOnce: missing port mapping"
        Just hostPort -> deletePort d hostPort

deletePort :: Diagram -> PortId -> Either Text Diagram
deletePort diag pid =
  let k = portKey pid
      portKey (PortId n) = n
   in case (IM.lookup k (dProd diag), IM.lookup k (dCons diag)) of
        (Just Nothing, Just Nothing) ->
          let d1 =
                diag
                  { dPortTy = IM.delete k (dPortTy diag)
                  , dPortLabel = IM.delete k (dPortLabel diag)
                  , dProd = IM.delete k (dProd diag)
                  , dCons = IM.delete k (dCons diag)
                  , dIn = filter (/= pid) (dIn diag)
                  , dOut = filter (/= pid) (dOut diag)
                  }
           in Right d1
        _ -> Left "rewriteOnce: cannot delete port with remaining incidence"

insertDiagram :: Diagram -> Diagram -> Either Text Diagram
insertDiagram base extra = do
  portTy <- unionDisjointIntMap "insertDiagram ports" (dPortTy base) (dPortTy extra)
  portLabel <- unionDisjointIntMap "insertDiagram labels" (dPortLabel base) (dPortLabel extra)
  prod <- unionDisjointIntMap "insertDiagram producers" (dProd base) (dProd extra)
  cons <- unionDisjointIntMap "insertDiagram consumers" (dCons base) (dCons extra)
  edges <- unionDisjointIntMap "insertDiagram edges" (dEdges base) (dEdges extra)
  pure
    base
      { dPortTy = portTy
      , dPortLabel = portLabel
      , dProd = prod
      , dCons = cons
      , dEdges = edges
      , dNextPort = dNextPort extra
      , dNextEdge = dNextEdge extra
      }

rulesFromDoctrine :: Doctrine -> [RewriteRule]
rulesFromDoctrine doc = rulesFromPolicy UseAllOriented (dCells2 doc)

rulesFromPolicy :: RewritePolicy -> [Cell2] -> [RewriteRule]
rulesFromPolicy policy cells = concatMap (rulesForCell policy) cells

rulesForCell :: RewritePolicy -> Cell2 -> [RewriteRule]
rulesForCell policy cell =
  case policy of
    UseStructuralAsBidirectional ->
      case c2Class cell of
        Structural -> both
        Computational -> oriented
    UseOnlyComputationalLR ->
      case c2Class cell of
        Computational ->
          case c2Orient cell of
            LR -> [mk (c2LHS cell) (c2RHS cell)]
            Bidirectional -> [mk (c2LHS cell) (c2RHS cell)]
            _ -> []
        Structural -> []
    UseAllOriented -> oriented
  where
    mk lhs rhs =
      RewriteRule
        { rrName = c2Name cell
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = c2TyVars cell
        }

    oriented =
      case c2Orient cell of
        LR -> [mk (c2LHS cell) (c2RHS cell)]
        RL -> [mk (c2RHS cell) (c2LHS cell)]
        Bidirectional -> [mk (c2LHS cell) (c2RHS cell), mk (c2RHS cell) (c2LHS cell)]
        Unoriented -> []

    both =
      [ mk (c2LHS cell) (c2RHS cell)
      , mk (c2RHS cell) (c2LHS cell)
      ]

rejectSplice :: Text -> Diagram -> Either Text ()
rejectSplice label diag =
  if hasSplice diag
    then Left (label <> ": splice nodes are not allowed in evaluation terms")
    else Right ()

hasSplice :: Diagram -> Bool
hasSplice diag =
  any edgeHasSplice (IM.elems (dEdges diag))
  where
    edgeHasSplice edge =
      case ePayload edge of
        PSplice _ -> True
        PBox _ inner -> hasSplice inner
        PGen _ _ bargs -> any binderHasSplice bargs

    binderHasSplice barg =
      case barg of
        BAConcrete inner -> hasSplice inner
        BAMeta _ -> False
