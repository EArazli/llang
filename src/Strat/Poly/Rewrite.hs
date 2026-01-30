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
import Strat.Poly.TypeExpr (TyVar)
import Strat.Poly.Cell2
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (Orientation(..), RuleClass(..))
import Strat.Poly.Doctrine (Doctrine(..))


data RewriteRule = RewriteRule
  { rrName   :: Text
  , rrLHS    :: Diagram
  , rrRHS    :: Diagram
  , rrTyVars :: [TyVar]
  } deriving (Eq, Show)

rewriteOnce :: [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnce rules diag = do
  top <- rewriteOnceTop rules diag
  case top of
    Just _ -> pure top
    Nothing -> rewriteOnceInBoxes rules diag

rewriteOnceTop :: [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceTop rules diag = go rules
  where
    go [] = Right Nothing
    go (r:rs) = do
      if dMode (rrLHS r) /= dMode diag
        then go rs
        else do
          matches <- findAllMatchesWithTyVars (S.fromList (rrTyVars r)) (rrLHS r) diag
          tryMatches matches
      where
        tryMatches [] = go rs
        tryMatches (m:ms) =
          case applyMatch r m diag of
            Left _ -> tryMatches ms
            Right d -> do
              canon <- renumberDiagram d
              pure (Just canon)

rewriteOnceInBoxes :: [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnceInBoxes rules diag =
  go (IM.toAscList (dEdges diag))
  where
    go [] = Right Nothing
    go ((edgeKey, edge):rest) =
      case ePayload edge of
        PGen _ -> go rest
        PBox name inner -> do
          innerRes <- rewriteOnce rules inner
          case innerRes of
            Nothing -> go rest
            Just inner' -> do
              let edge' = edge { ePayload = PBox name inner' }
              let diag' = diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
              canon <- renumberDiagram diag'
              pure (Just canon)

rewriteAll :: Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAll cap rules diag = do
  top <- rewriteAllTop rules diag
  inner <- rewriteAllInBoxes cap rules diag
  pure (take cap (top <> inner))
  where
    rewriteAllTop rules' diag' = go [] rules'
      where
        go acc [] = Right acc
        go acc (r:rs) = do
          if dMode (rrLHS r) /= dMode diag'
            then go acc rs
            else do
              matches <- findAllMatchesWithTyVars (S.fromList (rrTyVars r)) (rrLHS r) diag'
              applied <- foldl collect (Right []) matches
              canon <- mapM renumberDiagram applied
              go (acc <> canon) rs
          where
            collect acc m =
              case acc of
                Left err -> Left err
                Right ds ->
                  case applyMatch r m diag' of
                    Left _ -> Right ds
                    Right d -> Right (ds <> [d])
    rewriteAllInBoxes cap' rules' diag' = do
      let edges = IM.toAscList (dEdges diag')
      fmap concat (mapM (rewriteInEdge cap' rules' diag') edges)
    rewriteInEdge cap' rules' diag' (edgeKey, edge) =
      case ePayload edge of
        PGen _ -> Right []
        PBox name inner -> do
          innerRes <- rewriteAll cap' rules' inner
          mapM
            (\d -> do
              let edge' = edge { ePayload = PBox name d }
              let diag'' = diag' { dEdges = IM.insert edgeKey edge' (dEdges diag') }
              renumberDiagram diag'')
            innerRes

-- no doctrine needed for matching at the moment

applyMatch :: RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatch rule match host = do
  let lhs = rrLHS rule
  let rhs = applySubstDiagram (mTySub match) (rrRHS rule)
  host1 <- deleteMatchedEdges host (M.elems (mEdges match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPorts match)
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
      hostPort <- case M.lookup lhsPort (mPorts match) of
        Nothing -> Left "rewriteOnce: missing boundary port mapping"
        Just p -> Right p
      case M.lookup rhsPort seen of
        Nothing -> do
          diag' <- mergePorts diag hostPort rhsPort
          pure (diag', M.insert rhsPort hostPort seen)
        Just hostPort' -> do
          diag' <- mergePorts diag hostPort' hostPort
          pure (diag', seen)

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
          mp = dCons d
      in d { dCons = foldl clearOne mp ports }
    clearProducers d ports =
      let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
          portKey (PortId k) = k
          mp = dProd d
      in d { dProd = foldl clearOne mp ports }

deleteMatchedPorts :: Diagram -> [PortId] -> M.Map PortId PortId -> Either Text Diagram
deleteMatchedPorts diag ports portMap = foldl step (Right diag) ports
  where
    step acc p = do
      d <- acc
      case M.lookup p portMap of
        Nothing -> Left "rewriteOnce: missing port mapping"
        Just hostPort -> deletePort d hostPort

deletePort diag pid =
  let k = portKey pid
      portKey (PortId n) = n
  in case (IM.lookup k (dProd diag), IM.lookup k (dCons diag)) of
      (Just Nothing, Just Nothing) ->
        let d1 = diag
              { dPortTy = IM.delete k (dPortTy diag)
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
  prod <- unionDisjointIntMap "insertDiagram producers" (dProd base) (dProd extra)
  cons <- unionDisjointIntMap "insertDiagram consumers" (dCons base) (dCons extra)
  edges <- unionDisjointIntMap "insertDiagram edges" (dEdges base) (dEdges extra)
  pure base
    { dPortTy = portTy
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
