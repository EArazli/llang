{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Rewrite
  ( RewriteRule(..)
  , rewriteOnce
  , rewriteAll
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
import Strat.Poly.UnifyTy
import Strat.Poly.Cell2
import Strat.Kernel.Types (Orientation(..))
import Strat.Poly.Doctrine (Doctrine(..))


data RewriteRule = RewriteRule
  { rrName   :: Text
  , rrLHS    :: Diagram
  , rrRHS    :: Diagram
  , rrTyVars :: [TyVar]
  } deriving (Eq, Show)

rewriteOnce :: [RewriteRule] -> Diagram -> Either Text (Maybe Diagram)
rewriteOnce rules diag = go rules
  where
    go [] = Right Nothing
    go (r:rs) = do
      if dMode (rrLHS r) /= dMode diag
        then go rs
        else do
          mMatch <- findFirstMatchNoDoc (rrLHS r) diag
          case mMatch of
            Nothing -> go rs
            Just match -> do
              diag' <- applyMatch r match diag
              pure (Just (canonicalizeDiagram diag'))

rewriteAll :: Int -> [RewriteRule] -> Diagram -> Either Text [Diagram]
rewriteAll cap rules diag = do
  results <- go [] rules
  pure (take cap results)
  where
    go acc [] = Right acc
    go acc (r:rs) = do
      if dMode (rrLHS r) /= dMode diag
        then go acc rs
        else do
          matches <- findAllMatchesNoDoc (rrLHS r) diag
          let diags = [ applyMatch r m diag | m <- matches ]
          applied <- sequence diags
          go (acc <> map canonicalizeDiagram applied) rs

-- no doctrine needed for matching at the moment

applyMatch :: RewriteRule -> Match -> Diagram -> Either Text Diagram
applyMatch rule match host = do
  let lhs = rrLHS rule
  let rhs = applySubstDiagram (mTySub match) (rrRHS rule)
  host1 <- deleteMatchedEdges host (M.elems (mEdges match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPorts match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  let host3 = insertDiagram host2 rhsShift
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

insertDiagram :: Diagram -> Diagram -> Diagram
insertDiagram base extra =
  base
    { dPortTy = IM.union (dPortTy base) (dPortTy extra)
    , dProd = IM.union (dProd base) (dProd extra)
    , dCons = IM.union (dCons base) (dCons extra)
    , dEdges = IM.union (dEdges base) (dEdges extra)
    , dNextPort = dNextPort extra
    , dNextEdge = dNextEdge extra
    }

rulesFromDoctrine :: Doctrine -> [RewriteRule]
rulesFromDoctrine doc = concatMap fromCell (dCells2 doc)
  where
    fromCell cell =
      case c2Orient cell of
        LR -> [mkRule cell (c2LHS cell) (c2RHS cell)]
        RL -> [mkRule cell (c2RHS cell) (c2LHS cell)]
        Bidirectional -> [mkRule cell (c2LHS cell) (c2RHS cell), mkRule cell (c2RHS cell) (c2LHS cell)]
        Unoriented -> []
    mkRule cell lhs rhs =
      RewriteRule
        { rrName = c2Name cell
        , rrLHS = lhs
        , rrRHS = rhs
        , rrTyVars = c2TyVars cell
        }
