{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.GraphRead
  ( TermPortReader(..)
  , readTermPort
  , readTermOutput
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Poly.Graph (Diagram(..), Edge, PortId, unEdgeId, unPortId)
import Strat.Poly.Obj (Obj)

data TermPortReader a = TermPortReader
  { tprBoundaryLookup :: PortId -> Maybe Int
  , tprOnBoundary :: Obj -> Int -> PortId -> Either Text a
  , tprOnEdge :: (Obj -> PortId -> Either Text a) -> Obj -> PortId -> Edge -> Either Text a
  , tprSingleOutputErr :: Text
  , tprCycleErr :: Text
  , tprMissingProducerErr :: Text
  }

readTermOutput :: TermPortReader a -> Diagram -> Obj -> Either Text a
readTermOutput reader diag expectedSort =
  case dOut diag of
    [outPid] -> readTermPort reader diag expectedSort outPid
    _ -> Left (tprSingleOutputErr reader)

readTermPort :: TermPortReader a -> Diagram -> Obj -> PortId -> Either Text a
readTermPort reader diag = go S.empty
  where
    go seen currentSort pid =
      case tprBoundaryLookup reader pid of
        Just localIx ->
          tprOnBoundary reader currentSort localIx pid
        Nothing ->
          if pid `S.member` seen
            then Left (tprCycleErr reader)
            else do
              edge <- producerEdge pid
              let recur = go (S.insert pid seen)
              tprOnEdge reader recur currentSort pid edge

    producerEdge pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) ->
          case IM.lookup (unEdgeId eid) (dEdges diag) of
            Just edge -> Right edge
            Nothing -> Left (tprMissingProducerErr reader)
        _ -> Left (tprMissingProducerErr reader)
