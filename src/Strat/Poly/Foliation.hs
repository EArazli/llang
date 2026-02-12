{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Foliation
  ( SSA(..)
  , SSAStep(..)
  , foliate
  , forgetSSA
  , canonicalizeDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Char (isAlphaNum)
import Strat.Pipeline (FoliationPolicy(..), NamingPolicy(..))
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.Graph
  ( PortId(..)
  , EdgeId(..)
  , Edge(..)
  , EdgePayload(..)
  , BinderArg(..)
  , Diagram(..)
  , getPortLabel
  , renumberDiagram
  )
import Strat.Poly.Names (GenName, BoxName)
import Strat.Poly.Attr (AttrMap)
import Strat.Poly.ModeTheory (ModeName)


data SSA = SSA
  { ssaBaseDoctrine :: Text
  , ssaMode :: ModeName
  , ssaInputs :: [PortId]
  , ssaSteps :: [SSAStep]
  , ssaOutputs :: [PortId]
  , ssaPortNames :: M.Map PortId Text
  , ssaOriginal :: Diagram
  }
  deriving (Eq, Show)


data SSAStep
  = StepGen
      { stepEdgeId :: EdgeId
      , stepGen :: GenName
      , stepAttrs :: AttrMap
      , stepIns :: [PortId]
      , stepOuts :: [PortId]
      , stepBinders :: [SSA]
      }
  | StepBox
      { stepEdgeId :: EdgeId
      , stepBoxName :: BoxName
      , stepInner :: SSA
      , stepIns :: [PortId]
      , stepOuts :: [PortId]
      }
  | StepFeedback
      { stepEdgeId :: EdgeId
      , stepBody :: SSA
      , stepIns :: [PortId]
      , stepOuts :: [PortId]
      }
  deriving (Eq, Show)


foliate :: FoliationPolicy -> Doctrine -> ModeName -> Diagram -> Either Text SSA
foliate policy doc mode diag = do
  diag0 <- canonicalizeDiagram diag
  if mode /= dMode diag0
    then Left "foliate: mode mismatch"
    else Right ()
  if mode `S.member` dAcyclicModes doc
    then Right ()
    else Left "foliate: mode is not declared acyclic"
  ordered <- topoOrder diag0
  names <- assignPortNames policy diag0
  steps <- mapM mkStep ordered
  pure
    SSA
      { ssaBaseDoctrine = dName doc
      , ssaMode = mode
      , ssaInputs = dIn diag0
      , ssaSteps = steps
      , ssaOutputs = dOut diag0
      , ssaPortNames = names
      , ssaOriginal = diag0
      }
  where
    mkStep edge =
      case ePayload edge of
        PGen g attrs bargs -> do
          binders <- mapM foliateBinder bargs
          pure
            StepGen
              { stepEdgeId = eId edge
              , stepGen = g
              , stepAttrs = attrs
              , stepIns = eIns edge
              , stepOuts = eOuts edge
              , stepBinders = binders
              }
        PBox name inner -> do
          innerSSA <- foliate policy doc mode inner
          pure
            StepBox
              { stepEdgeId = eId edge
              , stepBoxName = name
              , stepInner = innerSSA
              , stepIns = eIns edge
              , stepOuts = eOuts edge
              }
        PFeedback body -> do
          bodySSA <- foliate policy doc mode body
          pure
            StepFeedback
              { stepEdgeId = eId edge
              , stepBody = bodySSA
              , stepIns = eIns edge
              , stepOuts = eOuts edge
              }
        PSplice _ -> Left "foliate: splice is not allowed in runtime diagrams"

    foliateBinder barg =
      case barg of
        BAConcrete inner -> foliate policy doc mode inner
        BAMeta _ -> Left "foliate: binder metavariable is not allowed in runtime diagrams"


topoOrder :: Diagram -> Either Text [Edge]
topoOrder diag =
  if IM.null edgeTable
    then Right []
    else if length orderedIds == IM.size edgeTable
      then mapM lookupEdge orderedIds
      else Left "foliate: diagram is cyclic"
  where
    edgeTable = dEdges diag
    edges = IM.elems edgeTable
    edgeIds = map eId edges

    deps0 = M.fromList [(eid, depsFor eid) | eid <- edgeIds]
    dependents = foldl insertDeps M.empty (M.toList deps0)

    insertDeps acc (eid, deps) =
      S.foldl' (\m dep -> M.insertWith S.union dep (S.singleton eid) m) acc deps

    depsFor eid =
      case findEdge eid of
        Nothing -> S.empty
        Just edge ->
          S.fromList
            [ prod
            | p <- eIns edge
            , Just (Just prod) <- [IM.lookup (portInt p) (dProd diag)]
            ]

    ready0 =
      S.fromList
        [ eid
        | (eid, deps) <- M.toList deps0
        , S.null deps
        ]

    orderedIds = go ready0 deps0 []

    go ready deps acc =
      case nextReady ready of
        Nothing -> reverse acc
        Just (eid, readyRest) ->
          let out = M.findWithDefault S.empty eid dependents
              (deps', ready') =
                S.foldl'
                  (dropDep eid)
                  (deps, readyRest)
                  out
           in go ready' deps' (eid : acc)

    dropDep done (deps, ready) target =
      let old = M.findWithDefault S.empty target deps
          new = S.delete done old
          deps' = M.insert target new deps
          ready' = if S.null new then S.insert target ready else ready
       in (deps', ready')

    nextReady ready =
      case S.lookupMin ready of
        Nothing -> Nothing
        Just eid -> Just (eid, S.deleteMin ready)

    findEdge eid =
      let EdgeId k = eid
       in IM.lookup k edgeTable

    lookupEdge eid =
      case findEdge eid of
        Nothing -> Left "foliate: internal missing edge"
        Just edge -> Right edge

    portInt (PortId i) = i


assignPortNames :: FoliationPolicy -> Diagram -> Either Text (M.Map PortId Text)
assignPortNames pol diag = go S.empty M.empty ordered
  where
    ordered = boundaryItems <> internalItems

    boundaryItems =
      zipWith (\i p -> (p, True, i)) [0 :: Int ..] boundaryOrder

    internalItems =
      zipWith (\i p -> (p, False, i)) [0 :: Int ..] internalOrder

    boundaryOrder = dedupePorts (dIn diag <> dOut diag)

    boundarySet = S.fromList boundaryOrder

    internalOrder =
      [ PortId k
      | k <- IM.keys (dPortTy diag)
      , PortId k `S.notMember` boundarySet
      ]

    go _ acc [] = Right acc
    go used acc ((p, isBoundary, i):ps)
      | M.member p acc = go used acc ps
      | otherwise = do
          base <-
            case fpNaming pol of
              BoundaryLabelsFirst ->
                if isBoundary
                  then
                    case getPortLabel diag p of
                      Just lbl | not (T.null lbl) -> Right (sanitize lbl)
                      _ -> Right ("p" <> T.pack (show i))
                  else
                    Right ("t" <> T.pack (show i))
          name <- uniqueName used base
          go (S.insert name used) (M.insert p name acc) ps

    sanitize txt =
      let mapped = T.map mapChar txt
       in if T.null mapped then "p" else mapped

    mapChar c = if isAlphaNum c || c == '_' then c else '_'

    uniqueName used base =
      if base `S.member` reserved
        then trySuffix 1
        else Right base
      where
        reserved = used `S.union` fpReserved pol

        trySuffix n =
          let candidate = base <> "_" <> T.pack (show n)
           in if candidate `S.member` reserved
                then trySuffix (n + 1)
                else Right candidate

    dedupePorts = goDedupe S.empty []
      where
        goDedupe _ acc [] = reverse acc
        goDedupe seen acc (p:ps)
          | p `S.member` seen = goDedupe seen acc ps
          | otherwise = goDedupe (S.insert p seen) (p : acc) ps


forgetSSA :: SSA -> Diagram
forgetSSA = ssaOriginal


canonicalizeDiagram :: Diagram -> Either Text Diagram
canonicalizeDiagram = renumberDiagram
