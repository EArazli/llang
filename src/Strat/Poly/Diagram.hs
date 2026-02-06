{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Diagram
  ( Diagram(..)
  , idD
  , genD
  , genDWithAttrs
  , compD
  , tensorD
  , diagramDom
  , diagramCod
  , applySubstDiagram
  , applyAttrSubstDiagram
  , freeTyVarsDiagram
  , freeAttrVarsDiagram
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (Context, TypeExpr(..), TyVar)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar, freeAttrVarsMap, applyAttrSubstMap)
import Strat.Poly.UnifyTy


idD :: ModeName -> Context -> Diagram
idD mode ctx =
  let (ports, diag') = allocPorts ctx (emptyDiagram mode)
  in diag'
      { dIn = ports
      , dOut = ports
      }

genD :: ModeName -> Context -> Context -> GenName -> Either Text Diagram
genD mode dom cod gen =
  genDWithAttrs mode dom cod gen M.empty

genDWithAttrs :: ModeName -> Context -> Context -> GenName -> AttrMap -> Either Text Diagram
genDWithAttrs mode dom cod gen attrs = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode)
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- case addEdgePayload (PGen gen attrs) inPorts outPorts diag2 of
    Left err -> Left ("genD " <> renderGen gen <> ": " <> err)
    Right d -> Right d
  let diagFinal = diag3 { dIn = inPorts, dOut = outPorts }
  validateDiagram diagFinal
  pure diagFinal

renderGen :: GenName -> Text
renderGen (GenName t) = t

compD :: Diagram -> Diagram -> Either Text Diagram
compD g f
  | dMode g /= dMode f = Left "diagram composition mode mismatch"
  | otherwise = do
      domG <- diagramDom g
      codF <- diagramCod f
      subst <- case unifyCtx codF domG of
        Left err -> Left ("diagram composition boundary mismatch: " <> err)
        Right s -> Right s
      let f' = applySubstDiagram subst f
      let g' = applySubstDiagram subst g
      let gShift = shiftDiagram (dNextPort f') (dNextEdge f') g'
      merged <- unionDiagram f' gShift
      let merged' = merged { dIn = dIn f', dOut = dOut gShift }
      let outsF = dOut f'
      let insG = dIn gShift
      if length outsF /= length insG
        then Left "diagram composition boundary mismatch"
        else do
          merged'' <- foldl step (Right merged') (zip outsF insG)
          validateDiagram merged''
          pure merged''
  where
    step acc (pOut, pIn) = do
      d <- acc
      mergePorts d pOut pIn

tensorD :: Diagram -> Diagram -> Either Text Diagram
tensorD f g
  | dMode f /= dMode g = Left "diagram tensor mode mismatch"
  | otherwise = do
      let gShift = shiftDiagram (dNextPort f) (dNextEdge f) g
      merged <- unionDiagram f gShift
      let result = merged
            { dIn = dIn f <> dIn gShift
            , dOut = dOut f <> dOut gShift
            }
      validateDiagram result
      pure result

diagramDom :: Diagram -> Either Text Context
diagramDom diag = mapM (lookupPort "diagramDom") (dIn diag)
  where
    lookupPort label pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty
    portKey (PortId k) = k

diagramCod :: Diagram -> Either Text Context
diagramCod diag = mapM (lookupPort "diagramCod") (dOut diag)
  where
    lookupPort label pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty
    portKey (PortId k) = k

applySubstDiagram :: Subst -> Diagram -> Diagram
applySubstDiagram subst diag =
  let dPortTy' = IM.map (applySubstTy subst) (dPortTy diag)
      dEdges' = IM.map (mapEdgePayload subst) (dEdges diag)
  in diag { dPortTy = dPortTy', dEdges = dEdges' }

freeTyVarsDiagram :: Diagram -> S.Set TyVar
freeTyVarsDiagram diag =
  let portVars = S.fromList (concatMap varsInTy (IM.elems (dPortTy diag)))
      boxVars = S.unions
        [ freeTyVarsDiagram inner
        | edge <- IM.elems (dEdges diag)
        , PBox _ inner <- [ePayload edge]
        ]
  in S.union portVars boxVars

freeAttrVarsDiagram :: Diagram -> S.Set AttrVar
freeAttrVarsDiagram diag =
  let edgeVars = S.unions
        [ freeAttrVarsMap attrs
        | edge <- IM.elems (dEdges diag)
        , PGen _ attrs <- [ePayload edge]
        ]
      boxVars = S.unions
        [ freeAttrVarsDiagram inner
        | edge <- IM.elems (dEdges diag)
        , PBox _ inner <- [ePayload edge]
        ]
  in S.union edgeVars boxVars

varsInTy :: TypeExpr -> [TyVar]
varsInTy ty =
  case ty of
    TVar v -> [v]
    TCon _ args -> concatMap varsInTy args

mapEdgePayload :: Subst -> Edge -> Edge
mapEdgePayload subst edge =
  case ePayload edge of
    PGen g attrs -> edge { ePayload = PGen g attrs }
    PBox name inner -> edge { ePayload = PBox name (applySubstDiagram subst inner) }

applyAttrSubstDiagram :: AttrSubst -> Diagram -> Diagram
applyAttrSubstDiagram subst diag =
  let dEdges' = IM.map (mapEdgePayloadAttr subst) (dEdges diag)
  in diag { dEdges = dEdges' }

mapEdgePayloadAttr :: AttrSubst -> Edge -> Edge
mapEdgePayloadAttr subst edge =
  case ePayload edge of
    PGen g attrs -> edge { ePayload = PGen g (applyAttrSubstMap subst attrs) }
    PBox name inner -> edge { ePayload = PBox name (applyAttrSubstDiagram subst inner) }

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
  in (pid : pids, diag2)

unionDiagram :: Diagram -> Diagram -> Either Text Diagram
unionDiagram left right = do
  portTy <- unionDisjointIntMap "unionDiagram ports" (dPortTy left) (dPortTy right)
  prod <- unionDisjointIntMap "unionDiagram producers" (dProd left) (dProd right)
  cons <- unionDisjointIntMap "unionDiagram consumers" (dCons left) (dCons right)
  edges <- unionDisjointIntMap "unionDiagram edges" (dEdges left) (dEdges right)
  pure left
    { dPortTy = portTy
    , dProd = prod
    , dCons = cons
    , dEdges = edges
    , dNextPort = dNextPort right
    , dNextEdge = dNextEdge right
    }
