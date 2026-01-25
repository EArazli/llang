{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Diagram
  ( Diagram(..)
  , idD
  , genD
  , compD
  , tensorD
  , diagramDom
  , diagramCod
  , applySubstDiagram
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Graph
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (Context)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.UnifyTy


idD :: ModeName -> Context -> Diagram
idD mode ctx =
  let (ports, diag') = allocPorts ctx (emptyDiagram mode)
  in diag'
      { dIn = ports
      , dOut = ports
      }

genD :: ModeName -> Context -> Context -> GenName -> Either Text Diagram
genD mode dom cod gen = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode)
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- case addEdge gen inPorts outPorts diag2 of
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
      let domG = diagramDom g
      let codF = diagramCod f
      subst <- case unifyCtx codF domG of
        Left err -> Left ("diagram composition boundary mismatch: " <> err)
        Right s -> Right s
      let f' = applySubstDiagram subst f
      let g' = applySubstDiagram subst g
      let gShift = shiftDiagram (dNextPort f') (dNextEdge f') g'
      let merged = (unionDiagram f' gShift) { dIn = dIn f', dOut = dOut gShift }
      let outsF = dOut f'
      let insG = dIn gShift
      if length outsF /= length insG
        then Left "diagram composition boundary mismatch"
        else do
          merged' <- foldl step (Right merged) (zip outsF insG)
          validateDiagram merged'
          pure merged'
  where
    step acc (pOut, pIn) = do
      d <- acc
      mergePorts d pOut pIn

tensorD :: Diagram -> Diagram -> Either Text Diagram
tensorD f g
  | dMode f /= dMode g = Left "diagram tensor mode mismatch"
  | otherwise = do
      let gShift = shiftDiagram (dNextPort f) (dNextEdge f) g
      let merged = unionDiagram f gShift
      let result = merged
            { dIn = dIn f <> dIn gShift
            , dOut = dOut f <> dOut gShift
            }
      validateDiagram result
      pure result

diagramDom :: Diagram -> Context
diagramDom diag = map (lookupPort "diagramDom") (dIn diag)
  where
    lookupPort label pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> error (label <> ": missing port type")
        Just ty -> ty
    portKey (PortId k) = k

diagramCod :: Diagram -> Context
diagramCod diag = map (lookupPort "diagramCod") (dOut diag)
  where
    lookupPort label pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> error (label <> ": missing port type")
        Just ty -> ty
    portKey (PortId k) = k

applySubstDiagram :: Subst -> Diagram -> Diagram
applySubstDiagram subst diag =
  diag { dPortTy = IM.map (applySubstTy subst) (dPortTy diag) }

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
  in (pid : pids, diag2)

unionDiagram :: Diagram -> Diagram -> Diagram
unionDiagram left right = left
  { dPortTy = IM.union (dPortTy left) (dPortTy right)
  , dProd = IM.union (dProd left) (dProd right)
  , dCons = IM.union (dCons left) (dCons right)
  , dEdges = IM.union (dEdges left) (dEdges right)
  , dNextPort = dNextPort right
  , dNextEdge = dNextEdge right
  }
