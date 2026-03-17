{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DiagramBuild
  ( allocPorts
  , finalizeSingleOutputDiagram
  , saturateUnusedBoundaryInputs
  , emitMetaNode
  , emitGenNode
  , emitSpliceNode
  , emitLiteralNode
  ) where

import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import Data.Text (Text)
import Strat.Poly.Literal (Literal)
import Strat.Poly.ModeSyntax (ModExpr)
import Strat.Poly.Names (GenName)
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , BinderMetaVar
  , BinderArg
  , EdgePayload(..)
  , addEdgePayload
  , freshPort
  , unPortId
  )
import Strat.Poly.Obj (CodeArg, Context, Obj, TmVar)

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (restPorts, diag2) = allocPorts rest diag1
   in (pid : restPorts, diag2)

finalizeSingleOutputDiagram :: [PortId] -> PortId -> Diagram -> Either Text Diagram
finalizeSingleOutputDiagram inPorts outPort diag =
  saturateUnusedBoundaryInputs diag { dIn = inPorts, dOut = [outPort] }

saturateUnusedBoundaryInputs :: Diagram -> Either Text Diagram
saturateUnusedBoundaryInputs diag =
  foldM ensureConsumed diag (dIn diag)
  where
    ensureConsumed d pid =
      let isBoundaryOutput = pid `elem` dOut d
       in case IM.lookup (unPortId pid) (dCons d) of
            Just Nothing
              | isBoundaryOutput -> Right d
              | otherwise -> addEdgePayload PInternalDrop [pid] [] d
            _ -> Right d

emitMetaNode :: Obj -> TmVar -> [PortId] -> Diagram -> Either Text (PortId, Diagram)
emitMetaNode sortTy v =
  emitSingleOutputEdge sortTy (PTmMeta v)

emitGenNode
  :: Obj
  -> GenName
  -> [CodeArg]
  -> [BinderArg]
  -> [PortId]
  -> Diagram
  -> Either Text (PortId, Diagram)
emitGenNode sortTy g args bargs =
  emitSingleOutputEdge sortTy (PGen g args bargs)

emitSpliceNode :: Obj -> BinderMetaVar -> ModExpr -> [PortId] -> Diagram -> Either Text (PortId, Diagram)
emitSpliceNode sortTy hole me =
  emitSingleOutputEdge sortTy (PSplice hole me)

emitLiteralNode :: Obj -> Literal -> Diagram -> Either Text (PortId, Diagram)
emitLiteralNode sortTy lit =
  emitSingleOutputEdge sortTy (PTmLit lit) []

emitSingleOutputEdge :: Obj -> EdgePayload -> [PortId] -> Diagram -> Either Text (PortId, Diagram)
emitSingleOutputEdge sortTy payload inPorts diag = do
  let (outPort, diag1) = freshPort sortTy diag
  diag2 <- addEdgePayload payload inPorts [outPort] diag1
  pure (outPort, diag2)
