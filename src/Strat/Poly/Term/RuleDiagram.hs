{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RuleDiagram
  ( SpliceMapper
  , sameModeSpliceMapper
  , instantiateBinderMetas
  , expandSplices
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Strat.Poly.Obj (Obj)
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , BinderMetaVar
  , BinderArg(..)
  , PortId
  , deleteEdgeKeepPorts
  , diagramPortObj
  , mergeBoundaryPairs
  , shiftDiagram
  , unionDisjointIntMap
  , weakenDiagramTmCtxTo
  , validateDiagram
  )
import Strat.Poly.ModeSyntax (ModExpr(..))
import Strat.Poly.Traversal (traverseDiagram)

type SpliceMapper = ModExpr -> Diagram -> Either Text Diagram

sameModeSpliceMapper :: Text -> SpliceMapper
sameModeSpliceMapper label me captured =
  if null (mePath me) && meSrc me == dMode captured && meTgt me == dMode captured
    then Right captured
    else Left (label <> ": splice requires modality-action mapping but no splice mapper is available")

requirePortType :: Text -> Diagram -> PortId -> Either Text Obj
requirePortType ctx diag p =
  case diagramPortObj diag p of
    Nothing -> Left (ctx <> ": missing port type")
    Just ty -> Right ty

spliceEdge :: Diagram -> Int -> Diagram -> Either Text Diagram
spliceEdge diag edgeKey image = do
  edge <-
    case IM.lookup edgeKey (dEdges diag) of
      Nothing -> Left "spliceEdge: missing edge"
      Just e -> Right e
  let ins = eIns edge
  let outs = eOuts edge
  diag1 <- deleteEdgeKeepPorts diag (EdgeId edgeKey)
  let imageShift = shiftDiagram (dNextPort diag1) (dNextEdge diag1) image
  diag2 <- unionDiagramRaw diag1 imageShift
  let boundary = dIn imageShift <> dOut imageShift
  if length boundary /= length (ins <> outs)
    then Left "spliceEdge: boundary mismatch"
    else do
      diag3 <- mergeBoundaryPairs diag2 (zip (ins <> outs) boundary)
      validateDiagram diag3
      pure diag3

unionDiagramRaw :: Diagram -> Diagram -> Either Text Diagram
unionDiagramRaw left right
  | dMode left /= dMode right = Left "unionDiagram: mode mismatch"
  | dTmCtx left /= dTmCtx right = Left "unionDiagram: term-context mismatch"
  | otherwise = do
      portTy <- unionDisjointIntMap "unionDiagram ports" (dPortObj left) (dPortObj right)
      portLabel <- unionDisjointIntMap "unionDiagram labels" (dPortLabel left) (dPortLabel right)
      prod <- unionDisjointIntMap "unionDiagram producers" (dProd left) (dProd right)
      cons <- unionDisjointIntMap "unionDiagram consumers" (dCons left) (dCons right)
      edges <- unionDisjointIntMap "unionDiagram edges" (dEdges left) (dEdges right)
      pure left
        { dPortObj = portTy
        , dPortLabel = portLabel
        , dProd = prod
        , dCons = cons
        , dEdges = edges
        , dNextPort = max (dNextPort left) (dNextPort right)
        , dNextEdge = max (dNextEdge left) (dNextEdge right)
        }

instantiateBinderMetas :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
instantiateBinderMetas binderSub =
  traverseDiagram pure pure pure onBinderArg
  where
    onBinderArg barg =
      case barg of
        BAConcrete inner -> Right (BAConcrete inner)
        BAMeta x ->
          case M.lookup x binderSub of
            Nothing -> Left "rewriteOnce: RHS uses uncaptured binder meta"
            Just captured -> Right (BAConcrete captured)

expandSplices :: SpliceMapper -> M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
expandSplices spliceMapper binderSub =
  traverseDiagram expandTop pure pure pure
  where
    expandTop diag =
      case findSpliceEdge diag of
        Nothing -> Right diag
        Just (edgeKey, edge, x, me) -> do
          captured <-
            case M.lookup x binderSub of
              Nothing -> Left "rewriteOnce: splice uses uncaptured binder meta"
              Just d -> Right d
          if dMode captured == meSrc me
            then Right ()
            else Left "rewriteOnce: splice mapper source-mode mismatch"
          capturedMapped <-
            if null (mePath me)
              then Right captured
              else spliceMapper me captured
          capturedAligned <- weakenDiagramTmCtxTo (dTmCtx diag) capturedMapped
          if dMode capturedMapped == meTgt me
            then Right ()
            else Left "rewriteOnce: splice mapper target-mode mismatch"
          domSplice <- mapM (requirePortType "rewriteOnce" diag) (eIns edge)
          codSplice <- mapM (requirePortType "rewriteOnce" diag) (eOuts edge)
          domCaptured <- mapM (requirePortType "rewriteOnce" capturedAligned) (dIn capturedAligned)
          codCaptured <- mapM (requirePortType "rewriteOnce" capturedAligned) (dOut capturedAligned)
          if domSplice /= domCaptured || codSplice /= codCaptured
            then Left "rewriteOnce: splice boundary mismatch"
            else Right ()
          diagMerged <- spliceEdge diag edgeKey capturedAligned
          expandTop diagMerged

findSpliceEdge :: Diagram -> Maybe (Int, Edge, BinderMetaVar, ModExpr)
findSpliceEdge diag =
  case
    [ (k, edge, x, me)
    | (k, edge) <- IM.toAscList (dEdges diag)
    , PSplice x me <- [ePayload edge]
    ]
    of
      [] -> Nothing
      (x:_) -> Just x
