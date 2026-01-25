{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pretty
  ( renderDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Graph
import Strat.Poly.TypeExpr
import Strat.Poly.Names (GenName(..))
import Strat.Poly.ModeTheory (ModeName(..))


renderDiagram :: Diagram -> Text
renderDiagram diag =
  let diag' = canonicalizeDiagram diag
  in
  T.intercalate "\n"
    [ "mode: " <> renderMode (dMode diag')
    , "in: [" <> renderPorts diag' (dIn diag') <> "]"
    , "out: [" <> renderPorts diag' (dOut diag') <> "]"
    , "edges:"
    , renderEdges (IM.elems (dEdges diag'))
    ]

renderMode :: ModeName -> Text
renderMode (ModeName t) = t

renderPorts :: Diagram -> [PortId] -> Text
renderPorts diag ports =
  T.intercalate ", " [ renderPort p | p <- ports ]
  where
    renderPort p =
      case IM.lookup (portKey p) (dPortTy diag) of
        Nothing -> renderPortId p
        Just ty -> renderPortId p <> ":" <> renderType ty
    portKey (PortId k) = k

renderEdges :: [Edge] -> Text
renderEdges edges =
  T.intercalate "\n" (map renderEdge edges)
  where
    renderEdge e =
      "  " <> renderEdgeId (eId e) <> ": " <> renderGen (eGen e)
        <> " [" <> renderPortList (eIns e) <> "] -> [" <> renderPortList (eOuts e) <> "]"
    renderPortList = T.intercalate ", " . map renderPortId

renderGen :: GenName -> Text
renderGen (GenName t) = t

renderPortId :: PortId -> Text
renderPortId (PortId k) = "p" <> T.pack (show k)

renderEdgeId :: EdgeId -> Text
renderEdgeId (EdgeId k) = "e" <> T.pack (show k)

renderType :: TypeExpr -> Text
renderType ty =
  case ty of
    TVar (TyVar t) -> t
    TCon (TypeName n) [] -> n
    TCon (TypeName n) args ->
      n <> "(" <> T.intercalate ", " (map renderType args) <> ")"
