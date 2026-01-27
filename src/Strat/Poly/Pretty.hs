{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pretty
  ( renderDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Graph
import Strat.Poly.TypeExpr
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.ModeTheory (ModeName(..))


renderDiagram :: Diagram -> Either Text Text
renderDiagram diag = do
  diag' <- canonicalizeDiagram diag
  edgesTxt <- renderEdges (IM.elems (dEdges diag'))
  pure $
    T.intercalate "\n"
      [ "mode: " <> renderMode (dMode diag')
      , "in: [" <> renderPorts diag' (dIn diag') <> "]"
      , "out: [" <> renderPorts diag' (dOut diag') <> "]"
      , "edges:"
      , edgesTxt
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

renderEdges :: [Edge] -> Either Text Text
renderEdges edges = do
  rendered <- mapM renderEdge edges
  pure (T.intercalate "\n" rendered)
  where
    renderEdge e =
      case ePayload e of
        PGen g ->
          Right ("  " <> renderEdgeId (eId e) <> ": " <> renderGen g
            <> " [" <> renderPortList (eIns e) <> "] -> [" <> renderPortList (eOuts e) <> "]")
        PBox name inner -> do
          innerTxt <- renderDiagram inner
          let header =
                "  " <> renderEdgeId (eId e) <> ": box " <> renderBox name
                  <> " [" <> renderPortList (eIns e) <> "] -> [" <> renderPortList (eOuts e) <> "]"
          let body = indent innerTxt
          Right (header <> "\n" <> body)
    renderPortList = T.intercalate ", " . map renderPortId

indent :: Text -> Text
indent txt =
  let ls = T.lines txt
  in T.intercalate "\n" (map ("    " <>) ls)

renderGen :: GenName -> Text
renderGen (GenName t) = t

renderBox :: BoxName -> Text
renderBox (BoxName t) = t

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
