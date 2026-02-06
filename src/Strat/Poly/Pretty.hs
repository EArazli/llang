{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pretty
  ( renderDiagram
  , renderType
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Strat.Poly.Graph
import Strat.Poly.TypeExpr
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Attr (AttrTerm(..), AttrLit(..), AttrMap, AttrVar(..))
import Strat.Poly.TypePretty (renderMode, renderType)


renderDiagram :: Diagram -> Either Text Text
renderDiagram diag = do
  diag' <- renumberDiagram diag
  edgesTxt <- renderEdges (IM.elems (dEdges diag'))
  pure $
    T.intercalate "\n"
      [ "mode: " <> renderMode (dMode diag')
      , "in: [" <> renderPorts diag' (dIn diag') <> "]"
      , "out: [" <> renderPorts diag' (dOut diag') <> "]"
      , "edges:"
      , edgesTxt
      ]

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
        PGen g attrs ->
          Right ("  " <> renderEdgeId (eId e) <> ": " <> renderGenWithAttrs g attrs
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

renderGenWithAttrs :: GenName -> AttrMap -> Text
renderGenWithAttrs g attrs
  | M.null attrs = renderGen g
  | otherwise =
      renderGen g
        <> "("
        <> T.intercalate ", " [ name <> "=" <> renderAttrTerm term | (name, term) <- M.toAscList attrs ]
        <> ")"

renderAttrTerm :: AttrTerm -> Text
renderAttrTerm term =
  case term of
    ATVar v -> avName v
    ATLit lit ->
      case lit of
        ALInt n -> T.pack (show n)
        ALString s -> T.pack (show s)
        ALBool True -> "true"
        ALBool False -> "false"

renderBox :: BoxName -> Text
renderBox (BoxName t) = t

renderPortId :: PortId -> Text
renderPortId (PortId k) = "p" <> T.pack (show k)

renderEdgeId :: EdgeId -> Text
renderEdgeId (EdgeId k) = "e" <> T.pack (show k)

-- renderType and renderMode come from Strat.Poly.TypePretty
