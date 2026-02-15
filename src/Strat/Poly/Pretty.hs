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
  diag' <- reindexDiagramForDisplay diag
  edgesTxt <- renderEdges (IM.elems (dEdges diag'))
  pure $
    T.intercalate "\n"
      [ "mode: " <> renderMode (dMode diag')
      , "tmctx: [" <> T.intercalate ", " (map renderType (dTmCtx diag')) <> "]"
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
      let renderedPort =
            case getPortLabel diag p of
              Nothing -> renderPortId p
              Just lbl -> renderPortId p <> "(" <> lbl <> ")"
      in case IM.lookup (unPortId p) (dPortTy diag) of
          Nothing -> renderedPort
          Just ty -> renderedPort <> ":" <> renderType ty

renderEdges :: [Edge] -> Either Text Text
renderEdges edges = do
  rendered <- mapM renderEdge edges
  pure (T.intercalate "\n" rendered)
  where
    renderEdge e =
      case ePayload e of
        PGen g attrs bargs -> do
          bargsTxt <- renderBinderArgs bargs
          Right
            ( "  "
                <> renderEdgeId (eId e)
                <> ": "
                <> renderGenWithAttrs g attrs
                <> bargsTxt
                <> " ["
                <> renderPortList (eIns e)
                <> "] -> ["
                <> renderPortList (eOuts e)
                <> "]"
            )
        PBox name inner -> do
          innerTxt <- renderDiagram inner
          let header =
                "  " <> renderEdgeId (eId e) <> ": box " <> renderBox name
                  <> " [" <> renderPortList (eIns e) <> "] -> [" <> renderPortList (eOuts e) <> "]"
          let body = indent innerTxt
          Right (header <> "\n" <> body)
        PFeedback inner -> do
          innerTxt <- renderDiagram inner
          let header =
                "  " <> renderEdgeId (eId e) <> ": feedback"
                  <> " [" <> renderPortList (eIns e) <> "] -> [" <> renderPortList (eOuts e) <> "]"
          let body = indent innerTxt
          Right (header <> "\n" <> body)
        PSplice x ->
          Right
            ( "  "
                <> renderEdgeId (eId e)
                <> ": splice("
                <> renderBinderMeta x
                <> ") ["
                <> renderPortList (eIns e)
                <> "] -> ["
                <> renderPortList (eOuts e)
                <> "]"
            )
        PTmMeta v ->
          Right
            ( "  "
                <> renderEdgeId (eId e)
                <> ": tmmeta("
                <> tmvName v
                <> "#"
                <> T.pack (show (tmvScope v))
                <> ") ["
                <> renderPortList (eIns e)
                <> "] -> ["
                <> renderPortList (eOuts e)
                <> "]"
            )
    renderPortList = T.intercalate ", " . map renderPortId

    renderBinderArgs [] = Right ""
    renderBinderArgs args = do
      xs <- mapM renderBinderArg args
      Right (" [" <> T.intercalate ", " xs <> "]")

    renderBinderArg barg =
      case barg of
        BAMeta x -> Right (renderBinderMeta x)
        BAConcrete d -> do
          txt <- renderDiagram d
          Right ("{" <> T.replace "\n" " " txt <> "}")

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

renderBinderMeta :: BinderMetaVar -> Text
renderBinderMeta (BinderMetaVar x) = "?" <> x

-- renderType and renderMode come from Strat.Poly.TypePretty
