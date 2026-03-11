{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pretty
  ( renderDiagram
  , renderType
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.Obj
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Literal (renderLiteral)
import Strat.Poly.ObjPretty (renderMode, renderType)


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
      in case IM.lookup (unPortId p) (dPortObj diag) of
          Nothing -> renderedPort
          Just ty -> renderedPort <> ":" <> renderType ty

renderEdges :: [Edge] -> Either Text Text
renderEdges edges = do
  rendered <- mapM renderEdge edges
  pure (T.intercalate "\n" rendered)
  where
    renderEdge e =
      case ePayload e of
        PGen g args bargs -> do
          bargsTxt <- renderBinderArgs bargs
          Right
            ( "  "
                <> renderEdgeId (eId e)
                <> ": "
                <> renderGenCall g args
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
        PSplice x _ ->
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
        PTmLit lit ->
          Right
            ( "  "
                <> renderEdgeId (eId e)
                <> ": lit("
                <> renderLiteral lit
                <> ") ["
                <> renderPortList (eIns e)
                <> "] -> ["
                <> renderPortList (eOuts e)
                <> "]"
            )
        PInternalDrop ->
          Right
            ( "  "
                <> renderEdgeId (eId e)
                <> ": internal_drop ["
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

renderGenCall :: GenName -> [CodeArg] -> Text
renderGenCall g [] = renderGen g
renderGenCall g args =
  renderGen g <> "(" <> T.intercalate ", " (map renderCodeArg args) <> ")"

renderCodeArg :: CodeArg -> Text
renderCodeArg arg =
  case arg of
    CAObj obj -> renderType obj
    CATm tm -> renderTermDiagramArg tm

renderTermDiagramArg :: TermDiagram -> Text
renderTermDiagramArg (TermDiagram diag) =
  case dOut diag of
    [outPort] -> go S.empty outPort
    _ -> "<term>"
  where
    modeInputs = modeCtxEntries (dTmCtx diag) (dMode diag)
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])
    localToGlobal = map fst (take (length (dIn diag)) modeInputs)

    go seen pid =
      case M.lookup pid inMap of
        Just local ->
          case nth localToGlobal local of
            Just globalTm -> "bound#" <> T.pack (show globalTm)
            Nothing -> "<bound>"
        Nothing ->
          if pid `S.member` seen
            then "<cycle>"
            else
              case IM.lookup (unPortId pid) (dProd diag) of
                Just (Just eid) ->
                  case IM.lookup (unEdgeId eid) (dEdges diag) of
                    Just edge ->
                      case ePayload edge of
                        PTmLit lit -> renderLiteral lit
                        PTmMeta v -> tmvName v
                        PGen gen args [] -> renderGenCall gen args
                        _ -> "<term>"
                    Nothing -> "<term>"
                _ -> "<term>"

    nth xs i
      | i < 0 = Nothing
      | otherwise =
          case drop i xs of
            (x:_) -> Just x
            [] -> Nothing

    modeCtxEntries tmCtx mode =
      [ (i, ty)
      | (i, ty) <- zip [0 :: Int ..] tmCtx
      , objMode ty == mode
      ]

renderBox :: BoxName -> Text
renderBox (BoxName t) = t

renderPortId :: PortId -> Text
renderPortId (PortId k) = "p" <> T.pack (show k)

renderEdgeId :: EdgeId -> Text
renderEdgeId (EdgeId k) = "e" <> T.pack (show k)

renderBinderMeta :: BinderMetaVar -> Text
renderBinderMeta (BinderMetaVar x) = "?" <> x

-- renderType and renderMode come from Strat.Poly.ObjPretty
