{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Graph
  ( PortId(..)
  , EdgeId(..)
  , unPortId
  , unEdgeId
  , CanonDiagram(..)
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , Edge(..)
  , Diagram(..)
  , emptyDiagram
  , freshPort
  , addEdge
  , addEdgePayload
  , validateDiagram
  , mergePorts
  , mergeBoundaryPairs
  , deleteEdgeKeepPorts
  , deletePortIfDangling
  , deletePortsIfDangling
  , reindexDiagramForDisplay
  , canonDiagram
  , canonDiagramRaw
  , canonKey
  , shiftDiagram
  , diagramPortType
  , getPortLabel
  , setPortLabel
  , diagramPortIds
  , unionDisjointIntMap
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS8
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad (foldM)
import qualified Data.List as L
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Syntax
  ( PortId(..)
  , EdgeId(..)
  , unPortId
  , unEdgeId
  , CanonDiagram(..)
  , BinderMetaVar(..)
  , BinderArg(..)
  , EdgePayload(..)
  , Edge(..)
  , Diagram(..)
  , TypeExpr
  , TmVar(..)
  )
import Strat.Poly.TypeExpr (boundTmIndicesType, typeMode)
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Attr (AttrMap)
import Strat.Util.List (dedupe)


emptyDiagram :: ModeName -> [TypeExpr] -> Diagram
emptyDiagram mode tmCtx = Diagram
  { dMode = mode
  , dTmCtx = tmCtx
  , dIn = []
  , dOut = []
  , dPortTy = IM.empty
  , dPortLabel = IM.empty
  , dProd = IM.empty
  , dCons = IM.empty
  , dEdges = IM.empty
  , dNextPort = 0
  , dNextEdge = 0
  }

diagramPortIds :: Diagram -> [PortId]
diagramPortIds diag = map PortId (IM.keys (dPortTy diag))

diagramPortType :: Diagram -> PortId -> Maybe TypeExpr
diagramPortType diag pid = IM.lookup (unPortId pid) (dPortTy diag)

getPortLabel :: Diagram -> PortId -> Maybe Text
getPortLabel diag pid =
  case IM.lookup (unPortId pid) (dPortLabel diag) of
    Nothing -> Nothing
    Just label -> label

setPortLabel :: PortId -> Text -> Diagram -> Either Text Diagram
setPortLabel pid name diag =
  if IM.member (unPortId pid) (dPortTy diag)
    then
      Right
        diag
          { dPortLabel = IM.insert (unPortId pid) (Just name) (dPortLabel diag)
          }
    else Left "setPortLabel: port does not exist"

freshPort :: TypeExpr -> Diagram -> (PortId, Diagram)
freshPort ty diag =
  let pid = PortId (dNextPort diag)
      k = unPortId pid
      diag' = diag
        { dPortTy = IM.insert k ty (dPortTy diag)
        , dPortLabel = IM.insert k Nothing (dPortLabel diag)
        , dProd = IM.insert k Nothing (dProd diag)
        , dCons = IM.insert k Nothing (dCons diag)
        , dNextPort = dNextPort diag + 1
        }
  in (pid, diag')

addEdge :: GenName -> [PortId] -> [PortId] -> Diagram -> Either Text Diagram
addEdge gen ins outs diag =
  addEdgePayload (PGen gen M.empty []) ins outs diag

addEdgePayload :: EdgePayload -> [PortId] -> [PortId] -> Diagram -> Either Text Diagram
addEdgePayload payload ins outs diag = do
  case traverse (ensurePortExists diag) (ins <> outs) of
    Left err ->
      Left (err
        <> " (ins=" <> T.pack (show ins)
        <> ", outs=" <> T.pack (show outs)
        <> ", ports=" <> T.pack (show (IM.keys (dPortTy diag)))
        <> ", next=" <> T.pack (show (dNextPort diag))
        <> ")")
    Right _ -> Right ()
  mapM_ (ensureFreeConsumer diag) ins
  mapM_ (ensureFreeProducer diag) outs
  let eid = EdgeId (dNextEdge diag)
  let edge = Edge { eId = eid, ePayload = payload, eIns = ins, eOuts = outs }
  let diag' = diag
        { dEdges = IM.insert (unEdgeId eid) edge (dEdges diag)
        , dCons = foldr (\p -> IM.insert (unPortId p) (Just eid)) (dCons diag) ins
        , dProd = foldr (\p -> IM.insert (unPortId p) (Just eid)) (dProd diag) outs
        , dNextEdge = dNextEdge diag + 1
        }
  pure diag'

ensurePortExists :: Diagram -> PortId -> Either Text ()
ensurePortExists diag pid =
  case IM.lookup (unPortId pid) (dPortTy diag) of
    Nothing ->
      Left ("addEdge: port does not exist: " <> T.pack (show pid))
    Just _ -> Right ()

ensureFreeConsumer :: Diagram -> PortId -> Either Text ()
ensureFreeConsumer diag pid =
  case IM.lookup (unPortId pid) (dCons diag) of
    Just Nothing -> Right ()
    Just (Just _) -> Left "addEdge: port already has consumer"
    Nothing -> Left "addEdge: port missing consumer slot"

ensureFreeProducer :: Diagram -> PortId -> Either Text ()
ensureFreeProducer diag pid =
  case IM.lookup (unPortId pid) (dProd diag) of
    Just Nothing -> Right ()
    Just (Just _) -> Left "addEdge: port already has producer"
    Nothing -> Left "addEdge: port missing producer slot"

validateDiagram :: Diagram -> Either Text ()
validateDiagram diag = do
  ensureKeysets
  ensureEdgeIdKeyAgreement
  ensureNextIdBounds
  ensureBoundaryUnique "inputs" (dIn diag)
  ensureBoundaryUnique "outputs" (dOut diag)
  mapM_ (ensurePortExists diag) (dIn diag)
  mapM_ (ensurePortExists diag) (dOut diag)
  mapM_ (ensureBoundaryEndpoint "input" (dProd diag)) (dIn diag)
  mapM_ (ensureBoundaryEndpoint "output" (dCons diag)) (dOut diag)
  mapM_ checkEdge (IM.elems (dEdges diag))
  mapM_ checkPortMode (IM.toList (dPortTy diag))
  mapM_ checkPort (IM.keys (dPortTy diag))
  pure ()
  where
    ensureKeysets =
      do
        ensureSameKeySet "port types" (dPortTy diag) (dPortLabel diag)
        ensureSameKeySet "port labels" (dPortLabel diag) (dProd diag)
        ensureSameKeySet "port labels" (dPortLabel diag) (dCons diag)
    ensureSameKeySet label left right =
      if IM.keysSet left == IM.keysSet right
        then Right ()
        else Left ("validateDiagram: " <> label <> " keysets mismatch")
    ensureEdgeIdKeyAgreement =
      mapM_ checkEdgeEntry (IM.toList (dEdges diag))
      where
        checkEdgeEntry (k, edge) =
          if k == unEdgeId (eId edge)
            then Right ()
            else Left "validateDiagram: edge map key does not match edge id"
    ensureNextIdBounds = do
      ensureNextBound "dNextPort" (dNextPort diag) (IM.keys (dPortTy diag))
      ensureNextBound "dNextEdge" (dNextEdge diag) (IM.keys (dEdges diag))
      where
        ensureNextBound label nextId keys =
          case keys of
            [] ->
              if nextId >= 0
                then Right ()
                else Left ("validateDiagram: " <> label <> " must be nonnegative")
            _ ->
              let maxKey = maximum keys
               in if nextId > maxKey
                    then Right ()
                    else Left ("validateDiagram: " <> label <> " must be greater than all existing ids")
    ensureBoundaryUnique label ports =
      let s = S.fromList ports
      in if S.size s == length ports
        then Right ()
        else Left ("validateDiagram: duplicate ports in boundary " <> label)
    ensureBoundaryEndpoint label mp pid =
      case IM.lookup (unPortId pid) mp of
        Just Nothing -> Right ()
        Just (Just _) -> Left ("validateDiagram: boundary " <> label <> " has incident edge")
        Nothing -> Left "validateDiagram: missing incidence entry"
    checkEdge edge = do
      mapM_ (ensurePortExists diag) (eIns edge <> eOuts edge)
      ensureNoDuplicates "ins" (eIns edge)
      ensureNoDuplicates "outs" (eOuts edge)
      ensureNoOverlap (eIns edge) (eOuts edge)
      mapM_ (checkCons edge) (eIns edge)
      mapM_ (checkProd edge) (eOuts edge)
      checkPayload edge
    checkCons edge pid =
      case IM.lookup (unPortId pid) (dCons diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: consumer incidence mismatch"
    checkProd edge pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) | eid == eId edge -> Right ()
        _ -> Left "validateDiagram: producer incidence mismatch"
    checkPort k = do
      checkEndpoint "producer" (IM.lookup k (dProd diag)) eOuts
      checkEndpoint "consumer" (IM.lookup k (dCons diag)) eIns
      checkBoundaryCompleteness k
      where
        checkEndpoint label entry sel =
          case entry of
            Just Nothing -> Right ()
            Just (Just eid) -> do
              edge <- requireEdge eid
              if PortId k `elem` sel edge
                then Right ()
                else Left ("validateDiagram: " <> label <> " back-pointer mismatch")
            Nothing -> Left "validateDiagram: missing incidence entry"
        checkBoundaryCompleteness k =
          let pid = PortId k
              prodMissing = IM.lookup k (dProd diag) == Just Nothing
              consMissing = IM.lookup k (dCons diag) == Just Nothing
              inBoundary = pid `elem` dIn diag
              outBoundary = pid `elem` dOut diag
          in if prodMissing && not inBoundary
            then Left "validateDiagram: missing boundary input for open port"
            else if consMissing && not outBoundary
              then Left "validateDiagram: missing boundary output for open port"
              else Right ()
    requireEdge eid =
      case IM.lookup (unEdgeId eid) (dEdges diag) of
        Nothing -> Left "validateDiagram: missing edge referenced by incidence"
        Just edge -> Right edge
    requirePortType d pid =
      case diagramPortType d pid of
        Nothing -> Left "validateDiagram: missing port type"
        Just ty -> Right ty
    checkPayload edge =
      case ePayload edge of
        PGen _ _ binderArgs -> mapM_ checkBinderArg binderArgs
        PBox _ inner -> do
          if dMode inner /= dMode diag
            then Left "validateDiagram: box mode mismatch"
            else Right ()
          if dTmCtx inner /= dTmCtx diag
            then Left "validateDiagram: box term context mismatch"
            else Right ()
          validateDiagram inner
          domOuter <- mapM (requirePortType diag) (eIns edge)
          codOuter <- mapM (requirePortType diag) (eOuts edge)
          domInner <- mapM (requirePortType inner) (dIn inner)
          codInner <- mapM (requirePortType inner) (dOut inner)
          if domOuter == domInner && codOuter == codInner
            then Right ()
            else Left "validateDiagram: box boundary mismatch"
        PFeedback inner -> do
          if dMode inner /= dMode diag
            then Left "validateDiagram: feedback mode mismatch"
            else Right ()
          if dTmCtx inner /= dTmCtx diag
            then Left "validateDiagram: feedback term context mismatch"
            else Right ()
          validateDiagram inner
          innerDom <- mapM (requirePortType inner) (dIn inner)
          innerCod <- mapM (requirePortType inner) (dOut inner)
          outerDom <- mapM (requirePortType diag) (eIns edge)
          outerCod <- mapM (requirePortType diag) (eOuts edge)
          if null outerDom
            then Right ()
            else Left "validateDiagram: feedback edge must not consume outer inputs"
          case (innerDom, innerCod) of
            ([stateIn], stateOut : codTail) -> do
              if stateIn /= stateOut
                then Left "validateDiagram: feedback body first output must match input type"
                else Right ()
              if outerCod == codTail
                then Right ()
                else Left "validateDiagram: feedback outer outputs mismatch body outputs"
            _ ->
              Left "validateDiagram: feedback body must have one input and at least one output"
        PSplice _ -> Right ()
        PTmMeta v -> do
          outTy <-
            case eOuts edge of
              [pid] -> requirePortType diag pid
              _ -> Left "validateDiagram: PTmMeta must have exactly one output"
          if typeMode outTy == typeMode (tmvSort v)
            then Right ()
            else Left "validateDiagram: PTmMeta output mode mismatch"
          if outTy == tmvSort v
            then Right ()
            else Left "validateDiagram: PTmMeta output sort mismatch"
          let modeIns =
                [ pid
                | pid <- dIn diag
                , Just ty <- [diagramPortType diag pid]
                , typeMode ty == typeMode (tmvSort v)
                ]
          if tmvScope v > length modeIns
            then Left "validateDiagram: PTmMeta scope exceeds available bound variables"
            else Right ()
          let expectedIns = take (tmvScope v) modeIns
          if eIns edge == expectedIns
            then Right ()
            else Left "validateDiagram: PTmMeta inputs must be canonical scoped boundary prefix"
        PInternalDrop ->
          case (eIns edge, eOuts edge) of
            ([_], []) -> Right ()
            _ -> Left "validateDiagram: PInternalDrop must have exactly one input and no outputs"
    checkBinderArg barg =
      case barg of
        BAConcrete inner -> validateDiagram inner
        BAMeta _ -> Right ()
    ensureNoDuplicates label ports =
      let s = S.fromList ports
      in if S.size s == length ports
        then Right ()
        else Left ("validateDiagram: duplicate ports in edge " <> label)
    ensureNoOverlap ins outs =
      let s = S.fromList ins `S.intersection` S.fromList outs
      in if S.null s
        then Right ()
        else Left "validateDiagram: port appears in both inputs and outputs"
    checkPortMode (k, ty) =
      if typeMode ty == dMode diag
        then
          let bad = S.filter (>= length (dTmCtx diag)) (boundTmIndicesType ty)
           in if S.null bad
                then Right ()
                else Left "validateDiagram: port type uses out-of-scope bound term variable"
        else
          Left
            ( "validateDiagram: port p" <> T.pack (show k)
                <> " has type in wrong mode (diagram mode "
                <> case dMode diag of ModeName name -> name
                <> ", type "
                <> T.pack (show ty)
                <> ")"
            )

mergePorts :: Diagram -> PortId -> PortId -> Either Text Diagram
mergePorts diag keep drop
  | keep == drop = Right diag
  | otherwise = do
      tyKeep <- requireType keep
      tyDrop <- requireType drop
      labelKeep <- requireLabel keep
      labelDrop <- requireLabel drop
      if tyKeep /= tyDrop
        then Left "mergePorts: type mismatch"
        else do
          let prodKeep = IM.lookup (unPortId keep) (dProd diag)
          let prodDrop = IM.lookup (unPortId drop) (dProd diag)
          let consKeep = IM.lookup (unPortId keep) (dCons diag)
          let consDrop = IM.lookup (unPortId drop) (dCons diag)
          prod <- mergeEndpoint "producer" prodKeep prodDrop
          cons <- mergeEndpoint "consumer" consKeep consDrop
          let diag' = diag
                { dPortTy = IM.delete (unPortId drop) (dPortTy diag)
                , dPortLabel =
                    IM.insert
                      (unPortId keep)
                      (mergeLabel labelKeep labelDrop)
                      (IM.delete (unPortId drop) (dPortLabel diag))
                , dProd = IM.insert (unPortId keep) prod (IM.delete (unPortId drop) (dProd diag))
                , dCons = IM.insert (unPortId keep) cons (IM.delete (unPortId drop) (dCons diag))
                , dIn = replacePort keep drop (dIn diag)
                , dOut = replacePort keep drop (dOut diag)
                , dEdges = IM.map (mergeEdge keep drop) (dEdges diag)
                }
          pure diag'
  where
    requireType pid =
      case IM.lookup (unPortId pid) (dPortTy diag) of
        Nothing -> Left "mergePorts: missing port"
        Just ty -> Right ty
    requireLabel pid =
      case IM.lookup (unPortId pid) (dPortLabel diag) of
        Nothing -> Left "mergePorts: missing port"
        Just label -> Right label
    mergeLabel keepLabel dropLabel =
      case keepLabel of
        Nothing -> dropLabel
        Just _ -> keepLabel
    mergeEndpoint label a b =
      case (a, b) of
        (Just (Just e1), Just (Just e2))
          | e1 == e2 -> Right (Just e1)
          | otherwise -> Left ("mergePorts: " <> label <> " conflict")
        (Just (Just e), Just Nothing) -> Right (Just e)
        (Just Nothing, Just (Just e)) -> Right (Just e)
        (Just Nothing, Just Nothing) -> Right Nothing
        _ -> Left "mergePorts: missing incidence entry"
    replacePort keep' drop' =
      dedupe . map (\p -> if p == drop' then keep' else p)
    mergeEdge keep' drop' edge =
      edge { eIns = map replace (eIns edge), eOuts = map replace (eOuts edge) }
      where
        replace p = if p == drop' then keep' else p

mergeBoundaryPairs :: Diagram -> [(PortId, PortId)] -> Either Text Diagram
mergeBoundaryPairs diag pairs = fst <$> foldM step (diag, M.empty) pairs
  where
    step (d, seen) (keep, dropPort) =
      case M.lookup dropPort seen of
        Nothing -> do
          d' <- mergePorts d keep dropPort
          pure (d', M.insert dropPort keep seen)
        Just keep' -> do
          d' <- mergePorts d keep' keep
          pure (d', seen)

deleteEdgeKeepPorts :: Diagram -> EdgeId -> Either Text Diagram
deleteEdgeKeepPorts diag eid = do
  edge <-
    case IM.lookup (unEdgeId eid) (dEdges diag) of
      Nothing -> Left "deleteEdgeKeepPorts: missing edge"
      Just e -> Right e
  cons' <- clearIncidence "consumer" (dCons diag) (eIns edge)
  prod' <- clearIncidence "producer" (dProd diag) (eOuts edge)
  pure
    diag
      { dEdges = IM.delete (unEdgeId eid) (dEdges diag)
      , dCons = cons'
      , dProd = prod'
      }
  where
    clearIncidence label mp ports =
      foldM clearOne mp ports
      where
        clearOne mp' pid =
          case IM.lookup (unPortId pid) mp' of
            Nothing -> Left ("deleteEdgeKeepPorts: missing " <> label <> " incidence entry")
            Just _ -> Right (IM.insert (unPortId pid) Nothing mp')

deletePortIfDangling :: Diagram -> PortId -> Either Text Diagram
deletePortIfDangling diag pid =
  let k = unPortId pid
   in case (IM.lookup k (dProd diag), IM.lookup k (dCons diag)) of
        (Just Nothing, Just Nothing) ->
          Right
            diag
              { dPortTy = IM.delete k (dPortTy diag)
              , dPortLabel = IM.delete k (dPortLabel diag)
              , dProd = IM.delete k (dProd diag)
              , dCons = IM.delete k (dCons diag)
              , dIn = filter (/= pid) (dIn diag)
              , dOut = filter (/= pid) (dOut diag)
              }
        (Nothing, _) -> Left "deletePortIfDangling: missing producer incidence entry"
        (_, Nothing) -> Left "deletePortIfDangling: missing consumer incidence entry"
        _ -> Left "deletePortIfDangling: port still has incidence"

deletePortsIfDangling :: Diagram -> [PortId] -> Either Text Diagram
deletePortsIfDangling = foldM deletePortIfDangling

shiftDiagram :: Int -> Int -> Diagram -> Diagram
shiftDiagram portOff edgeOff diag =
  let shiftPort (PortId k) = PortId (k + portOff)
      shiftEdge (EdgeId k) = EdgeId (k + edgeOff)
      shiftPorts = map shiftPort
      shiftEdgeRec edge =
        edge
          { eId = shiftEdge (eId edge)
          , ePayload = shiftPayload (ePayload edge)
          , eIns = shiftPorts (eIns edge)
          , eOuts = shiftPorts (eOuts edge)
          }
      shiftPayload payload =
        case payload of
          PGen g attrs bargs -> PGen g attrs (map shiftBinderArg bargs)
          PBox name inner -> PBox name (shiftDiagram portOff edgeOff inner)
          PFeedback inner -> PFeedback (shiftDiagram portOff edgeOff inner)
          PSplice x -> PSplice x
          PTmMeta v -> PTmMeta v
          PInternalDrop -> PInternalDrop
      shiftBinderArg barg =
        case barg of
          BAConcrete inner -> BAConcrete (shiftDiagram portOff edgeOff inner)
          BAMeta x -> BAMeta x
      shiftPortMap = IM.mapKeysMonotonic (+ portOff)
      shiftEdgeMap = IM.mapKeysMonotonic (+ edgeOff)
  in diag
      { dIn = shiftPorts (dIn diag)
      , dOut = shiftPorts (dOut diag)
      , dPortTy = shiftPortMap (dPortTy diag)
      , dPortLabel = shiftPortMap (dPortLabel diag)
      , dProd = shiftPortMap (fmap (fmap shiftEdge) (dProd diag))
      , dCons = shiftPortMap (fmap (fmap shiftEdge) (dCons diag))
      , dEdges = shiftEdgeMap (IM.map shiftEdgeRec (dEdges diag))
      , dNextPort = dNextPort diag + portOff
      , dNextEdge = dNextEdge diag + edgeOff
      }

reindexDiagramForDisplay :: Diagram -> Either Text Diagram
reindexDiagramForDisplay diag = do
  let (portMap, nextPort) = assignPorts diag
  let edgeMap = assignEdges diag
  dPortTy' <- buildPortMap portMap (dPortTy diag)
  dPortLabel' <- buildPortMap portMap (dPortLabel diag)
  dProd' <- buildEdgeRefMap portMap edgeMap (dProd diag)
  dCons' <- buildEdgeRefMap portMap edgeMap (dCons diag)
  dEdges' <- buildEdges portMap edgeMap (dEdges diag)
  dIn' <- mapM (requirePort portMap) (dIn diag)
  dOut' <- mapM (requirePort portMap) (dOut diag)
  pure Diagram
    { dMode = dMode diag
    , dTmCtx = dTmCtx diag
    , dIn = dIn'
    , dOut = dOut'
    , dPortTy = dPortTy'
    , dPortLabel = dPortLabel'
    , dProd = dProd'
    , dCons = dCons'
    , dEdges = dEdges'
    , dNextPort = nextPort
    , dNextEdge = M.size edgeMap
    }
  where
    assignPorts d =
      let boundary = dIn d <> dOut d
          (mp0, next0) = foldl assign (M.empty, 0) boundary
          remaining = filter (`M.notMember` mp0) (diagramPortIds d)
          remainingSorted = sortPorts remaining
          (mp1, next1) = foldl assign (mp0, next0) remainingSorted
      in (mp1, next1)
    assign (mp, n) pid =
      if M.member pid mp
        then (mp, n)
        else (M.insert pid (PortId n) mp, n + 1)
    sortPorts = map PortId . IM.keys . IM.fromList . map (\p -> (unPortId p, ()))
    assignEdges d =
      let edges = IM.elems (dEdges d)
          edgesSorted = sortEdges edges
          mp = foldl (\m (i, e) -> M.insert (eId e) (EdgeId i) m) M.empty (zip [0..] edgesSorted)
      in mp
    sortEdges = map snd . M.toAscList . M.fromList . map (\e -> (unEdgeId (eId e), e))
    buildPortMap mp portMap =
      fmap IM.fromList $
        mapM
          (\(k, ty) -> do
            p <- requirePort mp (PortId k)
            pure (unPortId p, ty))
          (IM.toList portMap)
    buildEdgeRefMap mp em refMap =
      fmap IM.fromList $
        mapM
          (\(k, edgeRef) -> do
            p <- requirePort mp (PortId k)
            edgeRef' <- traverse (requireEdge em) edgeRef
            pure (unPortId p, edgeRef'))
          (IM.toList refMap)
    buildEdges mp em edges =
      fmap IM.fromList $
        mapM
          (\edge -> do
            eid <- requireEdge em (eId edge)
            ins <- mapM (requirePort mp) (eIns edge)
            outs <- mapM (requirePort mp) (eOuts edge)
            payload <- mapPayload (ePayload edge)
            pure (unEdgeId eid, edge { eId = eid, ePayload = payload, eIns = ins, eOuts = outs }))
          (IM.elems edges)
    mapPayload payload =
      case payload of
        PGen g attrs bargs -> do
          bargs' <- mapM mapBinderArg bargs
          Right (PGen g attrs bargs')
        PBox name inner -> do
          inner' <- reindexDiagramForDisplay inner
          Right (PBox name inner')
        PFeedback inner -> do
          inner' <- reindexDiagramForDisplay inner
          Right (PFeedback inner')
        PSplice x -> Right (PSplice x)
        PTmMeta v -> Right (PTmMeta v)
        PInternalDrop -> Right PInternalDrop
    mapBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> reindexDiagramForDisplay inner
        BAMeta x -> Right (BAMeta x)
    requirePort mp pid =
      case M.lookup pid mp of
        Nothing -> Left "reindexDiagramForDisplay: missing port mapping"
        Just v -> Right v
    requireEdge mp eid =
      case M.lookup eid mp of
        Nothing -> Left "reindexDiagramForDisplay: missing edge mapping"
        Just v -> Right v

data CanonVertex
  = VPort PortId
  | VEdge EdgeId
  | VSlotIn EdgeId Int
  | VSlotOut EdgeId Int
  | VBoundIn Int
  | VBoundOut Int
  deriving (Eq, Ord, Show)

data BinderArgKey
  = BKConcrete ByteString
  | BKMeta BinderMetaVar
  deriving (Eq, Ord, Show)

data PayloadKey
  = PKGen GenName AttrMap [BinderArgKey]
  | PKBox ByteString
  | PKFeedback ByteString
  | PKSplice BinderMetaVar
  | PKTmMeta Text Int
  | PKInternalDrop
  deriving (Eq, Ord, Show)

data ColorKey
  = CKBoundIn Int
  | CKBoundOut Int
  | CKSlotIn Int
  | CKSlotOut Int
  | CKPort TypeExpr (Maybe Text)
  | CKEdge PayloadKey Int Int
  deriving (Eq, Ord, Show)

canonDiagram :: Diagram -> Either Text CanonDiagram
canonDiagram diag =
  CanonDiagram <$> canonDiagramRaw diag

canonDiagramRaw :: Diagram -> Either Text Diagram
canonDiagramRaw diag = do
  validateDiagram diag
  diagRec <- canonizeChildren diag
  canon <- canonizeOuter diagRec
  validateDiagram canon
  pure canon
  where
    canonizeChildren d = do
      edges' <- mapM canonEdge (IM.toAscList (dEdges d))
      pure d { dEdges = IM.fromAscList edges' }
      where
        canonEdge (k, edge) = do
          payload' <- canonPayload (ePayload edge)
          pure (k, edge { ePayload = payload' })

canonKey :: CanonDiagram -> ByteString
canonKey (CanonDiagram diag) = BS8.pack (show diag)

canonPayload :: EdgePayload -> Either Text EdgePayload
canonPayload payload =
  case payload of
    PGen g attrs bargs -> do
      bargs' <- mapM canonBinderArg bargs
      pure (PGen g attrs bargs')
    PBox _ inner -> do
      inner' <- canonDiagramRaw inner
      pure (PBox (BoxName "") inner')
    PFeedback inner -> do
      inner' <- canonDiagramRaw inner
      pure (PFeedback inner')
    PSplice x ->
      Right (PSplice x)
    PTmMeta v ->
      Right (PTmMeta v)
    PInternalDrop ->
      Right PInternalDrop
  where
    canonBinderArg barg =
      case barg of
        BAConcrete inner ->
          BAConcrete <$> canonDiagramRaw inner
        BAMeta x ->
          Right (BAMeta x)

canonizeOuter :: Diagram -> Either Text Diagram
canonizeOuter diag = do
  let ports = map PortId (IM.keys (dPortTy diag))
  let edges = L.sortOn (unEdgeId . eId) (IM.elems (dEdges diag))
  let edgeIds = map eId edges
  let vertices =
        [ VBoundIn i | i <- [0 .. length (dIn diag) - 1] ]
          <> [ VBoundOut j | j <- [0 .. length (dOut diag) - 1] ]
          <> [ VPort p | p <- ports ]
          <> [ VEdge eid | eid <- edgeIds ]
          <> concat
              [ [ VSlotIn (eId e) i | i <- [0 .. length (eIns e) - 1] ]
                  <> [ VSlotOut (eId e) j | j <- [0 .. length (eOuts e) - 1] ]
              | e <- edges
              ]
  let vertexIx = M.fromList (zip vertices [0 :: Int ..])
  colorKeys <- mapM (colorKeyFor diag) vertices
  colorIds <- colorClassIds colorKeys
  graphEdges <- encodeGraphEdges diag edges vertexIx
  let n = length vertices
  let adj = buildAdjacency n graphEdges
  let perm = canonicalPermutation n adj colorIds
  let canonLabelByVertexIx = IM.fromList [ (oldIx, newIx) | (newIx, oldIx) <- zip [0 :: Int ..] perm ]
  portRanked <-
    mapM
      ( \pid -> do
          rank <- vertexRank (VPort pid) vertexIx canonLabelByVertexIx
          pure (rank, pid)
      )
      ports
  edgeRanked <-
    mapM
      ( \eid -> do
          rank <- vertexRank (VEdge eid) vertexIx canonLabelByVertexIx
          pure (rank, eid)
      )
      edgeIds
  let portOrder = map snd (L.sortOn fst portRanked)
  let edgeOrder = map snd (L.sortOn fst edgeRanked)
  rebuildCanonicalDiagram diag portOrder edgeOrder
  where
    colorClassIds keys =
      let classes = S.toAscList (S.fromList keys)
          classMap = M.fromList (zip classes [0 :: Int ..])
       in mapM
            (\k -> maybe (Left "canonDiagram: missing color class") Right (M.lookup k classMap))
            keys

    vertexRank v ixMap rankMap = do
      ix <-
        case M.lookup v ixMap of
          Nothing -> Left "canonDiagram: vertex index missing"
          Just i -> Right i
      case IM.lookup ix rankMap of
        Nothing -> Left "canonDiagram: canonical label missing"
        Just rank -> Right rank

colorKeyFor :: Diagram -> CanonVertex -> Either Text ColorKey
colorKeyFor diag v =
  case v of
    VBoundIn i ->
      Right (CKBoundIn i)
    VBoundOut j ->
      Right (CKBoundOut j)
    VSlotIn _ i ->
      Right (CKSlotIn i)
    VSlotOut _ j ->
      Right (CKSlotOut j)
    VPort pid -> do
      ty <-
        case IM.lookup (unPortId pid) (dPortTy diag) of
          Nothing -> Left "canonDiagram: missing port type"
          Just t -> Right t
      Right (CKPort ty Nothing)
    VEdge eid -> do
      edge <-
        case IM.lookup (unEdgeId eid) (dEdges diag) of
          Nothing -> Left "canonDiagram: missing edge"
          Just e -> Right e
      payloadKey <- edgePayloadKey (ePayload edge)
      Right (CKEdge payloadKey (length (eIns edge)) (length (eOuts edge)))
  where
    edgePayloadKey payload =
      case payload of
        PGen g attrs bargs -> do
          bargs' <- mapM binderArgKey bargs
          pure (PKGen g attrs bargs')
        PBox _ inner ->
          Right (PKBox (BS8.pack (show inner)))
        PFeedback inner ->
          Right (PKFeedback (BS8.pack (show inner)))
        PSplice x ->
          Right (PKSplice x)
        PTmMeta tmv ->
          Right (PKTmMeta (tmvName tmv) (tmvScope tmv))
        PInternalDrop ->
          Right PKInternalDrop

    binderArgKey barg =
      case barg of
        BAConcrete inner ->
          Right (BKConcrete (BS8.pack (show inner)))
        BAMeta x ->
          Right (BKMeta x)

encodeGraphEdges
  :: Diagram
  -> [Edge]
  -> M.Map CanonVertex Int
  -> Either Text [(Int, Int)]
encodeGraphEdges diag edges vertexIx = do
  pairs <- fmap concat (mapM edgePairs edges)
  let boundaryPairs =
        [ (VBoundIn i, VPort pid)
        | (i, pid) <- zip [0 :: Int ..] (dIn diag)
        ]
          <> [ (VBoundOut j, VPort pid)
             | (j, pid) <- zip [0 :: Int ..] (dOut diag)
             ]
  mapM toIxPair (boundaryPairs <> pairs)
  where
    edgePairs edge =
      let eid = eId edge
          insPairs =
            concat
              [ [ (VEdge eid, VSlotIn eid i)
                , (VSlotIn eid i, VPort pid)
                ]
              | (i, pid) <- zip [0 :: Int ..] (eIns edge)
              ]
          outsPairs =
            concat
              [ [ (VEdge eid, VSlotOut eid j)
                , (VSlotOut eid j, VPort pid)
                ]
              | (j, pid) <- zip [0 :: Int ..] (eOuts edge)
              ]
       in Right (insPairs <> outsPairs)
    toIxPair (v1, v2) = do
      i1 <-
        case M.lookup v1 vertexIx of
          Nothing -> Left "canonDiagram: missing vertex in encoding"
          Just i -> Right i
      i2 <-
        case M.lookup v2 vertexIx of
          Nothing -> Left "canonDiagram: missing vertex in encoding"
          Just i -> Right i
      Right (i1, i2)

buildAdjacency :: Int -> [(Int, Int)] -> IM.IntMap IS.IntSet
buildAdjacency n pairs =
  foldl addEdge initial uniquePairs
  where
    initial = IM.fromList [ (i, IS.empty) | i <- [0 .. n - 1] ]
    uniquePairs =
      S.toList $
        S.fromList
          [ if u < v then (u, v) else (v, u)
          | (u, v) <- pairs
          , u /= v
          ]
    addEdge mp (u, v) =
      IM.insertWith IS.union u (IS.singleton v)
        (IM.insertWith IS.union v (IS.singleton u) mp)

canonicalPermutation :: Int -> IM.IntMap IS.IntSet -> [Int] -> [Int]
canonicalPermutation n adj colors =
  case search (refinePartition adj initialPartition) Nothing of
    Nothing -> [0 .. n - 1]
    Just candidate -> ccPerm candidate
  where
    initialPartition =
      map L.sort
        [ vs
        | (_, vs) <- M.toAscList (M.fromListWith (<>) [ (c, [v]) | (v, c) <- zip [0 :: Int ..] colors ])
        ]

    search part best0 =
      let part' = refinePartition adj part
       in if all ((== 1) . length) part'
            then
              case mapM onlyVertex part' of
                Nothing -> best0
                Just perm ->
                  let code = canonicalCode perm
                      candidate = CanonCandidate code perm
                   in Just (pickBetter best0 candidate)
            else
              case pickCell part' of
                Nothing -> best0
                Just (idx, cell) ->
                  foldl
                    (\bestAcc v -> search (individualize part' idx v) bestAcc)
                    best0
                    cell

    canonicalCode perm =
      concat
        [ [vertexColor v]
            <> [ if adjacent v (perm !! j) then 1 else 0
               | j <- [i + 1 .. n - 1]
               ]
        | (i, v) <- zip [0 :: Int ..] perm
        ]

    vertexColor v =
      case drop v colors of
        (c:_) -> c
        [] -> 0

    adjacent u v =
      case IM.lookup u adj of
        Nothing -> False
        Just nbrs -> IS.member v nbrs

    onlyVertex cell =
      case cell of
        [v] -> Just v
        _ -> Nothing

data CanonCandidate = CanonCandidate
  { ccCode :: [Int]
  , ccPerm :: [Int]
  }

pickBetter :: Maybe CanonCandidate -> CanonCandidate -> CanonCandidate
pickBetter existing candidate =
  case existing of
    Nothing -> candidate
    Just old ->
      if ccCode candidate < ccCode old
        then candidate
        else old

pickCell :: [[Int]] -> Maybe (Int, [Int])
pickCell cells =
  case
    [ (length cell, idx, cell)
    | (idx, cell) <- zip [0 :: Int ..] cells
    , length cell > 1
    ]
    of
      [] -> Nothing
      xs ->
        case L.sortOn (\(len, idx, _) -> (len, idx)) xs of
          [] -> Nothing
          (_, idx, cell) : _ -> Just (idx, cell)

individualize :: [[Int]] -> Int -> Int -> [[Int]]
individualize cells idx v =
  let before = take idx cells
      cell =
        case drop idx cells of
          (x:_) -> x
          [] -> []
      after =
        case drop (idx + 1) cells of
          xs -> xs
      rest = filter (/= v) cell
   in before <> [[v], rest] <> after

refinePartition :: IM.IntMap IS.IntSet -> [[Int]] -> [[Int]]
refinePartition adj part =
  let refined = refineOnce part
   in if refined == part
        then part
        else refinePartition adj refined
  where
    refineOnce cells =
      let cellSets = map IS.fromList cells
          signature v =
            [ countNeighbors v cset
            | cset <- cellSets
            ]
          splitCell cell =
            map L.sort
              [ vs
              | (_, vs) <- M.toAscList (M.fromListWith (<>) [ (signature v, [v]) | v <- cell ])
              ]
       in concatMap splitCell cells

    countNeighbors v cellSet =
      case IM.lookup v adj of
        Nothing -> 0
        Just nbrs -> IS.size (IS.intersection nbrs cellSet)

rebuildCanonicalDiagram :: Diagram -> [PortId] -> [EdgeId] -> Either Text Diagram
rebuildCanonicalDiagram diag portOrder edgeOrder = do
  let portMap = M.fromList (zip portOrder [ PortId i | i <- [0 :: Int .. length portOrder - 1] ])
  let edgeMap = M.fromList (zip edgeOrder [ EdgeId i | i <- [0 :: Int .. length edgeOrder - 1] ])
  dPortTy' <-
    fmap IM.fromList $
      mapM
        ( \oldPid -> do
            newPid <- requirePortMap portMap oldPid
            ty <- requirePortType oldPid
            pure (unPortId newPid, ty)
        )
        portOrder
  let dPortLabel' = IM.fromList [ (unPortId pid, Nothing) | pid <- M.elems portMap ]
  dIn' <- mapM (requirePortMap portMap) (dIn diag)
  dOut' <- mapM (requirePortMap portMap) (dOut diag)
  edges' <- mapM (rebuildEdge portMap edgeMap) edgeOrder
  let dEdges' = IM.fromList [ (unEdgeId (eId edge), edge) | edge <- edges' ]
  dProd' <- buildIncidence "producer" eOuts edges' dPortTy'
  dCons' <- buildIncidence "consumer" eIns edges' dPortTy'
  pure
    Diagram
      { dMode = dMode diag
      , dTmCtx = dTmCtx diag
      , dIn = dIn'
      , dOut = dOut'
      , dPortTy = dPortTy'
      , dPortLabel = dPortLabel'
      , dProd = dProd'
      , dCons = dCons'
      , dEdges = dEdges'
      , dNextPort = length portOrder
      , dNextEdge = length edgeOrder
      }
  where
    requirePortMap mp pid =
      case M.lookup pid mp of
        Nothing -> Left "canonDiagram: missing port mapping"
        Just pid' -> Right pid'

    requireEdgeMap mp eid =
      case M.lookup eid mp of
        Nothing -> Left "canonDiagram: missing edge mapping"
        Just eid' -> Right eid'

    requirePortType pid =
      case IM.lookup (unPortId pid) (dPortTy diag) of
        Nothing -> Left "canonDiagram: missing source port type"
        Just ty -> Right ty

    requireEdge eid =
      case IM.lookup (unEdgeId eid) (dEdges diag) of
        Nothing -> Left "canonDiagram: missing source edge"
        Just edge -> Right edge

    rebuildEdge portMap edgeMap oldEid = do
      oldEdge <- requireEdge oldEid
      newEid <- requireEdgeMap edgeMap oldEid
      ins' <- mapM (requirePortMap portMap) (eIns oldEdge)
      outs' <- mapM (requirePortMap portMap) (eOuts oldEdge)
      pure oldEdge { eId = newEid, eIns = ins', eOuts = outs' }

    buildIncidence label select edges portTy =
      foldM insertEdge initial edges
      where
        initial = IM.fromList [ (k, Nothing) | k <- IM.keys portTy ]
        insertEdge mp edge = foldM (insertPort (eId edge)) mp (select edge)
        insertPort eid mp pid =
          let k = unPortId pid
           in case IM.lookup k mp of
                Nothing ->
                  Left ("canonDiagram: missing " <> label <> " incidence slot")
                Just Nothing ->
                  Right (IM.insert k (Just eid) mp)
                Just (Just _) ->
                  Left ("canonDiagram: duplicate " <> label <> " incidence")

unionDisjointIntMap :: Text -> IM.IntMap a -> IM.IntMap a -> Either Text (IM.IntMap a)
unionDisjointIntMap label left right =
  let ksL = IM.keysSet left
      ksR = IM.keysSet right
      overlap = IS.toList (IS.intersection ksL ksR)
  in if null overlap
    then Right (IM.union left right)
    else Left (label <> ": key collision " <> T.pack (show overlap))
