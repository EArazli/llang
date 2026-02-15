{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DiagramIso
  ( diagramIsoEq
  , diagramIsoEqSlow
  , diagramIsoMatchWithVars
  , diagramIsoMatchWithVarsFrom
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Attr (AttrSubst, AttrVar, unifyAttrFlex)
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , PortId
  , EdgeId
  , BinderArg(..)
  , diagramPortType
  , unPortId
  , unEdgeId
  , canonDiagram
  )
import Strat.Poly.TypeExpr (TypeExpr, TyVar, TmVar(..))
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.UnifyTy (Subst, emptySubst, unifyTyFlex, applySubstCtx)


data IsoState extra = IsoState
  { isoPortMap :: M.Map PortId PortId
  , isoEdgeMap :: M.Map EdgeId EdgeId
  , isoUsedPorts :: S.Set PortId
  , isoUsedEdges :: S.Set EdgeId
  , isoQueue :: [(PortId, PortId)]
  , isoExtra :: extra
  } deriving (Eq, Show)

data IsoExtra = IsoExtra
  { ieTySubst :: Subst
  , ieAttrSubst :: AttrSubst
  } deriving (Eq, Show)

data IsoAlgo extra = IsoAlgo
  { iaComparePorts
      :: Diagram
      -> Diagram
      -> extra
      -> TypeExpr
      -> TypeExpr
      -> Either Text [extra]
  , iaComparePayload
      :: (extra -> Diagram -> Diagram -> Either Text [extra])
      -> extra
      -> EdgePayload
      -> EdgePayload
      -> Either Text [extra]
  , iaPayloadShapeOk :: EdgePayload -> EdgePayload -> Bool
  , iaTmCtxOk :: Diagram -> Diagram -> extra -> Bool
  }

diagramIsoEq :: Diagram -> Diagram -> Either Text Bool
diagramIsoEq left right = do
  left' <- canonDiagram left
  right' <- canonDiagram right
  pure (left' == right')

diagramIsoEqSlow :: Diagram -> Diagram -> Either Text Bool
diagramIsoEqSlow left right =
  fmap (not . null) (diagramIsoWith algoEq () left right)

diagramIsoMatchWithVars
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set TmVar
  -> S.Set AttrVar
  -> Diagram
  -> Diagram
  -> Either Text [(Subst, AttrSubst)]
diagramIsoMatchWithVars tt tyFlex tmFlex attrFlex =
  diagramIsoMatchWithVarsFrom tt tyFlex tmFlex attrFlex emptySubst M.empty

diagramIsoMatchWithVarsFrom
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set TmVar
  -> S.Set AttrVar
  -> Subst
  -> AttrSubst
  -> Diagram
  -> Diagram
  -> Either Text [(Subst, AttrSubst)]
diagramIsoMatchWithVarsFrom tt tyFlex tmFlex attrFlex tySubst attrSubst left right = do
  let initExtra = IsoExtra tySubst attrSubst
  xs <- diagramIsoWith (algoMatch tt tyFlex tmFlex attrFlex) initExtra left right
  pure [ (ieTySubst ex, ieAttrSubst ex) | ex <- xs ]

diagramIsoWith
  :: IsoAlgo extra
  -> extra
  -> Diagram
  -> Diagram
  -> Either Text [extra]
diagramIsoWith algo extra0 left right
  | dMode left /= dMode right = Right []
  | not (iaTmCtxOk algo left right extra0) = Right []
  | length (dIn left) /= length (dIn right) = Right []
  | length (dOut left) /= length (dOut right) = Right []
  | IM.size (dPortTy left) /= IM.size (dPortTy right) = Right []
  | IM.size (dEdges left) /= IM.size (dEdges right) = Right []
  | otherwise =
      case foldl addInit (Just emptyState) initPairs of
        Nothing -> Right []
        Just st0 -> isoSearch st0
  where
    emptyState = IsoState M.empty M.empty S.empty S.empty [] extra0
    initPairs = zip (dIn left) (dIn right) <> zip (dOut left) (dOut right)

    addInit st (p1, p2) = st >>= \st' -> addPortPair st' p1 p2

    recurse extra d1 d2 = diagramIsoWith algo extra d1 d2

    isoSearch st = do
      propagated <- propagateQueue st
      fmap concat (mapM expand propagated)

    expand st
      | done st = Right [isoExtra st]
      | otherwise =
          case pickNextUnmappedEdge st of
            Nothing -> Right []
            Just e1 -> do
              let candidates = filter (edgeCandidate e1) (unmappedEdges st)
              fmap concat
                ( mapM
                    (\e2 -> do
                      sts <- addEdgePair recurse st e1 e2
                      fmap concat (mapM isoSearch sts)
                    )
                    candidates
                )

    done st =
      M.size (isoEdgeMap st) == IM.size (dEdges left)
        && M.size (isoPortMap st) == IM.size (dPortTy left)

    propagateQueue st0 =
      case isoQueue st0 of
        [] -> Right [st0]
        ((p1, p2) : rest) -> do
          ty1 <- requirePortType "diagramIsoWith: missing left port type" left p1
          ty2 <- requirePortType "diagramIsoWith: missing right port type" right p2
          extras <- iaComparePorts algo left right (isoExtra st0) ty1 ty2
          st1s <-
            fmap concat
              ( mapM
                  ( \extra' ->
                      mapIncidentEdges
                        p1
                        p2
                        st0 { isoQueue = rest, isoExtra = extra' }
                  )
                  extras
              )
          fmap concat (mapM propagateQueue st1s)

    mapIncidentEdges p1 p2 st = do
      stProd <-
        mapEndpoint
          (lookupIncidentEdge left (dProd left) p1)
          (lookupIncidentEdge right (dProd right) p2)
          st
      fmap concat
        ( mapM
            ( mapEndpoint
                (lookupIncidentEdge left (dCons left) p1)
                (lookupIncidentEdge right (dCons right) p2)
            )
            stProd
        )

    mapEndpoint Nothing Nothing st = Right [st]
    mapEndpoint (Just e1) (Just e2) st = addEdgePair recurse st e1 e2
    mapEndpoint _ _ _ = Right []

    lookupIncidentEdge diag mp pid =
      case IM.lookup (unPortId pid) mp of
        Just (Just eid) -> IM.lookup (unEdgeId eid) (dEdges diag)
        _ -> Nothing

    addPortPair st p1 p2 =
      case M.lookup p1 (isoPortMap st) of
        Just mapped ->
          if mapped == p2
            then Just st
            else Nothing
        Nothing ->
          if p2 `S.member` isoUsedPorts st
            then Nothing
            else
              Just
                st
                  { isoPortMap = M.insert p1 p2 (isoPortMap st)
                  , isoUsedPorts = S.insert p2 (isoUsedPorts st)
                  , isoQueue = isoQueue st <> [(p1, p2)]
                  }

    addEdgePair recurse' st e1 e2 =
      case M.lookup (eId e1) (isoEdgeMap st) of
        Just mapped ->
          if mapped == eId e2
            then Right [st]
            else Right []
        Nothing ->
          if eId e2 `S.member` isoUsedEdges st
            || length (eIns e1) /= length (eIns e2)
            || length (eOuts e1) /= length (eOuts e2)
            || not (iaPayloadShapeOk algo (ePayload e1) (ePayload e2))
            then Right []
            else do
              extras <- iaComparePayload algo recurse' (isoExtra st) (ePayload e1) (ePayload e2)
              let pairs = zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2)
              pure
                [ st''
                | extra' <- extras
                , let st' =
                        st
                          { isoEdgeMap = M.insert (eId e1) (eId e2) (isoEdgeMap st)
                          , isoUsedEdges = S.insert (eId e2) (isoUsedEdges st)
                          , isoExtra = extra'
                          }
                , Just st'' <- [foldl addPair (Just st') pairs]
                ]
      where
        addPair mSt (p1, p2) = mSt >>= \st' -> addPortPair st' p1 p2

    pickNextUnmappedEdge st =
      case filter (\e -> M.notMember (eId e) (isoEdgeMap st)) (IM.elems (dEdges left)) of
        [] -> Nothing
        e : _ -> Just e

    unmappedEdges st =
      [ e
      | e <- IM.elems (dEdges right)
      , eId e `S.notMember` isoUsedEdges st
      ]

    edgeCandidate e1 e2 =
      length (eIns e1) == length (eIns e2)
        && length (eOuts e1) == length (eOuts e2)
        && iaPayloadShapeOk algo (ePayload e1) (ePayload e2)

    requirePortType msg diag pid =
      case diagramPortType diag pid of
        Nothing -> Left msg
        Just ty -> Right ty

algoEq :: IsoAlgo ()
algoEq =
  IsoAlgo
    { iaComparePorts = \_ _ _ ty1 ty2 -> Right [() | ty1 == ty2]
    , iaComparePayload = comparePayload
    , iaPayloadShapeOk = payloadShape
    , iaTmCtxOk = \left right _ -> dTmCtx left == dTmCtx right
    }
  where
    comparePayload recurse _ p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2)
          | g1 == g2
              && attrs1 == attrs2
              && length bargs1 == length bargs2 ->
              foldl step (Right [()]) (zip bargs1 bargs2)
          | otherwise ->
              Right []
        (PBox _ d1, PBox _ d2) ->
          recurse () d1 d2
        (PFeedback d1, PFeedback d2) ->
          recurse () d1 d2
        (PSplice x, PSplice y)
          | x == y ->
              Right [()]
          | otherwise ->
              Right []
        (PTmMeta x, PTmMeta y)
          | sameTmMetaId x y ->
              Right [()]
          | otherwise ->
              Right []
        (PInternalDrop, PInternalDrop) ->
          Right [()]
        _ ->
          Right []
      where
        step acc pair = do
          xs <- acc
          fmap concat (mapM (\_ -> compareBinder pair) xs)

        compareBinder (a, b) =
          case (a, b) of
            (BAConcrete d1, BAConcrete d2) ->
              recurse () d1 d2
            (BAMeta x, BAMeta y)
              | x == y ->
                  Right [()]
              | otherwise ->
                  Right []
            _ ->
              Right []

    payloadShape p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          g1 == g2
            && attrs1 == attrs2
            && length bargs1 == length bargs2
            && and (zipWith binderShape bargs1 bargs2)
        (PBox _ _, PBox _ _) -> True
        (PFeedback _, PFeedback _) -> True
        (PSplice x, PSplice y) -> x == y
        (PTmMeta x, PTmMeta y) -> sameTmMetaId x y
        (PInternalDrop, PInternalDrop) -> True
        _ -> False

    binderShape (BAConcrete _) (BAConcrete _) = True
    binderShape (BAMeta x) (BAMeta y) = x == y
    binderShape _ _ = False

algoMatch
  :: TypeTheory
  -> S.Set TyVar
  -> S.Set TmVar
  -> S.Set AttrVar
  -> IsoAlgo IsoExtra
algoMatch tt tyFlex tmFlex attrFlex =
  IsoAlgo
    { iaComparePorts = comparePorts
    , iaComparePayload = comparePayload
    , iaPayloadShapeOk = payloadShape
    , iaTmCtxOk = tmCtxOk
    }
  where
    tmCtxOk left right extra =
      case
        ( applySubstCtx tt (ieTySubst extra) (dTmCtx left)
        , applySubstCtx tt (ieTySubst extra) (dTmCtx right)
        )
        of
        (Right left', Right right') -> left' == right'
        _ -> False

    comparePorts left _ extra ty1 ty2 =
      case applySubstCtx tt (ieTySubst extra) (dTmCtx left) of
        Left _ -> Right []
        Right tmCtx' ->
          case unifyTyFlex tt tmCtx' tyFlex tmFlex (ieTySubst extra) ty1 ty2 of
            Left _ -> Right []
            Right tySubst' ->
              Right [extra { ieTySubst = tySubst' }]

    comparePayload recurse extra p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2)
          | g1 /= g2
              || M.keysSet attrs1 /= M.keysSet attrs2
              || length bargs1 /= length bargs2 ->
              Right []
          | otherwise ->
              case foldl unifyField (Right (ieAttrSubst extra)) (M.toList attrs1) of
                Left _ -> Right []
                Right attrSubst ->
                  foldl step (Right [extra { ieAttrSubst = attrSubst }]) (zip bargs1 bargs2)
          where
            unifyField acc (field, term1) = do
              sub <- acc
              case M.lookup field attrs2 of
                Nothing -> Left "diagramIsoMatchWithVars: missing attribute field"
                Just term2 -> unifyAttrFlex attrFlex sub term1 term2

            step acc pair = do
              xs <- acc
              fmap concat (mapM (\ex -> compareBinder ex pair) xs)

            compareBinder ex (a, b) =
              case (a, b) of
                (BAConcrete d1, BAConcrete d2) ->
                  recurse ex d1 d2
                (BAMeta x, BAMeta y)
                  | x == y ->
                      Right [ex]
                  | otherwise ->
                      Right []
                _ ->
                  Right []
        (PBox _ d1, PBox _ d2) ->
          recurse extra d1 d2
        (PFeedback d1, PFeedback d2) ->
          recurse extra d1 d2
        (PSplice x, PSplice y)
          | x == y ->
              Right [extra]
          | otherwise ->
              Right []
        (PTmMeta x, PTmMeta y)
          | sameTmMetaId x y ->
              Right [extra]
          | otherwise ->
              Right []
        (PInternalDrop, PInternalDrop) ->
          Right [extra]
        _ ->
          Right []

    payloadShape p1 p2 =
      case (p1, p2) of
        (PGen g1 attrs1 bargs1, PGen g2 attrs2 bargs2) ->
          g1 == g2
            && M.keysSet attrs1 == M.keysSet attrs2
            && length bargs1 == length bargs2
            && and (zipWith binderShape bargs1 bargs2)
        (PBox _ _, PBox _ _) -> True
        (PFeedback _, PFeedback _) -> True
        (PSplice x, PSplice y) -> x == y
        (PTmMeta x, PTmMeta y) -> sameTmMetaId x y
        (PInternalDrop, PInternalDrop) -> True
        _ -> False

    binderShape (BAConcrete _) (BAConcrete _) = True
    binderShape (BAMeta x) (BAMeta y) = x == y
    binderShape _ _ = False

sameTmMetaId :: TmVar -> TmVar -> Bool
sameTmMetaId a b = tmvName a == tmvName b && tmvScope a == tmvScope b
