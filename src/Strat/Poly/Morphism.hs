{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Morphism
  ( Morphism(..)
  , applyMorphismDiagram
  , checkMorphism
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Cell2
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, joinableWithin, NormalizationStatus(..))
import Strat.Poly.ModeTheory (ModeName(..))


data Morphism = Morphism
  { morName   :: Text
  , morSrc    :: Doctrine
  , morTgt    :: Doctrine
  , morTypeMap :: M.Map (ModeName, TypeName) TypeExpr
  , morGenMap  :: M.Map (ModeName, GenName) Diagram
  , morPolicy  :: RewritePolicy
  , morFuel    :: Int
  } deriving (Eq, Show)

applyMorphismDiagram :: Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagram mor diagSrc = do
  let diagTgt0 = applyTypeMapDiagram mor diagSrc
  diagTgt <- foldl step (Right diagTgt0) edgeIds
  validateDiagram diagTgt
  pure diagTgt
  where
    edgeIds = IM.keys (dEdges diagSrc)
    step acc edgeKey = do
      diagTgt <- acc
      case IM.lookup edgeKey (dEdges diagSrc) of
        Nothing -> Left "applyMorphismDiagram: missing source edge"
        Just edgeSrc ->
          case ePayload edgeSrc of
            PGen genName -> do
              genDecl <- lookupGen (morSrc mor) genName
              subst <- instantiateGen genDecl diagSrc edgeSrc
              let mode = gdMode genDecl
              let substTgt = M.map (applyTypeMapTy mor mode) subst
              case M.lookup (mode, genName) (morGenMap mor) of
                Nothing -> Left "applyMorphismDiagram: missing generator mapping"
                Just image -> do
                  let instImage = applySubstDiagram substTgt image
                  spliceEdge diagTgt edgeKey instImage
            PBox name inner -> do
              inner' <- applyMorphismDiagram mor inner
              updateEdgePayload diagTgt edgeKey (PBox name inner')

checkMorphism :: Morphism -> Either Text ()
checkMorphism mor = do
  mapM_ (checkGenMapping mor) (allGens (morSrc mor))
  mapM_ (checkCell mor) (dCells2 (morSrc mor))
  pure ()

checkGenMapping :: Morphism -> GenDecl -> Either Text ()
checkGenMapping mor gen = do
  let mode = gdMode gen
  let dom = map (applyTypeMapTy mor mode) (gdDom gen)
  let cod = map (applyTypeMapTy mor mode) (gdCod gen)
  image <- case M.lookup (mode, gdName gen) (morGenMap mor) of
    Nothing -> Left "checkMorphism: missing generator mapping"
    Just d -> Right d
  if dMode image /= mode
    then Left "checkMorphism: generator mapping mode mismatch"
    else do
      domImg <- diagramDom image
      codImg <- diagramCod image
      _ <- unifyCtx dom domImg
      _ <- unifyCtx cod codImg
      pure ()

checkCell :: Morphism -> Cell2 -> Either Text ()
checkCell mor cell = do
  lhs <- applyMorphismDiagram mor (c2LHS cell)
  rhs <- applyMorphismDiagram mor (c2RHS cell)
  let rules = rulesFromPolicy (morPolicy mor) (dCells2 (morTgt mor))
  let fuel = morFuel mor
  statusL <- normalize fuel rules lhs
  statusR <- normalize fuel rules rhs
  case (statusL, statusR) of
    (Finished l, Finished r) ->
      do
        l' <- canonicalizeDiagram l
        r' <- canonicalizeDiagram r
        if l' == r'
          then Right ()
          else Left "checkMorphism: equation violation (normal forms differ)"
    _ -> do
      ok <- joinableWithin fuel rules lhs rhs
      if ok
        then Right ()
        else Left "checkMorphism: equation undecided or violated"

allGens :: Doctrine -> [GenDecl]
allGens doc =
  concatMap M.elems (M.elems (dGens doc))

lookupGen :: Doctrine -> GenName -> Either Text GenDecl
lookupGen doc name =
  case [g | table <- M.elems (dGens doc), g <- M.elems table, gdName g == name] of
    (g:_) -> Right g
    [] -> Left "applyMorphismDiagram: unknown generator"

instantiateGen :: GenDecl -> Diagram -> Edge -> Either Text Subst
instantiateGen gen diag edge = do
  dom <- mapM (requirePortType diag) (eIns edge)
  cod <- mapM (requirePortType diag) (eOuts edge)
  s1 <- unifyCtx (gdDom gen) dom
  s2 <- unifyCtx (applySubstCtx s1 (gdCod gen)) cod
  pure (composeSubst s2 s1)

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "applyMorphismDiagram: missing port type"
    Just ty -> Right ty

spliceEdge :: Diagram -> Int -> Diagram -> Either Text Diagram
spliceEdge diag edgeKey image = do
  edge <-
    case IM.lookup edgeKey (dEdges diag) of
      Nothing -> Left "spliceEdge: missing edge"
      Just e -> Right e
  let ins = eIns edge
  let outs = eOuts edge
  diag1 <- deleteEdge diag edgeKey
  let imageShift = shiftDiagram (dNextPort diag1) (dNextEdge diag1) image
  diag2 <- insertDiagram diag1 imageShift
  let boundary = dIn imageShift <> dOut imageShift
  if length boundary /= length (ins <> outs)
    then Left "spliceEdge: boundary mismatch"
    else do
      (diag3, _) <- foldl step (Right (diag2, M.empty)) (zip (ins <> outs) boundary)
      validateDiagram diag3
      pure diag3
  where
    step acc (hostPort, imgPort) = do
      (d, seen) <- acc
      case M.lookup imgPort seen of
        Nothing -> do
          d' <- mergePorts d hostPort imgPort
          pure (d', M.insert imgPort hostPort seen)
        Just hostPort' -> do
          d' <- mergePorts d hostPort' hostPort
          pure (d', seen)

updateEdgePayload :: Diagram -> Int -> EdgePayload -> Either Text Diagram
updateEdgePayload diag edgeKey payload =
  case IM.lookup edgeKey (dEdges diag) of
    Nothing -> Left "updateEdgePayload: missing edge"
    Just edge ->
      let edge' = edge { ePayload = payload }
      in Right diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }

deleteEdge :: Diagram -> Int -> Either Text Diagram
deleteEdge diag edgeKey =
  case IM.lookup edgeKey (dEdges diag) of
    Nothing -> Left "deleteEdge: missing edge"
    Just edge -> do
      let d1 = diag { dEdges = IM.delete edgeKey (dEdges diag) }
      let d2 = clearConsumers d1 (eIns edge)
      let d3 = clearProducers d2 (eOuts edge)
      pure d3

clearConsumers :: Diagram -> [PortId] -> Diagram
clearConsumers d ports =
  let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
      portKey (PortId k) = k
      mp = dCons d
  in d { dCons = foldl clearOne mp ports }

clearProducers :: Diagram -> [PortId] -> Diagram
clearProducers d ports =
  let clearOne mp p = IM.adjust (const Nothing) (portKey p) mp
      portKey (PortId k) = k
      mp = dProd d
  in d { dProd = foldl clearOne mp ports }

insertDiagram :: Diagram -> Diagram -> Either Text Diagram
insertDiagram base extra = do
  portTy <- unionDisjointIntMap "insertDiagram ports" (dPortTy base) (dPortTy extra)
  prod <- unionDisjointIntMap "insertDiagram producers" (dProd base) (dProd extra)
  cons <- unionDisjointIntMap "insertDiagram consumers" (dCons base) (dCons extra)
  edges <- unionDisjointIntMap "insertDiagram edges" (dEdges base) (dEdges extra)
  pure base
    { dPortTy = portTy
    , dProd = prod
    , dCons = cons
    , dEdges = edges
    , dNextPort = dNextPort extra
    , dNextEdge = dNextEdge extra
    }

applyTypeMapDiagram :: Morphism -> Diagram -> Diagram
applyTypeMapDiagram mor diag =
  let mode = dMode diag
  in diag { dPortTy = IM.map (applyTypeMapTy mor mode) (dPortTy diag) }

applyTypeMapTy :: Morphism -> ModeName -> TypeExpr -> TypeExpr
applyTypeMapTy mor mode ty =
  case ty of
    TVar v -> TVar v
    TCon name args ->
      let args' = map (applyTypeMapTy mor mode) args
      in case M.lookup (mode, name) (morTypeMap mor) of
          Nothing -> TCon name args'
          Just tmpl -> applyTemplate args' tmpl
  where
    applyTemplate args tmpl =
      case tmpl of
        TCon name params ->
          if length params == length args && all isVar params
            then applySubstTy (M.fromList (zip (map extractVar params) args)) (TCon name params)
            else tmpl
        _ -> tmpl
    isVar (TVar _) = True
    isVar _ = False
    extractVar (TVar v) = v
    extractVar _ = TyVar "_"
