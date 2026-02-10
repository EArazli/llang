{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Diagram
  ( Diagram(..)
  , idDIx
  , idD
  , genDIx
  , genD
  , genDWithAttrsIx
  , genDWithAttrs
  , compD
  , tensorD
  , unionDiagram
  , diagramDom
  , diagramCod
  , applySubstDiagram
  , applyAttrSubstDiagram
  , renameAttrVarsDiagram
  , freeTyVarsDiagram
  , freeIxVarsDiagram
  , freeAttrVarsDiagram
  , binderMetaVarsDiagram
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.ModeTheory (ModeName, ModeTheory)
import Strat.Poly.TypeExpr (Context, TypeExpr(..), TyVar, TypeArg(..), IxTerm(..), IxVar(..), freeIxVarsType)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar, freeAttrVarsMap, applyAttrSubstMap, renameAttrTerm)
import Strat.Poly.UnifyTy


idDIx :: ModeName -> [TypeExpr] -> Context -> Diagram
idDIx mode ixCtx ctx =
  let (ports, diag') = allocPorts ctx (emptyDiagram mode ixCtx)
  in diag'
      { dIn = ports
      , dOut = ports
      }

idD :: ModeName -> Context -> Diagram
idD mode = idDIx mode []

genDIx :: ModeName -> [TypeExpr] -> Context -> Context -> GenName -> Either Text Diagram
genDIx mode ixCtx dom cod gen =
  genDWithAttrsIx mode ixCtx dom cod gen M.empty

genD :: ModeName -> Context -> Context -> GenName -> Either Text Diagram
genD mode dom cod gen =
  genDIx mode [] dom cod gen

genDWithAttrsIx :: ModeName -> [TypeExpr] -> Context -> Context -> GenName -> AttrMap -> Either Text Diagram
genDWithAttrsIx mode ixCtx dom cod gen attrs = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode ixCtx)
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- case addEdgePayload (PGen gen attrs []) inPorts outPorts diag2 of
    Left err -> Left ("genD " <> renderGen gen <> ": " <> err)
    Right d -> Right d
  let diagFinal = diag3 { dIn = inPorts, dOut = outPorts }
  validateDiagram diagFinal
  pure diagFinal

genDWithAttrs :: ModeName -> Context -> Context -> GenName -> AttrMap -> Either Text Diagram
genDWithAttrs mode = genDWithAttrsIx mode []

renderGen :: GenName -> Text
renderGen (GenName t) = t

compD :: ModeTheory -> Diagram -> Diagram -> Either Text Diagram
compD mt g f
  | dMode g /= dMode f = Left "diagram composition mode mismatch"
  | dIxCtx g /= dIxCtx f = Left "diagram composition index-context mismatch"
  | otherwise = do
      domG <- diagramDom g
      codF <- diagramCod f
      substTy <-
        case unifyCtxLegacy mt codF domG of
          Right s -> Right s
          Left err ->
            if codF == domG
              then Right M.empty
              else Left ("diagram composition boundary mismatch: " <> err)
      let subst = fromTyOnlySubst substTy
      let f' = applySubstDiagram mt subst f
      let g' = applySubstDiagram mt subst g
      let gShift = shiftDiagram (dNextPort f') (dNextEdge f') g'
      merged <- unionDiagram f' gShift
      let merged' = merged { dIn = dIn f', dOut = dOut gShift }
      let outsF = dOut f'
      let insG = dIn gShift
      if length outsF /= length insG
        then Left "diagram composition boundary mismatch"
        else do
          merged'' <- foldl step (Right merged') (zip outsF insG)
          validateDiagram merged''
          pure merged''
  where
    step acc (pOut, pIn) = do
      d <- acc
      mergePorts d pOut pIn

tensorD :: Diagram -> Diagram -> Either Text Diagram
tensorD f g
  | dMode f /= dMode g = Left "diagram tensor mode mismatch"
  | dIxCtx f /= dIxCtx g = Left "diagram tensor index-context mismatch"
  | otherwise = do
      let gShift = shiftDiagram (dNextPort f) (dNextEdge f) g
      merged <- unionDiagram f gShift
      let result = merged
            { dIn = dIn f <> dIn gShift
            , dOut = dOut f <> dOut gShift
            }
      validateDiagram result
      pure result

diagramDom :: Diagram -> Either Text Context
diagramDom diag = mapM (lookupPort "diagramDom") (dIn diag)
  where
    lookupPort label pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty
    portKey (PortId k) = k

diagramCod :: Diagram -> Either Text Context
diagramCod diag = mapM (lookupPort "diagramCod") (dOut diag)
  where
    lookupPort label pid =
      case IM.lookup (portKey pid) (dPortTy diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty
    portKey (PortId k) = k

applySubstDiagram :: ModeTheory -> Subst -> Diagram -> Diagram
applySubstDiagram mt subst diag =
  let dPortTy' = IM.map (applySubstTyLegacy mt (toTyOnlySubst subst)) (dPortTy diag)
      dIxCtx' = map (applySubstTyLegacy mt (toTyOnlySubst subst)) (dIxCtx diag)
      dEdges' = IM.map (mapEdgePayload mt subst) (dEdges diag)
  in diag { dIxCtx = dIxCtx', dPortTy = dPortTy', dEdges = dEdges' }

freeTyVarsDiagram :: Diagram -> S.Set TyVar
freeTyVarsDiagram diag =
  let portVars = S.fromList (concatMap varsInTy (IM.elems (dPortTy diag)))
      ixCtxVars = S.fromList (concatMap varsInTy (dIxCtx diag))
      payloadVars = S.unions (map freeTyVarsPayload (IM.elems (dEdges diag)))
  in S.unions [portVars, ixCtxVars, payloadVars]

freeAttrVarsDiagram :: Diagram -> S.Set AttrVar
freeAttrVarsDiagram diag =
  let payloadVars = S.unions (map freeAttrVarsPayload (IM.elems (dEdges diag)))
  in payloadVars

freeIxVarsDiagram :: Diagram -> S.Set IxVar
freeIxVarsDiagram diag =
  let portVars = S.unions (map freeIxVarsType (IM.elems (dPortTy diag)))
      ixCtxVars = S.unions (map freeIxVarsType (dIxCtx diag))
      payloadVars = S.unions (map freeIxVarsPayload (IM.elems (dEdges diag)))
   in S.unions [portVars, ixCtxVars, payloadVars]

binderMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
binderMetaVarsDiagram diag =
  S.unions (map binderMetasPayload (IM.elems (dEdges diag)))

varsInTy :: TypeExpr -> [TyVar]
varsInTy ty =
  case ty of
    TVar v -> [v]
    TCon _ args -> concatMap varsInArg args
    TMod _ inner -> varsInTy inner
  where
    varsInArg arg =
      case arg of
        TAType innerTy -> varsInTy innerTy
        TAIndex ix -> varsInIx ix

    varsInIx ix =
      case ix of
        IXVar v -> varsInTy (ixvSort v)
        IXBound _ -> []
        IXFun _ args -> concatMap varsInIx args

freeTyVarsPayload :: Edge -> S.Set TyVar
freeTyVarsPayload edge =
  case ePayload edge of
    PGen _ _ bargs ->
      S.unions (map freeFromBinderArg bargs)
    PBox _ inner ->
      freeTyVarsDiagram inner
    PSplice _ ->
      S.empty
  where
    freeFromBinderArg barg =
      case barg of
        BAConcrete inner -> freeTyVarsDiagram inner
        BAMeta _ -> S.empty

freeAttrVarsPayload :: Edge -> S.Set AttrVar
freeAttrVarsPayload edge =
  case ePayload edge of
    PGen _ attrs bargs ->
      S.union (freeAttrVarsMap attrs) (S.unions (map freeFromBinderArg bargs))
    PBox _ inner ->
      freeAttrVarsDiagram inner
    PSplice _ ->
      S.empty
  where
    freeFromBinderArg barg =
      case barg of
        BAConcrete inner -> freeAttrVarsDiagram inner
        BAMeta _ -> S.empty

freeIxVarsPayload :: Edge -> S.Set IxVar
freeIxVarsPayload edge =
  case ePayload edge of
    PGen _ _ bargs ->
      S.unions (map freeFromBinderArg bargs)
    PBox _ inner ->
      freeIxVarsDiagram inner
    PSplice _ ->
      S.empty
  where
    freeFromBinderArg barg =
      case barg of
        BAConcrete inner -> freeIxVarsDiagram inner
        BAMeta _ -> S.empty

binderMetasPayload :: Edge -> S.Set BinderMetaVar
binderMetasPayload edge =
  case ePayload edge of
    PGen _ _ bargs ->
      S.unions (map fromBinderArg bargs)
    PBox _ inner ->
      binderMetaVarsDiagram inner
    PSplice x ->
      S.singleton x
  where
    fromBinderArg barg =
      case barg of
        BAConcrete inner -> binderMetaVarsDiagram inner
        BAMeta x -> S.singleton x

mapEdgePayload :: ModeTheory -> Subst -> Edge -> Edge
mapEdgePayload mt subst edge =
  case ePayload edge of
    PGen g attrs bargs -> edge { ePayload = PGen g attrs (map mapBinderArg bargs) }
    PBox name inner -> edge { ePayload = PBox name (applySubstDiagram mt subst inner) }
    PSplice x -> edge { ePayload = PSplice x }
  where
    mapBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete (applySubstDiagram mt subst inner)
        BAMeta x -> BAMeta x


applyAttrSubstDiagram :: AttrSubst -> Diagram -> Diagram
applyAttrSubstDiagram subst diag =
  let dEdges' = IM.map (mapEdgePayloadAttr subst) (dEdges diag)
  in diag { dEdges = dEdges' }

renameAttrVarsDiagram :: (Text -> Text) -> Diagram -> Diagram
renameAttrVarsDiagram rename diag =
  let dEdges' = IM.map (mapEdgePayloadRename rename) (dEdges diag)
  in diag { dEdges = dEdges' }

mapEdgePayloadAttr :: AttrSubst -> Edge -> Edge
mapEdgePayloadAttr subst edge =
  case ePayload edge of
    PGen g attrs bargs -> edge { ePayload = PGen g (applyAttrSubstMap subst attrs) (map mapBinderArg bargs) }
    PBox name inner -> edge { ePayload = PBox name (applyAttrSubstDiagram subst inner) }
    PSplice x -> edge { ePayload = PSplice x }
  where
    mapBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete (applyAttrSubstDiagram subst inner)
        BAMeta x -> BAMeta x

mapEdgePayloadRename :: (Text -> Text) -> Edge -> Edge
mapEdgePayloadRename rename edge =
  case ePayload edge of
    PGen g attrs bargs -> edge { ePayload = PGen g (M.map (renameAttrTerm rename) attrs) (map mapBinderArg bargs) }
    PBox name inner -> edge { ePayload = PBox name (renameAttrVarsDiagram rename inner) }
    PSplice x -> edge { ePayload = PSplice x }
  where
    mapBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete (renameAttrVarsDiagram rename inner)
        BAMeta x -> BAMeta x

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
  in (pid : pids, diag2)

unionDiagram :: Diagram -> Diagram -> Either Text Diagram
unionDiagram left right
  | dMode left /= dMode right = Left "unionDiagram: mode mismatch"
  | dIxCtx left /= dIxCtx right = Left "unionDiagram: index-context mismatch"
  | otherwise = do
  portTy <- unionDisjointIntMap "unionDiagram ports" (dPortTy left) (dPortTy right)
  portLabel <- unionDisjointIntMap "unionDiagram labels" (dPortLabel left) (dPortLabel right)
  prod <- unionDisjointIntMap "unionDiagram producers" (dProd left) (dProd right)
  cons <- unionDisjointIntMap "unionDiagram consumers" (dCons left) (dCons right)
  edges <- unionDisjointIntMap "unionDiagram edges" (dEdges left) (dEdges right)
  pure left
    { dPortTy = portTy
    , dPortLabel = portLabel
    , dProd = prod
    , dCons = cons
    , dEdges = edges
    , dNextPort = dNextPort right
    , dNextEdge = dNextEdge right
    }
