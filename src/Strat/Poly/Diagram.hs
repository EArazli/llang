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
  , binderArgMetaVarsDiagram
  , spliceMetaVarsDiagram
  , binderMetaVarsDiagram
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Functor.Identity (runIdentity)
import Strat.Poly.Graph
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (Context, TypeExpr, TyVar, IxVar, freeTyVarsType, freeIxVarsType)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar, freeAttrVarsMap, applyAttrSubstMap, renameAttrTerm)
import Strat.Poly.UnifyTy
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.Traversal (foldDiagram, traverseDiagram)


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

compD :: TypeTheory -> Diagram -> Diagram -> Either Text Diagram
compD tt g f
  | dMode g /= dMode f = Left "diagram composition mode mismatch"
  | otherwise = do
      ixCtxF <- applySubstCtx tt emptySubst (dIxCtx f)
      ixCtxG <- applySubstCtx tt emptySubst (dIxCtx g)
      if ixCtxG == ixCtxF
        then Right ()
        else Left "diagram composition index-context mismatch"
      domG <- diagramDom g
      codF <- diagramCod f
      let tyFlex = S.unions (map freeTyVarsType (codF <> domG))
      let ixFlex = S.unions (map freeIxVarsType (codF <> domG))
      subst <-
        case unifyCtx tt ixCtxF tyFlex ixFlex codF domG of
          Left err -> Left ("diagram composition boundary mismatch: " <> err)
          Right s -> Right s
      f' <- applySubstDiagram tt subst f
      g' <- applySubstDiagram tt subst g
      composeAligned g' f'

composeAligned :: Diagram -> Diagram -> Either Text Diagram
composeAligned g f = do
  let gShift = shiftDiagram (dNextPort f) (dNextEdge f) g
  merged <- unionDiagram f gShift
  let merged' = merged { dIn = dIn f, dOut = dOut gShift }
  let outsF = dOut f
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
      case IM.lookup (unPortId pid) (dPortTy diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty

diagramCod :: Diagram -> Either Text Context
diagramCod diag = mapM (lookupPort "diagramCod") (dOut diag)
  where
    lookupPort label pid =
      case IM.lookup (unPortId pid) (dPortTy diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty

applySubstDiagram :: TypeTheory -> Subst -> Diagram -> Either Text Diagram
applySubstDiagram tt subst =
  traverseDiagram onDiag pure pure
  where
    onDiag d = do
      dPortTy' <- IM.traverseWithKey (\_ ty -> applySubstTy tt subst ty) (dPortTy d)
      dIxCtx' <- mapM (applySubstTy tt subst) (dIxCtx d)
      pure d { dIxCtx = dIxCtx', dPortTy = dPortTy' }

freeTyVarsDiagram :: Diagram -> S.Set TyVar
freeTyVarsDiagram =
  foldDiagram onDiag (\_ -> mempty) (\_ -> mempty)
  where
    onDiag d =
      S.unions
        [ S.unions (map freeTyVarsType (IM.elems (dPortTy d)))
        , S.unions (map freeTyVarsType (dIxCtx d))
        ]

freeAttrVarsDiagram :: Diagram -> S.Set AttrVar
freeAttrVarsDiagram =
  foldDiagram (\_ -> mempty) onPayload (\_ -> mempty)
  where
    onPayload payload =
      case payload of
        PGen _ attrs _ -> freeAttrVarsMap attrs
        _ -> mempty

freeIxVarsDiagram :: Diagram -> S.Set IxVar
freeIxVarsDiagram =
  foldDiagram onDiag (\_ -> mempty) (\_ -> mempty)
  where
    onDiag d =
      S.unions
        [ S.unions (map freeIxVarsType (IM.elems (dPortTy d)))
        , S.unions (map freeIxVarsType (dIxCtx d))
        ]

binderArgMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
binderArgMetaVarsDiagram =
  foldDiagram (\_ -> mempty) (\_ -> mempty) onBArg
  where
    onBArg barg =
      case barg of
        BAMeta x -> S.singleton x
        _ -> mempty

spliceMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
spliceMetaVarsDiagram =
  foldDiagram (\_ -> mempty) onPayload (\_ -> mempty)
  where
    onPayload payload =
      case payload of
        PSplice x -> S.singleton x
        _ -> mempty

binderMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
binderMetaVarsDiagram d =
  binderArgMetaVarsDiagram d <> spliceMetaVarsDiagram d

applyAttrSubstDiagram :: AttrSubst -> Diagram -> Diagram
applyAttrSubstDiagram subst =
  runIdentity . traverseDiagram pure onPayload pure
  where
    onPayload payload =
      pure $
        case payload of
          PGen g attrs bargs -> PGen g (applyAttrSubstMap subst attrs) bargs
          _ -> payload

renameAttrVarsDiagram :: (Text -> Text) -> Diagram -> Diagram
renameAttrVarsDiagram rename =
  runIdentity . traverseDiagram pure onPayload pure
  where
    onPayload payload =
      pure $
        case payload of
          PGen g attrs bargs -> PGen g (M.map (renameAttrTerm rename) attrs) bargs
          _ -> payload

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
        , dNextPort = max (dNextPort left) (dNextPort right)
        , dNextEdge = max (dNextEdge left) (dNextEdge right)
        }
