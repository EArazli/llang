{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Diagram
  ( Diagram(..)
  , idDTm
  , idD
  , genDTm
  , genD
  , genDWithArgsTm
  , genDWithArgs
  , weakenDiagramTmCtxTo
  , compD
  , tensorD
  , unionDiagram
  , diagramDom
  , diagramCod
  , applySubstDiagram
  , freeVarsDiagram
  , providerRefsDiagram
  , moduleValueRefsDiagram
  , mapProviderRefsDiagram
  , mapModuleValueRefsDiagram
  , binderArgMetaVarsDiagram
  , spliceMetaVarsDiagram
  , binderMetaVarsDiagram
  ) where

import Control.Monad.Identity (runIdentity)
import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Common.ModuleRef (ModuleValueRef)
import Strat.Common.Provider (ProviderRef)
import Strat.Poly.DiagramBuild (allocPorts)
import Strat.Poly.Graph
import qualified Strat.Poly.DiagramInfo as DI
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (Context, Obj, TmVar(..), CodeArg(..), freeVarsObj, freeVarsTerm)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Subst (Subst, emptySubst)
import Strat.Poly.Term.SubstRuntime (applySubstCtx)
import qualified Strat.Poly.Term.SubstRuntime as SubstRuntime (applySubstDiagram)
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.UnifyFlex (unifyCtx)
import Strat.Poly.Traversal (foldDiagram, traverseDiagram)


idDTm :: ModeName -> [Obj] -> Context -> Diagram
idDTm mode tmCtx ctx =
  let (ports, diag') = allocPorts ctx (emptyDiagram mode tmCtx)
  in diag'
      { dIn = ports
      , dOut = ports
      }

idD :: ModeName -> Context -> Diagram
idD mode = idDTm mode []

genDTm :: ModeName -> [Obj] -> Context -> Context -> GenName -> Either Text Diagram
genDTm mode tmCtx dom cod gen =
  genDWithArgsTm mode tmCtx dom cod gen []

genD :: ModeName -> Context -> Context -> GenName -> Either Text Diagram
genD mode dom cod gen =
  genDTm mode [] dom cod gen

genDWithArgsTm :: ModeName -> [Obj] -> Context -> Context -> GenName -> [CodeArg] -> Either Text Diagram
genDWithArgsTm mode tmCtx dom cod gen args = do
  let (inPorts, diag1) = allocPorts dom (emptyDiagram mode tmCtx)
  let (outPorts, diag2) = allocPorts cod diag1
  diag3 <- case addEdgePayload (PGen gen args []) inPorts outPorts diag2 of
    Left err -> Left ("genD " <> renderGen gen <> ": " <> err)
    Right d -> Right d
  let diagFinal = diag3 { dIn = inPorts, dOut = outPorts }
  validateDiagram diagFinal
  pure diagFinal

genDWithArgs :: ModeName -> Context -> Context -> GenName -> [CodeArg] -> Either Text Diagram
genDWithArgs mode = genDWithArgsTm mode []

renderGen :: GenName -> Text
renderGen (GenName t) = t

compD :: TypeTheory -> Diagram -> Diagram -> Either Text Diagram
compD tt g f
  | dMode g /= dMode f = Left "diagram composition mode mismatch"
  | otherwise = do
      tmCtxF <- applySubstCtx tt emptySubst (dTmCtx f)
      tmCtxG <- applySubstCtx tt emptySubst (dTmCtx g)
      if tmCtxG == tmCtxF
        then Right ()
        else Left "diagram composition term-context mismatch"
      domG <- diagramDom g
      codF <- diagramCod f
      let flex = S.unions (map freeVarsObj (codF <> domG))
      subst <-
        case unifyCtx tt tmCtxF flex codF domG of
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
  | dTmCtx f /= dTmCtx g = Left "diagram tensor term-context mismatch"
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
      case IM.lookup (unPortId pid) (dPortObj diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty

diagramCod :: Diagram -> Either Text Context
diagramCod diag = mapM (lookupPort "diagramCod") (dOut diag)
  where
    lookupPort label pid =
      case IM.lookup (unPortId pid) (dPortObj diag) of
        Nothing -> Left (label <> ": missing port type")
        Just ty -> Right ty

applySubstDiagram :: TypeTheory -> Subst -> Diagram -> Either Text Diagram
applySubstDiagram = SubstRuntime.applySubstDiagram

freeVarsDiagram :: Diagram -> S.Set TmVar
freeVarsDiagram = DI.freeVarsDiagram

providerRefsDiagram :: Diagram -> S.Set ProviderRef
providerRefsDiagram =
  foldDiagram (\_ -> mempty) onPayload (\_ -> mempty) (\_ -> mempty)
  where
    onPayload payload =
      case payload of
        PProvider ref -> S.singleton ref
        _ -> S.empty


moduleValueRefsDiagram :: Diagram -> S.Set ModuleValueRef
moduleValueRefsDiagram =
  foldDiagram (\_ -> mempty) onPayload (\_ -> mempty) (\_ -> mempty)
  where
    onPayload payload =
      case payload of
        PModuleRef ref -> S.singleton ref
        _ -> S.empty


mapProviderRefsDiagram :: (ProviderRef -> ProviderRef) -> Diagram -> Diagram
mapProviderRefsDiagram f =
  runIdentity . traverseDiagram pure onPayload pure pure
  where
    onPayload payload =
      pure $
        case payload of
          PProvider ref -> PProvider (f ref)
          _ -> payload


mapModuleValueRefsDiagram :: (ModuleValueRef -> ModuleValueRef) -> Diagram -> Diagram
mapModuleValueRefsDiagram f =
  runIdentity . traverseDiagram pure onPayload pure pure
  where
    onPayload payload =
      pure $
        case payload of
          PModuleRef ref -> PModuleRef (f ref)
          _ -> payload

binderArgMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
binderArgMetaVarsDiagram =
  foldDiagram (\_ -> mempty) (\_ -> mempty) (\_ -> mempty) onBArg
  where
    onBArg barg =
      case barg of
        BAMeta x -> S.singleton x
        _ -> mempty

spliceMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
spliceMetaVarsDiagram =
  foldDiagram (\_ -> mempty) onPayload (\_ -> mempty) (\_ -> mempty)
  where
    onPayload payload =
      case payload of
        PSplice x _ -> S.singleton x
        _ -> mempty

binderMetaVarsDiagram :: Diagram -> S.Set BinderMetaVar
binderMetaVarsDiagram d =
  binderArgMetaVarsDiagram d <> spliceMetaVarsDiagram d

unionDiagram :: Diagram -> Diagram -> Either Text Diagram
unionDiagram left right
  | dMode left /= dMode right = Left "unionDiagram: mode mismatch"
  | dTmCtx left /= dTmCtx right = Left "unionDiagram: term-context mismatch"
  | otherwise = do
      portTy <- unionDisjointIntMap "unionDiagram ports" (dPortObj left) (dPortObj right)
      portLabel <- unionDisjointIntMap "unionDiagram labels" (dPortLabel left) (dPortLabel right)
      prod <- unionDisjointIntMap "unionDiagram producers" (dProd left) (dProd right)
      cons <- unionDisjointIntMap "unionDiagram consumers" (dCons left) (dCons right)
      edges <- unionDisjointIntMap "unionDiagram edges" (dEdges left) (dEdges right)
      pure left
        { dPortObj = portTy
        , dPortLabel = portLabel
        , dProd = prod
        , dCons = cons
        , dEdges = edges
        , dNextPort = max (dNextPort left) (dNextPort right)
        , dNextEdge = max (dNextEdge left) (dNextEdge right)
        }
