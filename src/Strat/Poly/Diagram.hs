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
  , binderArgMetaVarsDiagram
  , spliceMetaVarsDiagram
  , binderMetaVarsDiagram
  ) where

import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (Context, Obj, TmVar(..), CodeArg(..), freeVarsObj, freeVarsTerm)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.UnifyObj
  ( Subst
  , emptySubst
  , applySubstCtx
  , unifyCtx
  )
import qualified Strat.Poly.UnifyObj as U (applySubstDiagram)
import Strat.Poly.TypeTheory (TypeTheory)
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
applySubstDiagram = U.applySubstDiagram

freeVarsDiagram :: Diagram -> S.Set TmVar
freeVarsDiagram =
  foldDiagram onDiag onPayload onCodeArg (\_ -> mempty)
  where
    onDiag d =
      S.unions
        [ S.unions (map freeVarsObj (IM.elems (dPortObj d)))
        , S.unions (map freeVarsObj (dTmCtx d))
        ]
    onPayload payload =
      case payload of
        PTmMeta v -> S.singleton v
        PTmLit _ -> S.empty
        _ -> S.empty
    onCodeArg arg =
      case arg of
        CAObj obj -> freeVarsObj obj
        CATm tm -> freeVarsTerm tm

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

allocPorts :: Context -> Diagram -> ([PortId], Diagram)
allocPorts [] diag = ([], diag)
allocPorts (ty:rest) diag =
  let (pid, diag1) = freshPort ty diag
      (pids, diag2) = allocPorts rest diag1
  in (pid : pids, diag2)

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
