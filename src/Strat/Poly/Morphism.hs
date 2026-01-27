{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Morphism
  ( Morphism(..)
  , applyMorphismDiagram
  , checkMorphism
  , isRenamingMorphism
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
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
import Strat.Kernel.Types (RuleClass(..), Orientation(..))


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
    modeSrc = dMode diagSrc
    edgeIds = IM.keys (dEdges diagSrc)
    step acc edgeKey = do
      diagTgt <- acc
      case IM.lookup edgeKey (dEdges diagSrc) of
        Nothing -> Left "applyMorphismDiagram: missing source edge"
        Just edgeSrc ->
          case ePayload edgeSrc of
            PGen genName -> do
              genDecl <- lookupGenInMode (morSrc mor) modeSrc genName
              subst <- instantiateGen genDecl diagSrc edgeSrc
              let substTgt = M.map (applyTypeMapTy mor modeSrc) subst
              case M.lookup (modeSrc, genName) (morGenMap mor) of
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
  let cells = filter (cellEnabled (morPolicy mor)) (dCells2 (morSrc mor))
  fastOk <- inclusionFastPath mor
  if fastOk
    then Right ()
    else do
      renameOk <- renamingFastPath mor cells
      if renameOk
        then Right ()
        else mapM_ (checkCell mor) cells
  pure ()

isRenamingMorphism :: Morphism -> Bool
isRenamingMorphism mor =
  case (buildTypeRenaming mor, buildGenRenaming mor) of
    (Just _tyRen, Just _genRen) -> True
    _ -> False

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
        l' <- renumberDiagram l
        r' <- renumberDiagram r
        ok <- diagramIsoEq l' r'
        if ok
          then Right ()
          else Left "checkMorphism: equation violation (normal forms differ)"
    _ -> do
      ok <- joinableWithin fuel rules lhs rhs
      if ok
        then Right ()
        else Left "checkMorphism: equation undecided or violated"

inclusionFastPath :: Morphism -> Either Text Bool
inclusionFastPath mor
  | not (M.null (morTypeMap mor)) = Right False
  | otherwise = do
      okGens <- allM (genIsIdentity mor) (allGens (morSrc mor))
      if not okGens
        then Right False
        else do
          let tgtCells = M.fromList [(c2Name c, c) | c <- dCells2 (morTgt mor)]
          allM (cellMatches tgtCells) (dCells2 (morSrc mor))
  where
    genIsIdentity m gen = do
      let mode = gdMode gen
      let name = gdName gen
      let dom = gdDom gen
      let cod = gdCod gen
      case M.lookup (mode, name) (morGenMap m) of
        Nothing -> Right False
        Just image -> do
          expected <- genD mode dom cod name
          diagramIsoEq expected image
    cellMatches tgtMap cell =
      case M.lookup (c2Name cell) tgtMap of
        Nothing -> Right False
        Just tgt ->
          if c2Class cell /= c2Class tgt || c2Orient cell /= c2Orient tgt
            then Right False
            else do
              okL <- diagramIsoEq (c2LHS cell) (c2LHS tgt)
              okR <- diagramIsoEq (c2RHS cell) (c2RHS tgt)
              pure (okL && okR)

renamingFastPath :: Morphism -> [Cell2] -> Either Text Bool
renamingFastPath mor srcCells = do
  let tgt = morTgt mor
  case (buildTypeRenaming mor, buildGenRenaming mor) of
    (Just _tyRen, Just _genRen) -> do
      let tgtSig = S.fromList [ (c2Name c, c2Class c, c2Orient c) | c <- dCells2 tgt ]
      allM (\cell -> Right ((c2Name cell, c2Class cell, c2Orient cell) `S.member` tgtSig)) srcCells
    _ -> Right False

buildTypeRenaming :: Morphism -> Maybe (M.Map (ModeName, TypeName) TypeName)
buildTypeRenaming mor = do
  let src = morSrc mor
  mp <- foldl step (Just M.empty) (allTypes src)
  if injective (M.elems mp)
    then Just mp
    else Nothing
  where
    step acc (mode, name, arity) = do
      mp <- acc
      let key = (mode, name)
      let mapped =
            case M.lookup key (morTypeMap mor) of
              Nothing -> Just name
              Just expr ->
                case expr of
                  TCon tgt params
                    | length params == arity && all isVar params && distinct params -> Just tgt
                  _ -> Nothing
      case mapped of
        Nothing -> Nothing
        Just tgt -> Just (M.insert key tgt mp)
    isVar (TVar _) = True
    isVar _ = False
    distinct params =
      let vars = [ v | TVar v <- params ]
      in length vars == length (S.fromList vars)

buildGenRenaming :: Morphism -> Maybe (M.Map (ModeName, GenName) GenName)
buildGenRenaming mor = do
  mp <- foldl step (Just M.empty) (allGens (morSrc mor))
  if injective (M.elems mp)
    then Just mp
    else Nothing
  where
    step acc gen = do
      mp <- acc
      let mode = gdMode gen
      let name = gdName gen
      diag <- M.lookup (mode, name) (morGenMap mor)
      case singleGenNameMaybe diag of
        Nothing -> Nothing
        Just tgt -> Just (M.insert (mode, name) tgt mp)

singleGenNameMaybe :: Diagram -> Maybe GenName
singleGenNameMaybe diag =
  case renumberDiagram diag of
    Left _ -> Nothing
    Right canon ->
      case IM.elems (dEdges canon) of
        [edge] ->
          let boundary = dIn canon <> dOut canon
              edgePorts = eIns edge <> eOuts edge
              allPorts = diagramPortIds canon
          in case ePayload edge of
            PGen g
              | boundary == edgePorts && length allPorts == length boundary -> Just g
            _ -> Nothing
        _ -> Nothing

injective :: Ord a => [a] -> Bool
injective xs =
  let set = S.fromList xs
  in length xs == S.size set

cellEnabled :: RewritePolicy -> Cell2 -> Bool
cellEnabled policy cell =
  case policy of
    UseStructuralAsBidirectional -> True
    UseOnlyComputationalLR ->
      c2Class cell == Computational && (c2Orient cell == LR || c2Orient cell == Bidirectional)
    UseAllOriented ->
      case c2Orient cell of
        Unoriented -> False
        _ -> True

allM :: (a -> Either Text Bool) -> [a] -> Either Text Bool
allM _ [] = Right True
allM f (x:xs) = do
  ok <- f x
  if ok
    then allM f xs
    else Right False

allGens :: Doctrine -> [GenDecl]
allGens doc =
  concatMap M.elems (M.elems (dGens doc))

allTypes :: Doctrine -> [(ModeName, TypeName, Int)]
allTypes doc =
  [ (mode, name, arity)
  | (mode, table) <- M.toList (dTypes doc)
  , (name, arity) <- M.toList table
  ]

lookupGenInMode :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGenInMode doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "applyMorphismDiagram: unknown generator"
    Just gd -> Right gd

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
