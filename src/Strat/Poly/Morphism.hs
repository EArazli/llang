{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Morphism
  ( Morphism(..)
  , TypeTemplate(..)
  , applyMorphismDiagram
  , checkMorphism
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Cell2
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.Attr
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, joinableWithin, NormalizationStatus(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))


data Morphism = Morphism
  { morName   :: Text
  , morSrc    :: Doctrine
  , morTgt    :: Doctrine
  , morIsCoercion :: Bool
  , morModeMap :: M.Map ModeName ModeName
  , morAttrSortMap :: M.Map AttrSort AttrSort
  , morTypeMap :: M.Map TypeRef TypeTemplate
  , morGenMap  :: M.Map (ModeName, GenName) Diagram
  , morPolicy  :: RewritePolicy
  , morFuel    :: Int
  } deriving (Eq, Show)

data TypeTemplate = TypeTemplate
  { ttParams :: [TyVar]
  , ttBody :: TypeExpr
  } deriving (Eq, Show)

mapMode :: Morphism -> ModeName -> Either Text ModeName
mapMode mor mode =
  case M.lookup mode (morModeMap mor) of
    Nothing -> Left "morphism: missing mode mapping"
    Just mode' -> Right mode'

mapAttrSort :: Morphism -> AttrSort -> Either Text AttrSort
mapAttrSort mor sortName =
  case M.lookup sortName (morAttrSortMap mor) of
    Nothing -> Left "morphism: missing attribute sort mapping"
    Just sortName' -> Right sortName'

mapTyVar :: Morphism -> TyVar -> Either Text TyVar
mapTyVar mor v = do
  mode' <- mapMode mor (tvMode v)
  pure v { tvMode = mode' }

mapTypeRef :: Morphism -> TypeRef -> Either Text TypeRef
mapTypeRef mor ref = do
  mode' <- mapMode mor (trMode ref)
  pure ref { trMode = mode' }

applyMorphismAttrTerm :: Morphism -> AttrTerm -> Either Text AttrTerm
applyMorphismAttrTerm mor term =
  case term of
    ATLit lit -> Right (ATLit lit)
    ATVar v -> do
      sortName' <- mapAttrSort mor (avSort v)
      Right (ATVar v { avSort = sortName' })

applyMorphismTy :: Morphism -> TypeExpr -> Either Text TypeExpr
applyMorphismTy mor ty =
  case ty of
    TVar v -> TVar <$> mapTyVar mor v
    TCon ref args -> do
      args' <- mapM (applyMorphismTy mor) args
      case M.lookup ref (morTypeMap mor) of
        Nothing -> do
          ref' <- mapTypeRef mor ref
          pure (TCon ref' args')
        Just tmpl -> do
          let subst = M.fromList (zip (ttParams tmpl) args')
          pure (applySubstTy subst (ttBody tmpl))

applyMorphismDiagram :: Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagram mor diagSrc = do
  modeTgt <- mapMode mor modeSrc
  portTy <- mapM (applyMorphismTy mor) (dPortTy diagSrc)
  let diagTgt0 = diagSrc { dMode = modeTgt, dPortTy = portTy }
  let edgeIds = IM.keys (dEdges diagSrc)
  let step acc edgeKey = do
        diagTgt <- acc
        case IM.lookup edgeKey (dEdges diagSrc) of
          Nothing -> Left "applyMorphismDiagram: missing source edge"
          Just edgeSrc ->
            case ePayload edgeSrc of
              PGen genName attrsSrc -> do
                genDecl <- lookupGenInMode (morSrc mor) modeSrc genName
                subst <- instantiateGen genDecl diagSrc edgeSrc
                substTgt <- mapSubst mor subst
                case M.lookup (modeSrc, genName) (morGenMap mor) of
                  Nothing -> Left "applyMorphismDiagram: missing generator mapping"
                  Just image -> do
                    if dMode image /= modeTgt
                      then Left "applyMorphismDiagram: generator mapping mode mismatch"
                      else Right ()
                    attrSubst <- instantiateAttrSubst mor genDecl attrsSrc
                    let instImage0 = applySubstDiagram substTgt image
                    let instImage = applyAttrSubstDiagram attrSubst instImage0
                    spliceEdge diagTgt edgeKey instImage
              PBox name inner -> do
                inner' <- applyMorphismDiagram mor inner
                updateEdgePayload diagTgt edgeKey (PBox name inner')
  diagTgt <- foldl step (Right diagTgt0) edgeIds
  validateDiagram diagTgt
  pure diagTgt
  where
    modeSrc = dMode diagSrc

mapSubst :: Morphism -> Subst -> Either Text Subst
mapSubst mor subst = do
  pairs <- mapM mapOne (M.toList subst)
  pure (M.fromList pairs)
  where
    mapOne (v, t) = do
      v' <- mapTyVar mor v
      t' <- applyMorphismTy mor t
      pure (v', t')

checkMorphism :: Morphism -> Either Text ()
checkMorphism mor = do
  validateModeMap mor
  validateAttrSortMap mor
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

validateModeMap :: Morphism -> Either Text ()
validateModeMap mor = do
  let srcModes = mtModes (dModes (morSrc mor))
  let tgtModes = mtModes (dModes (morTgt mor))
  case [ m | m <- S.toList srcModes, M.notMember m (morModeMap mor) ] of
    (m:_) -> Left ("checkMorphism: missing mode mapping for " <> renderModeName m)
    [] -> Right ()
  case [ m | (_, m) <- M.toList (morModeMap mor), m `S.notMember` tgtModes ] of
    (m:_) -> Left ("checkMorphism: unknown target mode " <> renderModeName m)
    [] -> Right ()
  where
    renderModeName (ModeName name) = name

validateAttrSortMap :: Morphism -> Either Text ()
validateAttrSortMap mor = do
  let srcSorts = dAttrSorts (morSrc mor)
  let tgtSorts = dAttrSorts (morTgt mor)
  case [ s | (s, _) <- M.toList (morAttrSortMap mor), M.notMember s srcSorts ] of
    (s:_) -> Left ("checkMorphism: unknown source attribute sort " <> renderAttrSort s)
    [] -> Right ()
  case [ s | (_, s) <- M.toList (morAttrSortMap mor), M.notMember s tgtSorts ] of
    (s:_) -> Left ("checkMorphism: unknown target attribute sort " <> renderAttrSort s)
    [] -> Right ()
  let usedSrcSorts =
        S.fromList
          [ sortName
          | table <- M.elems (dGens (morSrc mor))
          , gen <- M.elems table
          , (_, sortName) <- gdAttrs gen
          ]
  case [ s | s <- S.toList usedSrcSorts, M.notMember s (morAttrSortMap mor) ] of
    (s:_) -> Left ("checkMorphism: missing attribute sort mapping for " <> renderAttrSort s)
    [] -> Right ()
  mapM_ (checkLiteralKind srcSorts tgtSorts) (M.toList (morAttrSortMap mor))
  where
    renderAttrSort (AttrSort name) = name
    renderLitKind kind =
      case kind of
        LKInt -> "int"
        LKString -> "string"
        LKBool -> "bool"
    renderMaybeKind mKind =
      case mKind of
        Nothing -> "none"
        Just kind -> renderLitKind kind
    checkLiteralKind srcSorts tgtSorts (srcSort, tgtSort) = do
      srcDecl <-
        case M.lookup srcSort srcSorts of
          Nothing -> Left "checkMorphism: unknown source attribute sort declaration"
          Just decl -> Right decl
      tgtDecl <-
        case M.lookup tgtSort tgtSorts of
          Nothing -> Left "checkMorphism: unknown target attribute sort declaration"
          Just decl -> Right decl
      case asLitKind srcDecl of
        Nothing -> Right ()
        Just srcKind ->
          case asLitKind tgtDecl of
            Just tgtKind | tgtKind == srcKind -> Right ()
            tgtKind ->
              Left
                ( "morphism: attrsort mapping changes literal kind: "
                    <> renderAttrSort srcSort
                    <> " admits "
                    <> renderLitKind srcKind
                    <> ", but "
                    <> renderAttrSort tgtSort
                    <> " admits "
                    <> renderMaybeKind tgtKind
                )

modeMapIsIdentity :: Morphism -> Bool
modeMapIsIdentity mor =
  all (\m -> M.lookup m (morModeMap mor) == Just m) (S.toList (mtModes (dModes (morSrc mor))))

attrSortMapIsIdentity :: Morphism -> Bool
attrSortMapIsIdentity mor =
  all (\s -> M.lookup s (morAttrSortMap mor) == Just s) (S.toList usedSorts)
  where
    usedSorts =
      S.fromList
        [ sortName
        | table <- M.elems (dGens (morSrc mor))
        , gen <- M.elems table
        , (_, sortName) <- gdAttrs gen
        ]

checkGenMapping :: Morphism -> GenDecl -> Either Text ()
checkGenMapping mor gen = do
  let modeSrc = gdMode gen
  modeTgt <- mapMode mor modeSrc
  dom <- mapM (applyMorphismTy mor) (gdDom gen)
  cod <- mapM (applyMorphismTy mor) (gdCod gen)
  image <- case M.lookup (modeSrc, gdName gen) (morGenMap mor) of
    Nothing -> Left "checkMorphism: missing generator mapping"
    Just d -> Right d
  if dMode image /= modeTgt
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
  | not (modeMapIsIdentity mor) = Right False
  | not (attrSortMapIsIdentity mor) = Right False
  | not (M.null (morTypeMap mor)) = Right False
  | otherwise = do
      okGens <- allM (genIsIdentity mor) (allGens (morSrc mor))
      if not okGens
        then Right False
        else do
          let tgtCells = M.fromList [(cellKey c, c) | c <- dCells2 (morTgt mor)]
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
          expected <- genDWithAttrs mode dom cod name (identityAttrArgs (gdAttrs gen))
          isoOrFalse expected image
    identityAttrArgs attrs =
      M.fromList [ (fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- attrs ]
    cellMatches tgtMap cell =
      case M.lookup (cellKey cell) tgtMap of
        Nothing -> Right False
        Just tgt ->
          if c2Class cell /= c2Class tgt || c2Orient cell /= c2Orient tgt
            then Right False
            else do
              okL <- isoOrFalse (c2LHS cell) (c2LHS tgt)
              okR <- isoOrFalse (c2RHS cell) (c2RHS tgt)
              pure (okL && okR)

renamingFastPath :: Morphism -> [Cell2] -> Either Text Bool
renamingFastPath mor srcCells = do
  if not (modeMapIsIdentity mor) || not (attrSortMapIsIdentity mor)
    then Right False
    else do
      let tgt = morTgt mor
      case (buildTypeRenaming mor, buildGenRenaming mor) of
        (Just tyRen, Just genRen) -> do
          mTgtMap <- buildCellMap (dCells2 tgt)
          nameOk <- case mTgtMap of
            Nothing -> Right False
            Just tgtMap -> allM (cellMatchesRenaming tyRen genRen tgtMap) srcCells
          if nameOk
            then Right True
            else matchCellsByBody tyRen genRen srcCells (dCells2 tgt)
        _ -> Right False
  where
    buildCellMap cells =
      let dup = firstDup (map cellKey cells)
      in case dup of
        Just _ -> Right Nothing
        Nothing -> Right (Just (M.fromList [ (cellKey c, c) | c <- cells ]))
    firstDup xs = go S.empty xs
      where
        go _ [] = Nothing
        go seen (x:rest)
          | x `S.member` seen = Just x
          | otherwise = go (S.insert x seen) rest
    cellMatchesRenaming tyRen genRen tgtMap cell =
      case M.lookup (cellKey cell) tgtMap of
        Nothing -> Right False
        Just tgt ->
          if c2Class cell /= c2Class tgt || c2Orient cell /= c2Orient tgt
            then Right False
            else do
              let lhsRen = renameDiagram tyRen genRen (c2LHS cell)
              let rhsRen = renameDiagram tyRen genRen (c2RHS cell)
              okL <- isoOrFalse lhsRen (c2LHS tgt)
              okR <- isoOrFalse rhsRen (c2RHS tgt)
              pure (okL && okR)

    matchCellsByBody tyRen genRen cells tgtCells =
      go tgtCells cells
      where
        go _ [] = Right True
        go remaining (cell:rest) = do
          matches <- foldl (collectMatches cell) (Right []) remaining
          if null matches
            then Right False
            else go remaining rest
        collectMatches cell acc tgt = do
          hits <- acc
          ok <- matchesCell cell tgt
          if ok then Right (hits <> [tgt]) else Right hits
        matchesCell cell tgt =
          if dMode (c2LHS cell) /= dMode (c2LHS tgt)
            || c2Class cell /= c2Class tgt
            || c2Orient cell /= c2Orient tgt
            then Right False
            else do
              let lhsRen = renameDiagram tyRen genRen (c2LHS cell)
              let rhsRen = renameDiagram tyRen genRen (c2RHS cell)
              okL <- isoOrFalse lhsRen (c2LHS tgt)
              okR <- isoOrFalse rhsRen (c2RHS tgt)
              pure (okL && okR)

isoOrFalse :: Diagram -> Diagram -> Either Text Bool
isoOrFalse d1 d2 =
  case diagramIsoEq d1 d2 of
    Left _ -> Right False
    Right ok -> Right ok

cellKey :: Cell2 -> (ModeName, Text)
cellKey cell = (dMode (c2LHS cell), c2Name cell)

buildTypeRenaming :: Morphism -> Maybe (M.Map TypeRef TypeRef)
buildTypeRenaming mor = do
  let src = morSrc mor
  mp <- foldl step (Just M.empty) (allTypes src)
  if injective (M.elems mp)
    then Just mp
    else Nothing
  where
    tgt = morTgt mor
    step acc (ref, sig) = do
      mp <- acc
      let mapped =
            case M.lookup ref (morTypeMap mor) of
              Nothing -> Just ref
              Just tmpl -> renamingTarget tmpl (length (tsParams sig))
      case mapped of
        Nothing -> Nothing
        Just tgtRef ->
          case lookupTypeSig tgt tgtRef of
            Right sigTgt
              | length (tsParams sigTgt) == length (tsParams sig) ->
                  Just (M.insert ref tgtRef mp)
            _ -> Nothing

    renamingTarget tmpl arity =
      case ttBody tmpl of
        TCon tgtRef params
          | length (ttParams tmpl) == arity
          , length params == arity
          , all isVar params
          , let vars = [ v | TVar v <- params ]
          , length vars == length (S.fromList vars)
          , S.fromList vars == S.fromList (ttParams tmpl)
          -> Just tgtRef
        _ -> Nothing

    isVar (TVar _) = True
    isVar _ = False

buildGenRenaming :: Morphism -> Maybe (M.Map (ModeName, GenName) GenName)
buildGenRenaming mor = do
  mp <- foldl step (Just M.empty) (allGens (morSrc mor))
  if injective (M.elems mp)
    then Just mp
    else Nothing
  where
    tgt = morTgt mor
    step acc gen = do
      mp <- acc
      let mode = gdMode gen
      let name = gdName gen
      diag <- M.lookup (mode, name) (morGenMap mor)
      case singleGenNameMaybe gen diag of
        Nothing -> Nothing
        Just tgtName ->
          case M.lookup mode (dGens tgt) >>= M.lookup tgtName of
            Nothing -> Nothing
            Just _ -> Just (M.insert (mode, name) tgtName mp)

singleGenNameMaybe :: GenDecl -> Diagram -> Maybe GenName
singleGenNameMaybe srcGen diag =
  case renumberDiagram diag of
    Left _ -> Nothing
    Right canon ->
      case IM.elems (dEdges canon) of
        [edge] ->
          let boundary = dIn canon <> dOut canon
              edgePorts = eIns edge <> eOuts edge
              allPorts = diagramPortIds canon
          in case ePayload edge of
            PGen g attrs
              | boundary == edgePorts
              , length allPorts == length boundary
              , attrs == passThroughAttrs (gdAttrs srcGen) ->
                  Just g
            _ -> Nothing
        _ -> Nothing
  where
    passThroughAttrs attrs =
      M.fromList [ (fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- attrs ]

renameDiagram :: M.Map TypeRef TypeRef -> M.Map (ModeName, GenName) GenName -> Diagram -> Diagram
renameDiagram tyRen genRen diag =
  let mode = dMode diag
      dPortTy' = IM.map (renameTypeExpr tyRen) (dPortTy diag)
      dEdges' = IM.map (renameEdge mode) (dEdges diag)
  in diag { dPortTy = dPortTy', dEdges = dEdges' }
  where
    renameEdge mode edge =
      case ePayload edge of
        PGen gen attrs ->
          let gen' = M.findWithDefault gen (mode, gen) genRen
          in edge { ePayload = PGen gen' attrs }
        PBox name inner ->
          let inner' = renameDiagram tyRen genRen inner
          in edge { ePayload = PBox name inner' }

renameTypeExpr :: M.Map TypeRef TypeRef -> TypeExpr -> TypeExpr
renameTypeExpr ren ty =
  case ty of
    TVar v -> TVar v
    TCon ref args ->
      let ref' = M.findWithDefault ref ref ren
      in TCon ref' (map (renameTypeExpr ren) args)

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

allTypes :: Doctrine -> [(TypeRef, TypeSig)]
allTypes doc =
  [ (TypeRef mode name, sig)
  | (mode, table) <- M.toList (dTypes doc)
  , (name, sig) <- M.toList table
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

instantiateAttrSubst :: Morphism -> GenDecl -> AttrMap -> Either Text AttrSubst
instantiateAttrSubst mor gen attrsSrc = do
  mappedFields <- mapM mapField (gdAttrs gen)
  attrsSrcTgt <- mapM (applyMorphismAttrTerm mor) attrsSrc
  let flex = S.fromList [ v | (_, v) <- mappedFields ]
  let unifyOne acc (fieldName, formalVar) = do
        subst <- acc
        term <-
          case M.lookup fieldName attrsSrcTgt of
            Nothing -> Left "applyMorphismDiagram: missing source attribute argument"
            Just t -> Right t
        unifyAttrFlex flex subst (ATVar formalVar) term
  foldl unifyOne (Right M.empty) mappedFields
  where
    mapField (fieldName, sortName) = do
      sortName' <- mapAttrSort mor sortName
      let v = AttrVar fieldName sortName'
      Right (fieldName, v)

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
