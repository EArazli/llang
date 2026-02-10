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
import Control.Monad (foldM)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Cell2
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.IndexTheory (IxTheory(..), IxFunSig(..), normalizeTypeDeep)
import Strat.Poly.Attr
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, joinableWithin, NormalizationStatus(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModName(..), ModDecl(..), ModExpr(..), composeMod, normalizeModExpr)
import Strat.Common.Rules (RuleClass(..), Orientation(..))

unifyCtxCompat :: TypeTheory -> [TypeExpr] -> Context -> Context -> Either Text Subst
unifyCtxCompat tt ixCtx ctxA ctxB =
  let tyFlex = S.unions (map freeTyVarsTypeLocal (ctxA <> ctxB))
      ixFlex = S.unions (map freeIxVarsType (ctxA <> ctxB))
   in unifyCtx tt ixCtx tyFlex ixFlex ctxA ctxB

freeTyVarsTypeLocal :: TypeExpr -> S.Set TyVar
freeTyVarsTypeLocal ty =
  case ty of
    TVar v -> S.singleton v
    TCon _ args -> S.unions (map freeArg args)
    TMod _ inner -> freeTyVarsTypeLocal inner
  where
    freeArg arg =
      case arg of
        TAType t -> freeTyVarsTypeLocal t
        TAIndex ix -> S.unions [ freeTyVarsTypeLocal (ixvSort v) | v <- S.toList (freeIxVarsIx ix) ]


data Morphism = Morphism
  { morName   :: Text
  , morSrc    :: Doctrine
  , morTgt    :: Doctrine
  , morIsCoercion :: Bool
  , morModeMap :: M.Map ModeName ModeName
  , morModMap :: M.Map ModName ModExpr
  , morAttrSortMap :: M.Map AttrSort AttrSort
  , morTypeMap :: M.Map TypeRef TypeTemplate
  , morGenMap  :: M.Map (ModeName, GenName) Diagram
  , morIxFunMap :: M.Map IxFunName IxFunName
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
    TMod me inner -> do
      inner' <- applyMorphismTy mor inner
      me' <- mapModExpr mor me
      normalizeTypeExpr (dModes (morTgt mor)) (TMod me' inner')
    TCon ref args -> do
      args' <- mapM mapArg args
      case M.lookup ref (morTypeMap mor) of
        Nothing -> do
          ref' <- mapTypeRef mor ref
          pure (TCon ref' args')
        Just tmpl -> do
          tyArgs <- mapM requireTyArg args'
          let subst = Subst (M.fromList (zip (ttParams tmpl) tyArgs)) M.empty
          case applySubstTy (doctrineTypeTheory (morTgt mor)) subst (ttBody tmpl) of
            Left err -> Left err
            Right out -> Right out
  where
    mapArg arg =
      case arg of
        TAType t -> TAType <$> applyMorphismTy mor t
        TAIndex ix -> TAIndex <$> applyMorphismIxTerm mor ix

    requireTyArg arg =
      case arg of
        TAType t -> Right t
        TAIndex _ -> Left "morphism: type template cannot be instantiated by index arguments"

applyMorphismIxTerm :: Morphism -> IxTerm -> Either Text IxTerm
applyMorphismIxTerm mor tm =
  case tm of
    IXVar v -> do
      sort' <- applyMorphismTy mor (ixvSort v)
      Right (IXVar v { ixvSort = sort' })
    IXBound i -> Right (IXBound i)
    IXFun f args -> do
      args' <- mapM (applyMorphismIxTerm mor) args
      let f' = M.findWithDefault f f (morIxFunMap mor)
      Right (IXFun f' args')

mapModExpr :: Morphism -> ModExpr -> Either Text ModExpr
mapModExpr mor me = do
  srcMapped <- mapMode mor (meSrc me)
  tgtMapped <- mapMode mor (meTgt me)
  let start = ModExpr { meSrc = srcMapped, meTgt = srcMapped, mePath = [] }
  pieces <- mapM lookupPiece (mePath me)
  composed <- foldM compose start pieces
  let normalized = normalizeModExpr (dModes (morTgt mor)) composed
  if meSrc normalized /= srcMapped || meTgt normalized /= tgtMapped
    then Left "morphism: mapped modality expression has wrong endpoints"
    else Right normalized
  where
    lookupPiece name =
      case M.lookup name (morModMap mor) of
        Nothing -> Left "morphism: missing modality mapping"
        Just out -> Right out
    compose acc nxt = composeMod (dModes (morTgt mor)) acc nxt

applyMorphismDiagram :: Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagram mor diagSrc = do
  let srcTheory = doctrineTypeTheory (morSrc mor)
  let tgtTheory = doctrineTypeTheory (morTgt mor)
  modeTgt <- mapMode mor modeSrc
  ixCtx <- mapM (applyMorphismTy mor) (dIxCtx diagSrc)
  portTy <- mapM (applyMorphismTy mor) (dPortTy diagSrc)
  let diagTgt0 = diagSrc { dMode = modeTgt, dIxCtx = ixCtx, dPortTy = portTy }
  let edgeIds = IM.keys (dEdges diagSrc)
  let step acc edgeKey = do
        diagTgt <- acc
        case IM.lookup edgeKey (dEdges diagSrc) of
          Nothing -> Left "applyMorphismDiagram: missing source edge"
          Just edgeSrc ->
            case ePayload edgeSrc of
              PGen genName attrsSrc bargsSrc -> do
                if not (null bargsSrc)
                  then Left "applyMorphismDiagram: binder arguments not supported in morphisms"
                  else Right ()
                genDecl <- lookupGenInMode (morSrc mor) modeSrc genName
                subst <- instantiateGen srcTheory genDecl diagSrc edgeSrc
                substTgt <- mapSubst mor subst
                case M.lookup (modeSrc, genName) (morGenMap mor) of
                  Nothing -> Left "applyMorphismDiagram: missing generator mapping"
                  Just image -> do
                    if dMode image /= modeTgt
                      then Left "applyMorphismDiagram: generator mapping mode mismatch"
                      else Right ()
                    attrSubst <- instantiateAttrSubst mor genDecl attrsSrc
                    instImage0 <- applySubstDiagramTT tgtTheory substTgt image
                    let instImage = applyAttrSubstDiagram attrSubst instImage0
                    spliceEdge diagTgt edgeKey instImage
              PBox name inner -> do
                inner' <- applyMorphismDiagram mor inner
                updateEdgePayload diagTgt edgeKey (PBox name inner')
              PSplice x ->
                updateEdgePayload diagTgt edgeKey (PSplice x)
  diagTgt <- foldl step (Right diagTgt0) edgeIds
  validateDiagram diagTgt
  pure diagTgt
  where
    modeSrc = dMode diagSrc

mapSubst :: Morphism -> Subst -> Either Text Subst
mapSubst mor subst = do
  tyPairs <- mapM mapTyOne (M.toList (sTy subst))
  ixPairs <- mapM mapIxOne (M.toList (sIx subst))
  pure (Subst (M.fromList tyPairs) (M.fromList ixPairs))
  where
    mapTyOne (v, t) = do
      v' <- mapTyVar mor v
      t' <- applyMorphismTy mor t
      pure (v', t')
    mapIxOne (v, t) = do
      sort' <- applyMorphismTy mor (ixvSort v)
      t' <- applyMorphismIxTerm mor t
      pure (v { ixvSort = sort' }, t')

checkMorphism :: Morphism -> Either Text ()
checkMorphism mor = do
  validateModeMap mor
  validateModMap mor
  validateAttrSortMap mor
  validateIxFunMap mor
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
  case [ m | m <- M.keys srcModes, M.notMember m (morModeMap mor) ] of
    (m:_) -> Left ("checkMorphism: missing mode mapping for " <> renderModeName m)
    [] -> Right ()
  case [ m | (_, m) <- M.toList (morModeMap mor), M.notMember m tgtModes ] of
    (m:_) -> Left ("checkMorphism: unknown target mode " <> renderModeName m)
    [] -> Right ()
  where
    renderModeName (ModeName name) = name

validateModMap :: Morphism -> Either Text ()
validateModMap mor = do
  let srcDecls = mtDecls (dModes (morSrc mor))
  case [ m | (m, _) <- M.toList (morModMap mor), M.notMember m srcDecls ] of
    (m:_) -> Left ("checkMorphism: unknown source modality " <> renderModName m)
    [] -> Right ()
  case [ m | m <- M.keys srcDecls, M.notMember m (morModMap mor) ] of
    (m:_) -> Left ("checkMorphism: missing modality mapping for " <> renderModName m)
    [] -> Right ()
  mapM_ checkOne (M.toList srcDecls)
  where
    checkOne (name, decl) = do
      image <-
        case M.lookup name (morModMap mor) of
          Nothing -> Left "checkMorphism: missing modality mapping"
          Just me -> Right me
      srcMode <- mapMode mor (mdSrc decl)
      tgtMode <- mapMode mor (mdTgt decl)
      if meSrc image /= srcMode || meTgt image /= tgtMode
        then Left ("checkMorphism: modality mapping mode mismatch for " <> renderModName name)
        else checkModExprWellTyped (dModes (morTgt mor)) image
    renderModName (ModName name) = name

checkModExprWellTyped :: ModeTheory -> ModExpr -> Either Text ()
checkModExprWellTyped mt me = do
  if M.member (meSrc me) (mtModes mt)
    then Right ()
    else Left "checkMorphism: modality expression has unknown source mode"
  if M.member (meTgt me) (mtModes mt)
    then Right ()
    else Left "checkMorphism: modality expression has unknown target mode"
  end <- walk (meSrc me) (mePath me)
  if end == meTgt me
    then Right ()
    else Left "checkMorphism: ill-typed modality expression"
  where
    walk cur [] = Right cur
    walk cur (m:rest) =
      case M.lookup m (mtDecls mt) of
        Nothing -> Left "checkMorphism: modality expression uses unknown modality"
        Just decl ->
          if mdSrc decl == cur
            then walk (mdTgt decl) rest
            else Left "checkMorphism: modality expression composition mismatch"

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
  all (\m -> M.lookup m (morModeMap mor) == Just m) (M.keys (mtModes (dModes (morSrc mor))))

modMapIsIdentity :: Morphism -> Bool
modMapIsIdentity mor =
  all isIdentity (M.toList (mtDecls (dModes (morSrc mor))))
  where
    isIdentity (name, decl) =
      M.lookup name (morModMap mor)
        == Just
          ( ModExpr
              { meSrc = mdSrc decl
              , meTgt = mdTgt decl
              , mePath = [name]
              }
          )

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

ixFunMapIsIdentity :: Morphism -> Bool
ixFunMapIsIdentity mor =
  all (\f -> M.findWithDefault f f (morIxFunMap mor) == f) (allIxFunNames (morSrc mor))

checkGenMapping :: Morphism -> GenDecl -> Either Text ()
checkGenMapping mor gen = do
  let ttTgt = doctrineTypeTheory (morTgt mor)
  let modeSrc = gdMode gen
  modeTgt <- mapMode mor modeSrc
  dom <- mapM (applyMorphismTy mor) (gdPlainDom gen)
  cod <- mapM (applyMorphismTy mor) (gdCod gen)
  image <- case M.lookup (modeSrc, gdName gen) (morGenMap mor) of
    Nothing -> Left "checkMorphism: missing generator mapping"
    Just d -> Right d
  if dMode image /= modeTgt
    then Left "checkMorphism: generator mapping mode mismatch"
    else do
      domImg <- diagramDom image
      codImg <- diagramCod image
      _ <- unifyCtxCompat ttTgt [] dom domImg
      _ <- unifyCtxCompat ttTgt [] cod codImg
      pure ()

checkCell :: Morphism -> Cell2 -> Either Text ()
checkCell mor cell = do
  lhs <- applyMorphismDiagram mor (c2LHS cell)
  rhs <- applyMorphismDiagram mor (c2RHS cell)
  let tt = doctrineTypeTheory (morTgt mor)
  let rules = rulesFromPolicy (morPolicy mor) (dCells2 (morTgt mor))
  let fuel = morFuel mor
  statusL <- normalize tt fuel rules lhs
  statusR <- normalize tt fuel rules rhs
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
      ok <- joinableWithin tt fuel rules lhs rhs
      if ok
        then Right ()
        else Left "checkMorphism: equation undecided or violated"

inclusionFastPath :: Morphism -> Either Text Bool
inclusionFastPath mor
  | not (modeMapIsIdentity mor) = Right False
  | not (modMapIsIdentity mor) = Right False
  | not (attrSortMapIsIdentity mor) = Right False
  | not (ixFunMapIsIdentity mor) = Right False
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
      let dom = gdPlainDom gen
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
  if not (modeMapIsIdentity mor) || not (modMapIsIdentity mor) || not (attrSortMapIsIdentity mor) || not (ixFunMapIsIdentity mor)
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

validateIxFunMap :: Morphism -> Either Text ()
validateIxFunMap mor = do
  mapM_ checkOne (M.toList (morIxFunMap mor))
  where
    ttTgt = doctrineTypeTheory (morTgt mor)

    checkOne (srcName, tgtName) = do
      (srcMode, srcSig) <- resolveUniqueIxFun "source" (morSrc mor) srcName
      (tgtMode, tgtSig) <- resolveUniqueIxFun "target" (morTgt mor) tgtName
      srcMode' <- mapMode mor srcMode
      if srcMode' == tgtMode
        then Right ()
        else Left ("checkMorphism: index function mode mismatch for " <> renderIxFunName srcName)
      let srcArgs = ifArgs srcSig
      let tgtArgs = ifArgs tgtSig
      if length srcArgs == length tgtArgs
        then Right ()
        else Left ("checkMorphism: index function arity mismatch for " <> renderIxFunName srcName)
      mapM_ (uncurry checkSortPreserved) (zip srcArgs tgtArgs)
      checkSortPreserved (ifRes srcSig) (ifRes tgtSig)

    checkSortPreserved srcSort tgtSort = do
      srcMapped <- applyMorphismTy mor srcSort
      srcNorm <- normalizeTypeDeep ttTgt srcMapped
      tgtNorm <- normalizeTypeDeep ttTgt tgtSort
      if srcNorm == tgtNorm
        then Right ()
        else Left "checkMorphism: index function sort mapping mismatch"

    resolveUniqueIxFun side doc funName =
      case
        [ (mode, sig)
        | (mode, ixTheory) <- M.toList (dIxTheory doc)
        , (name, sig) <- M.toList (itFuns ixTheory)
        , name == funName
        ]
      of
        [] -> Left ("checkMorphism: unknown " <> side <> " index function " <> renderIxFunName funName)
        [entry] -> Right entry
        _ -> Left ("checkMorphism: ambiguous " <> side <> " index function " <> renderIxFunName funName)

    renderIxFunName (IxFunName name) = name

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
          , let vars = [ v | TAType (TVar v) <- params ]
          , length vars == length (S.fromList vars)
          , S.fromList vars == S.fromList (ttParams tmpl)
          -> Just tgtRef
        _ -> Nothing

    isVar (TAType (TVar _)) = True
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
            PGen g attrs bargs
              | boundary == edgePorts
              , length allPorts == length boundary
              , null bargs
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
      dIxCtx' = map (renameTypeExpr tyRen) (dIxCtx diag)
      dPortTy' = IM.map (renameTypeExpr tyRen) (dPortTy diag)
      dEdges' = IM.map (renameEdge mode) (dEdges diag)
  in diag { dIxCtx = dIxCtx', dPortTy = dPortTy', dEdges = dEdges' }
  where
    renameEdge mode edge =
      case ePayload edge of
        PGen gen attrs bargs ->
          let gen' = M.findWithDefault gen (mode, gen) genRen
              bargs' = map renameBinderArg bargs
          in edge { ePayload = PGen gen' attrs bargs' }
        PBox name inner ->
          let inner' = renameDiagram tyRen genRen inner
          in edge { ePayload = PBox name inner' }
        PSplice x ->
          edge { ePayload = PSplice x }

    renameBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete (renameDiagram tyRen genRen inner)
        BAMeta x -> BAMeta x

renameTypeExpr :: M.Map TypeRef TypeRef -> TypeExpr -> TypeExpr
renameTypeExpr ren ty =
  case ty of
    TVar v -> TVar v
    TCon ref args ->
      let ref' = M.findWithDefault ref ref ren
      in TCon ref' (map renameArg args)
    TMod me inner ->
      TMod me (renameTypeExpr ren inner)
  where
    renameArg arg =
      case arg of
        TAType t -> TAType (renameTypeExpr ren t)
        TAIndex ix -> TAIndex (renameIx ix)

    renameIx ix =
      case ix of
        IXVar v -> IXVar v { ixvSort = renameTypeExpr ren (ixvSort v) }
        IXBound i -> IXBound i
        IXFun f args -> IXFun f (map renameIx args)

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

allIxFunNames :: Doctrine -> [IxFunName]
allIxFunNames doc =
  [ fname
  | ixTheory <- M.elems (dIxTheory doc)
  , fname <- M.keys (itFuns ixTheory)
  ]

lookupGenInMode :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGenInMode doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "applyMorphismDiagram: unknown generator"
    Just gd -> Right gd

instantiateGen :: TypeTheory -> GenDecl -> Diagram -> Edge -> Either Text Subst
instantiateGen tt gen diag edge = do
  dom <- mapM (requirePortType diag) (eIns edge)
  cod <- mapM (requirePortType diag) (eOuts edge)
  s1 <- unifyCtxCompat tt (dIxCtx diag) (gdPlainDom gen) dom
  codExpected <- applySubstCtx tt s1 (gdCod gen)
  s2 <- unifyCtxCompat tt (dIxCtx diag) codExpected cod
  composeSubst tt s2 s1

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
  portLabel <- unionDisjointIntMap "insertDiagram labels" (dPortLabel base) (dPortLabel extra)
  prod <- unionDisjointIntMap "insertDiagram producers" (dProd base) (dProd extra)
  cons <- unionDisjointIntMap "insertDiagram consumers" (dCons base) (dCons extra)
  edges <- unionDisjointIntMap "insertDiagram edges" (dEdges base) (dEdges extra)
  pure base
    { dPortTy = portTy
    , dPortLabel = portLabel
    , dProd = prod
    , dCons = cons
    , dEdges = edges
    , dNextPort = dNextPort extra
    , dNextEdge = dNextEdge extra
    }
