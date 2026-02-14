{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Morphism
  ( Morphism(..)
  , MorphismCheck(..)
  , GenImage(..)
  , TemplateParam(..)
  , TypeTemplate(..)
  , applyMorphismMode
  , applyMorphismModExpr
  , applyMorphismTy
  , applyMorphismBinderSig
  , applyMorphismDiagram
  , instantiateGenImageBinders
  , checkMorphism
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Control.Monad (foldM)
import Data.Functor.Identity (runIdentity)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Cell2
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Names
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.TypeNormalize (normalizeTypeDeep)
import Strat.Poly.Attr
import Strat.Poly.Rewrite
import Strat.Poly.Normalize (normalize, joinableWithin, NormalizationStatus(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModName(..), ModDecl(..), ModExpr(..), composeMod, normalizeModExpr)
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.Traversal (traverseDiagram)

unifyCtxCompat :: TypeTheory -> [TypeExpr] -> Context -> Context -> Either Text Subst
unifyCtxCompat tt tmCtx ctxA ctxB =
  let tyFlex = S.unions (map freeTyVarsType (ctxA <> ctxB))
      tmFlex = S.unions (map freeTmVarsType (ctxA <> ctxB))
   in unifyCtx tt tmCtx tyFlex tmFlex ctxA ctxB

unifyCtxFromPattern :: TypeTheory -> [TypeExpr] -> Context -> Context -> Either Text Subst
unifyCtxFromPattern tt tmCtx pat host =
  let tyFlex = S.unions (map freeTyVarsType pat)
      tmFlex = S.unions (map freeTmVarsType pat)
   in unifyCtx tt tmCtx tyFlex tmFlex pat host


data Morphism = Morphism
  { morName   :: Text
  , morSrc    :: Doctrine
  , morTgt    :: Doctrine
  , morIsCoercion :: Bool
  , morModeMap :: M.Map ModeName ModeName
  , morModMap :: M.Map ModName ModExpr
  , morAttrSortMap :: M.Map AttrSort AttrSort
  , morTypeMap :: M.Map TypeRef TypeTemplate
  , morGenMap  :: M.Map (ModeName, GenName) GenImage
  , morCheck :: MorphismCheck
  , morPolicy  :: RewritePolicy
  , morFuel    :: Int
  } deriving (Eq, Show)

data MorphismCheck
  = CheckAll
  | CheckStructural
  | CheckNone
  deriving (Eq, Ord, Show)

data GenImage = GenImage
  { giDiagram :: Diagram
  , giBinderSigs :: M.Map BinderMetaVar BinderSig
  } deriving (Eq, Show)

data TemplateParam
  = TPType TyVar
  | TPTm TmVar
  deriving (Eq, Ord, Show)

data TypeTemplate = TypeTemplate
  { ttParams :: [TemplateParam]
  , ttBody :: TypeExpr
  } deriving (Eq, Show)

mapMode :: Morphism -> ModeName -> Either Text ModeName
mapMode mor mode =
  case M.lookup mode (morModeMap mor) of
    Nothing -> Left "morphism: missing mode mapping"
    Just mode' -> Right mode'

applyMorphismMode :: Morphism -> ModeName -> Either Text ModeName
applyMorphismMode = mapMode

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
        Just tmpl ->
          instantiateTemplate tmpl args'
  where
    mapArg arg =
      case arg of
        TAType t -> TAType <$> applyMorphismTy mor t
        TATm tmArg -> TATm <$> applyMorphismTmTerm mor tmArg

    instantiateTemplate tmpl args
      | length (ttParams tmpl) /= length args =
          Left "morphism: type template arity mismatch during instantiation"
      | otherwise = do
          subst <- foldM addParam emptySubst (zip (ttParams tmpl) args)
          applySubstTy (doctrineTypeTheory (morTgt mor)) subst (ttBody tmpl)

    addParam s (param, arg) =
      case (param, arg) of
        (TPType v, TAType t) ->
          Right s { sTy = M.insert v t (sTy s) }
        (TPTm v, TATm tmArg) ->
          Right s { sTm = M.insert v tmArg (sTm s) }
        _ ->
          Left "morphism: type template kind mismatch during instantiation"

applyMorphismTmTerm :: Morphism -> TermDiagram -> Either Text TermDiagram
applyMorphismTmTerm mor (TermDiagram tm) =
  TermDiagram <$> applyMorphismDiagram mor tm

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

applyMorphismModExpr :: Morphism -> ModExpr -> Either Text ModExpr
applyMorphismModExpr = mapModExpr

applyMorphismDiagram :: Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagram mor diagSrc = do
  let srcTheory = doctrineTypeTheory (morSrc mor)
  let tgtTheory = doctrineTypeTheory (morTgt mor)
  modeTgt <- mapMode mor modeSrc
  tmCtx <- mapM (applyMorphismTy mor) (dTmCtx diagSrc)
  portTy <- mapM (applyMorphismTy mor) (dPortTy diagSrc)
  let diagTgt0 = diagSrc { dMode = modeTgt, dTmCtx = tmCtx, dPortTy = portTy }
  let edgeIds = IM.keys (dEdges diagSrc)
  let step acc edgeKey = do
        diagTgt <- acc
        case IM.lookup edgeKey (dEdges diagSrc) of
          Nothing -> Left "applyMorphismDiagram: missing source edge"
          Just edgeSrc ->
            case ePayload edgeSrc of
              PGen genName attrsSrc bargsSrc -> do
                genDecl <- lookupGenInMode (morSrc mor) modeSrc genName
                substSrc <- instantiateGen srcTheory genDecl diagSrc edgeSrc
                substTgt <- mapSubst mor substSrc
                case M.lookup (modeSrc, genName) (morGenMap mor) of
                  Nothing -> Left "applyMorphismDiagram: missing generator mapping"
                  Just image0 -> do
                    let image = giDiagram image0
                    if dMode image /= modeTgt
                      then Left "applyMorphismDiagram: generator mapping mode mismatch"
                      else Right ()
                    attrSubst <- instantiateAttrSubst mor genDecl attrsSrc
                    mappedBargs <- mapM (applyMorphismBinderArg mor) bargsSrc
                    holeSub <- buildBinderHoleSub genDecl mappedBargs
                    instImage0 <- applySubstDiagram tgtTheory substTgt image
                    instHoleSigs0 <- applySubstBinderSigsTT tgtTheory substTgt (giBinderSigs image0)
                    let instImage1 = applyAttrSubstDiagram attrSubst instImage0
                    instImage <- instantiateGenImageBinders tgtTheory instHoleSigs0 holeSub instImage1
                    let holeKeys = S.fromList (binderHoleNames (length (binderSlots genDecl)))
                    let remaining = S.intersection holeKeys (binderMetaVarsDiagram instImage)
                    if S.null remaining
                      then Right ()
                      else Left "applyMorphismDiagram: uninstantiated binder holes in generator image"
                    instImage' <- weakenDiagramTmCtxTo (dTmCtx diagTgt) instImage
                    spliceEdge diagTgt edgeKey instImage'
              PBox name inner -> do
                inner' <- applyMorphismDiagram mor inner
                updateEdgePayload diagTgt edgeKey (PBox name inner')
              PFeedback inner -> do
                inner' <- applyMorphismDiagram mor inner
                updateEdgePayload diagTgt edgeKey (PFeedback inner')
              PSplice x ->
                updateEdgePayload diagTgt edgeKey (PSplice x)
              PTmMeta v -> do
                sort' <- applyMorphismTy mor (tmvSort v)
                updateEdgePayload diagTgt edgeKey (PTmMeta v { tmvSort = sort' })
  diagTgt <- foldl step (Right diagTgt0) edgeIds
  validateDiagram diagTgt
  pure diagTgt
  where
    modeSrc = dMode diagSrc

    binderSlots gen =
      [ bs
      | InBinder bs <- gdDom gen
      ]

    binderHoleNames n =
      [ BinderMetaVar ("b" <> T.pack (show i))
      | i <- [0 .. n - 1]
      ]

    buildBinderHoleSub gen bargs = do
      let slots = binderSlots gen
      if length slots /= length bargs
        then Left "applyMorphismDiagram: source binder argument arity mismatch"
        else Right ()
      let holes = binderHoleNames (length bargs)
      pure (M.fromList (zip holes bargs))

mapSubst :: Morphism -> Subst -> Either Text Subst
mapSubst mor subst = do
  tyPairs <- mapM mapTyOne (M.toList (sTy subst))
  tmPairs <- mapM mapTmOne (M.toList (sTm subst))
  pure (Subst (M.fromList tyPairs) (M.fromList tmPairs))
  where
    mapTyOne (v, t) = do
      v' <- mapTyVar mor v
      t' <- applyMorphismTy mor t
      pure (v', t')
    mapTmOne (v, t) = do
      sort' <- applyMorphismTy mor (tmvSort v)
      t' <- applyMorphismTmTerm mor t
      pure (v { tmvSort = sort' }, t')

applyMorphismBinderArg :: Morphism -> BinderArg -> Either Text BinderArg
applyMorphismBinderArg mor barg =
  case barg of
    BAConcrete d -> BAConcrete <$> applyMorphismDiagram mor d
    BAMeta x -> Right (BAMeta x)

applyMorphismBinderSig :: Morphism -> BinderSig -> Either Text BinderSig
applyMorphismBinderSig mor sig = do
  tmCtx' <- mapM (applyMorphismTy mor) (bsTmCtx sig)
  dom' <- mapM (applyMorphismTy mor) (bsDom sig)
  cod' <- mapM (applyMorphismTy mor) (bsCod sig)
  pure sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

applySubstBinderSigTT :: TypeTheory -> Subst -> BinderSig -> Either Text BinderSig
applySubstBinderSigTT tt subst sig = do
  tmCtx' <- applySubstCtx tt subst (bsTmCtx sig)
  dom' <- applySubstCtx tt subst (bsDom sig)
  cod' <- applySubstCtx tt subst (bsCod sig)
  pure sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

applySubstBinderSigsTT :: TypeTheory -> Subst -> M.Map BinderMetaVar BinderSig -> Either Text (M.Map BinderMetaVar BinderSig)
applySubstBinderSigsTT tt subst =
  traverse (applySubstBinderSigTT tt subst)

data SpliceAction
  = SpliceRename BinderMetaVar
  | SpliceInsert Diagram

instantiateGenImageBinders
  :: TypeTheory
  -> M.Map BinderMetaVar BinderSig
  -> M.Map BinderMetaVar BinderArg
  -> Diagram
  -> Either Text Diagram
instantiateGenImageBinders tt binderSigs holeSub diag0 = do
  diag1 <- recurseDiagram diag0
  expandSplicesLoop diag1
  where
    recurseDiagram diag = do
      edges' <- traverse recurseEdge (dEdges diag)
      pure diag { dEdges = edges' }

    recurseEdge edge =
      case ePayload edge of
        PGen g attrs bargs -> do
          bargs' <- mapM recurseBinderArg bargs
          pure edge { ePayload = PGen g attrs bargs' }
        PBox name inner -> do
          inner' <- instantiateGenImageBinders tt binderSigs holeSub inner
          pure edge { ePayload = PBox name inner' }
        PFeedback inner -> do
          inner' <- instantiateGenImageBinders tt binderSigs holeSub inner
          pure edge { ePayload = PFeedback inner' }
        PSplice x ->
          pure edge { ePayload = PSplice x }
        PTmMeta v ->
          pure edge { ePayload = PTmMeta v }
      where
        recurseBinderArg barg =
          case barg of
            BAConcrete inner ->
              BAConcrete <$> instantiateGenImageBinders tt binderSigs holeSub inner
            BAMeta x ->
              case M.lookup x holeSub of
                Nothing ->
                  if M.member x binderSigs
                    then Left "applyMorphismDiagram: missing binder-hole substitution"
                    else Right (BAMeta x)
                Just mapped ->
                  case mapped of
                    BAConcrete d -> do
                      checkConcreteAgainstSig x d
                      Right (BAConcrete d)
                    BAMeta y ->
                      Right (BAMeta y)

    expandSplicesLoop diag = do
      mNext <- findExpandableSplice diag
      case mNext of
        Nothing -> Right diag
        Just (edgeKey, action) ->
          case action of
            SpliceRename x' -> do
              diag' <- updateEdgePayload diag edgeKey (PSplice x')
              expandSplicesLoop diag'
            SpliceInsert d -> do
              diag' <- spliceEdge diag edgeKey d
              expandSplicesLoop diag'

    findExpandableSplice diag =
      go (IM.toAscList (dEdges diag))
      where
        go [] = Right Nothing
        go ((edgeKey, edge):rest) =
          case ePayload edge of
            PSplice hole -> do
              resolved <- resolveSpliceHole hole
              case resolved of
                BAMeta x'
                  | x' /= hole -> Right (Just (edgeKey, SpliceRename x'))
                  | otherwise -> go rest
                BAConcrete d -> do
                  checkConcreteAgainstSig hole d
                  checkSpliceInsertion diag edge d
                  Right (Just (edgeKey, SpliceInsert d))
            _ -> go rest

    resolveSpliceHole x = resolveAliasChain S.empty [] x

    resolveAliasChain seen chain x
      | x `S.member` seen =
          Left ("applyMorphismDiagram: binder-hole alias cycle: " <> renderAliasCycle (reverse (x : chain)))
      | otherwise =
          case M.lookup x holeSub of
            Nothing ->
              if M.member x binderSigs
                then Left "applyMorphismDiagram: missing binder-hole substitution"
                else Right (BAMeta x)
            Just (BAConcrete d) ->
              Right (BAConcrete d)
            Just (BAMeta y) ->
              if M.member y holeSub
                then resolveAliasChain (S.insert x seen) (x : chain) y
                else
                  if M.member y binderSigs
                    then Left "applyMorphismDiagram: missing binder-hole substitution"
                    else Right (BAMeta y)

    checkSpliceInsertion diag edge d = do
      if dMode d == dMode diag
        then Right ()
        else Left "applyMorphismDiagram: splice insertion mode mismatch"
      tmCaptured <- applySubstCtx tt emptySubst (dTmCtx d)
      tmHost <- applySubstCtx tt emptySubst (dTmCtx diag)
      if tmCaptured == tmHost
        then Right ()
        else Left "applyMorphismDiagram: splice insertion term-context mismatch"
      if length (dIn d) == length (eIns edge) && length (dOut d) == length (eOuts edge)
        then Right ()
        else Left "applyMorphismDiagram: splice insertion boundary arity mismatch"
      domSplice <- mapM (requirePortType diag) (eIns edge)
      codSplice <- mapM (requirePortType diag) (eOuts edge)
      domCaptured <- mapM (requirePortType d) (dIn d)
      codCaptured <- mapM (requirePortType d) (dOut d)
      if domSplice == domCaptured && codSplice == codCaptured
        then Right ()
        else Left "applyMorphismDiagram: splice insertion boundary mismatch"

    checkConcreteAgainstSig hole d =
      case M.lookup hole binderSigs of
        Nothing -> Right ()
        Just sig -> do
          sigTm <- applySubstCtx tt emptySubst (bsTmCtx sig)
          dTm <- applySubstCtx tt emptySubst (dTmCtx d)
          if dTm == sigTm
            then Right ()
            else Left "applyMorphismDiagram: binder argument term-context mismatch"
          dDom <- diagramDom d
          dCod <- diagramCod d
          dDom' <- applySubstCtx tt emptySubst dDom
          dCod' <- applySubstCtx tt emptySubst dCod
          sigDom <- applySubstCtx tt emptySubst (bsDom sig)
          sigCod <- applySubstCtx tt emptySubst (bsCod sig)
          if dDom' == sigDom && dCod' == sigCod
            then Right ()
            else Left "applyMorphismDiagram: binder argument boundary mismatch"

    renderAliasCycle xs =
      T.intercalate " -> " (map renderMeta xs)

    renderMeta (BinderMetaVar name) = "?" <> name

checkMorphism :: Morphism -> Either Text ()
checkMorphism mor = do
  validateModeMap mor
  validateModMap mor
  validateAttrSortMap mor
  validateTypeMap mor
  mapM_ (checkGenMapping mor) (allGens (morSrc mor))
  case morCheck mor of
    CheckNone -> Right ()
    _ -> do
      let srcCells =
            case morCheck mor of
              CheckAll -> dCells2 (morSrc mor)
              CheckStructural -> filter ((== Structural) . c2Class) (dCells2 (morSrc mor))
      fastOk <- inclusionFastPath mor
      if fastOk
        then Right ()
        else do
          renameOk <- renamingFastPath mor srcCells
          if renameOk
            then Right ()
            else mapM_ (checkCell mor) srcCells
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

validateTypeMap :: Morphism -> Either Text ()
validateTypeMap mor = do
  ensureAcyclicTypeTemplates mor
  mapM_ checkEntry (M.toList (morTypeMap mor))
  where
    ttTgt = doctrineTypeTheory (morTgt mor)

    checkEntry (srcRef, tmpl) = do
      srcSig <-
        case lookupTypeSig (morSrc mor) srcRef of
          Left _ -> Left "checkMorphism: unknown source type in type map"
          Right sig -> Right sig
      let srcParams = tsParams srcSig
      let tmplParams = ttParams tmpl
      if length tmplParams /= length srcParams
        then Left "checkMorphism: type template arity mismatch"
        else Right ()
      ensureDistinctTemplateParamNames tmplParams
      mapM_ (uncurry checkParam) (zip srcParams tmplParams)
      let tyVars = [ v | TPType v <- tmplParams ]
      let tmVars = [ v | TPTm v <- tmplParams ]
      checkType (morTgt mor) tyVars tmVars [] (ttBody tmpl)
      mappedMode <- mapMode mor (trMode srcRef)
      if typeMode (ttBody tmpl) == mappedMode
        then Right ()
        else Left "checkMorphism: type template body mode mismatch"

    ensureDistinctTemplateParamNames params =
      let names = [ tvName v | TPType v <- params ] <> [ tmvName v | TPTm v <- params ]
          set = S.fromList names
      in if S.size set == length names
          then Right ()
          else Left "checkMorphism: duplicate type template parameter name"

    checkParam srcParam tmplParam =
      case (srcParam, tmplParam) of
        (PS_Ty srcMode, TPType v) -> do
          expectedMode <- mapMode mor srcMode
          if tvMode v == expectedMode
            then Right ()
            else Left "checkMorphism: type template type-parameter mode mismatch"
        (PS_Tm srcSort, TPTm tmParam) -> do
          expectedMode <- mapMode mor (typeMode srcSort)
          if typeMode (tmvSort tmParam) == expectedMode
            then do
              expectedSortTgt <- applyMorphismTy mor srcSort
              sortOk <- sortDefEq expectedSortTgt (tmvSort tmParam)
              if sortOk
                then Right ()
                else Left "checkMorphism: type template term-parameter sort mismatch"
            else Left "checkMorphism: type template term-parameter mode mismatch"
        (PS_Ty _, _) ->
          Left "checkMorphism: type template kind mismatch"
        (PS_Tm _, _) ->
          Left "checkMorphism: type template kind mismatch"

    sortDefEq lhs rhs = do
      lhs' <- normalizeTypeDeep ttTgt lhs
      rhs' <- normalizeTypeDeep ttTgt rhs
      pure (lhs' == rhs')

ensureAcyclicTypeTemplates :: Morphism -> Either Text ()
ensureAcyclicTypeTemplates mor =
  case findTemplateCycle mor of
    Nothing -> Right ()
    Just refs ->
      Left ("checkMorphism: cyclic type template map: " <> renderCycle refs)
  where
    renderCycle refs = T.intercalate " -> " (map renderRef refs)
    renderRef ref = renderMode (trMode ref) <> "." <> renderType (trName ref)
    renderMode (ModeName name) = name
    renderType (TypeName name) = name

findTemplateCycle :: Morphism -> Maybe [TypeRef]
findTemplateCycle mor =
  goRoots S.empty (M.keys (morTypeMap mor))
  where
    keys = M.keysSet (morTypeMap mor)

    goRoots _ [] = Nothing
    goRoots seen (ref:rest)
      | ref `S.member` seen = goRoots seen rest
      | otherwise =
          case dfs seen [] ref of
            (seen', Nothing) -> goRoots seen' rest
            (_, Just cyc) -> Just cyc

    dfs seen stack ref
      | ref `elem` stack = (seen, Just (cycleFrom ref stack))
      | ref `S.member` seen = (seen, Nothing)
      | otherwise =
          let seen' = S.insert ref seen
              deps = templateDeps ref
          in dfsDeps seen' (ref : stack) deps

    dfsDeps seen _ [] = (seen, Nothing)
    dfsDeps seen stack (dep:rest) =
      case dfs seen stack dep of
        (seen', Nothing) -> dfsDeps seen' stack rest
        (seen', Just cyc) -> (seen', Just cyc)

    templateDeps ref =
      case M.lookup ref (morTypeMap mor) of
        Nothing -> []
        Just tmpl ->
          [ dep
          | dep <- S.toList (typeRefsInType (ttBody tmpl))
          , dep `S.member` keys
          ]

    cycleFrom ref stack =
      let prefix = takeWhile (/= ref) stack
      in ref : reverse prefix <> [ref]

typeRefsInType :: TypeExpr -> S.Set TypeRef
typeRefsInType ty =
  case ty of
    TVar _ -> S.empty
    TCon ref args ->
      S.insert ref (S.unions (map typeRefsInArg args))
    TMod _ inner ->
      typeRefsInType inner
  where
    typeRefsInArg arg =
      case arg of
        TAType t -> typeRefsInType t
        TATm tmArg -> typeRefsInTerm tmArg

    typeRefsInTerm (TermDiagram diag) =
      S.unions
        [ S.unions (map typeRefsInType (IM.elems (dPortTy diag)))
        , S.unions (map typeRefsInType (dTmCtx diag))
        , S.unions
            [ typeRefsInType (tmvSort v)
            | edge <- IM.elems (dEdges diag)
            , PTmMeta v <- [ePayload edge]
            ]
        ]

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

checkGenMapping :: Morphism -> GenDecl -> Either Text ()
checkGenMapping mor gen = do
  let ttTgt = doctrineTypeTheory (morTgt mor)
  let modeSrc = gdMode gen
  modeTgt <- mapMode mor modeSrc
  dom <- mapM (applyMorphismTy mor) (gdPlainDom gen)
  cod <- mapM (applyMorphismTy mor) (gdCod gen)
  image0 <- case M.lookup (modeSrc, gdName gen) (morGenMap mor) of
    Nothing -> Left "checkMorphism: missing generator mapping"
    Just d -> Right d
  let image = giDiagram image0
  if dMode image /= modeTgt
    then Left "checkMorphism: generator mapping mode mismatch"
    else do
      domImg <- diagramDom image
      codImg <- diagramCod image
      _ <- unifyCtxCompat ttTgt [] dom domImg
      _ <- unifyCtxCompat ttTgt [] cod codImg
      let binderSlotsSrc =
            [ bs
            | InBinder bs <- gdDom gen
            ]
      let holes =
            [ BinderMetaVar ("b" <> T.pack (show i))
            | i <- [0 .. length binderSlotsSrc - 1]
            ]
      binderSlotsTgt <- mapM (applyMorphismBinderSig mor) binderSlotsSrc
      let expectedBinderSigs = M.fromList (zip holes binderSlotsTgt)
      if giBinderSigs image0 == expectedBinderSigs
        then Right ()
        else Left "checkMorphism: generator mapping binder-hole signatures mismatch"
      let usedMetas = binderMetaVarsDiagram image
      let declaredMetas = M.keysSet (giBinderSigs image0)
      if usedMetas `S.isSubsetOf` declaredMetas
        then Right ()
        else Left "checkMorphism: generator mapping uses undeclared binder metas"
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
      case M.lookup (mode, name) (morGenMap m) of
        Nothing -> Right False
        Just image ->
          pure (singleGenNameMaybe gen image == Just name)
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
  if not (modeMapIsIdentity mor) || not (modMapIsIdentity mor) || not (attrSortMapIsIdentity mor)
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
          , let positions = map (argParamIndex (ttParams tmpl)) params
          , all isJust positions
          , let idxs = [ i | Just i <- positions ]
          , length idxs == arity
          , length idxs == S.size (S.fromList idxs)
          -> Just tgtRef
        _ -> Nothing

    argParamIndex params arg =
      case arg of
        TAType (TVar v) ->
          findParamIndex params (\p -> case p of TPType v' -> v' == v; _ -> False)
        TATm tm ->
          case termMetaOnly tm of
            Just v ->
              findParamIndex params (\p -> case p of TPTm v' -> v' == v; _ -> False)
            Nothing -> Nothing
        _ -> Nothing

    termMetaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dIn diag, dOut diag) of
        ([edge], [], [outBoundary]) ->
          case (ePayload edge, eIns edge, eOuts edge) of
            (PTmMeta v, [], [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
        _ -> Nothing

    findParamIndex params p =
      case [ i | (i, param) <- zip [0 :: Int ..] params, p param ] of
        [i] -> Just i
        _ -> Nothing

    isJust mv =
      case mv of
        Just _ -> True
        Nothing -> False

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
      image <- M.lookup (mode, name) (morGenMap mor)
      case singleGenNameMaybe gen image of
        Nothing -> Nothing
        Just tgtName ->
          case M.lookup mode (dGens tgt) >>= M.lookup tgtName of
            Nothing -> Nothing
            Just _ -> Just (M.insert (mode, name) tgtName mp)

singleGenNameMaybe :: GenDecl -> GenImage -> Maybe GenName
singleGenNameMaybe srcGen image0 =
  if giBinderSigs image0 /= expectedBinderSigs
    then Nothing
    else
      case renumberDiagram (giDiagram image0) of
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
                  , bargs == expectedBinderArgs
                  , attrs == passThroughAttrs (gdAttrs srcGen) ->
                      Just g
                _ -> Nothing
            _ -> Nothing
  where
    binderSlots =
      [ bs
      | InBinder bs <- gdDom srcGen
      ]
    holes =
      [ BinderMetaVar ("b" <> T.pack (show i))
      | i <- [0 .. length binderSlots - 1]
      ]
    expectedBinderArgs = map BAMeta holes
    expectedBinderSigs = M.fromList (zip holes binderSlots)
    passThroughAttrs attrs =
      M.fromList [ (fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- attrs ]

renameDiagram :: M.Map TypeRef TypeRef -> M.Map (ModeName, GenName) GenName -> Diagram -> Diagram
renameDiagram tyRen genRen diag =
  runIdentity (traverseDiagram onDiag onPayload pure diag)
  where
    onDiag d =
      pure d
        { dTmCtx = map (renameTypeExpr tyRen) (dTmCtx d)
        , dPortTy = IM.map (renameTypeExpr tyRen) (dPortTy d)
        }

    onPayload payload =
      pure $
        case payload of
          PGen gen attrs bargs ->
            let gen' = M.findWithDefault gen (dMode diag, gen) genRen
            in PGen gen' attrs bargs
          PTmMeta v ->
            PTmMeta v { tmvSort = renameTypeExpr tyRen (tmvSort v) }
          _ -> payload

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
        TATm tmArg -> TATm (renameTermDiagram tmArg)

    renameTermDiagram (TermDiagram diag) =
      TermDiagram
        diag
          { dTmCtx = map (renameTypeExpr ren) (dTmCtx diag)
          , dPortTy = IM.map (renameTypeExpr ren) (dPortTy diag)
          , dEdges = IM.map renameEdge (dEdges diag)
          }

    renameEdge edge =
      case ePayload edge of
        PTmMeta v ->
          edge { ePayload = PTmMeta v { tmvSort = renameTypeExpr ren (tmvSort v) } }
        _ -> edge

injective :: Ord a => [a] -> Bool
injective xs =
  let set = S.fromList xs
  in length xs == S.size set

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

instantiateGen :: TypeTheory -> GenDecl -> Diagram -> Edge -> Either Text Subst
instantiateGen tt gen diag edge = do
  dom <- mapM (requirePortType diag) (eIns edge)
  cod <- mapM (requirePortType diag) (eOuts edge)
  s1 <- unifyCtxFromPattern tt (dTmCtx diag) (gdPlainDom gen) dom
  codExpected <- applySubstCtx tt s1 (gdCod gen)
  s2 <- unifyCtxFromPattern tt (dTmCtx diag) codExpected cod
  s0 <- composeSubst tt s2 s1
  if length binderSlots /= length bargs
    then Left "applyMorphismDiagram: source binder argument arity mismatch"
    else foldM checkBinderSlot s0 (zip binderSlots bargs)
  where
    binderSlots =
      [ bs
      | InBinder bs <- gdDom gen
      ]

    bargs =
      case ePayload edge of
        PGen _ _ bs -> bs
        _ -> []

    checkBinderSlot subst (slot, barg) =
      case barg of
        BAMeta _ ->
          Right subst
        BAConcrete inner -> do
          slot0 <- applySubstBinderSigTT tt subst slot
          slotTm <- applySubstCtx tt emptySubst (bsTmCtx slot0)
          innerTm <- applySubstCtx tt emptySubst (dTmCtx inner)
          if innerTm == slotTm
            then Right ()
            else Left "applyMorphismDiagram: binder argument term-context mismatch"
          domInner <- diagramDom inner
          sDom <- unifyCtxFromPattern tt slotTm (bsDom slot0) domInner
          subst1 <- composeSubst tt sDom subst
          slot1 <- applySubstBinderSigTT tt subst1 slot
          slotTm1 <- applySubstCtx tt emptySubst (bsTmCtx slot1)
          codInner <- diagramCod inner
          sCod <- unifyCtxFromPattern tt slotTm1 (bsCod slot1) codInner
          composeSubst tt sCod subst1

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
  diag1 <- deleteEdgeKeepPorts diag (EdgeId edgeKey)
  let imageShift = shiftDiagram (dNextPort diag1) (dNextEdge diag1) image
  diag2 <- unionDiagram diag1 imageShift
  let boundary = dIn imageShift <> dOut imageShift
  if length boundary /= length (ins <> outs)
    then Left "spliceEdge: boundary mismatch"
    else do
      diag3 <- mergeBoundaryPairs diag2 (zip (ins <> outs) boundary)
      validateDiagram diag3
      pure diag3

updateEdgePayload :: Diagram -> Int -> EdgePayload -> Either Text Diagram
updateEdgePayload diag edgeKey payload =
  case IM.lookup edgeKey (dEdges diag) of
    Nothing -> Left "updateEdgePayload: missing edge"
    Just edge ->
      let edge' = edge { ePayload = payload }
      in Right diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
