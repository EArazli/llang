{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Morphism
  ( Morphism(..)
  , MorphismCheck(..)
  , MorphismCheckResult(..)
  , GenImage(..)
  , TypeTemplate(..)
  , applyMorphismMode
  , applyMorphismModExpr
  , applyMorphismTy
  , applyMorphismTyWithTables
  , applyMorphismTyWithCaches
  , applyMorphismBinderSig
  , applyMorphismBinderSigWithTables
  , applyMorphismDiagram
  , applyMorphismDiagramWithTables
  , applyMorphismDiagramWithTheories
  , checkMorphismResultWithBudget
  , checkMorphismWithBudget
  , checkMorphism
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Set as S
import Control.Monad (foldM)
import Data.Functor.Identity (runIdentity)
import Data.Bifunctor (first)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.Doctrine
import Strat.Poly.Cell2
import Strat.Poly.Graph
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Diagram
import Strat.Poly.DiagramInterpretation
  ( DiagramInterpretation(..)
  , applySubstBinderSig
  , applySubstBinderSigs
  , binderHoleCaptureRiskMetasDiagram
  , binderHoleNames
  , instantiateGenImageBindersWithMapper
  , interpretDiagram
  , renameBinderArgMetas
  , requirePortType
  , spliceEdge
  , stableHoleCaptureRenaming
  )
import Strat.Poly.Names
import Strat.Poly.Obj
import Strat.Poly.UnifyObj hiding (applySubstDiagram)
import Strat.Poly.TypeTheory (TypeTheory, TypeParamSig(..), literalKindForObj)
import Strat.Poly.DefEq (normalizeObjDeep, defEqObj, termExprToDiagramChecked)
import Strat.Poly.Literal (renderLiteralKind)
import Strat.Poly.Rewrite
import Strat.Poly.ObjClassifier (modeUniverseObj, modeClassifierMode)
import Strat.Poly.Normalize (autoJoinProofWithMapper)
import Strat.Poly.ModAction (applyModExpr)
import Strat.Poly.Proof
  ( JoinProof
  , SearchBudget
  , SearchLimit
  , SearchOutcome(..)
  , defaultSearchBudget
  , renderSearchLimit
  , checkJoinProofWithMapper
  )
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModeTheory(..)
  , ModName(..)
  , ModDecl(..)
  , ModExpr(..)
  , ModEqn(..)
  , ClassificationDecl(..)
  , CompDecl(..)
  , composeMod
  , normalizeModExpr
  , classifierLiftForModality
  , classifierLiftForModExpr
  )
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.TermExpr (TermExpr(..))

unifyCtxCompat :: TypeTheory -> [Obj] -> Context -> Context -> Either Text Subst
unifyCtxCompat tt tmCtx ctxA ctxB =
  let flex = S.unions (map freeVarsObj (ctxA <> ctxB))
   in unifyCtx tt tmCtx flex ctxA ctxB

unifyCtxFromPattern :: TypeTheory -> [Obj] -> Context -> Context -> Either Text Subst
unifyCtxFromPattern tt tmCtx pat host =
  let flex = S.unions (map freeVarsObj pat)
   in unifyCtx tt tmCtx flex pat host


data Morphism = Morphism
  { morName   :: Text
  , morSrc    :: Doctrine
  , morTgt    :: Doctrine
  , morIsCoercion :: Bool
  , morModeMap :: M.Map ModeName ModeName
  , morModMap :: M.Map ModName ModExpr
  , morTypeMap :: M.Map ObjRef TypeTemplate
  , morGenMap  :: M.Map (ModeName, GenName) GenImage
  , morCheck :: MorphismCheck
  , morPolicy  :: RewritePolicy
  } deriving (Eq, Show)

data MorphismCheck
  = CheckAll
  | CheckStructural
  | CheckNone
  deriving (Eq, Ord, Show)

data MorphismCheckResult
  = MorphismCheckProved [(Text, JoinProof)]
  | MorphismCheckUndecided Text SearchLimit
  deriving (Eq, Show)

data GenImage = GenImage
  { giDiagram :: Diagram
  , giBinderSigs :: M.Map BinderMetaVar BinderSig
  } deriving (Eq, Show)

data TypeTemplate = TypeTemplate
  { ttParams :: [GenParam]
  , ttBody :: Obj
  } deriving (Eq, Show)

mapMode :: Morphism -> ModeName -> Either Text ModeName
mapMode mor mode =
  case M.lookup mode (morModeMap mor) of
    Nothing -> Left "morphism: missing mode mapping"
    Just mode' -> Right mode'

applyMorphismMode :: Morphism -> ModeName -> Either Text ModeName
applyMorphismMode = mapMode

mapTypeRef :: CtorTables -> Morphism -> ModeName -> ModeName -> ObjRef -> Either Text ObjRef
mapTypeRef tgtCtorTables mor ownerSrc ownerTgt ref = do
  classifierTgt <- mapMode mor (orMode ref)
  let mapped = ref { orMode = classifierTgt }
  if isOpaqueMetaSort ref
    then Right mapped
    else
      case lookupCtorSigForOwnerInTables (morTgt mor) tgtCtorTables ownerTgt mapped of
        Right _ ->
          Right mapped
        Left _ ->
          case fallbackUniverseRef of
            Just uRef ->
              case lookupCtorSigForOwnerInTables (morTgt mor) tgtCtorTables ownerTgt uRef of
                Right _ -> Right uRef
                Left _ -> missingCtor mapped
            Nothing -> missingCtor mapped
  where
    isOpaqueMetaSort r =
      case orName r of
        ObjName "__obj_meta_sort" -> True
        _ -> False

    missingCtor mapped =
      Left
        ( "morphism: missing mapped constructor "
            <> renderRef mapped
            <> " for owner mode "
            <> renderMode ownerTgt
            <> " (source ref "
            <> renderRef ref
            <> ", source owner "
            <> renderMode ownerSrc
            <> "). Add a type_map entry or declare the constructor in the target doctrine."
        )

    fallbackUniverseRef =
      case modeUniverseObj (dModes (morSrc mor)) ownerSrc of
        Just srcUniverse ->
          case objCode srcUniverse of
            CTCon srcUniverseRef []
              | srcUniverseRef == ref ->
                  case modeUniverseObj (dModes (morTgt mor)) ownerTgt of
                    Just tgtUniverse ->
                      case objCode tgtUniverse of
                        CTCon tgtUniverseRef [] -> Just tgtUniverseRef
                        _ -> Nothing
                    Nothing -> Nothing
              | otherwise -> Nothing
            _ -> Nothing
        Nothing -> Nothing

    renderMode (ModeName name) = name
    renderRef (ObjRef mode (ObjName name)) = renderMode mode <> "." <> name

applyMorphismTy :: Morphism -> Obj -> Either Text Obj
applyMorphismTy mor ty = do
  tgtCtorTables <- deriveCtorTables (morTgt mor)
  applyMorphismTyWithTables tgtCtorTables mor ty

applyMorphismTyWithTables :: CtorTables -> Morphism -> Obj -> Either Text Obj
applyMorphismTyWithTables tgtCtorTables mor ty = do
  srcTheory <- doctrineTypeTheory (morSrc mor)
  tgtTheory <- doctrineTypeTheoryFromTables (morTgt mor) tgtCtorTables
  applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor ty

applyMorphismTyWithCaches
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> Morphism
  -> Obj
  -> Either Text Obj
applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor ty = do
  go ty
  where
    go ty = do
      let ownerSrc = objOwnerMode ty
      owner' <- mapMode mor (objOwnerMode ty)
      code' <- goCode ownerSrc owner' (objCode ty)
      normalizeObjExpr
        (dModes (morTgt mor))
        Obj
          { objOwnerMode = owner'
          , objCode = code'
          }

    goCode ownerSrc ownerTgt code =
      case code of
        CTMeta v -> do
          sort' <- go (tmvSort v)
          let v' = v { tmvSort = sort', tmvOwnerMode = Just ownerTgt }
          pure (CTMeta v')
        CTLift me innerCode -> do
          me' <- mapModExpr mor me
          inner' <- goCode (meSrc me) (meSrc me') innerCode
          pure (CTLift me' inner')
        CTCon ref args -> do
          args' <- mapM mapArg args
          case M.lookup ref (morTypeMap mor) of
            Nothing -> do
              ref' <- mapTypeRef tgtCtorTables mor ownerSrc ownerTgt ref
              pure (CTCon ref' args')
            Just tmpl ->
              if ownerSrc == orMode ref
                then do
                  inst <- instantiateTemplate tmpl args'
                  if objOwnerMode inst == ownerTgt
                    then Right (objCode inst)
                    else Left "morphism: type template instantiation changed owner mode"
                else do
                  ref' <- mapTypeRef tgtCtorTables mor ownerSrc ownerTgt ref
                  pure (CTCon ref' args')

    mapArg arg =
      case arg of
        OAObj t -> OAObj <$> go t
        OATm tmArg -> OATm <$> applyMorphismTmTermWithTheories srcTheory tgtTheory tgtCtorTables mor tmArg

    instantiateTemplate tmpl args
      | length (ttParams tmpl) /= length args =
          Left "morphism: type template arity mismatch during instantiation"
      | otherwise = do
          subst <- foldM addParam emptySubst (zip (ttParams tmpl) args)
          applySubstObj tgtTheory subst (ttBody tmpl)

    addParam s (param, arg) =
      case (param, arg) of
        (GP_Ty v, OAObj t) ->
          insertCodeMeta v t s
        (GP_Tm v, OATm tmArg) ->
          insertTmMeta v tmArg s
        _ ->
          Left "morphism: type template kind mismatch during instantiation"

applyMorphismTmTermWithTheories
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> Morphism
  -> TermDiagram
  -> Either Text TermDiagram
applyMorphismTmTermWithTheories srcTheory tgtTheory tgtCtorTables mor (TermDiagram tm) =
  TermDiagram <$> applyMorphismDiagramWithTheories srcTheory tgtTheory tgtCtorTables mor tm

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
  tgtCtorTables <- deriveCtorTables (morTgt mor)
  applyMorphismDiagramWithTables tgtCtorTables mor diagSrc

applyMorphismDiagramWithTables :: CtorTables -> Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagramWithTables = applyMorphismDiagramInTables

applyMorphismDiagramInTables :: CtorTables -> Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagramInTables tgtCtorTables mor diagSrc = do
  srcTheory <- doctrineTypeTheory (morSrc mor)
  tgtTheory <- doctrineTypeTheoryFromTables (morTgt mor) tgtCtorTables
  applyMorphismDiagramWithTheories srcTheory tgtTheory tgtCtorTables mor diagSrc

applyMorphismDiagramWithTheories
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> Morphism
  -> Diagram
  -> Either Text Diagram
applyMorphismDiagramWithTheories srcTheory tgtTheory tgtCtorTables mor diagSrc = do
  let mapType = applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor
  let interp =
        DiagramInterpretation
          { diMapMode = mapMode mor
          , diMapTmCtxObj = mapType
          , diMapPortObj = mapType
          , diMapTmMetaSort = mapType
          , diMapSplice = \x me ->
              do
                me' <- applyMorphismModExpr mor me
                pure (x, me')
          , diOnGenEdge = onGenEdge
          }
  interpretDiagram interp diagSrc
  where
    stableCaptureRenaming =
      stableHoleCaptureRenaming
        (binderHoleCaptureRiskMetasDiagram diagSrc)
        (binderArgMetaVarsDiagram diagSrc)

    binderSlots gen =
      [ bs
      | InBinder bs <- gdDom gen
      ]

    buildBinderHoleSub gen bargs = do
      let slots = binderSlots gen
      if length slots /= length bargs
        then Left "applyMorphismDiagram: source binder argument arity mismatch"
      else Right ()
      let holes = binderHoleNames (length bargs)
      let bargs' = renameBinderArgMetas stableCaptureRenaming bargs
      pure (M.fromList (zip holes bargs'))

    onGenEdge diagSrc0 diagTgt edgeKey edgeSrc mappedBargs =
      case ePayload edgeSrc of
        PGen genName _argsSrc _bargsSrc -> do
          let modeSrc = dMode diagSrc0
          case M.lookup (modeSrc, genName) (morGenMap mor) of
            Nothing -> Left "applyMorphismDiagram: missing generator mapping"
            Just image0 -> do
              genDecl0 <- lookupGenDeclInDoctrine "applyMorphismDiagram: unknown generator" (morSrc mor) modeSrc genName
              (genDecl, image0Fresh) <-
                freshenGenDeclAndImage
                  srcTheory
                  tgtTheory
                  tgtCtorTables
                  mor
                  edgeKey
                  genDecl0
                  image0
              substSrc <- instantiateGen srcTheory genDecl diagSrc0 edgeSrc
              substTgt <- mapSubstWithTheories srcTheory tgtTheory tgtCtorTables mor substSrc
              let modeTgt = dMode diagTgt
              let image = giDiagram image0Fresh
              if dMode image /= modeTgt
                then Left "applyMorphismDiagram: generator mapping mode mismatch"
                else Right ()
              instImage0 <- applySubstDiagram tgtTheory substTgt image
              instHoleSigs0 <- applySubstBinderSigs tgtTheory substTgt (giBinderSigs image0Fresh)
              holeSub <- buildBinderHoleSub genDecl mappedBargs
              instImage <- instantiateGenImageBindersWithMapper tgtTheory (applyModExpr (morTgt mor)) instHoleSigs0 holeSub instImage0
              let holeKeys = S.fromList (binderHoleNames (length (binderSlots genDecl)))
              let remaining = S.intersection holeKeys (binderMetaVarsDiagram instImage)
              if S.null remaining
                then Right ()
                else Left "applyMorphismDiagram: uninstantiated binder holes in generator image"
              instImage' <- weakenDiagramTmCtxTo (dTmCtx diagTgt) instImage
              first
                (\err ->
                  "applyMorphismDiagram: generator mapping for "
                    <> renderGenName genName
                    <> " failed: "
                    <> err
                )
                (spliceEdge diagTgt edgeKey instImage')
        _ ->
          Left "applyMorphismDiagram: internal error: diOnGenEdge called on non-PGen"

    freshenGenDeclAndImage
      :: TypeTheory
      -> TypeTheory
      -> CtorTables
      -> Morphism
      -> Int
      -> GenDecl
      -> GenImage
      -> Either Text (GenDecl, GenImage)
    freshenGenDeclAndImage ttSrc ttTgt tgtTables mor' edgeIdx genDecl image0 = do
      (freshParams, renameSrc) <- freshenSourceParams ttSrc edgeIdx (gdParams genDecl)
      domFresh <- mapM (renameInputShape renameSrc) (gdDom genDecl)
      codFresh <- applySubstCtx ttSrc renameSrc (gdCod genDecl)
      renameTgt <- buildTargetRenameSubst ttSrc ttTgt tgtTables mor' (gdParams genDecl) freshParams
      imageFresh <- applySubstDiagram ttTgt renameTgt (giDiagram image0)
      sigsFresh <- applySubstBinderSigs ttTgt renameTgt (giBinderSigs image0)
      pure
        ( genDecl
            { gdParams = freshParams
            , gdDom = domFresh
            , gdCod = codFresh
            }
        , image0
            { giDiagram = imageFresh
            , giBinderSigs = sigsFresh
            }
        )

    freshenSourceParams
      :: TypeTheory
      -> Int
      -> [GenParam]
      -> Either Text ([GenParam], Subst)
    freshenSourceParams tt edgeIdx =
      go 0 emptySubst []
      where
        go _ subst acc [] =
          Right (reverse acc, subst)
        go i subst acc (param : rest) =
          case param of
            GP_Ty v -> do
              sort' <- applySubstObj tt subst (tmvSort v)
              let fresh = freshTyParamVar edgeIdx i v sort'
              singleton <- mkSubst [(v, CAObj (OVar fresh))]
              subst' <- composeSubst tt singleton subst
              go (i + 1) subst' (GP_Ty fresh : acc) rest
            GP_Tm v -> do
              sort' <- applySubstObj tt subst (tmvSort v)
              let fresh = freshTmParamVar edgeIdx i v sort'
              tmFresh <- termExprToDiagramChecked tt [] sort' (TMMeta fresh [])
              singleton <- mkSubst [(v, CATm tmFresh)]
              subst' <- composeSubst tt singleton subst
              go (i + 1) subst' (GP_Tm fresh : acc) rest

    renameInputShape :: Subst -> InputShape -> Either Text InputShape
    renameInputShape subst shape =
      case shape of
        InPort ty -> InPort <$> applySubstObj srcTheory subst ty
        InBinder sig -> InBinder <$> applySubstBinderSig srcTheory subst sig

    buildTargetRenameSubst
      :: TypeTheory
      -> TypeTheory
      -> CtorTables
      -> Morphism
      -> [GenParam]
      -> [GenParam]
      -> Either Text Subst
    buildTargetRenameSubst ttSrc ttTgt tgtTables mor' oldParams newParams =
      mkSubst =<< mapM renameOne (zip oldParams newParams)
      where
        renameOne (oldParam, newParam) =
          case (oldParam, newParam) of
            (GP_Ty oldVar, GP_Ty newVar) -> do
              oldTgt <- mapTyParamToTarget ttSrc ttTgt tgtTables mor' oldVar
              newTgt <- mapTyParamToTarget ttSrc ttTgt tgtTables mor' newVar
              pure (oldTgt, CAObj (OVar newTgt))
            (GP_Tm oldVar, GP_Tm newVar) -> do
              oldTgt <- mapTmParamToTarget ttSrc ttTgt tgtTables mor' oldVar
              newTgt <- mapTmParamToTarget ttSrc ttTgt tgtTables mor' newVar
              tmFresh <- termExprToDiagramChecked ttTgt [] (tmvSort newTgt) (TMMeta newTgt [])
              pure (oldTgt, CATm tmFresh)
            _ ->
              Left "applyMorphismDiagram: internal error: parameter kind mismatch during freshening"

    mapTyParamToTarget
      :: TypeTheory
      -> TypeTheory
      -> CtorTables
      -> Morphism
      -> TmVar
      -> Either Text TmVar
    mapTyParamToTarget ttSrc ttTgt tgtTables mor' v = do
      ownerTgt <- mapMode mor' (tmVarOwner v)
      sortTgt <- applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor' (tmvSort v)
      pure v { tmvSort = sortTgt, tmvOwnerMode = Just ownerTgt }

    mapTmParamToTarget
      :: TypeTheory
      -> TypeTheory
      -> CtorTables
      -> Morphism
      -> TmVar
      -> Either Text TmVar
    mapTmParamToTarget ttSrc ttTgt tgtTables mor' v = do
      sortTgt <- applyMorphismTyWithCaches ttSrc ttTgt tgtTables mor' (tmvSort v)
      pure v { tmvSort = sortTgt, tmvOwnerMode = Nothing }

    freshTyParamVar :: Int -> Int -> TmVar -> Obj -> TmVar
    freshTyParamVar edgeIdx i v sort' =
      v
        { tmvName = tmvName v <> "__mor" <> T.pack (show edgeIdx) <> "_" <> T.pack (show i)
        , tmvSort = sort'
        }

    freshTmParamVar :: Int -> Int -> TmVar -> Obj -> TmVar
    freshTmParamVar edgeIdx i v sort' =
      v
        { tmvName = tmvName v <> "__mor" <> T.pack (show edgeIdx) <> "_" <> T.pack (show i)
        , tmvSort = sort'
        , tmvOwnerMode = Nothing
        }

mapSubstWithTheories
  :: TypeTheory
  -> TypeTheory
  -> CtorTables
  -> Morphism
  -> Subst
  -> Either Text Subst
mapSubstWithTheories srcTheory tgtTheory tgtCtorTables mor subst = do
  tyPairs <- mapM mapTyOne (codeBindings subst)
  tmPairs <- mapM mapTmOne (tmBindings subst)
  mkSubst
    ( [ (v, CAObj t)
      | (v, t) <- tyPairs
      ]
        <> [ (v, CATm t)
           | (v, t) <- tmPairs
           ]
    )
  where
    mapTyOne :: (TmVar, Obj) -> Either Text (TmVar, Obj)
    mapTyOne (v, t) = do
      ownerSrc <- pure (tmVarOwner v)
      ownerTgt <- mapMode mor ownerSrc
      sortV' <- applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor (tmvSort v)
      let v' = v { tmvSort = sortV', tmvOwnerMode = Just ownerTgt }
      t' <- applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor t
      pure (v', t')
    mapTmOne (v, t) = do
      sort' <- applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor (tmvSort v)
      t' <- applyMorphismTmTermWithTheories srcTheory tgtTheory tgtCtorTables mor t
      pure (v { tmvSort = sort' }, t')

applyMorphismBinderSig :: Morphism -> BinderSig -> Either Text BinderSig
applyMorphismBinderSig mor sig = do
  tgtCtorTables <- deriveCtorTables (morTgt mor)
  applyMorphismBinderSigWithTables tgtCtorTables mor sig

applyMorphismBinderSigWithTables :: CtorTables -> Morphism -> BinderSig -> Either Text BinderSig
applyMorphismBinderSigWithTables = applyMorphismBinderSigInTables

applyMorphismBinderSigInTables :: CtorTables -> Morphism -> BinderSig -> Either Text BinderSig
applyMorphismBinderSigInTables tgtCtorTables mor sig = do
  srcTheory <- doctrineTypeTheory (morSrc mor)
  tgtTheory <- doctrineTypeTheoryFromTables (morTgt mor) tgtCtorTables
  tmCtx' <- mapM (applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor) (bsTmCtx sig)
  dom' <- mapM (applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor) (bsDom sig)
  cod' <- mapM (applyMorphismTyWithCaches srcTheory tgtTheory tgtCtorTables mor) (bsCod sig)
  pure sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

renderGenName :: GenName -> Text
renderGenName (GenName name) = name

checkMorphismResultWithBudget :: SearchBudget -> Morphism -> Either Text MorphismCheckResult
checkMorphismResultWithBudget budget mor = do
  srcCtorTables <- deriveCtorTables (morSrc mor)
  tgtCtorTables <- deriveCtorTables (morTgt mor)
  ttSrc <- doctrineTypeTheoryFromTables (morSrc mor) srcCtorTables
  ttTgt <- doctrineTypeTheoryFromTables (morTgt mor) tgtCtorTables
  let srcGens = allGensInTables (morSrc mor) srcCtorTables
  validateModeMap mor
  validateModMap mor
  validateModEqPreservation mor
  validateClassificationPreservation tgtCtorTables ttSrc ttTgt mor
  validateLiteralKindPreservation tgtCtorTables ttSrc ttTgt mor
  validateTypeMap srcCtorTables tgtCtorTables ttSrc ttTgt mor
  mapM_ (checkGenMapping tgtCtorTables ttSrc ttTgt mor) srcGens
  case morCheck mor of
    CheckNone -> Right (MorphismCheckProved [])
    _ -> do
      let srcCells =
            case morCheck mor of
              CheckAll -> dCells2 (morSrc mor)
              CheckStructural -> filter ((== Structural) . c2Class) (dCells2 (morSrc mor))
      fastOk <- inclusionFastPath srcCtorTables mor
      if fastOk
        then Right (MorphismCheckProved [])
        else do
          renameOk <- renamingFastPath srcCtorTables tgtCtorTables mor srcCells
          if renameOk
            then Right (MorphismCheckProved [])
            else checkCells budget ttSrc ttTgt tgtCtorTables mor srcCells

checkMorphismWithBudget :: SearchBudget -> Morphism -> Either Text ()
checkMorphismWithBudget budget mor = do
  result <- checkMorphismResultWithBudget budget mor
  case result of
    MorphismCheckProved _ ->
      Right ()
    MorphismCheckUndecided cellName lim ->
      Left
        ( "checkMorphism: equation undecided for "
            <> cellName
            <> " ("
            <> renderSearchLimit lim
            <> ")"
        )

checkMorphism :: Morphism -> Either Text ()
checkMorphism = checkMorphismWithBudget defaultSearchBudget

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

validateModEqPreservation :: Morphism -> Either Text ()
validateModEqPreservation mor =
  mapM_ checkOne (mtEqns (dModes (morSrc mor)))
  where
    tgtMt = dModes (morTgt mor)
    checkOne eqn = do
      lhsMapped <- applyMorphismModExpr mor (meLHS eqn)
      rhsMapped <- applyMorphismModExpr mor (meRHS eqn)
      let lhsNorm = normalizeModExpr tgtMt lhsMapped
      let rhsNorm = normalizeModExpr tgtMt rhsMapped
      if lhsNorm == rhsNorm
        then Right ()
        else
          Left
            ( "checkMorphism: source mod_eq is not preserved: "
                <> renderEqn eqn
                <> "; mapped: "
                <> renderModExpr lhsMapped
                <> " -> "
                <> renderModExpr rhsMapped
                <> "; normalized: "
                <> renderModExpr lhsNorm
                <> " vs "
                <> renderModExpr rhsNorm
            )
    renderEqn eqn = renderModExpr (meLHS eqn) <> " -> " <> renderModExpr (meRHS eqn)
    renderModExpr me =
      case mePath me of
        [] -> "id@" <> renderMode (meSrc me)
        path ->
          T.intercalate "." (map renderMod path)
            <> " : "
            <> renderMode (meSrc me)
            <> " -> "
            <> renderMode (meTgt me)
    renderMode (ModeName name) = name
    renderMod (ModName name) = name

validateClassificationPreservation :: CtorTables -> TypeTheory -> TypeTheory -> Morphism -> Either Text ()
validateClassificationPreservation tgtCtorTables ttSrc ttTgt mor = do
  mapM_ checkClassificationEdge (M.toList (mtClassifiedBy srcMt))
  mapM_ checkLiftCoherence (M.toList (mtDecls srcMt))
  where
    srcMt = dModes (morSrc mor)
    tgtMt = dModes (morTgt mor)

    checkClassificationEdge (modeSrc, srcDecl) = do
      modeTgt <- mapMode mor modeSrc
      tgtDecl <-
        case M.lookup modeTgt (mtClassifiedBy tgtMt) of
          Nothing ->
            Left
              ( "checkMorphism: mapped mode "
                  <> renderMode modeSrc
                  <> " -> "
                  <> renderMode modeTgt
                  <> " is not classified in target"
              )
          Just decl -> Right decl
      mappedClassifier <- mapMode mor (cdClassifier srcDecl)
      if cdClassifier tgtDecl == mappedClassifier
        then Right ()
        else
          Left
            ( "checkMorphism: classifier edge mismatch for mode "
                <> renderMode modeSrc
                <> " (expected "
                <> renderMode mappedClassifier
                <> ", got "
                <> renderMode (cdClassifier tgtDecl)
                <> ")"
            )
      srcUniverseMapped <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables mor (cdUniverse srcDecl)
      universeOk <- defEqObj ttTgt [] srcUniverseMapped (cdUniverse tgtDecl)
      if universeOk
        then Right ()
        else
          Left
            ( "checkMorphism: universe mismatch for classified mode "
                <> renderMode modeSrc
                <> " after mapping"
            )
      case cdComp srcDecl of
        Nothing -> Right ()
        Just compSrc -> do
          compTgt <-
            case cdComp tgtDecl of
              Nothing ->
                Left
                  ( "checkMorphism: mapped classified mode "
                      <> renderMode modeSrc
                      <> " is missing comprehension witnesses in target"
                  )
              Just comp -> Right comp
          ctxExt' <- mappedWitnessName modeSrc modeTgt (compCtxExt compSrc)
          var' <- mappedWitnessName modeSrc modeTgt (compVar compSrc)
          reindex' <- mappedWitnessName modeSrc modeTgt (compReindex compSrc)
          if ctxExt' == compCtxExt compTgt && var' == compVar compTgt && reindex' == compReindex compTgt
            then Right ()
            else
              Left
                ( "checkMorphism: comprehension witness mismatch for mode "
                    <> renderMode modeSrc
                )

    mappedWitnessName modeSrc modeTgt witnessName =
      case M.lookup (modeSrc, witnessName) (morGenMap mor) of
        Just image -> do
          mapped <- singleGeneratorWitnessName modeTgt image
          _ <- lookupGenDeclInDoctrine "applyMorphismDiagram: unknown generator" (morTgt mor) modeTgt mapped
          Right mapped
        Nothing ->
          Left
            ( "checkMorphism: missing generator mapping for comprehension witness "
                <> renderMode modeSrc
                <> "."
                <> renderGen witnessName
            )

    singleGeneratorWitnessName modeTgt image =
      let diag = giDiagram image
       in if dMode diag /= modeTgt
            then Left "checkMorphism: comprehension witness image mode mismatch"
            else
              case IM.elems (dEdges diag) of
                [edge] ->
                  case ePayload edge of
                    PGen genName _ binderArgs
                      | null binderArgs -> Right genName
                      | otherwise -> Left "checkMorphism: comprehension witness image cannot use binder arguments"
                    _ -> Left "checkMorphism: comprehension witness image must be a single generator edge"
                _ -> Left "checkMorphism: comprehension witness image must be a single-edge generator diagram"

    checkLiftCoherence (modName, decl)
      | not (isClassifiedMode (mdSrc decl) && isClassifiedMode (mdTgt decl)) = Right ()
      | otherwise = do
          mappedModality <-
            case M.lookup modName (morModMap mor) of
              Nothing -> Left "checkMorphism: missing modality mapping"
              Just me -> Right me
          srcLift <-
            case classifierLiftForModality srcMt modName of
              Left err -> Left ("checkMorphism: " <> err)
              Right me -> Right me
          liftMapped <- applyMorphismModExpr mor srcLift
          liftExpected <-
            case classifierLiftForModExpr tgtMt mappedModality of
              Left err -> Left ("checkMorphism: " <> err)
              Right me -> Right me
          let liftMappedNorm = normalizeModExpr tgtMt liftMapped
          let liftExpectedNorm = normalizeModExpr tgtMt liftExpected
          if liftMappedNorm == liftExpectedNorm
            then Right ()
            else
              Left
                ( "checkMorphism: classifier lift coherence mismatch for modality "
                    <> renderMod modName
                )

    isClassifiedMode mode = M.member mode (mtClassifiedBy srcMt)

    renderMode (ModeName name) = name
    renderGen (GenName name) = name
    renderMod (ModName name) = name

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

validateLiteralKindPreservation :: CtorTables -> TypeTheory -> TypeTheory -> Morphism -> Either Text ()
validateLiteralKindPreservation tgtCtorTables ttSrc ttTgt mor =
  mapM_ checkOne literalGens
  where
    literalGens =
      [ gd
      | table <- M.elems (dGens (morSrc mor))
      , gd <- M.elems table
      , Just _ <- [gdLiteralKind gd]
      ]

    checkOne gd =
      case gdLiteralKind gd of
        Nothing -> Right ()
        Just srcKind -> do
          tgtTy <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables mor (sourceTy gd)
          case literalKindForObj ttTgt tgtTy of
            Just tgtKind
              | tgtKind == srcKind -> Right ()
              | otherwise ->
                  Left
                    ( "morphism: literal kind changes for "
                        <> renderGen (gdName gd)
                        <> " @"
                        <> renderMode (gdMode gd)
                        <> " (expected "
                        <> renderLiteralKind srcKind
                        <> ", got "
                        <> renderLiteralKind tgtKind
                        <> ")"
                    )
            Nothing ->
              Left
                ( "morphism: literal kind is not preserved for "
                    <> renderGen (gdName gd)
                    <> " @"
                    <> renderMode (gdMode gd)
                )

    sourceTy gd =
      Obj
        { objOwnerMode = gdMode gd
        , objCode =
            CTCon
              ( ObjRef
                  (modeClassifierMode (dModes (morSrc mor)) (gdMode gd))
                  (ObjName (renderGen (gdName gd)))
              )
              []
        }

    renderMode (ModeName name) = name
    renderGen (GenName name) = name

validateTypeMap :: CtorTables -> CtorTables -> TypeTheory -> TypeTheory -> Morphism -> Either Text ()
validateTypeMap srcCtorTables tgtCtorTables ttSrc ttTgt mor = do
  ensureAcyclicTypeTemplates mor
  mapM_ (checkEntry ttTgt) (M.toList (morTypeMap mor))
  where
    checkEntry ttTgt (srcRef, tmpl) = do
      srcParams <- lookupCtorSigByRefInTables (morSrc mor) srcCtorTables srcRef
      let tmplParams = ttParams tmpl
      if length tmplParams /= length srcParams
        then Left "checkMorphism: type template arity mismatch"
        else Right ()
      ensureDistinctTemplateNames tmplParams
      mapM_ (uncurry (checkParam ttTgt)) (zip srcParams tmplParams)
      let tyVars = [ v | GP_Ty v <- tmplParams ]
      let tmVars = [ v | GP_Tm v <- tmplParams ]
      checkType (morTgt mor) ttTgt tyVars tmVars [] (ttBody tmpl)
      mappedMode <- mapMode mor (orMode srcRef)
      if objMode (ttBody tmpl) == mappedMode
        then Right ()
        else Left "checkMorphism: type template body mode mismatch"

    ensureDistinctTemplateNames params =
      let names = [ tmvName v | GP_Ty v <- params ] <> [ tmvName v | GP_Tm v <- params ]
          set = S.fromList names
      in if S.size set == length names
          then Right ()
          else Left "checkMorphism: duplicate type template parameter name"

    checkParam ttTgt srcParam tmplParam =
      case (srcParam, tmplParam) of
        (TPS_Ty srcMode, GP_Ty v) -> do
          expectedMode <- mapMode mor srcMode
          expectedUniverse <-
            case modeUniverseObj (dModes (morTgt mor)) expectedMode of
              Nothing ->
                Left
                  ( "checkMorphism: type template type parameter requires classified universe for mode "
                      <> renderMode expectedMode
                  )
              Just u -> Right u
          sortOk <- sortDefEq ttTgt expectedUniverse (tmvSort v)
          if sortOk
            then Right ()
            else Left "checkMorphism: type template type-parameter universe mismatch"
        (TPS_Tm srcSort, GP_Tm tmParam) -> do
          expectedMode <- mapMode mor (objMode srcSort)
          if objMode (tmvSort tmParam) == expectedMode
            then do
              expectedSortTgt <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables mor srcSort
              sortOk <- sortDefEq ttTgt expectedSortTgt (tmvSort tmParam)
              if sortOk
                then Right ()
                else Left "checkMorphism: type template term-parameter sort mismatch"
            else Left "checkMorphism: type template term-parameter mode mismatch"
        (TPS_Ty _, _) ->
          Left "checkMorphism: type template kind mismatch"
        (TPS_Tm _, _) ->
          Left "checkMorphism: type template kind mismatch"
      where
        renderMode (ModeName n) = n

    sortDefEq ttTgt lhs rhs = do
      lhs' <- normalizeObjDeep ttTgt lhs
      rhs' <- normalizeObjDeep ttTgt rhs
      pure (lhs' == rhs')

ensureAcyclicTypeTemplates :: Morphism -> Either Text ()
ensureAcyclicTypeTemplates mor =
  case findTemplateCycle mor of
    Nothing -> Right ()
    Just refs ->
      Left ("checkMorphism: cyclic type template map: " <> renderCycle refs)
  where
    renderCycle refs = T.intercalate " -> " (map renderRef refs)
    renderRef ref = renderMode (orMode ref) <> "." <> renderType (orName ref)
    renderMode (ModeName name) = name
    renderType (ObjName name) = name

findTemplateCycle :: Morphism -> Maybe [ObjRef]
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
          , dep /= ref
          ]

    cycleFrom ref stack =
      let prefix = takeWhile (/= ref) stack
      in ref : reverse prefix <> [ref]

typeRefsInType :: Obj -> S.Set ObjRef
typeRefsInType ty =
  case ty of
    OVar _ -> S.empty
    OCon ref args ->
      S.insert ref (S.unions (map typeRefsInArg args))
    OLift _ inner ->
      typeRefsInType inner
  where
    typeRefsInArg arg =
      case arg of
        OAObj t -> typeRefsInType t
        OATm tmArg -> typeRefsInTerm tmArg

    typeRefsInTerm (TermDiagram diag) =
      S.unions
        [ S.unions (map typeRefsInType (IM.elems (dPortObj diag)))
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

checkGenMapping :: CtorTables -> TypeTheory -> TypeTheory -> Morphism -> GenDecl -> Either Text ()
checkGenMapping tgtCtorTables ttSrc ttTgt mor gen = do
  let modeSrc = gdMode gen
  modeTgt <- mapMode mor modeSrc
  dom <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables mor) (gdPlainDom gen)
  cod <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables mor) (gdCod gen)
  case M.lookup (modeSrc, gdName gen) (morGenMap mor) of
    Nothing ->
      Left "checkMorphism: missing generator mapping"
    Just image0 -> do
      let image = giDiagram image0
      if dMode image /= modeTgt
        then Left "checkMorphism: generator mapping mode mismatch"
        else do
          domImg <- diagramDom image
          codImg <- diagramCod image
          _ <-
            case unifyCtxCompat ttTgt [] dom domImg of
              Left err -> Left ("checkMorphism: generator mapping domain mismatch for " <> renderGen (gdName gen) <> ": " <> err)
              Right subst -> Right subst
          _ <-
            case unifyCtxCompat ttTgt [] cod codImg of
              Left err -> Left ("checkMorphism: generator mapping codomain mismatch for " <> renderGen (gdName gen) <> ": " <> err)
              Right subst -> Right subst
          let binderSlotsSrc =
                [ bs
                | InBinder bs <- gdDom gen
                ]
          let holes = binderHoleNames (length binderSlotsSrc)
          binderSlotsTgt <- mapM (applyMorphismBinderSigWithTables tgtCtorTables mor) binderSlotsSrc
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
  where
    renderGen (GenName name) = name

checkCells :: SearchBudget -> TypeTheory -> TypeTheory -> CtorTables -> Morphism -> [Cell2] -> Either Text MorphismCheckResult
checkCells _ _ _ _ _ [] = Right (MorphismCheckProved [])
checkCells budget ttSrc ttTgt tgtCtorTables mor (cell:rest) = do
  result <- checkCell budget ttSrc ttTgt tgtCtorTables mor cell
  case result of
    MorphismCheckProved proofs -> do
      restResult <- checkCells budget ttSrc ttTgt tgtCtorTables mor rest
      case restResult of
        MorphismCheckProved restProofs ->
          Right (MorphismCheckProved (proofs <> restProofs))
        MorphismCheckUndecided{} ->
          Right restResult
    MorphismCheckUndecided{} ->
      Right result

checkCell :: SearchBudget -> TypeTheory -> TypeTheory -> CtorTables -> Morphism -> Cell2 -> Either Text MorphismCheckResult
checkCell budget ttSrc ttTgt tgtCtorTables mor cell = do
  lhs <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables mor (c2LHS cell)
  rhs <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables mor (c2RHS cell)
  let rules = rulesFromPolicy (morPolicy mor) (dCells2 (morTgt mor))
  proof <- autoJoinProofWithMapper (applyModExpr (morTgt mor)) ttTgt budget rules lhs rhs
  case proof of
    SearchUndecided lim ->
      Right (MorphismCheckUndecided (c2Name cell) lim)
    SearchProved witness -> do
      checkJoinProofWithMapper (applyModExpr (morTgt mor)) ttTgt rules witness
      Right (MorphismCheckProved [(c2Name cell, witness)])

inclusionFastPath :: CtorTables -> Morphism -> Either Text Bool
inclusionFastPath srcCtorTables mor
  | not (modeMapIsIdentity mor) = Right False
  | not (modMapIsIdentity mor) = Right False
  | not (M.null (morTypeMap mor)) = Right False
  | otherwise = do
      let srcGens = allGensInTables (morSrc mor) srcCtorTables
      okGens <- allM (genIsIdentity mor) srcGens
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

renamingFastPath :: CtorTables -> CtorTables -> Morphism -> [Cell2] -> Either Text Bool
renamingFastPath srcCtorTables tgtCtorTables mor srcCells = do
  if not (modeMapIsIdentity mor) || not (modMapIsIdentity mor)
    then Right False
  else do
    let tgt = morTgt mor
    mTypeRen <- buildTypeRenaming srcCtorTables tgtCtorTables mor
    mGenRen <- buildGenRenaming srcCtorTables mor
    case (mTypeRen, mGenRen) of
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
        Just tgt0 ->
          if c2Class cell /= c2Class tgt0 || c2Orient cell /= c2Orient tgt0
            then Right False
            else
              case alphaAlignCellTo cell tgt0 of
                Left _ -> Right False
                Right tgt -> do
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
        matchesCell cell tgt0 =
          if dMode (c2LHS cell) /= dMode (c2LHS tgt0)
            || c2Class cell /= c2Class tgt0
            || c2Orient cell /= c2Orient tgt0
            then Right False
            else
              case alphaAlignCellTo cell tgt0 of
                Left _ -> Right False
                Right tgt -> do
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

buildTypeRenaming :: CtorTables -> CtorTables -> Morphism -> Either Text (Maybe (M.Map ObjRef ObjRef))
buildTypeRenaming srcCtorTables tgtCtorTables mor = do
  let src = morSrc mor
  srcCtors <- allCtorsInTables src srcCtorTables
  case foldl step (Just M.empty) srcCtors of
    Nothing -> Right Nothing
    Just mp ->
      if injective (M.elems mp)
        then Right (Just mp)
        else Right Nothing
  where
    tgt = morTgt mor
    step acc (ref, sig) = do
      mp <- acc
      let mapped =
            case M.lookup ref (morTypeMap mor) of
              Nothing -> Just ref
              Just tmpl -> renamingTarget tmpl (length sig)
      case mapped of
        Nothing -> Nothing
        Just tgtRef ->
          case lookupCtorSigByRefInTables tgt tgtCtorTables tgtRef of
            Right sigTgt
              | length sigTgt == length sig ->
                  Just (M.insert ref tgtRef mp)
            _ -> Nothing

    renamingTarget tmpl arity =
      case ttBody tmpl of
        OCon tgtRef params
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
        OAObj (OVar v) ->
          findParamIndex params (\p -> case p of GP_Ty v' -> v' == v; _ -> False)
        OATm tm ->
          case termMetaOnly tm of
            Just v ->
              findParamIndex params (\p -> case p of GP_Tm v' -> v' == v; _ -> False)
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

buildGenRenaming :: CtorTables -> Morphism -> Either Text (Maybe (M.Map (ModeName, GenName) GenName))
buildGenRenaming srcCtorTables mor = do
  let srcGens = allGensInTables (morSrc mor) srcCtorTables
  case foldl step (Just M.empty) srcGens of
    Nothing -> Right Nothing
    Just mp ->
      if injective (M.elems mp)
        then Right (Just mp)
        else Right Nothing
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
      case canonDiagramRaw (giDiagram image0) of
        Left _ -> Nothing
        Right canon ->
          case IM.elems (dEdges canon) of
            [edge] ->
              let boundary = dIn canon <> dOut canon
                  edgePorts = eIns edge <> eOuts edge
                  allPorts = diagramPortIds canon
              in case ePayload edge of
                PGen g args bargs
                  | boundary == edgePorts
                  , length allPorts == length boundary
                  , bargs == expectedBinderArgs
                  , passThroughArgs (gdParams srcGen) args ->
                      Just g
                _ -> Nothing
            _ -> Nothing
  where
    binderSlots =
      [ bs
      | InBinder bs <- gdDom srcGen
      ]
    holes = binderHoleNames (length binderSlots)
    expectedBinderArgs = map BAMeta holes
    expectedBinderSigs = M.fromList (zip holes binderSlots)
    passThroughArgs params args =
      length params == length args
        && and (zipWith argMatches params args)

    argMatches param arg =
      case (param, arg) of
        (GP_Ty v, CAObj (OVar v')) -> v == v'
        (GP_Tm v, CATm tm) -> termMetaOnly tm == Just v
        _ -> False

    termMetaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dIn diag, dOut diag) of
        ([edge], [], [outBoundary]) ->
          case (ePayload edge, eIns edge, eOuts edge) of
            (PTmMeta v, [], [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
        _ -> Nothing

renameDiagram :: M.Map ObjRef ObjRef -> M.Map (ModeName, GenName) GenName -> Diagram -> Diagram
renameDiagram tyRen genRen diag =
  runIdentity (traverseDiagram onDiag onPayload onCodeArg pure diag)
  where
    onDiag d =
      pure d
        { dTmCtx = map (renameObjExpr tyRen) (dTmCtx d)
        , dPortObj = IM.map (renameObjExpr tyRen) (dPortObj d)
        }

    onPayload payload =
      pure $
        case payload of
          PGen gen args bargs ->
            let gen' = M.findWithDefault gen (dMode diag, gen) genRen
            in PGen gen' args bargs
          PTmMeta v ->
            PTmMeta v { tmvSort = renameObjExpr tyRen (tmvSort v) }
          _ -> payload

    onCodeArg arg =
      pure $
        case arg of
          CAObj obj -> CAObj (renameObjExpr tyRen obj)
          CATm tm -> CATm tm

renameObjExpr :: M.Map ObjRef ObjRef -> Obj -> Obj
renameObjExpr ren ty =
  ty { objCode = renameCode (objCode ty) }
  where
    renameCode code =
      case code of
        CTMeta v -> CTMeta v
        CTCon ref args ->
          let ref' = M.findWithDefault ref ref ren
          in CTCon ref' (map renameArg args)
        CTLift me inner ->
          CTLift me (renameCode inner)

    renameArg arg =
      case arg of
        OAObj t -> OAObj (renameObjExpr ren t)
        OATm tmArg -> OATm (renameTermDiagram tmArg)

    renameTermDiagram (TermDiagram diag) =
      TermDiagram
        diag
          { dTmCtx = map (renameObjExpr ren) (dTmCtx diag)
          , dPortObj = IM.map (renameObjExpr ren) (dPortObj diag)
          , dEdges = IM.map renameEdge (dEdges diag)
          }

    renameEdge edge =
      case ePayload edge of
        PTmMeta v ->
          edge { ePayload = PTmMeta v { tmvSort = renameObjExpr ren (tmvSort v) } }
        _ -> edge

injective :: Ord a => [a] -> Bool
injective xs =
  let set = S.fromList xs
  in length xs == S.size set

alphaAlignCellTo :: Cell2 -> Cell2 -> Either Text Cell2
alphaAlignCellTo target source
  | length (c2TyVars source) /= length (c2TyVars target) =
      Left "alphaAlignCellTo: type-parameter arity mismatch"
  | length (c2TmVars source) /= length (c2TmVars target) =
      Left "alphaAlignCellTo: term-parameter arity mismatch"
  | otherwise =
      let tyMap = M.fromList (zip (c2TyVars source) (c2TyVars target))
          tmMap = M.fromList (zip (c2TmVars source) (c2TmVars target))
      in Right
           source
             { c2Params = map (renameParamAlpha tyMap tmMap) (c2Params source)
             , c2LHS = renameDiagramAlpha tyMap tmMap (c2LHS source)
             , c2RHS = renameDiagramAlpha tyMap tmMap (c2RHS source)
             }

renameParamAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> GenParam -> GenParam
renameParamAlpha tyMap tmMap param =
  case param of
    GP_Ty v -> GP_Ty (renameTyVarAlpha tyMap v)
    GP_Tm v -> GP_Tm (renameTmVarAlpha tyMap tmMap v)

renameTyVarAlpha :: M.Map TmVar TmVar -> TmVar -> TmVar
renameTyVarAlpha tyMap v =
  M.findWithDefault v v tyMap

renameTmVarAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TmVar -> TmVar
renameTmVarAlpha tyMap tmMap v =
  case M.lookup v tmMap of
    Just v' -> v'
    Nothing -> v { tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v) }

renameTypeAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> Obj -> Obj
renameTypeAlpha tyMap tmMap = goObj
  where
    goObj ty =
      ty { objCode = goCode (objCode ty) }

    goCode code =
      case code of
        CTMeta v ->
          CTMeta (renameTyVarAlpha tyMap v)
        CTCon ref args ->
          CTCon ref (map goArg args)
        CTLift me inner ->
          CTLift me (goCode inner)

    goArg arg =
      case arg of
        CAObj ty -> CAObj (goObj ty)
        CATm tm -> CATm (renameTermDiagramAlpha tyMap tmMap tm)

renameDiagramAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> Diagram -> Diagram
renameDiagramAlpha tyMap tmMap =
  runIdentity . traverseDiagram onDiag onPayload onCodeArg onBinderArg
  where
    onDiag d =
      pure d
        { dTmCtx = map (renameTypeAlpha tyMap tmMap) (dTmCtx d)
        , dPortObj = IM.map (renameTypeAlpha tyMap tmMap) (dPortObj d)
        }

    onPayload payload =
      pure $
        case payload of
          PGen g args bargs -> PGen g args bargs
          PBox name inner -> PBox name inner
          PFeedback inner -> PFeedback inner
          PTmMeta v ->
            PTmMeta (renameTmVarAlpha tyMap tmMap v)
          other ->
            other

    onCodeArg arg =
      pure (renameCodeArgAlpha tyMap tmMap arg)

    onBinderArg barg =
      pure (renameBinderArgAlpha tyMap tmMap barg)

renameCodeArgAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> CodeArg -> CodeArg
renameCodeArgAlpha tyMap tmMap arg =
  case arg of
    CAObj ty -> CAObj (renameTypeAlpha tyMap tmMap ty)
    CATm tm -> CATm (renameTermDiagramAlpha tyMap tmMap tm)

renameBinderArgAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> BinderArg -> BinderArg
renameBinderArgAlpha tyMap tmMap barg =
  case barg of
    BAConcrete inner -> BAConcrete (renameDiagramAlpha tyMap tmMap inner)
    BAMeta x -> BAMeta x

renameTermDiagramAlpha :: M.Map TmVar TmVar -> M.Map TmVar TmVar -> TermDiagram -> TermDiagram
renameTermDiagramAlpha tyMap tmMap (TermDiagram diag) =
  TermDiagram (renameDiagramAlpha tyMap tmMap diag)

allM :: (a -> Either Text Bool) -> [a] -> Either Text Bool
allM _ [] = Right True
allM f (x:xs) = do
  ok <- f x
  if ok
    then allM f xs
    else Right False

allGensInTables :: Doctrine -> CtorTables -> [GenDecl]
allGensInTables doc tables =
  [ gd
  | (mode, table) <- M.toList (dGens doc)
  , gd <- M.elems table
  , let GenName gName = gdName gd
  , let ctorNames = M.findWithDefault S.empty mode ctorNamesByClassifier
  , ObjName gName `S.notMember` ctorNames
  ]
  where
    ctorNamesByClassifier =
      M.fromListWith S.union
        [ (modeClassifierMode (dModes doc) ownerMode, S.fromList (M.keys table))
        | (ownerMode, table) <- M.toList tables
        ]

allCtorsInTables :: Doctrine -> CtorTables -> Either Text [(ObjRef, [TypeParamSig])]
allCtorsInTables doc tables = do
  merged <- foldM insertOwner M.empty (M.toList tables)
  pure (M.toList merged)
  where
    insertOwner acc (ownerMode, table) =
      let classifierMode = modeClassifierMode (dModes doc) ownerMode
       in foldM (insertCtor classifierMode) acc (M.toList table)

    insertCtor classifierMode acc (ctorName, sig) =
      let ref = ObjRef classifierMode ctorName
       in case M.lookup ref acc of
            Nothing -> Right (M.insert ref sig acc)
            Just sig0
              | sig0 == sig -> Right acc
              | otherwise -> Left "ambiguous constructor signature across owner modes"

lookupCtorSigByRefInTables :: Doctrine -> CtorTables -> ObjRef -> Either Text [TypeParamSig]
lookupCtorSigByRefInTables doc tables ref = do
  let sigs =
        [ sig
        | (ownerMode, table) <- M.toList tables
        , modeClassifierMode (dModes doc) ownerMode == orMode ref
        , Just sig <- [M.lookup (orName ref) table]
        ]
  case L.nub sigs of
    [] -> Left "checkMorphism: unknown source type in type map"
    [sig] -> Right sig
    _ -> Left "checkMorphism: ambiguous constructor signature across owner modes"

instantiateGen :: TypeTheory -> GenDecl -> Diagram -> Edge -> Either Text Subst
instantiateGen tt gen diag edge = do
  sArgs <- instantiateGenParams tt gen args
  dom <- mapM (requirePortType "applyMorphismDiagram" diag) (eIns edge)
  cod <- mapM (requirePortType "applyMorphismDiagram" diag) (eOuts edge)
  domExpected <- applySubstCtx tt sArgs (gdPlainDom gen)
  s1 <- unifyCtxFromPattern tt (dTmCtx diag) domExpected dom
  sDom <- composeSubst tt s1 sArgs
  codExpected <- applySubstCtx tt sDom (gdCod gen)
  s2 <- unifyCtxFromPattern tt (dTmCtx diag) codExpected cod
  s0 <- composeSubst tt s2 sDom
  if length binderSlots /= length bargs
    then Left "applyMorphismDiagram: source binder argument arity mismatch"
    else foldM checkBinderSlot s0 (zip binderSlots bargs)
  where
    binderSlots =
      [ bs
      | InBinder bs <- gdDom gen
      ]

    args =
      case ePayload edge of
        PGen _ as _ -> as
        _ -> []

    bargs =
      case ePayload edge of
        PGen _ _ bs -> bs
        _ -> []

    checkBinderSlot subst (slot, barg) =
      case barg of
        BAMeta _ ->
          Right subst
        BAConcrete inner -> do
          slot0 <- applySubstBinderSig tt subst slot
          slotTm <- applySubstCtx tt emptySubst (bsTmCtx slot0)
          innerTm <- applySubstCtx tt emptySubst (dTmCtx inner)
          if innerTm == slotTm
            then Right ()
            else Left "applyMorphismDiagram: binder argument term-context mismatch"
          domInner <- diagramDom inner
          sDom <- unifyCtxFromPattern tt slotTm (bsDom slot0) domInner
          subst1 <- composeSubst tt sDom subst
          slot1 <- applySubstBinderSig tt subst1 slot
          slotTm1 <- applySubstCtx tt emptySubst (bsTmCtx slot1)
          codInner <- diagramCod inner
          sCod <- unifyCtxFromPattern tt slotTm1 (bsCod slot1) codInner
          composeSubst tt sCod subst1
