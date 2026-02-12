{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.AST
import Strat.DSL.Template (instantiateTemplate)
import Strat.Frontend.Env
import Strat.Frontend.Compile (compileDiagramArtifact)
import Strat.Pipeline
import Strat.Poly.Attr
import Strat.Poly.DSL.AST (rpdExtends, rpdName)
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.DSL.Elab (elabPolyDoctrine, elabPolyMorphism, parsePolicy)
import Strat.Poly.Diagram (Diagram(..), genDWithAttrs)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), InputShape(..), TypeSig(..), gdPlainDom)
import Strat.Poly.Graph (BinderArg(..), BinderMetaVar(..), Edge(..), EdgePayload(..))
import Strat.Poly.ModeTheory
  ( ModeTheory(..)
  , ModDecl(..)
  , ModExpr(..)
  , ModeName(..)
  , emptyModeTheory
  , addMode
  , setModeDiscipline
  , modeDiscipline
  )
import Strat.Poly.TypeExpr (TypeExpr(..), TypeRef(..), TypeName(..))
import Strat.Poly.Names (GenName(..))
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Poly.Pushout (PolyPushoutResult(..), computePolyPushout, computePolyCoproduct)
import Strat.Poly.Surface (elabPolySurfaceDecl)
import Strat.Poly.Surface.Spec (ssDoctrine, ssBaseDoctrine)


elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile = elabRawFileWithEnv emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv baseEnv (RawFile decls) = do
  (env, rawTerms, rawRuns) <- foldM step (baseEnv, [], []) decls
  envWithTerms <- elabTerms env rawTerms
  runs <- elabRuns envWithTerms rawRuns
  pure envWithTerms { meRuns = runs }
  where
    step (env, rawTerms, rawRuns) decl =
      case decl of
        DeclImport _ -> Right (env, rawTerms, rawRuns)
        DeclDoctrine raw -> do
          env' <- insertDoctrine env raw
          pure (env', rawTerms, rawRuns)
        DeclDoctrinePushout name leftMor rightMor -> do
          env' <- insertPushout env name leftMor rightMor
          pure (env', rawTerms, rawRuns)
        DeclDoctrineCoproduct name leftDoc rightDoc -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          left <- lookupDoctrine env leftDoc
          right <- lookupDoctrine env rightDoc
          PolyPushoutResult doc inl inr glue <- computePolyCoproduct name left right
          ensureAbsent "morphism" (PolyMorph.morName inl) (meMorphisms env)
          ensureAbsent "morphism" (PolyMorph.morName inr) (meMorphisms env)
          ensureAbsent "morphism" (PolyMorph.morName glue) (meMorphisms env)
          let env' =
                env
                  { meDoctrines = M.insert name doc (meDoctrines env)
                  , meMorphisms =
                      M.insert (PolyMorph.morName glue) glue
                        (M.insert (PolyMorph.morName inl) inl
                          (M.insert (PolyMorph.morName inr) inr (meMorphisms env)))
                  }
          pure (env', rawTerms, rawRuns)
        DeclDoctrineTemplate tmpl -> do
          ensureAbsent "doctrine_template" (rdtName tmpl) (meTemplates env)
          let env' = env { meTemplates = M.insert (rdtName tmpl) tmpl (meTemplates env) }
          pure (env', rawTerms, rawRuns)
        DeclDoctrineInstantiate inst -> do
          env' <- elabDoctrineInstantiate env inst
          pure (env', rawTerms, rawRuns)
        DeclDoctrineEffects name base effects -> do
          env' <- elabDoctrineEffects env name base effects
          pure (env', rawTerms, rawRuns)
        DeclDerivedDoctrine rawDerived -> do
          env' <- insertDerivedDoctrine env rawDerived
          pure (env', rawTerms, rawRuns)
        DeclSurface name spec -> do
          ensureAbsent "surface" name (meSurfaces env)
          doc <- lookupDoctrine env (ssDoctrine spec)
          mBaseDoc <-
            case ssBaseDoctrine spec of
              Nothing -> Right Nothing
              Just baseName ->
                if baseName == ssDoctrine spec
                  then Right (Just doc)
                  else Just <$> lookupDoctrine env baseName
          def <- elabPolySurfaceDecl name doc mBaseDoc spec
          let env' = env { meSurfaces = M.insert name def (meSurfaces env) }
          pure (env', rawTerms, rawRuns)
        DeclPipeline rawPipeline -> do
          ensureAbsent "pipeline" (rplName rawPipeline) (mePipelines env)
          pipeline <- elabPipeline rawPipeline
          let env' = env { mePipelines = M.insert (plName pipeline) pipeline (mePipelines env) }
          pure (env', rawTerms, rawRuns)
        DeclMorphism morphDecl -> do
          let name = rpmName morphDecl
          ensureAbsent "morphism" name (meMorphisms env)
          morph <- elabPolyMorphism env morphDecl
          let env' = env { meMorphisms = M.insert name morph (meMorphisms env) }
          pure (env', rawTerms, rawRuns)
        DeclImplements iface tgt morphName -> do
          (key, name) <- elabImplements env iface tgt morphName
          let defaults = M.findWithDefault [] key (meImplDefaults env)
          let defaults' = if name `elem` defaults then defaults else defaults <> [name]
          let env' = env { meImplDefaults = M.insert key defaults' (meImplDefaults env) }
          pure (env', rawTerms, rawRuns)
        DeclRun rawRun ->
          pure (env, rawTerms, rawRuns <> [rawRun])
        DeclTerm rawTerm ->
          pure (env, rawTerms <> [rawTerm], rawRuns)


ensureAbsent :: Text -> Text -> M.Map Text v -> Either Text ()
ensureAbsent label name mp =
  if M.member name mp
    then Left ("Duplicate " <> label <> " name: " <> name)
    else Right ()


insertDoctrine :: ModuleEnv -> PolyAST.RawPolyDoctrine -> Either Text ModuleEnv
insertDoctrine env raw = do
  let name = rpdName raw
  ensureAbsent "doctrine" name (meDoctrines env)
  doc <- elabPolyDoctrine env raw
  env' <- case rpdExtends raw of
    Nothing -> Right env
    Just base -> do
      mor <- buildPolyFromBase base name env doc
      pure env { meMorphisms = M.insert (PolyMorph.morName mor) mor (meMorphisms env) }
  let env'' = env' { meDoctrines = M.insert name doc (meDoctrines env') }
  pure env''


insertPushout :: ModuleEnv -> Text -> Text -> Text -> Either Text ModuleEnv
insertPushout env name leftMor rightMor = do
  ensureAbsent "doctrine" name (meDoctrines env)
  f <- lookupMorphism env leftMor
  g <- lookupMorphism env rightMor
  insertPushoutWithMorphs env name f g


insertPushoutWithMorphs :: ModuleEnv -> Text -> PolyMorph.Morphism -> PolyMorph.Morphism -> Either Text ModuleEnv
insertPushoutWithMorphs env name f g = do
  ensureAbsent "doctrine" name (meDoctrines env)
  PolyPushoutResult doc inl inr glue <- computePolyPushout name f g
  ensureAbsent "morphism" (PolyMorph.morName inl) (meMorphisms env)
  ensureAbsent "morphism" (PolyMorph.morName inr) (meMorphisms env)
  ensureAbsent "morphism" (PolyMorph.morName glue) (meMorphisms env)
  let env' =
        env
          { meDoctrines = M.insert name doc (meDoctrines env)
          , meMorphisms =
              M.insert (PolyMorph.morName glue) glue
                (M.insert (PolyMorph.morName inl) inl
                  (M.insert (PolyMorph.morName inr) inr (meMorphisms env)))
          }
  pure env'


elabDoctrineInstantiate :: ModuleEnv -> RawDoctrineInstantiate -> Either Text ModuleEnv
elabDoctrineInstantiate env inst = do
  tmpl <- lookupTemplate env (rdiTemplate inst)
  raw <- instantiateTemplate tmpl (rdiName inst) (rdiArgs inst)
  insertDoctrine env raw


lookupTemplate :: ModuleEnv -> Text -> Either Text RawDoctrineTemplate
lookupTemplate env name =
  case M.lookup name (meTemplates env) of
    Nothing -> Left ("Unknown doctrine_template: " <> name)
    Just tmpl -> Right tmpl


elabDoctrineEffects :: ModuleEnv -> Text -> Text -> [Text] -> Either Text ModuleEnv
elabDoctrineEffects env name baseName effects = do
  _ <- lookupDoctrine env baseName
  case effects of
    [] ->
      insertDoctrine env (PolyAST.RawPolyDoctrine name (Just baseName) [])
    [e1] -> do
      baseDoc <- lookupDoctrine env baseName
      _ <- requireEffectFromBase env baseDoc e1
      insertDoctrine env (PolyAST.RawPolyDoctrine name (Just e1) [])
    _ -> do
      baseDoc <- lookupDoctrine env baseName
      morphs <- mapM (requireEffectFromBase env baseDoc) effects
      let stepName1 = stepName 1
      env1 <- insertPushoutWithMorphs env stepName1 (head morphs) (morphs !! 1)
      let rest = drop 2 morphs
      (envFinal, lastStep) <- foldM pushoutStep (env1, stepName1) (zip [2 ..] rest)
      insertDoctrine envFinal (PolyAST.RawPolyDoctrine name (Just lastStep) [])
  where
    stepName k = name <> "__step" <> T.pack (show k)

    requireEffectFromBase env' baseDoc effectName = do
      effDoc <- lookupDoctrine env' effectName
      mor <- lookupMorphism env' (effectName <> ".fromBase")
      if dName (PolyMorph.morSrc mor) /= dName baseDoc
        then Left ("effects: " <> effectName <> ".fromBase has wrong source")
        else
          if dName (PolyMorph.morTgt mor) /= dName effDoc
            then Left ("effects: " <> effectName <> ".fromBase has wrong target")
            else
              if not (modeMapIdentity mor)
                then Left ("effects: " <> effectName <> ".fromBase must be mode-preserving")
                else Right mor

    modeMapIdentity mor =
      let modes = M.keys (mtModes (dModes (PolyMorph.morSrc mor)))
       in all (\m -> M.lookup m (PolyMorph.morModeMap mor) == Just m) modes

    pushoutStep (envAcc, prevStep) (idx, mor) = do
      glue <- lookupMorphism envAcc (prevStep <> ".glue")
      env' <- insertPushoutWithMorphs envAcc (stepName idx) glue mor
      pure (env', stepName idx)


insertDerivedDoctrine :: ModuleEnv -> RawDerivedDoctrine -> Either Text ModuleEnv
insertDerivedDoctrine env raw = do
  ensureAbsent "derived doctrine" (rddName raw) (meDerivedDoctrines env)
  ensureAbsent "doctrine" (rddName raw) (meDoctrines env)
  baseDoc <- lookupDoctrine env (rddBase raw)
  let mode = ModeName (rddMode raw)
  if M.member mode (mtModes (dModes baseDoc))
    then Right ()
    else Left "derived doctrine: unknown mode"
  if mode `S.member` dAcyclicModes baseDoc
    then Right ()
    else Left "derived doctrine: mode is not declared acyclic in base doctrine"
  policy <- elabFoliationPolicy (rddPolicy raw)
  let forgetName = rddName raw <> ".forget"
  ensureAbsent "morphism" forgetName (meMorphisms env)
  derivedDoc <- buildFoliatedDoctrine (rddName raw) baseDoc mode
  let forgetMorph = buildDerivedForgetMorphism forgetName derivedDoc baseDoc mode
  let dd =
        DerivedFoliated
          { ddName = rddName raw
          , ddBase = rddBase raw
          , ddMode = rddMode raw
          , ddDefaultPolicy = policy
          }
  let env' =
        env
          { meDoctrines = M.insert (rddName raw) derivedDoc (meDoctrines env)
          , meMorphisms = M.insert forgetName forgetMorph (meMorphisms env)
          , meDerivedDoctrines = M.insert (rddName raw) dd (meDerivedDoctrines env)
          }
  pure env'


buildFoliatedDoctrine :: Text -> Doctrine -> ModeName -> Either Text Doctrine
buildFoliatedDoctrine name baseDoc mode = do
  disc <- modeDiscipline (dModes baseDoc) mode
  mt0 <- addMode mode emptyModeTheory
  mt <- setModeDiscipline mode disc mt0
  let strSort = AttrSort "Str"
      portTy = ty "PortRef"
      portsTy = ty "PortList"
      stepTy = ty "Step"
      stepsTy = ty "StepList"
      ssaTy = ty "SSA"
      ty tName = TCon (TypeRef mode (TypeName tName)) []
      mkType tName = (TypeName tName, TypeSig [])
      mkGen gName dom cod attrs =
        ( GenName gName
        , GenDecl
            { gdName = GenName gName
            , gdMode = mode
            , gdTyVars = []
            , gdIxVars = []
            , gdDom = map InPort dom
            , gdCod = cod
            , gdAttrs = attrs
            }
        )
      gens =
        M.fromList
          [ mkGen "portRef" [] [portTy] [("name", strSort)]
          , mkGen "portsNil" [] [portsTy] []
          , mkGen "portsCons" [portTy, portsTy] [portsTy] []
          , mkGen "stepGen" [portsTy, portsTy] [stepTy] [("name", strSort)]
          , mkGen "stepBox" [portsTy, portsTy] [stepTy] [("name", strSort)]
          , mkGen "stepFeedback" [portsTy, portsTy] [stepTy] []
          , mkGen "stepsNil" [] [stepsTy] []
          , mkGen "stepsCons" [stepTy, stepsTy] [stepsTy] []
          , mkGen "ssaProgram" [portsTy, portsTy, stepsTy] [ssaTy] []
          ]
  pure
    Doctrine
      { dName = name
      , dModes = mt
      , dAcyclicModes = S.singleton mode
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.singleton strSort (AttrSortDecl strSort (Just LKString))
      , dTypes =
          M.singleton
            mode
            ( M.fromList
                [ mkType "PortRef"
                , mkType "PortList"
                , mkType "Step"
                , mkType "StepList"
                , mkType "SSA"
                ]
            )
      , dGens = M.singleton mode gens
      , dCells2 = []
      }


buildDerivedForgetMorphism :: Text -> Doctrine -> Doctrine -> ModeName -> PolyMorph.Morphism
buildDerivedForgetMorphism name srcDoc tgtDoc mode =
  PolyMorph.Morphism
    { PolyMorph.morName = name
    , PolyMorph.morSrc = srcDoc
    , PolyMorph.morTgt = tgtDoc
    , PolyMorph.morIsCoercion = False
    , PolyMorph.morModeMap = M.singleton mode mode
    , PolyMorph.morModMap = M.empty
    , PolyMorph.morAttrSortMap = M.empty
    , PolyMorph.morTypeMap = M.empty
    , PolyMorph.morGenMap = M.empty
    , PolyMorph.morIxFunMap = M.empty
    , PolyMorph.morPolicy = UseStructuralAsBidirectional
    , PolyMorph.morFuel = 50
    }


elabPipeline :: RawPipeline -> Either Text Pipeline
elabPipeline raw = do
  phases <- mapM elabPhase (rplPhases raw)
  pure Pipeline { plName = rplName raw, plPhases = phases }


elabPhase :: RawPhase -> Either Text Phase
elabPhase raw =
  case raw of
    RPApply name -> Right (ApplyMorph name)
    RPNormalize opts -> do
      policy <- parsePipelinePolicy (rnoPolicy opts)
      let fuel = maybe 50 id (rnoFuel opts)
      Right (Normalize policy fuel)
    RPExtractFoliate targetName mOpts ->
      case mOpts of
        Nothing ->
          Right (ExtractFoliation targetName Nothing)
        Just opts -> do
          foliatePolicy <- elabFoliationPolicy opts
          Right (ExtractFoliation targetName (Just foliatePolicy))
    RPExtractValue doctrineName opts ->
      case doctrineName of
        "Doc" ->
          Right (ExtractValue "Doc" (ExtractDoc (maybe True id (rveStdout opts))))
        "FileTree" ->
          Right (ExtractValue "FileTree" (ExtractFileTree (maybe "./out" id (rveRoot opts))))
        _ ->
          Left ("pipeline: unsupported extractor doctrine " <> doctrineName)
    RPExtractDiagramPretty -> Right ExtractDiagramPretty


parsePipelinePolicy :: Maybe Text -> Either Text RewritePolicy
parsePipelinePolicy mName =
  case maybe "UseStructuralAsBidirectional" id mName of
    "topmost" -> Right UseStructuralAsBidirectional
    "computational_lr" -> Right UseOnlyComputationalLR
    "all_oriented" -> Right UseAllOriented
    other -> parsePolicy other


elabFoliationPolicy :: RawFoliationOpts -> Either Text FoliationPolicy
elabFoliationPolicy raw = do
  orderKey <-
    case rfoPolicy raw of
      Nothing -> Right StableEdgeId
      Just "stable_edge_id" -> Right StableEdgeId
      Just _ -> Left "foliation: unsupported policy"
  naming <-
    case rfoNaming raw of
      Nothing -> Right BoundaryLabelsFirst
      Just "boundary_labels_first" -> Right BoundaryLabelsFirst
      Just _ -> Left "foliation: unsupported naming policy"
  pure
    FoliationPolicy
      { fpOrderKey = orderKey
      , fpNaming = naming
      , fpReserved = S.fromList (rfoReserved raw)
      }


lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc


lookupMorphism :: ModuleEnv -> Text -> Either Text PolyMorph.Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just mor -> Right mor


elabImplements :: ModuleEnv -> Text -> Text -> Text -> Either Text ((Text, Text), Text)
elabImplements env ifaceName tgtName morphName = do
  ifaceDoc <- lookupDoctrine env ifaceName
  tgtDoc <- lookupDoctrine env tgtName
  morph <- lookupMorphism env morphName
  if PolyMorph.morSrc morph /= ifaceDoc
    then Left "Morphism source does not match implements interface"
    else
      if PolyMorph.morTgt morph /= tgtDoc
        then Left "Morphism target does not match implements target"
        else Right ((ifaceName, tgtName), morphName)


elabRuns :: ModuleEnv -> [RawNamedRun] -> Either Text (M.Map Text Run)
elabRuns env raws = foldM step M.empty raws
  where
    step acc raw = do
      let name = rnrName raw
      if M.member name acc
        then Left ("Duplicate run name: " <> name)
        else do
          runDef <- elabRun env raw
          pure (M.insert name runDef acc)


elabRun :: ModuleEnv -> RawNamedRun -> Either Text Run
elabRun env raw = do
  let rr = rnrRun raw
  pipelineName <- maybe (Left "run: missing pipeline") Right (rrPipeline rr)
  doctrineName <- maybe (Left "run: missing source doctrine") Right (rrDoctrine rr)
  _ <- lookupDoctrine env doctrineName
  _ <-
    case M.lookup pipelineName (mePipelines env) of
      Nothing -> Left ("Unknown pipeline: " <> pipelineName)
      Just _ -> Right ()
  case rrSurface rr of
    Nothing -> Right ()
    Just surfaceName ->
      case M.lookup surfaceName (meSurfaces env) of
        Nothing -> Left ("Unknown surface: " <> surfaceName)
        Just _surfaceDef -> Right ()
  exprText <- maybe (Left "run: missing expression") Right (rrExprText rr)
  pure
    Run
      { runName = rnrName raw
      , runUses = rrUses rr
      , runPipeline = pipelineName
      , runDoctrine = doctrineName
      , runMode = rrMode rr
      , runSurface = rrSurface rr
      , runExprText = exprText
      }


elabTerms :: ModuleEnv -> [RawNamedTerm] -> Either Text ModuleEnv
elabTerms env raws = foldM step env raws
  where
    step acc raw = do
      let name = rntName raw
      if M.member name (meTerms acc)
        then Left ("Duplicate term name: " <> name)
        else do
          term <- elabTerm acc (rntTerm raw)
          let terms' = M.insert name term (meTerms acc)
          pure acc { meTerms = terms' }


elabTerm :: ModuleEnv -> RawTerm -> Either Text TermDef
elabTerm env raw = do
  doctrine <- maybe (Left "term: missing doctrine") Right (rtDoctrine raw)
  let fuel = maybe 50 id (rtFuel raw)
  let policyName = maybe "UseStructuralAsBidirectional" id (rtPolicy raw)
  policy <- parsePolicy policyName
  (docFinal, _inputDiag, normDiag) <-
    case
        compileDiagramArtifact
          env
          doctrine
          (rtMode raw)
          (rtSurface raw)
          (rtUses raw)
          (rtMorphisms raw)
          policy
          fuel
          (rtExprText raw) of
      Left err -> Left ("term: " <> err)
      Right ok -> Right ok
  pure
    TermDef
      { tdDoctrine = dName docFinal
      , tdMode = dMode normDiag
      , tdDiagram = normDiag
      }


buildPolyFromBase :: Text -> Text -> ModuleEnv -> Doctrine -> Either Text PolyMorph.Morphism
buildPolyFromBase baseName newName env newDoc = do
  baseDoc <- lookupDoctrine env baseName
  ensureAbsent "morphism" morName (meMorphisms env)
  genMap <- fmap M.fromList (mapM genImage (allGens baseDoc))
  let mor =
        PolyMorph.Morphism
          { PolyMorph.morName = morName
          , PolyMorph.morSrc = baseDoc
          , PolyMorph.morTgt = newDoc
          , PolyMorph.morIsCoercion = True
          , PolyMorph.morModeMap = identityModeMap baseDoc
          , PolyMorph.morModMap = identityModMap baseDoc
          , PolyMorph.morAttrSortMap = identityAttrSortMap baseDoc
          , PolyMorph.morTypeMap = M.empty
          , PolyMorph.morGenMap = genMap
          , PolyMorph.morIxFunMap = M.empty
          , PolyMorph.morPolicy = UseStructuralAsBidirectional
          , PolyMorph.morFuel = 50
          }
  case PolyMorph.checkMorphism mor of
    Left err -> Left ("generated morphism " <> morName <> " invalid: " <> err)
    Right () -> Right mor
  where
    morName = newName <> ".fromBase"

    allGens doc =
      [ (mode, gen)
      | (mode, table) <- M.toList (dGens doc)
      , gen <- M.elems table
      ]

    genImage (mode, gen) = do
      let attrs = M.fromList [(fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- gdAttrs gen]
      img0 <- genDWithAttrs mode (gdPlainDom gen) (gdCod gen) (gdName gen) attrs
      let binderSlots = [bs | InBinder bs <- gdDom gen]
      let holes = [BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1]]
      let bargs = map BAMeta holes
      let binderSigs = M.fromList (zip holes binderSlots)
      img <- setSingleGenBargs (gdName gen) attrs bargs img0
      pure ((mode, gdName gen), PolyMorph.GenImage img binderSigs)

    setSingleGenBargs genName attrs bargs img =
      case IM.toList (dEdges img) of
        [(edgeKey, edge)] ->
          let edge' = edge {ePayload = PGen genName attrs bargs}
           in Right img {dEdges = IM.insert edgeKey edge' (dEdges img)}
        _ -> Left "generated morphism image is not a single generator edge"

    identityModeMap doc =
      M.fromList [(m, m) | m <- M.keys (mtModes (dModes doc))]

    identityModMap doc =
      M.fromList
        [ (name, ModExpr {meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name]})
        | (name, decl) <- M.toList (mtDecls (dModes doc))
        ]

    identityAttrSortMap doc =
      M.fromList [(s, s) | s <- M.keys (dAttrSorts doc)]
