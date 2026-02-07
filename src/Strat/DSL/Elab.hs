{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.AST
import Strat.Frontend.Env
import Strat.Model.Spec (ModelSpec(..), DefaultBehavior(..), OpClause(..))
import Strat.DSL.Template (instantiateTemplate)
import Strat.Poly.DSL.Elab (elabPolyDoctrine, elabPolyMorphism, elabPolyRun, parsePolicy)
import Strat.Poly.DSL.AST (rpdExtends, rpdName)
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.Diagram (Diagram(..), genDWithAttrs)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import Strat.Poly.ModeTheory (ModeTheory(..))
import Strat.Poly.Attr
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Poly.Pushout (PolyPushoutResult(..), computePolyPushout, computePolyCoproduct)
import Strat.Poly.Surface (elabPolySurfaceDecl)
import Strat.Poly.Surface.Spec (ssDoctrine)
import Strat.RunSpec (RunSpec)
import Strat.Frontend.Compile (compileDiagramArtifact)


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
          let env' = env
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
        DeclSurface name spec -> do
          ensureAbsent "surface" name (meSurfaces env)
          doc <- lookupDoctrine env (ssDoctrine spec)
          def <- elabPolySurfaceDecl name doc spec
          let env' = env { meSurfaces = M.insert name def (meSurfaces env) }
          pure (env', rawTerms, rawRuns)
        DeclModel name doc items -> do
          ensureAbsent "model" name (meModels env)
          spec <- elabModelSpec name items
          _ <- lookupDoctrine env doc
          let env' = env { meModels = M.insert name (doc, spec) (meModels env) }
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
        DeclRunSpec name rawSpec -> do
          ensureAbsent "run_spec" name (meRunSpecs env)
          let env' = env { meRunSpecs = M.insert name rawSpec (meRunSpecs env) }
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
  let env' = env
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
      (envFinal, lastStep) <- foldM pushoutStep (env1, stepName1) (zip [2..] rest)
      insertDoctrine envFinal (PolyAST.RawPolyDoctrine name (Just lastStep) [])
  where
    stepName k = name <> "__step" <> T.pack (show k)
    requireEffectFromBase env' baseDoc effectName = do
      effDoc <- lookupDoctrine env' effectName
      mor <- lookupMorphism env' (effectName <> ".fromBase")
      if dName (PolyMorph.morSrc mor) /= dName baseDoc
        then Left ("effects: " <> effectName <> ".fromBase has wrong source")
        else if dName (PolyMorph.morTgt mor) /= dName effDoc
          then Left ("effects: " <> effectName <> ".fromBase has wrong target")
          else if not (modeMapIdentity mor)
            then Left ("effects: " <> effectName <> ".fromBase must be mode-preserving")
            else Right mor
    modeMapIdentity mor =
      let modes = S.toList (mtModes (dModes (PolyMorph.morSrc mor)))
      in all (\m -> M.lookup m (PolyMorph.morModeMap mor) == Just m) modes
    pushoutStep (envAcc, prevStep) (idx, mor) = do
      glue <- lookupMorphism envAcc (prevStep <> ".glue")
      env' <- insertPushoutWithMorphs envAcc (stepName idx) glue mor
      pure (env', stepName idx)

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
    else if PolyMorph.morTgt morph /= tgtDoc
      then Left "Morphism target does not match implements target"
      else Right ((ifaceName, tgtName), morphName)

elabRuns :: ModuleEnv -> [RawNamedRun] -> Either Text (M.Map Text RunSpec)
elabRuns env raws = foldM step M.empty raws
  where
    step acc raw = do
      let name = rnrName raw
      if M.member name acc
        then Left ("Duplicate run name: " <> name)
        else do
          base <- case rnrUsing raw of
            Nothing -> Right Nothing
            Just specName -> Just <$> resolveRunSpec env specName
          let merged = mergeRawRun base (rnrRun raw)
          spec <- elabPolyRun name merged
          pure (M.insert name spec acc)

resolveRunSpec :: ModuleEnv -> Text -> Either Text RawRun
resolveRunSpec env root = go S.empty [root] root
  where
    go seen trail current = do
      rawSpec <-
        case M.lookup current (meRunSpecs env) of
          Nothing -> Left ("Unknown run_spec: " <> current)
          Just spec -> Right spec
      base <- case rrsUsing rawSpec of
        Nothing -> Right Nothing
        Just parent ->
          if parent `S.member` seen || parent `elem` trail
            then
              Left
                ( "run_spec inheritance cycle: "
                    <> T.intercalate " -> " (trail <> [parent])
                )
            else Just <$> go (S.insert current seen) (trail <> [parent]) parent
      pure (mergeRawRun base (rrsRun rawSpec))

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
    case compileDiagramArtifact
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
  pure TermDef
    { tdDoctrine = dName docFinal
    , tdMode = dMode normDiag
    , tdDiagram = normDiag
    }

mergeRawRun :: Maybe RawRun -> RawRun -> RawRun
mergeRawRun base override =
  case base of
    Nothing -> override
    Just b ->
      RawRun
        { rrDoctrine = pick rrDoctrine
        , rrMode = pick rrMode
        , rrSurface = pick rrSurface
        , rrModel = pick rrModel
        , rrMorphisms = rrMorphisms b <> rrMorphisms override
        , rrUses = rrUses b <> rrUses override
        , rrPolicy = pick rrPolicy
        , rrFuel = pick rrFuel
        , rrShowFlags = rrShowFlags b <> rrShowFlags override
        , rrExprText = pick rrExprText
        }
      where
        pick f = case f override of
          Just v -> Just v
          Nothing -> f b

elabModelSpec :: Text -> [RawModelItem] -> Either Text ModelSpec
elabModelSpec name items = do
  let defaults = [ d | RMDefault d <- items ]
  def <-
    case defaults of
      [] -> Right DefaultSymbolic
      [RawDefaultSymbolic] -> Right DefaultSymbolic
      [RawDefaultError msg] -> Right (DefaultError msg)
      _ -> Left "Multiple default clauses in model"
  let clauses = [ c | RMOp c <- items ]
  let opNames = map rmcOp clauses
  case findDup opNames of
    Just dup -> Left ("Duplicate op clause in model: " <> dup)
    Nothing -> pure ()
  let ops = map (\c -> OpClause (rmcOp c) (rmcArgs c) (rmcExpr c)) clauses
  pure ModelSpec
    { msName = name
    , msClauses = ops
    , msDefault = def
    }
  where
    findDup xs = go M.empty xs
    go _ [] = Nothing
    go seen (x:rest)
      | M.member x seen = Just x
      | otherwise = go (M.insert x () seen) rest

buildPolyFromBase :: Text -> Text -> ModuleEnv -> Doctrine -> Either Text PolyMorph.Morphism
buildPolyFromBase baseName newName env newDoc = do
  baseDoc <- lookupDoctrine env baseName
  ensureAbsent "morphism" morName (meMorphisms env)
  genMap <- fmap M.fromList (mapM genImage (allGens baseDoc))
  let mor = PolyMorph.Morphism
        { PolyMorph.morName = morName
        , PolyMorph.morSrc = baseDoc
        , PolyMorph.morTgt = newDoc
        , PolyMorph.morIsCoercion = True
        , PolyMorph.morModeMap = identityModeMap baseDoc
        , PolyMorph.morAttrSortMap = identityAttrSortMap baseDoc
        , PolyMorph.morTypeMap = M.empty
        , PolyMorph.morGenMap = genMap
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
      let attrs = M.fromList [ (fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- gdAttrs gen ]
      img <- genDWithAttrs mode (gdDom gen) (gdCod gen) (gdName gen) attrs
      pure ((mode, gdName gen), img)
    identityModeMap doc =
      M.fromList [ (m, m) | m <- S.toList (mtModes (dModes doc)) ]
    identityAttrSortMap doc =
      M.fromList [ (s, s) | s <- M.keys (dAttrSorts doc) ]
