{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.DSL.Elab
  ( ModuleDataReprElaborator
  , ModuleDataReprRegistry
  , ModuleSurfacePlugin(..)
  , ModuleSurfacePluginRegistry
  , standardModuleDataReprRegistry
  , standardModuleSurfacePluginRegistry
  , elabRawFile
  , elabRawFileWithModuleDataReprs
  , elabRawFileWithModuleSurfacePlugins
  , elabRawFileWithEnv
  , elabRawFileWithEnvAndModuleDataReprs
  , elabRawFileWithEnvAndModuleSurfacePlugins
  , elabRawFileWithEnvAndBudget
  , elabRawFileWithEnvAndBudgetAndModuleDataReprs
  , elabRawFileWithEnvAndBudgetAndRegistries
  , lookupInterface
  , ensureModuleMatchesInterface
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Set as S
import Data.Map.Strict (Map)
import Strat.Common.ModuleRef (ModuleValueRef(..), appendModuleValueRefAdapter)
import Strat.Common.OpaqueType
  ( opaqueInterfaceTypeName
  , opaqueModuleDataDescriptorPrefix
  , opaqueModuleDataProviderDescriptorWithPrefix
  , opaqueModuleDataProviderInterface
  , opaqueModuleDataTypeName
  )
import Strat.Common.Provider (ModuleProvider(..), ProviderRef(..), appendProviderAdapter)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.AST
import Strat.DSL.Parse (parseInterfaceItemsText, parseModuleItemsText)
import Strat.Frontend.Env
  ( ModuleEnv(..)
  , DoctrineFunctorDef(..)
  , FunctorParamDef(..)
  , ProofStats(..)
  , emptyEnv
  , ScopedType(..)
  , ScopedValue(..)
  )
import Strat.Frontend.Model
  ( LanguageDef(..)
  , CustomExpansionDef(..)
  , ModuleElaboratorDef(..)
  , ModuleDataReprDef(..)
  , ModuleSurfaceCapability(..)
  , ModuleSurfaceDef(..)
  , InterfaceItemDef(..)
  , InterfaceTypeSig(..)
  , InterfaceValueSig(..)
  , InterfaceDef(..)
  , ModuleImport(..)
  , ModuleItemDef(..)
  , ModuleDataDef(..)
  , ModuleTypeDef(..)
  , ModuleValueDef(..)
  , ModuleDef(..)
  , BuildDef(..)
  )
import qualified Strat.Frontend.Model as FM
import Strat.Frontend.Compile (CompiledDiagramArtifact(..), compileDiagramArtifact)
import Strat.Pipeline
import Strat.Poly.DSL.AST (rpdExtends, rpdName)
import qualified Strat.Poly.DSL.AST as PolyAST
import Strat.Poly.DSL.Elab
  ( elabPolyDoctrineWithBudgetResult
  , elabPolyDoctrineFromBaseWithBudgetResult
  , elabPolyMorphismWithBudgetResult
  , parsePolicy
  , checkImplementsObligationsWithBudget
  , ImplementsCheckResult(..)
  )
import Strat.Poly.Obj
  ( Obj(..)
  , CodeArg(..)
  , CodeTerm(..)
  , mkCon
  , pattern OVar
  , pattern OCon
  , pattern OAObj
  , pattern OATm
  , ObjRef(..)
  , ObjName(..)
  , TmVar
  , tmvName
  , tmVarOwner
  , tmvSort
  , TmVar(..)
  , TermDiagram(..)
  )
import Strat.Poly.Diagram
  ( Diagram(..)
  , genDWithArgs
  , diagramDom
  , diagramCod
  , mapModuleValueRefsDiagram
  , mapProviderRefsDiagram
  )
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , BuiltinDecl(..)
  , BinderSig(..)
  , GenDecl(..)
  , GenParam(..)
  , InputShape(..)
  , ObligationDecl(..)
  , CtorTables
  , deriveCtorTables
  , doctrineTypeTheory
  , doctrineTypeTheoryFromTables
  , allCtorSigsInTables
  , genericGenDiagram
  , gdPlainDom
  , isTypeDeclGenNameInTables
  , lookupCtorSigByRefInTables
  , lookupCtorRefForOwnerInTables
  , lookupCtorSigForOwnerInTables
  , lookupGenDeclInDoctrine
  , validateDoctrine
  )
import Strat.Poly.DiagramBuild (allocPorts)
import Strat.Poly.Graph (BinderArg(..), BinderMetaVar(..), Edge(..), EdgePayload(..), emptyDiagram, addEdgePayload, validateDiagram)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Literal (LiteralKind(..))
import Strat.Poly.ModeTheory
  ( ModeTheory(..)
  , ModeInfo(..)
  , ModDecl(..)
  , ModEqn(..)
  , ClassificationDecl(..)
  , CompDecl(..)
  , ModName(..)
  , ModExpr(..)
  , ModTransformName(..)
  , ModTransformDecl(..)
  , ModeName(..)
  , emptyModeTheory
  , addMode
  )
import Strat.Poly.Names (GenName(..))
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Poly.Pushout
  ( PolyPushoutResult(..)
  , computePolyPushout
  , computePolyPushoutPreferRight
  , computePolyCoproduct
  , mkInclusionMorphism
  , renameDoctrine
  )
import Strat.Poly.Surface (PolySurfaceDef(..), elabPolySurfaceDecl)
import Strat.Poly.Surface.Spec (ssDoctrine, ssBaseDoctrine)
import Strat.Poly.Proof (SearchBudget, defaultSearchBudget, renderSearchLimit)
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.DefEq (normalizeObjDeep, termExprToDiagramChecked)
import Strat.Poly.ObjClassifier (modeUniverseObj, modeClassifierMode)
import Strat.Poly.DSL.Elab.Term
  ( elabObjExpr
  , elabObjExprInScope
  , elabObjExprInferOwnerInScope
  , mkTypeMetaVar
  )
import qualified Strat.Poly.Subst as US
import qualified Strat.Poly.Term.SubstRuntime as SR
import Strat.Util.List (dedupe)


elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile =
  elabRawFileWithEnvAndBudgetAndRegistries
    defaultSearchBudget
    standardModuleDataReprRegistry
    standardModuleSurfacePluginRegistry
    emptyEnv


elabRawFileWithModuleDataReprs :: ModuleDataReprRegistry -> RawFile -> Either Text ModuleEnv
elabRawFileWithModuleDataReprs registry =
  elabRawFileWithEnvAndBudgetAndRegistries defaultSearchBudget registry standardModuleSurfacePluginRegistry emptyEnv


elabRawFileWithModuleSurfacePlugins :: ModuleSurfacePluginRegistry -> RawFile -> Either Text ModuleEnv
elabRawFileWithModuleSurfacePlugins registry =
  elabRawFileWithEnvAndBudgetAndRegistries defaultSearchBudget standardModuleDataReprRegistry registry emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv =
  elabRawFileWithEnvAndBudgetAndRegistries
    defaultSearchBudget
    standardModuleDataReprRegistry
    standardModuleSurfacePluginRegistry


elabRawFileWithEnvAndModuleDataReprs :: ModuleDataReprRegistry -> ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnvAndModuleDataReprs =
  \registry ->
    elabRawFileWithEnvAndBudgetAndRegistries
      defaultSearchBudget
      registry
      standardModuleSurfacePluginRegistry


elabRawFileWithEnvAndModuleSurfacePlugins :: ModuleSurfacePluginRegistry -> ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnvAndModuleSurfacePlugins =
  elabRawFileWithEnvAndBudgetAndRegistries
    defaultSearchBudget
    standardModuleDataReprRegistry

elabRawFileWithEnvAndBudget :: SearchBudget -> ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnvAndBudget budget =
  elabRawFileWithEnvAndBudgetAndRegistries
    budget
    standardModuleDataReprRegistry
    standardModuleSurfacePluginRegistry


elabRawFileWithEnvAndBudgetAndModuleDataReprs
  :: SearchBudget
  -> ModuleDataReprRegistry
  -> ModuleEnv
  -> RawFile
  -> Either Text ModuleEnv
elabRawFileWithEnvAndBudgetAndModuleDataReprs budget moduleDataReprs =
  elabRawFileWithEnvAndBudgetAndRegistries budget moduleDataReprs standardModuleSurfacePluginRegistry


elabRawFileWithEnvAndBudgetAndRegistries
  :: SearchBudget
  -> ModuleDataReprRegistry
  -> ModuleSurfacePluginRegistry
  -> ModuleEnv
  -> RawFile
  -> Either Text ModuleEnv
elabRawFileWithEnvAndBudgetAndRegistries budget moduleDataReprs moduleSurfacePlugins baseEnv (RawFile decls) =
  foldM step baseEnv decls
  where
    step env decl =
      case decl of
        DeclImport _ -> Right env
        DeclDoctrine raw -> do
          env' <- insertDoctrine budget env raw
          pure env'
        DeclDoctrinePushout name leftMor rightMor -> do
          env' <- insertPushout env name leftMor rightMor
          pure env'
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
          pure env'
        DeclDoctrineFunctor functorDecl -> do
          env' <- elabDoctrineFunctor budget env functorDecl
          pure env'
        DeclDoctrineApply applyDecl -> do
          env' <- elabDoctrineApply budget env applyDecl
          pure env'
        DeclDoctrineEffects name base effects -> do
          env' <- elabDoctrineEffects budget env name base effects
          pure env'
        DeclFragment rawFragment -> do
          env' <- insertFragmentDecl env rawFragment
          pure env'
        DeclDerivedDoctrine rawDerived -> do
          env' <- insertDerivedDoctrine env rawDerived
          pure env'
        DeclModuleElaborator rawElaborator -> do
          env' <- insertModuleElaborator moduleSurfacePlugins env rawElaborator
          pure env'
        DeclModuleDataRepr rawDataRepr -> do
          env' <- insertModuleDataRepr moduleDataReprs env rawDataRepr
          pure env'
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
          pure env'
        DeclModuleSurface rawModuleSurface -> do
          env' <- insertModuleSurface moduleDataReprs moduleSurfacePlugins env rawModuleSurface
          pure env'
        DeclLanguage rawLang -> do
          env' <- insertLanguage env rawLang
          pure env'
        DeclInterface rawInterface -> do
          env' <- insertInterface moduleDataReprs moduleSurfacePlugins env rawInterface
          pure env'
        DeclModule rawModule -> do
          env' <- insertModule moduleDataReprs moduleSurfacePlugins env rawModule
          pure env'
        DeclBuild rawBuild -> do
          env' <- insertBuild env rawBuild
          pure env'
        DeclPipeline rawPipeline -> do
          ensureAbsent "pipeline" (rplName rawPipeline) (mePipelines env)
          pipeline <- elabPipeline rawPipeline
          let env' = env { mePipelines = M.insert (plName pipeline) pipeline (mePipelines env) }
          pure env'
        DeclMorphism morphDecl -> do
          let name = rpmName morphDecl
          ensureAbsent "morphism" name (meMorphisms env)
          (morph, morphCheck) <- elabPolyMorphismWithBudgetResult budget env morphDecl
          let proofCount =
                case morphCheck of
                  PolyMorph.MorphismCheckProved proofs -> length proofs
                  PolyMorph.MorphismCheckUndecided _ _ -> 0
          let env' =
                addMorphismProofCount proofCount
                  (env { meMorphisms = M.insert name morph (meMorphisms env) })
          pure env'
        DeclImplements iface tgt morphName -> do
          ((key, name), proofCount) <- elabImplements budget env iface tgt morphName
          let defaults = M.findWithDefault [] key (meImplDefaults env)
          let defaults' = if name `elem` defaults then defaults else defaults <> [name]
          let env' =
                addImplementsProofCount proofCount
                  (env { meImplDefaults = M.insert key defaults' (meImplDefaults env) })
          pure env'


ensureAbsent :: Text -> Text -> M.Map Text v -> Either Text ()
ensureAbsent label name mp =
  if M.member name mp
    then Left ("Duplicate " <> label <> " name: " <> name)
    else Right ()

addMorphismProofCount :: Int -> ModuleEnv -> ModuleEnv
addMorphismProofCount n env =
  env
    { meProofStats =
        (meProofStats env)
          { psMorphismProofs = psMorphismProofs (meProofStats env) + max 0 n
          }
    }

addActionProofCount :: Int -> ModuleEnv -> ModuleEnv
addActionProofCount n env =
  env
    { meProofStats =
        (meProofStats env)
          { psActionProofs = psActionProofs (meProofStats env) + max 0 n
          }
    }

addImplementsProofCount :: Int -> ModuleEnv -> ModuleEnv
addImplementsProofCount n env =
  env
    { meProofStats =
        (meProofStats env)
          { psImplementsProofs = psImplementsProofs (meProofStats env) + max 0 n
          }
    }


insertDoctrine :: SearchBudget -> ModuleEnv -> PolyAST.RawPolyDoctrine -> Either Text ModuleEnv
insertDoctrine budget env raw = do
  let name = rpdName raw
  ensureAbsent "doctrine" name (meDoctrines env)
  (doc, actionProofs) <- elabPolyDoctrineWithBudgetResult budget env raw
  env' <- case rpdExtends raw of
    Nothing -> Right env
    Just base -> do
      (mor, morphProofs) <- buildPolyFromBase budget base name env doc
      pure
        ( addMorphismProofCount morphProofs
            (env { meMorphisms = M.insert (PolyMorph.morName mor) mor (meMorphisms env) })
        )
  let env'' =
        addActionProofCount actionProofs
          (env' { meDoctrines = M.insert name doc (meDoctrines env') })
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


elabDoctrineFunctor :: SearchBudget -> ModuleEnv -> RawDoctrineFunctor -> Either Text ModuleEnv
elabDoctrineFunctor budget env raw = do
  ensureAbsent "doctrine_functor" (rdfName raw) (meFunctors env)
  ensureDistinctFunctorParams (rdfParams raw)
  paramsWithSchemas <- mapM lookupParamSchema (rdfParams raw)
  renamedSchemas <- mapM namespaceParamSchema paramsWithSchemas
  ifaceDoc <- mergeIfaceDoctrines (rdfName raw <> ".__iface") renamedSchemas
  let rawBody =
        (rdfBody raw)
          { PolyAST.rpdName = rdfName raw <> ".__body"
          , PolyAST.rpdExtends = Nothing
          }
  (bodyDoc, actionProofs) <- elabPolyDoctrineFromBaseWithBudgetResult budget env ifaceDoc rawBody
  incl <- mkInclusionMorphism (rdfName raw <> ".incl") ifaceDoc bodyDoc
  let def =
        DoctrineFunctorDef
          { dfName = rdfName raw
          , dfParams = [ FunctorParamDef p s | (p, s, _) <- paramsWithSchemas ]
          , dfIface = ifaceDoc
          , dfBody = bodyDoc
          , dfIncl = incl
          }
  pure
    ( addActionProofCount actionProofs
        (env { meFunctors = M.insert (rdfName raw) def (meFunctors env) })
    )
  where
    lookupParamSchema param = do
      schemaDoc <- lookupDoctrine env (rfpSchema param)
      pure (rfpName param, rfpSchema param, schemaDoc)
    namespaceParamSchema (paramName, schemaName, schemaDoc) = do
      doc <- namespaceDoctrineWithParam paramName schemaDoc
      pure (FunctorParamDef paramName schemaName, doc)


elabDoctrineApply :: SearchBudget -> ModuleEnv -> RawDoctrineApply -> Either Text ModuleEnv
elabDoctrineApply budget env raw = do
  ensureAbsent "doctrine" (rdaName raw) (meDoctrines env)
  functorDef <- lookupFunctor env (rdaFunctor raw)
  targetDoc <- lookupDoctrine env (rdaTarget raw)
  implMorphs <- resolveApplyMorphisms env functorDef targetDoc (rdaUsing raw)
  let ifaceDoc = dfIface functorDef
  implIface <- buildIfaceImplMorphism raw functorDef targetDoc implMorphs
  case PolyMorph.checkMorphismWithBudget budget implIface of
    Left err -> Left ("apply: interface morphism check failed: " <> err)
    Right () -> Right ()
  implResult <- checkImplementsObligationsWithBudget budget env targetDoc implIface ifaceDoc
  proofCount <- case implResult of
    ImplementsCheckProved proofs -> Right (length proofs)
    ImplementsCheckUndecided label lim ->
      Left ("apply: interface obligation undecided: " <> label <> " (" <> renderSearchLimit lim <> ")")
  PolyPushoutResult doc inl inr _glueIface <-
    computePolyPushoutPreferRight (rdaName raw) (dfName functorDef) (dfIncl functorDef) implIface
  let glueMorphs =
        [ toGlueMorph (rdaName raw) paramName doc mor
        | (paramName, mor) <- implMorphs
        ]
  ensureAbsent "morphism" (PolyMorph.morName inl) (meMorphisms env)
  ensureAbsent "morphism" (PolyMorph.morName inr) (meMorphisms env)
  mapM_ (\m -> ensureAbsent "morphism" (PolyMorph.morName m) (meMorphisms env)) glueMorphs
  let morphisms' =
        foldr
          (\m acc -> M.insert (PolyMorph.morName m) m acc)
          (M.insert (PolyMorph.morName inr) inr (M.insert (PolyMorph.morName inl) inl (meMorphisms env)))
          glueMorphs
  pure
    ( addImplementsProofCount proofCount
        env
          { meDoctrines = M.insert (rdaName raw) doc (meDoctrines env)
          , meMorphisms = morphisms'
          }
    )


lookupFunctor :: ModuleEnv -> Text -> Either Text DoctrineFunctorDef
lookupFunctor env name =
  case M.lookup name (meFunctors env) of
    Nothing -> Left ("Unknown doctrine_functor: " <> name)
    Just def -> Right def

allTypeDeclsForDoc :: Doctrine -> Either Text [(ObjRef, CtorSig)]
allTypeDeclsForDoc doc =
  case deriveCtorTables doc of
    Left err -> Left ("allTypeDeclsForDoc: " <> err)
    Right tables ->
      allCtorSigsInTables doc tables

lookupCtorSigByRef :: Doctrine -> ObjRef -> Either Text CtorSig
lookupCtorSigByRef doc ref = do
  tables <- deriveCtorTables doc
  case lookupCtorSigByRefInTables doc tables ref of
    Left _ -> Left "apply: type constructor missing"
    Right sig -> Right sig

resolveApplyMorphisms
  :: ModuleEnv
  -> DoctrineFunctorDef
  -> Doctrine
  -> Map Text Text
  -> Either Text [(Text, PolyMorph.Morphism)]
resolveApplyMorphisms env functorDef targetDoc usingMap = do
  requireExactParamMap (dfParams functorDef) usingMap
  mapM resolveOne (dfParams functorDef)
  where
    resolveOne p = do
      morphName <-
        case M.lookup (fpdName p) usingMap of
          Nothing ->
            Left ("apply: missing mapping for parameter " <> fpdName p)
          Just n -> Right n
      mor <- lookupMorphism env morphName
      if dName (PolyMorph.morSrc mor) /= fpdSchemaName p
        then
          Left
            ( "apply: morphism "
                <> morphName
                <> " has source "
                <> dName (PolyMorph.morSrc mor)
                <> " but expected "
                <> fpdSchemaName p
                <> " for parameter "
                <> fpdName p
            )
        else
          if dName (PolyMorph.morTgt mor) /= dName targetDoc
            then
              Left
                ( "apply: morphism "
                    <> morphName
                    <> " has target "
                    <> dName (PolyMorph.morTgt mor)
                    <> " but expected "
                    <> dName targetDoc
                )
            else Right (fpdName p, mor)

requireExactParamMap :: [FunctorParamDef] -> Map Text Text -> Either Text ()
requireExactParamMap params usingMap = do
  let expected = S.fromList (map fpdName params)
  let actual = S.fromList (M.keys usingMap)
  let missing = S.toList (S.difference expected actual)
  let extra = S.toList (S.difference actual expected)
  case (missing, extra) of
    ([], []) -> Right ()
    _ ->
      Left
        ( "apply: `using` mapping keys must exactly match functor parameters; missing: "
            <> renderList missing
            <> "; extra: "
            <> renderList extra
        )
  where
    renderList [] = "(none)"
    renderList xs = T.intercalate ", " xs

buildIfaceImplMorphism
  :: RawDoctrineApply
  -> DoctrineFunctorDef
  -> Doctrine
  -> [(Text, PolyMorph.Morphism)]
  -> Either Text PolyMorph.Morphism
buildIfaceImplMorphism raw functorDef targetDoc implMorphs = do
  mapM_ (uncurry validateApplyCoverage) implMorphs
  modeMap <- mergeDisjoint "mode" [liftModeMap p (PolyMorph.morModeMap mor) | (p, mor) <- implMorphs]
  modMap <- mergeDisjoint "modality" [liftModMap p (PolyMorph.morModMap mor) | (p, mor) <- implMorphs]
  typeMaps <- mapM (uncurry liftCompletedTypeMap) implMorphs
  typeMap <- mergeDisjoint "type" typeMaps
  genMaps <- mapM (uncurry liftCompletedGenMap) implMorphs
  genMap <- mergeDisjoint "generator" genMaps
  pure
    PolyMorph.Morphism
      { PolyMorph.morName = rdaName raw <> ".__impl_iface"
      , PolyMorph.morSrc = dfIface functorDef
      , PolyMorph.morTgt = targetDoc
      , PolyMorph.morIsCoercion = False
      , PolyMorph.morModeMap = modeMap
      , PolyMorph.morModMap = modMap
      , PolyMorph.morTypeMap = typeMap
      , PolyMorph.morGenMap = genMap
      , PolyMorph.morCheck = PolyMorph.CheckAll
      , PolyMorph.morPolicy = UseAllOriented
      }
  where
    prefixText p txt = p <> "::" <> txt
    prefixMode p (ModeName n) = ModeName (prefixText p n)
    prefixMod p (ModName n) = ModName (prefixText p n)
    prefixTypeRef p ref =
      ref
        { orMode = prefixMode p (orMode ref)
        , orName = ObjName (prefixText p (renderTypeName (orName ref)))
        }
    renderTypeName (ObjName t) = t
    prefixGen p (mode, gen) = (prefixMode p mode, GenName (prefixText p (renderGenName gen)))
    renderGenName (GenName g) = g

    liftModeMap p mp =
      M.fromList
        [ (prefixMode p srcMode, tgtMode)
        | (srcMode, tgtMode) <- M.toList mp
        ]
    liftModMap p mp =
      M.fromList
        [ (prefixMod p srcMod, tgtExpr)
        | (srcMod, tgtExpr) <- M.toList mp
        ]
    liftTypeMap p mp =
      M.fromList
        [ (prefixTypeRef p srcRef, tmpl)
        | (srcRef, tmpl) <- M.toList mp
        ]
    liftCompletedTypeMap p mor = do
      completed <- completeTypeMap mor
      pure (liftTypeMap p completed)
    liftCompletedGenMap p mor = do
      completed <- completeGenMap mor
      pure (liftGenMap p completed)
    liftGenMap p mp =
      M.fromList
        [ (prefixGen p srcKey, img)
        | (srcKey, img) <- M.toList mp
        ]

    completeTypeMap mor = do
      tgtCtorTables <- deriveCtorTables (PolyMorph.morTgt mor)
      tt <- doctrineTypeTheoryFromTables (PolyMorph.morTgt mor) tgtCtorTables
      srcCtorTables <- deriveCtorTables (PolyMorph.morSrc mor)
      ctors <- allCtorSigsInTables (PolyMorph.morSrc mor) srcCtorTables
      let explicit = PolyMorph.morTypeMap mor
      let addType mp (srcRef, sig) =
            case M.lookup srcRef explicit of
              Just tmpl -> Right (M.insert srcRef tmpl mp)
              Nothing -> do
                tmpl <- identityTemplate tt tgtCtorTables mor srcRef sig
                Right (M.insert srcRef tmpl mp)
      foldM addType M.empty ctors

    completeGenMap mor =
      foldM addCompFallback explicit compSupportKeys
      where
        srcDoc = PolyMorph.morSrc mor
        explicit = PolyMorph.morGenMap mor
        compSupportKeys =
          [ (mode, genName)
          | (mode, classDecl) <- M.toList (mtClassifiedBy (dModes srcDoc))
          , Just comp <- [cdComp classDecl]
          , genName <- [compCtxExt comp, compVar comp, compReindex comp]
          , hasSourceGen mode genName
          ]
        hasSourceGen mode genName =
          case M.lookup mode (dGens srcDoc) of
            Nothing -> False
            Just table -> M.member genName table
        addCompFallback mp srcKey@(srcMode, srcGenName) =
          case M.lookup srcKey mp of
            Just _ -> Right mp
            Nothing -> do
              tgtMode <- PolyMorph.applyMorphismMode mor srcMode
              tgtGen <-
                case M.lookup tgtMode (dGens (PolyMorph.morTgt mor)) >>= M.lookup srcGenName of
                  Nothing ->
                    Left
                      ( "apply: morphism "
                          <> PolyMorph.morName mor
                          <> " missing generator mapping for comprehension support "
                          <> renderMode srcMode
                          <> "."
                          <> renderGen srcGenName
                      )
                  Just gd -> Right gd
              img <- canonicalGenImage tgtGen
              Right (M.insert srcKey img mp)

        canonicalGenImage gd = do
          diag <- genericGenDiagram gd
          let binderSlots = [bs | InBinder bs <- gdDom gd]
          let holes = [BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1]]
          pure (PolyMorph.GenImage diag (M.fromList (zip holes binderSlots)))

    identityTemplate tt tgtCtorTables mor srcRef sig = do
      tgtMode <- PolyMorph.applyMorphismMode mor (orMode srcRef)
      let tgtRef = srcRef { orMode = tgtMode }
      params <- mapM (mkParam tgtCtorTables mor) (zip [0 :: Int ..] (csParams sig))
      args <- mapM (paramArg tt) (zip (csParams sig) params)
      pure (PolyMorph.TypeTemplate params (mkCon tgtRef args))

    mkParam tgtCtorTables mor (i, param) =
      case param of
        GP_Ty srcVar -> do
          let srcMode = tmVarOwner srcVar
          tgtMode <- PolyMorph.applyMorphismMode mor srcMode
          case modeUniverseObj (dModes (PolyMorph.morTgt mor)) tgtMode of
            Just universe -> do
              let tv =
                    TmVar
                      { tmvName = "a" <> T.pack (show i)
                      , tmvSort = universe
                      , tmvScope = 0
                      , tmvOwnerMode = Just tgtMode
                      }
              Right (GP_Ty tv)
            Nothing ->
              Left
                ( "apply: type metavariable `a"
                    <> T.pack (show i)
                    <> "@"
                    <> renderMode tgtMode
                    <> "` requires `mode "
                    <> renderMode tgtMode
                    <> " classifiedBy ... via ...;` with a declared universe"
                )
        GP_Tm srcVar -> do
          let srcSort = tmvSort srcVar
          tgtSort <- PolyMorph.applyMorphismTyWithTables tgtCtorTables mor srcSort
          Right (GP_Tm TmVar { tmvName = "t" <> T.pack (show i), tmvSort = tgtSort, tmvScope = 0, tmvOwnerMode = Nothing })
      where
        renderMode (ModeName n) = n

    paramArg tt (srcParam, param) =
      case (srcParam, param) of
        (GP_Ty _, GP_Ty v) ->
          Right (OAObj Obj { objOwnerMode = tmVarOwner v, objCode = CTMeta v })
        (GP_Tm _, GP_Ty _) ->
          Left "apply: internal kind mismatch for type template argument"
        (_, GP_Tm v) -> do
          tm <- termExprToDiagramChecked tt [] (tmvSort v) (TMMeta v [])
          Right (OATm tm)

    validateApplyCoverage paramName mor = do
      let srcDoc = PolyMorph.morSrc mor
      let tgtDoc = PolyMorph.morTgt mor
      srcCtorTables <- deriveCtorTables srcDoc
      srcTypes <- allCtorSigsInTables srcDoc srcCtorTables
      let typeIssues =
            [ (srcRef, issue)
            | (srcRef, srcSig) <- srcTypes
            , Just issue <- [typeMappingIssue srcRef srcSig tgtDoc mor]
            ]
      let missingTypes = [ srcRef | (srcRef, isMissing) <- typeIssues, isMissing ]
      let incompatibleTypes = [ srcRef | (srcRef, isMissing) <- typeIssues, not isMissing ]
      let allBadTypes = missingTypes <> incompatibleTypes
      let missingGens = [ srcKey | srcKey <- allGenKeys srcDoc srcCtorTables, M.notMember srcKey (PolyMorph.morGenMap mor) ]
      if null allBadTypes && null missingGens
        then Right ()
        else
          Left
            ( "apply: parameter "
                <> paramName
                <> " via morphism "
                <> PolyMorph.morName mor
                <> " is missing/incompatible required mappings: "
                <> renderMissing "type" (map renderTypeRef allBadTypes)
                <> "; "
                <> renderMissing "type_incompatible" (map renderTypeRef incompatibleTypes)
                <> "; "
                <> renderMissing "gen" (map renderGenKey missingGens)
            )

    typeMappingIssue srcRef srcSig tgtDoc mor =
      case M.lookup srcRef (PolyMorph.morTypeMap mor) of
        Just _ -> Nothing
        Nothing ->
          case PolyMorph.applyMorphismMode mor (orMode srcRef) of
            Left _ -> Just True
            Right tgtMode ->
              let tgtRef = srcRef { orMode = tgtMode }
              in case lookupCtorSigByRef tgtDoc tgtRef of
                  Left _ -> Just True
                  Right tgtSig ->
                    if length (csParams srcSig) == length (csParams tgtSig)
                      then Nothing
                      else Just False

    allGenKeys doc ctorTables =
      [ (mode, gdName genDecl)
      | (mode, table) <- M.toList (dGens doc)
      , genDecl <- M.elems table
      , not (isComprehensionSupport doc mode (gdName genDecl))
      , not (isTypeDeclGenNameInTables doc ctorTables mode (genToObjName (gdName genDecl)))
      ]
    isComprehensionSupport doc mode genName =
      case M.lookup mode (mtClassifiedBy (dModes doc)) >>= cdComp of
        Nothing -> False
        Just comp ->
          genName == compCtxExt comp
            || genName == compVar comp
            || genName == compReindex comp

    renderMissing label vals =
      label <> "=" <> renderList vals

    renderList [] = "(none)"
    renderList vals = "[" <> T.intercalate ", " vals <> "]"

    renderModeName (ModeName n) = n
    renderMode (ModeName n) = n
    genToObjName (GenName n) = ObjName n
    renderGen (GenName n) = n
    renderTypeRef ref = renderModeName (orMode ref) <> "." <> renderTypeName (orName ref)
    renderGenKey (mode, GenName genName) = renderModeName mode <> "." <> genName

toGlueMorph :: Text -> Text -> Doctrine -> PolyMorph.Morphism -> PolyMorph.Morphism
toGlueMorph resultName paramName pres mor =
  mor
    { PolyMorph.morName = resultName <> ".glue_" <> paramName
    , PolyMorph.morTgt = pres
    , PolyMorph.morIsCoercion = True
    , PolyMorph.morPolicy = UseStructuralAsBidirectional
    }

mergeDisjoint :: (Ord k) => Text -> [Map k v] -> Either Text (Map k v)
mergeDisjoint label = foldM step M.empty
  where
    step acc mp =
      case [() | k <- M.keys mp, M.member k acc] of
        [] -> Right (M.union acc mp)
        (_:_) -> Left ("apply: duplicate lifted " <> label <> " mapping key")

ensureDistinctFunctorParams :: [RawFunctorParam] -> Either Text ()
ensureDistinctFunctorParams params =
  go S.empty params
  where
    go _ [] = Right ()
    go seen (p:rest)
      | rfpName p `S.member` seen = Left ("doctrine_functor: duplicate parameter name " <> rfpName p)
      | otherwise = go (S.insert (rfpName p) seen) rest

namespaceDoctrineWithParam :: Text -> Doctrine -> Either Text Doctrine
namespaceDoctrineWithParam paramName doc = do
  ctorDecls <- allTypeDeclsForDoc doc
  let prefix t = paramName <> "::" <> t
      renameModeName (ModeName t) = ModeName (prefix t)
      renameModName (ModName t) = ModName (prefix t)
      renameObjName (ObjName t) = ObjName (prefix t)
      renameGenName (GenName t) = GenName (prefix t)
      renameTransformName (ModTransformName t) = ModTransformName (prefix t)
      modeRenMap =
        M.fromList [ (m, renameModeName m) | m <- M.keys (mtModes (dModes doc)) ]
      modRenMap =
        M.fromList [ (m, renameModName m) | m <- M.keys (mtDecls (dModes doc)) ]
      typeRenMap =
        M.fromList
          [ ( ObjRef mode ctor
            , ObjRef (M.findWithDefault mode mode modeRenMap) (renameObjName ctor)
            )
          | (ObjRef mode ctor, _) <- ctorDecls
          ]
      genRenMap =
        M.fromList
          [ ((mode, gdName genDecl), renameGenName (gdName genDecl))
          | (mode, table) <- M.toList (dGens doc)
          , genDecl <- M.elems table
          ]
      cellRenMap =
        M.fromList
          [ ((dMode (c2LHS c), c2Name c), prefix (c2Name c))
          | c <- dCells2 doc
          ]
      oblRenMap =
        M.fromList
          [ (obName o, prefix (obName o))
          | o <- dObligations doc
          ]
      transformRenMap =
        M.fromList
          [ (tr, renameTransformName tr)
          | tr <- M.keys (mtTransforms (dModes doc))
          ]
  doc' <-
    renameDoctrine
      modeRenMap
      modRenMap
      typeRenMap
      M.empty
      genRenMap
      cellRenMap
      oblRenMap
      transformRenMap
      doc
  pure $ doc' { dName = prefix (dName doc) }

mergeIfaceDoctrines :: Text -> [(FunctorParamDef, Doctrine)] -> Either Text Doctrine
mergeIfaceDoctrines name params =
  case map snd params of
    [] -> Left "doctrine_functor: at least one parameter is required"
    (firstDoc:rest) -> do
      merged <- foldM mergeIface firstDoc rest
      let out = merged { dName = name }
      validateDoctrine out
      pure out

mergeIface :: Doctrine -> Doctrine -> Either Text Doctrine
mergeIface left right = do
  modes <- unionByEq "mode" (mtModes (dModes left)) (mtModes (dModes right))
  decls <- unionByEq "modality" (mtDecls (dModes left)) (mtDecls (dModes right))
  transforms <- unionByEq "mod_transform" (mtTransforms (dModes left)) (mtTransforms (dModes right))
  classified <- unionByEq "classifiedBy" (mtClassifiedBy (dModes left)) (mtClassifiedBy (dModes right))
  classifierLifts <- unionByEq "classifier_lift" (mtClassifierLifts (dModes left)) (mtClassifierLifts (dModes right))
  gens <- mergeModeTables "generator" (dGens left) (dGens right)
  cells <- mergeCellsWithAlphaRename (dCells2 left) (dCells2 right)
  builtins <- unionByEq "builtin" builtinTableLeft builtinTableRight
  actions <- unionByEq "action" (dActions left) (dActions right)
  obligations <- mergeObligationsWithRename (dObligations left) (dObligations right)
  pure
    left
      { dModes =
          (dModes left)
            { mtModes = modes
            , mtDecls = decls
            , mtEqns = mtEqns (dModes left) <> mtEqns (dModes right)
            , mtTransforms = transforms
            , mtClassifiedBy = classified
            , mtClassifierLifts = classifierLifts
            }
      , dAcyclicModes = S.union (dAcyclicModes left) (dAcyclicModes right)
      , dGens = gens
      , dCells2 = cells
      , dBuiltins = M.elems builtins
      , dActions = actions
      , dObligations = obligations
      }
  where
    builtinTableLeft = M.fromList [((bdMode decl, bdHead decl), decl) | decl <- dBuiltins left]
    builtinTableRight = M.fromList [((bdMode decl, bdHead decl), decl) | decl <- dBuiltins right]

unionByEq :: (Ord k, Eq v) => Text -> Map k v -> Map k v -> Either Text (Map k v)
unionByEq label left right =
  foldM step left (M.toList right)
  where
    step mp (k, v) =
      case M.lookup k mp of
        Nothing -> Right (M.insert k v mp)
        Just existing
          | existing == v -> Right mp
          | otherwise -> Left ("doctrine_functor interface merge: conflicting " <> label)

mergeModeTables :: (Ord a, Eq b) => Text -> Map ModeName (Map a b) -> Map ModeName (Map a b) -> Either Text (Map ModeName (Map a b))
mergeModeTables label left right =
  foldM step left (M.toList right)
  where
    step mp (mode, table) =
      case M.lookup mode mp of
        Nothing -> Right (M.insert mode table mp)
        Just table0 -> do
          merged <- unionByEq label table0 table
          Right (M.insert mode merged mp)

mergeCellsWithAlphaRename :: [Cell2] -> [Cell2] -> Either Text [Cell2]
mergeCellsWithAlphaRename left right = do
  (out, _) <- foldM step (left, used0) right
  Right out
  where
    used0 =
      foldl addUsed M.empty left

    addUsed mp cell =
      let mode = dMode (c2LHS cell)
          used = M.findWithDefault S.empty mode mp
      in M.insert mode (S.insert (c2Name cell) used) mp

    step (acc, usedByMode) cell =
      let mode = dMode (c2LHS cell)
          name = c2Name cell
          used = M.findWithDefault S.empty mode usedByMode
      in if name `S.member` used
        then
          case [ c | c <- acc, dMode (c2LHS c) == mode, c2Name c == name, c == cell ] of
            (_:_) -> Right (acc, usedByMode)
            [] ->
              let (fresh, used') = freshTextName name used
                  cell' = cell { c2Name = fresh }
                  usedByMode' = M.insert mode used' usedByMode
              in Right (acc <> [cell'], usedByMode')
        else
          let usedByMode' = M.insert mode (S.insert name used) usedByMode
          in Right (acc <> [cell], usedByMode')

mergeObligationsWithRename :: [ObligationDecl] -> [ObligationDecl] -> Either Text [ObligationDecl]
mergeObligationsWithRename left right = do
  (out, _) <- foldM step (left, S.fromList (map obName left)) right
  Right out
  where
    step (acc, used) obl =
      let name = obName obl
      in if name `S.member` used
        then
          case [ o | o <- acc, obName o == name, o == obl ] of
            (_:_) -> Right (acc, used)
            [] ->
              let (fresh, used') = freshTextName name used
                  obl' = obl { obName = fresh }
              in Right (acc <> [obl'], used')
        else
          Right (acc <> [obl], S.insert name used)

freshTextName :: Text -> S.Set Text -> (Text, S.Set Text)
freshTextName base used =
  if base `S.member` used
    then go (1 :: Int)
    else (base, S.insert base used)
  where
    go n =
      let candidate = base <> "_" <> T.pack (show n)
      in if candidate `S.member` used
        then go (n + 1)
        else (candidate, S.insert candidate used)

elabDoctrineEffects :: SearchBudget -> ModuleEnv -> Text -> Text -> [Text] -> Either Text ModuleEnv
elabDoctrineEffects budget env name baseName effects = do
  _ <- lookupDoctrine env baseName
  case effects of
    [] ->
      insertDoctrine budget env (PolyAST.RawPolyDoctrine name (Just baseName) [])
    [e1] -> do
      baseDoc <- lookupDoctrine env baseName
      _ <- requireEffectFromBase env baseDoc e1
      insertDoctrine budget env (PolyAST.RawPolyDoctrine name (Just e1) [])
    _ -> do
      baseDoc <- lookupDoctrine env baseName
      morphs <- mapM (requireEffectFromBase env baseDoc) effects
      let stepName1 = stepName 1
      env1 <- insertPushoutWithMorphs env stepName1 (head morphs) (morphs !! 1)
      let rest = drop 2 morphs
      (envFinal, lastStep) <- foldM pushoutStep (env1, stepName1) (zip [2 ..] rest)
      insertDoctrine budget envFinal (PolyAST.RawPolyDoctrine name (Just lastStep) [])
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
  case modeUniverseObj (dModes baseDoc) mode of
    Nothing -> Left "derived doctrine: reflected quotation requires a classified mode"
    Just _ -> Right ()
  derivedDoc <- deriveReflectedQuotationDoctrine env (rddName raw) baseDoc mode
  let dd =
        DerivedReflectQuotation
          { ddName = rddName raw
          , ddBase = rddBase raw
          , ddMode = rddMode raw
          }
  let env' =
        env
          { meDoctrines = M.insert (rddName raw) derivedDoc (meDoctrines env)
          , meDerivedDoctrines = M.insert (rddName raw) dd (meDerivedDoctrines env)
          }
  pure env'


insertFragmentDecl :: ModuleEnv -> RawFragmentDecl -> Either Text ModuleEnv
insertFragmentDecl env raw = do
  ensureAbsent "fragment" (rfdName raw) (meFragments env)
  baseDoc <- lookupDoctrine env (rfdBase raw)
  let mode = ModeName (rfdMode raw)
  if M.member mode (mtModes (dModes baseDoc))
    then Right ()
    else Left "fragment: unknown mode"
  let insertIncluded acc name = do
        let genName = GenName name
        if genName `S.member` acc
          then Left ("fragment: duplicate include for " <> name)
          else do
            _ <-
              lookupGenDeclInDoctrine
                ("fragment: unknown generator " <> name)
                baseDoc
                mode
                genName
            pure (S.insert genName acc)
  included <- foldM insertIncluded S.empty [ name | RFIncludeGen name <- rfdItems raw ]
  crossBinders <- singletonFlag False "fragment: duplicate cross binders setting" [ b | RFCrossBinders b <- rfdItems raw ]
  crossBoxes <- singletonFlag False "fragment: duplicate cross boxes setting" [ b | RFCrossBoxes b <- rfdItems raw ]
  crossFeedback <- singletonFlag False "fragment: duplicate cross feedback setting" [ b | RFCrossFeedback b <- rfdItems raw ]
  let fragment =
        FragmentDecl
          { frName = rfdName raw
          , frBase = rfdBase raw
          , frMode = rfdMode raw
          , frIncludedGens = included
          , frCrossBinders = crossBinders
          , frCrossBoxes = crossBoxes
          , frCrossFeedback = crossFeedback
          }
  pure env { meFragments = M.insert (rfdName raw) fragment (meFragments env) }

singletonFlag :: a -> Text -> [a] -> Either Text a
singletonFlag def _ [] = Right def
singletonFlag _ _ [x] = Right x
singletonFlag _ err (_:_:_) = Left err

deriveReflectedQuotationDoctrine :: ModuleEnv -> Text -> Doctrine -> ModeName -> Either Text Doctrine
deriveReflectedQuotationDoctrine env targetName baseDoc mode = do
  universeTy <-
    case modeUniverseObj (dModes baseDoc) mode of
      Nothing -> Left "derived doctrine: reflected quotation requires a classified mode"
      Just u -> Right u
  ctorTables <- deriveCtorTables baseDoc
  (doc0, _) <-
    elabPolyDoctrineFromBaseWithBudgetResult
      defaultSearchBudget
      env
      (baseDoc { dName = targetName })
      (rawReflectedSupportDoctrine targetName mode)
  doc1 <- insertGeneratedGen doc0 mode (mkTypeCtorDecl mode universeTy "Seq" Nothing)
  doc2 <- insertGeneratedGen doc1 mode (mkTypeCtorDecl mode universeTy "Prog" Nothing)
  let seqTy = mkCon (ObjRef mode (ObjName "Seq")) []
      progTy = mkCon (ObjRef mode (ObjName "Prog")) []
      refIdTy = mkCon (ObjRef mode (ObjName "RefId")) []
      refIdsTy = mkCon (ObjRef mode (ObjName "RefIds")) []
      tmParam name sortTy =
        GP_Tm
          TmVar
            { tmvName = name
            , tmvSort = sortTy
            , tmvScope = 0
            , tmvOwnerMode = Just mode
            }
      simpleGen name params dom cod =
        GenDecl
          { gdName = GenName name
          , gdMode = mode
          , gdParams = params
          , gdDom = map InPort dom
          , gdCod = cod
          , gdLiteralKind = Nothing
          }
      structuredGen name =
        simpleGen
          name
          [ tmParam "inputs" refIdsTy
          , tmParam "outputs" refIdsTy
          ]
          [seqTy, progTy]
          [seqTy]
  doc3 <- insertGeneratedGen doc2 mode (simpleGen "q_begin" [tmParam "inputs" refIdsTy] [] [seqTy])
  doc4 <- insertGeneratedGen doc3 mode (simpleGen "q_end" [tmParam "outputs" refIdsTy] [seqTy] [progTy])
  doc5 <- insertGeneratedGen doc4 mode (structuredGen "q_res_box")
  doc6 <- insertGeneratedGen doc5 mode (structuredGen "q_res_feedback")
  doc7 <-
    case uniqueStringLiteralTy baseDoc mode of
      Nothing -> Right doc6
      Just labelTy ->
        do
          doc6a <- insertGeneratedGen doc6 mode (simpleGen "refId_label" [tmParam "label" labelTy] [] [refIdTy])
          insertGeneratedGen
            doc6a
            mode
            ( simpleGen
                "q_provider"
                [ tmParam "provider" labelTy
                , tmParam "interface" labelTy
                , tmParam "descriptor" labelTy
                , tmParam "value" labelTy
                , tmParam "adapter" labelTy
                , tmParam "inputs" refIdsTy
                , tmParam "outputs" refIdsTy
                ]
                [seqTy]
                [seqTy]
            )
          >>= \doc6b ->
            insertGeneratedGen
              doc6b
              mode
              ( simpleGen
                  "q_module_ref"
                  [ tmParam "module" labelTy
                  , tmParam "value" labelTy
                  , tmParam "adapter" labelTy
                  , tmParam "inputs" refIdsTy
                  , tmParam "outputs" refIdsTy
                  ]
                  [seqTy]
                  [seqTy]
              )
  let sourceGens =
        [ entry
        | entry@(srcGen, _) <- M.toAscList (M.findWithDefault M.empty mode (dGens baseDoc))
        , not (isTypeDeclGenNameInTables baseDoc ctorTables mode (ObjName (renderGenNameText srcGen)))
        ]
  doc8 <- foldM (insertReflectedBindingGen mode seqTy progTy refIdTy) doc7 sourceGens
  validateDoctrine doc8
  pure doc8


rawReflectedSupportDoctrine :: Text -> ModeName -> PolyAST.RawPolyDoctrine
rawReflectedSupportDoctrine targetName mode =
  PolyAST.RawPolyDoctrine
    { PolyAST.rpdName = targetName
    , PolyAST.rpdExtends = Nothing
    , PolyAST.rpdItems =
        [ PolyAST.RPData digitDecl
        , PolyAST.RPData refIdDecl
        , PolyAST.RPData refIdsDecl
        ]
    }
  where
    modeName = modeText mode
    tyRef name = PolyAST.RawTypeRef { PolyAST.rtrMode = Nothing, PolyAST.rtrName = name }
    ty0 name = PolyAST.RPTCon (tyRef name) [] []
    ctor name args =
      PolyAST.RawPolyCtorDecl
        { PolyAST.rpcName = name
        , PolyAST.rpcArgs = args
        }
    digitDecl =
      PolyAST.RawPolyDataDecl
        { PolyAST.rpdTyName = "Digit"
        , PolyAST.rpdTyVars = []
        , PolyAST.rpdTyMode = modeName
        , PolyAST.rpdCtors =
            [ ctor "digit0" []
            , ctor "digit1" []
            , ctor "digit2" []
            , ctor "digit3" []
            , ctor "digit4" []
            , ctor "digit5" []
            , ctor "digit6" []
            , ctor "digit7" []
            , ctor "digit8" []
            , ctor "digit9" []
            ]
        }
    refIdDecl =
      PolyAST.RawPolyDataDecl
        { PolyAST.rpdTyName = "RefId"
        , PolyAST.rpdTyVars = []
        , PolyAST.rpdTyMode = modeName
        , PolyAST.rpdCtors =
            [ ctor "refId_nil" []
            , ctor "refId_cons" [ty0 "Digit", ty0 "RefId"]
            ]
        }
    refIdsDecl =
      PolyAST.RawPolyDataDecl
        { PolyAST.rpdTyName = "RefIds"
        , PolyAST.rpdTyVars = []
        , PolyAST.rpdTyMode = modeName
        , PolyAST.rpdCtors =
            [ ctor "refIds_nil" []
            , ctor "refIds_cons" [ty0 "RefId", ty0 "RefIds"]
            ]
        }
    modeText (ModeName name) = name


uniqueStringLiteralTy :: Doctrine -> ModeName -> Maybe Obj
uniqueStringLiteralTy doc mode =
  case candidates of
    [ty] -> Just ty
    _ -> Nothing
  where
    candidates =
      [ mkCon (ObjRef mode (ObjName (renderGenNameText genName))) []
      | (genName, genDecl) <- M.toAscList (M.findWithDefault M.empty mode (dGens doc))
      , gdLiteralKind genDecl == Just LKString
      , null (gdParams genDecl)
      , null (gdDom genDecl)
      ]


mkTypeCtorDecl :: ModeName -> Obj -> Text -> Maybe LiteralKind -> GenDecl
mkTypeCtorDecl mode universeTy name litKind =
  GenDecl
    { gdName = GenName name
    , gdMode = mode
    , gdParams = []
    , gdDom = []
    , gdCod = [universeTy]
    , gdLiteralKind = litKind
    }


insertReflectedBindingGen :: ModeName -> Obj -> Obj -> Obj -> Doctrine -> (GenName, GenDecl) -> Either Text Doctrine
insertReflectedBindingGen mode seqTy progTy refIdTy doc (srcGen, srcDecl) =
  insertGeneratedGen doc mode reflectedDecl
  where
    binderCount =
      length
        [ ()
        | InBinder _ <- gdDom srcDecl
        ]
    tmParam name sortTy =
      GP_Tm
        TmVar
          { tmvName = name
          , tmvSort = sortTy
          , tmvScope = 0
          , tmvOwnerMode = Just mode
          }
    inParams =
      [ tmParam ("in" <> T.pack (show i)) refIdTy
      | i <- [0 :: Int .. length (gdPlainDom srcDecl) - 1]
      ]
    outParams =
      [ tmParam ("out" <> T.pack (show i)) refIdTy
      | i <- [0 :: Int .. length (gdCod srcDecl) - 1]
      ]
    reflectedDecl =
      GenDecl
        { gdName = GenName ("q_" <> renderGenNameText srcGen)
        , gdMode = mode
        , gdParams = gdParams srcDecl <> inParams <> outParams
        , gdDom = map InPort (seqTy : replicate binderCount progTy)
        , gdCod = [seqTy]
        , gdLiteralKind = Nothing
        }


insertGeneratedGen :: Doctrine -> ModeName -> GenDecl -> Either Text Doctrine
insertGeneratedGen doc mode decl =
  let modeGens = M.findWithDefault M.empty mode (dGens doc)
      genName = gdName decl
   in if M.member genName modeGens
        then Left ("derived doctrine: generated generator collision: " <> renderGenNameText genName)
        else
          Right
            doc
              { dGens = M.insert mode (M.insert genName decl modeGens) (dGens doc) }


insertLanguage :: ModuleEnv -> RawLanguage -> Either Text ModuleEnv
insertLanguage env raw = do
  let name = rlangName raw
  ensureAbsent "language" name (meLanguages env)
  _ <- lookupDoctrine env (rlangDoctrine raw)
  case rlangModuleSurface raw of
    Nothing -> Right ()
    Just moduleSurfaceName ->
      case M.lookup moduleSurfaceName (meModuleSurfaces env) of
        Nothing -> Left ("Unknown module_surface: " <> moduleSurfaceName)
        Just moduleSurface ->
          if msdDoctrine moduleSurface /= rlangDoctrine raw
            then Left ("language " <> name <> ": module_surface doctrine mismatch")
            else Right ()
  let lang =
        LanguageDef
          { ldName = name
          , ldDoctrine = rlangDoctrine raw
          , ldModuleSurface = rlangModuleSurface raw
          }
  pure env { meLanguages = M.insert name lang (meLanguages env) }


standardModuleSurfaceCapabilities :: S.Set ModuleSurfaceCapability
standardModuleSurfaceCapabilities =
  S.fromList
    [ MSCImport
    , MSCForeignImport
    , MSCType
    , MSCData
    , MSCValue
    , MSCExport
    , MSCExportType
    , MSCExportInterface
    ]


toModuleSurfaceCapability :: RawModuleSurfaceCapability -> ModuleSurfaceCapability
toModuleSurfaceCapability raw =
  case raw of
    RMSCImport -> MSCImport
    RMSCForeignImport -> MSCForeignImport
    RMSCType -> MSCType
    RMSCData -> MSCData
    RMSCValue -> MSCValue
    RMSCExport -> MSCExport
    RMSCExportType -> MSCExportType
    RMSCExportInterface -> MSCExportInterface
    RMSCCustom -> MSCCustom


insertModuleElaborator :: ModuleSurfacePluginRegistry -> ModuleEnv -> RawModuleElaborator -> Either Text ModuleEnv
insertModuleElaborator moduleSurfacePlugins env raw = do
  let name = rmeName raw
  ensureAbsent "module_elaborator" name (meModuleElaborators env)
  _ <- resolveModuleSurfacePlugin moduleSurfacePlugins env S.empty (rmeBase raw)
  let def =
        ModuleElaboratorDef
          { medName = name
          , medBase = rmeBase raw
          , medInterfaceCustom = M.map toCustomExpansionDef (rmeInterfaceCustom raw)
          , medModuleCustom = M.map toCustomExpansionDef (rmeModuleCustom raw)
          }
  pure env { meModuleElaborators = M.insert name def (meModuleElaborators env) }


insertModuleDataRepr :: ModuleDataReprRegistry -> ModuleEnv -> RawModuleDataReprDecl -> Either Text ModuleEnv
insertModuleDataRepr moduleDataReprs env raw = do
  let name = rmdrName raw
  ensureAbsent "data_repr" name (meModuleDataReprs env)
  _ <- resolveModuleDataReprChoice moduleDataReprs env (rmdrBase raw)
  case rmdrProviderInterface raw of
    Nothing -> Right ()
    Just ifaceName -> do
      _ <- lookupInterface env ifaceName
      pure ()
  let def =
        ModuleDataReprDef
          { mdrName = name
          , mdrBase = rmdrBase raw
          , mdrProviderInterface = rmdrProviderInterface raw
          , mdrDescriptorPrefix = rmdrDescriptorPrefix raw
          }
      env' = env { meModuleDataReprs = M.insert name def (meModuleDataReprs env) }
  _ <- resolveModuleDataReprChoice moduleDataReprs env' name
  pure env'


toCustomExpansionDef :: RawCustomExpansion -> CustomExpansionDef
toCustomExpansionDef expansion =
  case expansion of
    RCXInlineItems -> CEDInlineItems


moduleSurfaceForLanguage :: ModuleEnv -> LanguageDef -> Either Text ModuleSurfaceDef
moduleSurfaceForLanguage env lang =
  case ldModuleSurface lang of
    Nothing ->
      Right
        ModuleSurfaceDef
          { msdName = ldName lang <> ".__implicit_module_surface"
          , msdDoctrine = ldDoctrine lang
          , msdElaborator = "standard"
          , msdMode = Nothing
          , msdExprSurface = Nothing
          , msdDefaultDataRepr = Nothing
          , msdUses = []
          , msdCapabilities = standardModuleSurfaceCapabilities
          }
    Just surfaceName ->
      case M.lookup surfaceName (meModuleSurfaces env) of
        Nothing -> Left ("Unknown module_surface: " <> surfaceName)
        Just surface -> Right surface


moduleSurfaceAllows :: ModuleSurfaceDef -> ModuleSurfaceCapability -> Bool
moduleSurfaceAllows surface cap =
  cap `S.member` msdCapabilities surface


insertModuleSurface :: ModuleDataReprRegistry -> ModuleSurfacePluginRegistry -> ModuleEnv -> RawModuleSurface -> Either Text ModuleEnv
insertModuleSurface moduleDataReprs moduleSurfacePlugins env raw = do
  let name = rmsName raw
  ensureAbsent "module_surface" name (meModuleSurfaces env)
  _ <- lookupDoctrine env (rmsDoctrine raw)
  case rmsExprSurface raw of
    Nothing -> Right ()
    Just surfaceName ->
      case M.lookup surfaceName (meSurfaces env) of
        Nothing -> Left ("Unknown surface: " <> surfaceName)
        Just surf ->
          if psDoctrine surf == rmsDoctrine raw
            then Right ()
            else Left ("module_surface " <> name <> ": expr_surface doctrine mismatch")
  case rmsElaborator raw of
    Nothing -> Right ()
    Just elaboratorName -> do
      _ <- resolveModuleSurfacePlugin moduleSurfacePlugins env S.empty elaboratorName
      pure ()
  case rmsDefaultDataRepr raw of
    Nothing -> Right ()
    Just reprName -> do
      _ <- resolveModuleDataReprChoice moduleDataReprs env reprName
      pure ()
  let moduleSurface =
        ModuleSurfaceDef
          { msdName = name
          , msdDoctrine = rmsDoctrine raw
          , msdElaborator = maybe "standard" id (rmsElaborator raw)
          , msdMode = rmsMode raw
          , msdExprSurface = rmsExprSurface raw
          , msdDefaultDataRepr = rmsDefaultDataRepr raw
          , msdUses = rmsUses raw
          , msdCapabilities =
              if null (rmsCapabilities raw)
                then standardModuleSurfaceCapabilities
                else S.fromList (map toModuleSurfaceCapability (rmsCapabilities raw))
          }
  pure env { meModuleSurfaces = M.insert name moduleSurface (meModuleSurfaces env) }


insertInterface :: ModuleDataReprRegistry -> ModuleSurfacePluginRegistry -> ModuleEnv -> RawInterface -> Either Text ModuleEnv
insertInterface moduleDataReprs moduleSurfacePlugins env raw = do
  let name = riName raw
  ensureAbsent "interface" name (meInterfaces env)
  (docName, surfaceElab) <- resolveInterfaceTarget moduleDataReprs moduleSurfacePlugins env (riTarget raw)
  state <- foldM (insertInterfaceItem surfaceElab) emptyInterfaceState (riItems raw)
  let iface =
        InterfaceDef
          { idefName = name
          , idefDoctrine = docName
          , idefItems = reverse (ifsRevItems state)
          , idefTypes = ifsTypes state
          , idefValues = ifsValues state
          }
  pure env { meInterfaces = M.insert name iface (meInterfaces env) }


data InterfaceState = InterfaceState
  { ifsRevItems :: [InterfaceItemDef]
  , ifsTypes :: M.Map Text InterfaceTypeSig
  , ifsValues :: M.Map Text InterfaceValueSig
  }


emptyInterfaceState :: InterfaceState
emptyInterfaceState =
  InterfaceState
    { ifsRevItems = []
    , ifsTypes = M.empty
    , ifsValues = M.empty
    }


insertInterfaceItem :: ModuleSurfaceElaborator -> InterfaceState -> RawInterfaceItem -> Either Text InterfaceState
insertInterfaceItem surfaceElab st rawItem =
  case rawItem of
    RIICustom rawCustom -> do
      if mseAllows surfaceElab MSCCustom
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow custom declarations")
      expanded <- mseExpandInterfaceCustom surfaceElab rawCustom
      foldM (insertInterfaceItem surfaceElab) st expanded
    RIIType rawType -> do
      types <-
        mseElabInterfaceType surfaceElab
          Nothing
          (ifsTypes st)
          rawType
      pure
        st
          { ifsRevItems = IIDType (rawInterfaceTypeName rawType) : ifsRevItems st
          , ifsTypes = types
          }
    RIIValue rawValue -> do
      values <-
        mseElabInterfaceValue surfaceElab
          Nothing
          (interfaceTypeReprs (ifsTypes st))
          (ifsValues st)
          rawValue
      pure
        st
          { ifsRevItems = IIDValue (rivName rawValue) : ifsRevItems st
          , ifsValues = values
          }

resolveInterfaceTarget
  :: ModuleDataReprRegistry
  -> ModuleSurfacePluginRegistry
  -> ModuleEnv
  -> Text
  -> Either Text (Text, ModuleSurfaceElaborator)
resolveInterfaceTarget moduleDataReprs moduleSurfacePlugins env target =
  case M.lookup target (meLanguages env) of
    Just lang -> do
      surfaceElab <- resolveModuleSurfaceElaborator moduleDataReprs moduleSurfacePlugins env lang
      Right (ldDoctrine lang, surfaceElab)
    Nothing -> do
      _ <- lookupDoctrine env target
      let lang =
            LanguageDef
              { ldName = target <> ".__implicit_language"
              , ldDoctrine = target
              , ldModuleSurface = Nothing
              }
      surfaceElab <- resolveModuleSurfaceElaborator moduleDataReprs moduleSurfacePlugins env lang
      Right (target, surfaceElab)


insertInterfaceType
  :: Doctrine
  -> Maybe Text
  -> M.Map Text InterfaceTypeSig
  -> RawInterfaceType
  -> Either Text (M.Map Text InterfaceTypeSig)
insertInterfaceType doc mDefaultMode acc raw =
  if M.member name acc
    then Left ("Duplicate interface type name: " <> name)
    else do
      (mode, repr, mBody) <-
        case raw of
          RITOpaque {} -> do
            mode <- resolveInterfaceMode doc mDefaultMode (ritMode raw)
            repr <- mkOpaqueInterfaceType doc mode name
            pure (mode, repr, Nothing)
          RITAlias {} -> do
            body <- elabScopedTypeExpr doc mDefaultMode (ritMode raw) (interfaceTypeReprs acc) (ritBody raw)
            pure (objOwnerMode body, body, Just body)
      let sig =
            InterfaceTypeSig
              { itsName = name
              , itsMode = mode
              , itsRepr = repr
              , itsBody = mBody
              }
      pure (M.insert name sig acc)
  where
    name = rawInterfaceTypeName raw


rawInterfaceTypeName :: RawInterfaceType -> Text
rawInterfaceTypeName raw =
  case raw of
    RITOpaque { ritName = n } -> n
    RITAlias { ritName = n } -> n


insertInterfaceValue
  :: Doctrine
  -> Maybe Text
  -> M.Map Text Obj
  -> M.Map Text InterfaceValueSig
  -> RawInterfaceValue
  -> Either Text (M.Map Text InterfaceValueSig)
insertInterfaceValue doc mDefaultMode typeScope acc raw =
  if M.member (rivName raw) acc
    then Left ("Duplicate interface value name: " <> rivName raw)
    else do
      mode <- resolveInterfaceMode doc mDefaultMode (rivMode raw)
      dom <- mapM (elabObjExprInScope typeScope doc [] [] M.empty mode) (rivDom raw)
      cod <- mapM (elabObjExprInScope typeScope doc [] [] M.empty mode) (rivCod raw)
      let sig =
            InterfaceValueSig
              { ivsName = rivName raw
              , ivsMode = mode
              , ivsDom = dom
              , ivsCod = cod
              }
      pure (M.insert (rivName raw) sig acc)


interfaceTypeReprs :: M.Map Text InterfaceTypeSig -> M.Map Text Obj
interfaceTypeReprs =
  M.map itsRepr


resolveInterfaceMode :: Doctrine -> Maybe Text -> Maybe Text -> Either Text ModeName
resolveInterfaceMode doc mDefaultMode mDeclared =
  case chooseModeText mDeclared mDefaultMode of
    Just name ->
      let mode = ModeName name
       in if M.member mode (mtModes (dModes doc))
            then Right mode
            else Left ("unknown mode " <> name)
    Nothing ->
      case M.keys (mtModes (dModes doc)) of
        [mode] -> Right mode
        [] -> Left "doctrine has no modes"
        _ -> Left "interface item must specify a mode"


chooseModeText :: Maybe Text -> Maybe Text -> Maybe Text
chooseModeText m1 m2 =
  case m1 of
    Just x -> Just x
    Nothing -> m2


mkOpaqueInterfaceType :: Doctrine -> ModeName -> Text -> Either Text Obj
mkOpaqueInterfaceType doc mode name = do
  meta <- mkTypeMetaVar doc mode (opaqueInterfaceTypeName name)
  pure Obj { objOwnerMode = mode, objCode = CTMeta meta }


elabScopedTypeExpr :: Doctrine -> Maybe Text -> Maybe Text -> M.Map Text Obj -> PolyAST.RawPolyObjExpr -> Either Text Obj
elabScopedTypeExpr doc mDefaultMode mDeclared typeScope raw =
  case chooseModeText mDeclared mDefaultMode of
    Just name -> do
      let mode = ModeName name
      if M.member mode (mtModes (dModes doc))
        then elabObjExprInScope typeScope doc [] [] M.empty mode raw
        else Left ("unknown mode " <> name)
    Nothing ->
      elabObjExprInferOwnerInScope typeScope doc [] [] M.empty raw


data ModuleSurfacePlugin = ModuleSurfacePlugin
  { mspName :: Text
  , mspExpandInterfaceCustom
      :: ModuleSurfaceDef
      -> ModuleEnv
      -> Doctrine
      -> RawCustomItem
      -> Either Text [RawInterfaceItem]
  , mspExpandModuleCustom
      :: ModuleSurfaceDef
      -> ModuleEnv
      -> LanguageDef
      -> RawCustomItem
      -> Either Text [RawModuleItem]
  , mspElabInterfaceType
      :: ModuleSurfaceDef
      -> ModuleEnv
      -> Doctrine
      -> Maybe Text
      -> M.Map Text InterfaceTypeSig
      -> RawInterfaceType
      -> Either Text (M.Map Text InterfaceTypeSig)
  , mspElabInterfaceValue
      :: ModuleSurfaceDef
      -> ModuleEnv
      -> Doctrine
      -> Maybe Text
      -> M.Map Text Obj
      -> M.Map Text InterfaceValueSig
      -> RawInterfaceValue
      -> Either Text (M.Map Text InterfaceValueSig)
  , mspElabModuleData
      :: ModuleDataReprRegistry
      -> ModuleSurfaceDef
      -> ModuleEnv
      -> LanguageDef
      -> M.Map Text ScopedType
      -> M.Map Text ScopedValue
      -> M.Map Text ModuleTypeDef
      -> M.Map Text ModuleValueDef
      -> M.Map Text ModuleDataDef
      -> RawModuleData
      -> Either Text ModuleDataDef
  , mspElabModuleType
      :: ModuleSurfaceDef
      -> ModuleEnv
      -> LanguageDef
      -> M.Map Text ScopedType
      -> M.Map Text ModuleTypeDef
      -> RawModuleType
      -> Either Text (M.Map Text ModuleTypeDef)
  , mspElabModuleValue
      :: ModuleSurfaceDef
      -> ModuleEnv
      -> LanguageDef
      -> M.Map Text ScopedValue
      -> M.Map Text ScopedType
      -> M.Map Text ModuleTypeDef
      -> M.Map Text ModuleValueDef
      -> RawModuleValue
      -> Either Text (M.Map Text ModuleValueDef)
  }


type ModuleSurfacePluginRegistry = M.Map Text ModuleSurfacePlugin


standardModuleSurfacePluginRegistry :: ModuleSurfacePluginRegistry
standardModuleSurfacePluginRegistry =
  M.fromList [("standard", standardModuleSurfacePlugin)]


standardModuleSurfacePlugin :: ModuleSurfacePlugin
standardModuleSurfacePlugin =
  ModuleSurfacePlugin
    { mspName = "standard"
    , mspExpandInterfaceCustom =
        \surface _env _doc raw ->
          Left
            ( "module_surface "
                <> msdName surface
                <> ": custom interface item "
                <> rciTag raw
                <> " is not supported by elaborator standard"
            )
    , mspExpandModuleCustom =
        \surface _env _lang raw ->
          Left
            ( "module_surface "
                <> msdName surface
                <> ": custom module item "
                <> rciTag raw
                <> " is not supported by elaborator standard"
            )
    , mspElabInterfaceType =
        \surface _env doc mDefaultMode acc rawType ->
          insertInterfaceType doc (chooseModeText (msdMode surface) mDefaultMode) acc rawType
    , mspElabInterfaceValue =
        \surface _env doc mDefaultMode typeScope acc rawValue ->
          insertInterfaceValue doc (chooseModeText (msdMode surface) mDefaultMode) typeScope acc rawValue
    , mspElabModuleData =
        \moduleDataReprs surface env lang importedTypes importedValues localTypes localValues dataPkgs rawData ->
          elabModuleData
            moduleDataReprs
            surface
            env
            lang
            importedTypes
            importedValues
            localTypes
            localValues
            dataPkgs
            rawData
    , mspElabModuleType =
        \surface env lang importedTypes localTypes rawType ->
          elabModuleType env lang surface importedTypes localTypes rawType
    , mspElabModuleValue =
        \surface env lang importedTerms importedTypes localTypes localValues rawValue ->
          elabModuleValue env lang surface importedTerms importedTypes localTypes localValues rawValue
    }


insertModule :: ModuleDataReprRegistry -> ModuleSurfacePluginRegistry -> ModuleEnv -> RawModule -> Either Text ModuleEnv
insertModule moduleDataReprs moduleSurfacePlugins env raw = do
  let name = rmName raw
  ensureAbsent "module" name (meModules env)
  lang <-
    case M.lookup (rmLanguage raw) (meLanguages env) of
      Nothing -> Left ("Unknown language: " <> rmLanguage raw)
      Just ld -> Right ld
  _ <- lookupDoctrine env (ldDoctrine lang)
  surfaceElab <- resolveModuleSurfaceElaborator moduleDataReprs moduleSurfacePlugins env lang
  if msdDoctrine (mseSurface surfaceElab) == ldDoctrine lang
    then Right ()
    else Left ("language " <> ldName lang <> ": module_surface doctrine mismatch")
  state <- foldM (insertModuleItem env lang surfaceElab) emptyModuleState (rmItems raw)
  let modDef :: ModuleDef
      modDef =
        ModuleDef
          name
          (ldName lang)
          (ldDoctrine lang)
          (reverse (msRevImports state))
          (reverse (msRevItems state))
          (isProviders (msImported state))
          (msDataPackages state)
          (msTypes state)
          (msValues state)
          (msExportTypes state)
          (msExportValueSigs state)
          (msExports state)
          (reverse (msRevExportInterfaces state))
  pure env { meModules = M.insert name modDef (meModules env) }


data ModuleState = ModuleState
  { msRevImports :: [ModuleImport]
  , msRevItems :: [ModuleItemDef]
  , msImported :: ImportedScope
  , msDataPackages :: M.Map Text ModuleDataDef
  , msTypes :: M.Map Text ModuleTypeDef
  , msValues :: M.Map Text ModuleValueDef
  , msExportTypes :: M.Map Text ModuleTypeDef
  , msExportValueSigs :: M.Map Text InterfaceValueSig
  , msExports :: M.Map Text ModuleValueDef
  , msRevExportInterfaces :: [Text]
  }


data ModuleSurfaceElaborator = ModuleSurfaceElaborator
  { mseSurface :: ModuleSurfaceDef
  , mseAllows :: ModuleSurfaceCapability -> Bool
  , mseExpandInterfaceCustom
      :: RawCustomItem
      -> Either Text [RawInterfaceItem]
  , mseExpandModuleCustom
      :: RawCustomItem
      -> Either Text [RawModuleItem]
  , mseElabInterfaceType
      :: Maybe Text
      -> M.Map Text InterfaceTypeSig
      -> RawInterfaceType
      -> Either Text (M.Map Text InterfaceTypeSig)
  , mseElabInterfaceValue
      :: Maybe Text
      -> M.Map Text Obj
      -> M.Map Text InterfaceValueSig
      -> RawInterfaceValue
      -> Either Text (M.Map Text InterfaceValueSig)
  , mseElabData
      :: M.Map Text ScopedType
      -> M.Map Text ScopedValue
      -> M.Map Text ModuleTypeDef
      -> M.Map Text ModuleValueDef
      -> M.Map Text ModuleDataDef
      -> RawModuleData
      -> Either Text ModuleDataDef
  , mseElabType
      :: M.Map Text ScopedType
      -> M.Map Text ModuleTypeDef
      -> RawModuleType
      -> Either Text (M.Map Text ModuleTypeDef)
  , mseElabValue
      :: M.Map Text ScopedValue
      -> M.Map Text ScopedType
      -> M.Map Text ModuleTypeDef
      -> M.Map Text ModuleValueDef
      -> RawModuleValue
      -> Either Text (M.Map Text ModuleValueDef)
  }


emptyModuleState :: ModuleState
emptyModuleState =
  ModuleState
    { msRevImports = []
    , msRevItems = []
    , msImported = emptyImportedScope
    , msDataPackages = M.empty
    , msTypes = M.empty
    , msValues = M.empty
    , msExportTypes = M.empty
    , msExportValueSigs = M.empty
    , msExports = M.empty
    , msRevExportInterfaces = []
    }


resolveModuleSurfaceElaborator
  :: ModuleDataReprRegistry
  -> ModuleSurfacePluginRegistry
  -> ModuleEnv
  -> LanguageDef
  -> Either Text ModuleSurfaceElaborator
resolveModuleSurfaceElaborator moduleDataReprs moduleSurfacePlugins env lang = do
  surface <- moduleSurfaceForLanguage env lang
  doc <- lookupDoctrine env (msdDoctrine surface)
  plugin <- resolveModuleSurfacePlugin moduleSurfacePlugins env S.empty (msdElaborator surface)
  pure
    ModuleSurfaceElaborator
      { mseSurface = surface
      , mseAllows = moduleSurfaceAllows surface
      , mseExpandInterfaceCustom =
          \rawCustom ->
            mspExpandInterfaceCustom plugin surface env doc rawCustom
      , mseExpandModuleCustom =
          \rawCustom ->
            mspExpandModuleCustom plugin surface env lang rawCustom
      , mseElabInterfaceType =
          \mDefaultMode ifaceTypes rawType ->
            mspElabInterfaceType plugin surface env doc mDefaultMode ifaceTypes rawType
      , mseElabInterfaceValue =
          \mDefaultMode typeScope ifaceValues rawValue ->
            mspElabInterfaceValue plugin surface env doc mDefaultMode typeScope ifaceValues rawValue
      , mseElabData =
          \importedTypes importedValues localTypes localValues dataPkgs rawData ->
            mspElabModuleData plugin moduleDataReprs surface env lang importedTypes importedValues localTypes localValues dataPkgs rawData
      , mseElabType =
          \importedTypes localTypes rawType ->
            mspElabModuleType plugin surface env lang importedTypes localTypes rawType
      , mseElabValue =
          \importedTerms importedTypes localTypes localValues rawValue ->
            mspElabModuleValue plugin surface env lang importedTerms importedTypes localTypes localValues rawValue
      }


resolveModuleSurfacePlugin
  :: ModuleSurfacePluginRegistry
  -> ModuleEnv
  -> S.Set Text
  -> Text
  -> Either Text ModuleSurfacePlugin
resolveModuleSurfacePlugin pluginRegistry env visiting name
  | name `S.member` visiting =
      Left ("module_surface elaborator cycle involving " <> name)
  | otherwise =
      case M.lookup name pluginRegistry of
        Just plugin -> Right plugin
        Nothing ->
          case M.lookup name (meModuleElaborators env) of
            Nothing -> Left ("Unknown module_surface elaborator: " <> name)
            Just def -> do
              base <- resolveModuleSurfacePlugin pluginRegistry env (S.insert name visiting) (medBase def)
              pure
                base
                  { mspName = medName def
                  , mspExpandInterfaceCustom = expandInterfaceCustom def base
                  , mspExpandModuleCustom = expandModuleCustom def base
                  }
  where
    expandInterfaceCustom def base surface env' doc rawCustom =
      case M.lookup (rciTag rawCustom) (medInterfaceCustom def) of
        Just expansion -> expandInterfaceBody def expansion rawCustom
        Nothing -> mspExpandInterfaceCustom base surface env' doc rawCustom

    expandModuleCustom def base surface env' lang rawCustom =
      case M.lookup (rciTag rawCustom) (medModuleCustom def) of
        Just expansion -> expandModuleBody def expansion rawCustom
        Nothing -> mspExpandModuleCustom base surface env' lang rawCustom

    expandInterfaceBody def expansion rawCustom =
      case expansion of
        CEDInlineItems ->
          firstPrefix
            ("module_elaborator " <> medName def <> ": ")
            (parseInterfaceItemsText (rciBody rawCustom))

    expandModuleBody def expansion rawCustom =
      case expansion of
        CEDInlineItems ->
          firstPrefix
            ("module_elaborator " <> medName def <> ": ")
            (parseModuleItemsText (rciBody rawCustom))


insertModuleItem :: ModuleEnv -> LanguageDef -> ModuleSurfaceElaborator -> ModuleState -> RawModuleItem -> Either Text ModuleState
insertModuleItem env lang surfaceElab st rawItem =
  case rawItem of
    RMCustom rawCustom -> do
      if mseAllows surfaceElab MSCCustom
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow custom declarations")
      expanded <- mseExpandModuleCustom surfaceElab rawCustom
      foldM (insertModuleItem env lang surfaceElab) st expanded
    RMImport rawImport -> do
      case rawImport of
        RawModuleImport{}
          | not (mseAllows surfaceElab MSCImport) ->
              Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow local imports")
        RawForeignImport{}
          | not (mseAllows surfaceElab MSCForeignImport) ->
              Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow foreign imports")
        _ -> Right ()
      imported <- importModuleItem env (ldDoctrine lang) (msImported st) rawImport
      let modImport = rawModuleImportToDef rawImport
      pure
        st
          { msRevImports = modImport : msRevImports st
          , msRevItems = MIDImport modImport : msRevItems st
          , msImported = imported
          }
    RMData rawData -> do
      if mseAllows surfaceElab MSCData
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow data declarations")
      dataPkg <-
        mseElabData surfaceElab
          (moduleTypesAsScope (isTypes (msImported st)))
          (moduleValuesAsScope (isValues (msImported st)))
          (msTypes st)
          (msValues st)
          (msDataPackages st)
          rawData
      pure
        st
          { msRevItems = MIDData (mddName dataPkg) (mddCtorNames dataPkg) : msRevItems st
          , msDataPackages = M.insert (mddName dataPkg) dataPkg (msDataPackages st)
          , msTypes = M.insert (rmdName rawData) (mddTypeDef dataPkg) (msTypes st)
          , msValues = M.union (mddCtorDefs dataPkg) (msValues st)
          }
    RMType rawType -> do
      if mseAllows surfaceElab MSCType
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow type declarations")
      types <-
        mseElabType surfaceElab
          (moduleTypesAsScope (isTypes (msImported st)))
          (msTypes st)
          rawType
      pure
        st
          { msRevItems = MIDType (rmtName rawType) : msRevItems st
          , msTypes = types
          }
    RMValue rawValue -> do
      if mseAllows surfaceElab MSCValue
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow value declarations")
      values <-
        mseElabValue surfaceElab
          (moduleValuesAsScope (isValues (msImported st)))
          (moduleTypesAsScope (isTypes (msImported st)))
          (msTypes st)
          (msValues st)
          rawValue
      pure
        st
          { msRevItems = MIDValue (rmvName rawValue) : msRevItems st
          , msValues = values
          }
    RMTypeExport rawExports -> do
      if mseAllows surfaceElab MSCExportType
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow type exports")
      exportTypes <- extendModuleTypeExports (moduleTypeScope st) (msExportTypes st) rawExports
      pure
        st
          { msRevItems =
              foldr (\rawExport acc -> MIDExportType (rmteLocal rawExport) (rmtePublic rawExport) : acc) (msRevItems st) rawExports
          , msExportTypes = exportTypes
          }
    RMExport rawExports -> do
      if mseAllows surfaceElab MSCExport
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow exports")
      exports <- extendModuleExports (moduleValueScope st) (msExports st) rawExports
      exportValueSigs <- extendModuleExportValueSigs (moduleValueScope st) (msExportValueSigs st) rawExports
      pure
        st
          { msRevItems =
              foldr (\rawExport acc -> MIDExport (rmeLocal rawExport) (rmePublic rawExport) : acc) (msRevItems st) rawExports
          , msExportValueSigs = exportValueSigs
          , msExports = exports
          }
    RMExportInterface ifaceName -> do
      if mseAllows surfaceElab MSCExportInterface
        then Right ()
        else Left ("module_surface " <> msdName (mseSurface surfaceElab) <> " does not allow interface exports")
      ensureModuleMatchesInterface env (ldDoctrine lang) (msExportTypes st) (msExports st) ifaceName
      pure
        st
          { msRevItems = MIDExportInterface ifaceName : msRevItems st
          , msRevExportInterfaces = ifaceName : msRevExportInterfaces st
          }


moduleTypeScope :: ModuleState -> M.Map Text ModuleTypeDef
moduleTypeScope st =
  M.union (msTypes st) (isTypes (msImported st))


moduleValueScope :: ModuleState -> M.Map Text ModuleValueDef
moduleValueScope st =
  M.union (msValues st) (isValues (msImported st))


rawModuleImportToDef :: RawModuleImport -> ModuleImport
rawModuleImportToDef rawImport =
  case rawImport of
    RawModuleImport {} ->
      ModuleImport
        { miModule = rmiModule rawImport
        , miAlias = rmiAlias rawImport
        , miInterface = rmiInterface rawImport
        , miAdapters =
            case rmiAdapter rawImport of
              Nothing -> []
              Just adapter -> [adapter]
        }
    RawForeignImport {} ->
      ModuleForeignImport
        { miForeignName = rfiName rawImport
        , miForeignInterface = rfiInterface rawImport
        , miForeignDescriptor = rfiProvider rawImport
        , miForeignAdapters =
            case rfiAdapter rawImport of
              Nothing -> []
              Just adapter -> [adapter]
        }


data ImportedScope = ImportedScope
  { isValues :: M.Map Text ModuleValueDef
  , isTypes :: M.Map Text ModuleTypeDef
  , isProviders :: [ModuleProvider]
  }


emptyImportedScope :: ImportedScope
emptyImportedScope =
  ImportedScope
    { isValues = M.empty
    , isTypes = M.empty
    , isProviders = []
    }


extendModuleExports
  :: M.Map Text ModuleValueDef
  -> M.Map Text ModuleValueDef
  -> [RawModuleExport]
  -> Either Text (M.Map Text ModuleValueDef)
extendModuleExports scopeValues =
  foldM step
  where
    step acc rawExport =
      case M.lookup (rmeLocal rawExport) scopeValues of
        Nothing -> Left ("module: unknown export " <> rmeLocal rawExport)
        Just mv ->
          if M.member (rmePublic rawExport) acc
            then Left ("module: duplicate export name " <> rmePublic rawExport)
            else Right (M.insert (rmePublic rawExport) mv acc)


extendModuleExportValueSigs
  :: M.Map Text ModuleValueDef
  -> M.Map Text InterfaceValueSig
  -> [RawModuleExport]
  -> Either Text (M.Map Text InterfaceValueSig)
extendModuleExportValueSigs scopeValues =
  foldM step
  where
    step acc rawExport =
      case M.lookup (rmeLocal rawExport) scopeValues of
        Nothing -> Left ("module: unknown export " <> rmeLocal rawExport)
        Just mv ->
          if M.member (rmePublic rawExport) acc
            then Left ("module: duplicate export name " <> rmePublic rawExport)
            else do
              sig <- moduleValueSigOf (rmePublic rawExport) mv
              Right (M.insert (rmePublic rawExport) sig acc)


moduleValueSigOf :: Text -> ModuleValueDef -> Either Text InterfaceValueSig
moduleValueSigOf publicName mv = do
  dom <- diagramDom (mvdDiagram mv)
  cod <- diagramCod (mvdDiagram mv)
  pure
    InterfaceValueSig
      { ivsName = publicName
      , ivsMode = mvdMode mv
      , ivsDom = dom
      , ivsCod = cod
      }


extendModuleTypeExports
  :: M.Map Text ModuleTypeDef
  -> M.Map Text ModuleTypeDef
  -> [RawModuleTypeExport]
  -> Either Text (M.Map Text ModuleTypeDef)
extendModuleTypeExports scopeTypes =
  foldM step
  where
    step acc rawExport =
      case M.lookup (rmteLocal rawExport) scopeTypes of
        Nothing -> Left ("module: unknown type export " <> rmteLocal rawExport)
        Just mt ->
          if M.member (rmtePublic rawExport) acc
            then Left ("module: duplicate type export name " <> rmtePublic rawExport)
            else Right (M.insert (rmtePublic rawExport) mt acc)


moduleTypesAsScope :: M.Map Text ModuleTypeDef -> M.Map Text ScopedType
moduleTypesAsScope =
  M.map
    (\mt ->
      ScopedType
        { stDoctrine = mtdDoctrine mt
        , stMode = mtdMode mt
        , stBody = mtdBody mt
        })


scopedTypeBodies :: M.Map Text ScopedType -> M.Map Text Obj
scopedTypeBodies =
  M.map stBody


moduleValuesAsScope :: M.Map Text ModuleValueDef -> M.Map Text ScopedValue
moduleValuesAsScope =
  M.map
    (\mv ->
      ScopedValue
        { svDoctrine = mvdDoctrine mv
        , svMode = mvdMode mv
        , svDiagram = mvdDiagram mv
        })


importModuleItem :: ModuleEnv -> Text -> ImportedScope -> RawModuleImport -> Either Text ImportedScope
importModuleItem env doctrineName acc rawImport =
  case rawImport of
    RawModuleImport {} -> importLocalModule
    RawForeignImport {} -> importForeignModule
  where
    importLocalModule = do
      modDef <-
        case M.lookup (rmiModule rawImport) (meModules env) of
          Nothing -> Left ("Unknown module import: " <> rmiModule rawImport)
          Just md -> Right md
      (selectedTypes, selectedValues) <-
        case rmiInterface rawImport of
          Nothing ->
            Right (mdExportTypes modDef, mdExportValueSigs modDef)
          Just ifaceName -> do
            ensureModuleMatchesInterface env (mdDoctrine modDef) (mdExportTypes modDef) (mdExports modDef) ifaceName
            iface <- lookupInterface env ifaceName
            pure
              ( M.restrictKeys (mdExportTypes modDef) (M.keysSet (idefTypes iface))
              , M.restrictKeys (mdExportValueSigs modDef) (M.keysSet (idefValues iface))
              )
      symbolicValues <- materializeLocalValues (mdDoctrine modDef) (FM.mdName modDef) selectedValues
      (adaptedTypes, adaptedValues) <-
        adaptImportedDefinitions
          env
          "module import"
          (mdDoctrine modDef)
          doctrineName
          (case rmiAdapter rawImport of
            Nothing -> []
            Just adapter -> [adapter])
          selectedTypes
          symbolicValues
      let localizedTypes = localizeImportedTypes (rmiAlias rawImport) adaptedTypes
          localizedValues = localizeImportedValues (rmiAlias rawImport) adaptedValues
      mergeImportedScope acc localizedTypes localizedValues []

    importForeignModule = do
      iface <- lookupInterface env (rfiInterface rawImport)
      let provider0 =
            ModuleProvider
              { mpName = rfiName rawImport
              , mpInterface = rfiInterface rawImport
              , mpDescriptor = rfiProvider rawImport
              , mpAdapters = []
              }
          provider = appendProviderAdapter (rfiAdapter rawImport) provider0
      manifestTypes <- materializeForeignTypes iface
      foreignValues <- traverse (providerValueDef provider0 (idefDoctrine iface)) (idefValues iface)
      (adaptedTypes, adaptedValues) <-
        adaptImportedDefinitions
          env
          "module foreign import"
          (idefDoctrine iface)
          doctrineName
          (case rfiAdapter rawImport of
            Nothing -> []
            Just adapter -> [adapter])
          manifestTypes
          foreignValues
      let localizedTypes = localizeImportedTypes (Just (rfiName rawImport)) adaptedTypes
          localizedValues = localizeImportedValues (Just (rfiName rawImport)) adaptedValues
      mergeImportedScope acc localizedTypes localizedValues [provider]

    providerValueDef provider docName sig = do
      doc <- lookupDoctrine env docName
      gd <-
        lookupGenDeclInDoctrine
          ("module: foreign import missing generator " <> ivsName sig)
          doc
          (ivsMode sig)
          (GenName (ivsName sig))
      if null (gdParams gd)
        then Right ()
        else Left ("module: foreign import generator " <> ivsName sig <> " must not take parameters")
      if all isPortShape (gdDom gd)
        then Right ()
        else Left ("module: foreign import generator " <> ivsName sig <> " must not take binder inputs")
      if gdPlainDom gd == ivsDom sig && gdCod gd == ivsCod sig
        then
          do
            diag <- providerRefDiagram (ivsMode sig) (ivsDom sig) (ivsCod sig) ref
            Right
              ModuleValueDef
                { mvdName = ivsName sig
                , mvdDoctrine = docName
                , mvdMode = ivsMode sig
                , mvdDiagram = diag
                , mvdPolicy = defaultModuleValuePolicy
                , mvdFuel = defaultModuleValueFuel
                }
        else Left ("module: foreign import generator " <> ivsName sig <> " signature mismatch")
      where
        ref =
          ProviderRef
            { prProvider = provider
            , prValueName = ivsName sig
            }

    isPortShape sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False

    materializeForeignTypes iface =
      foldM step M.empty (M.toList (idefTypes iface))
      where
        step acc (name, sig) =
          let body = maybe (itsRepr sig) id (itsBody sig)
          in Right
               ( M.insert
                   name
                   (ModuleTypeDef name (idefDoctrine iface) (itsMode sig) body)
                   acc
               )

    materializeLocalValues doctrineName0 moduleName =
      foldM step M.empty . M.toList
      where
        step acc (publicName, sig) = do
          let ref =
                ModuleValueRef
                  { mvrModule = moduleName
                  , mvrValueName = publicName
                  , mvrAdapters = []
                  }
          diag <- moduleValueRefDiagram (ivsMode sig) (ivsDom sig) (ivsCod sig) ref
          pure
            ( M.insert
                publicName
                ModuleValueDef
                  { mvdName = publicName
                  , mvdDoctrine = doctrineName0
                  , mvdMode = ivsMode sig
                  , mvdDiagram = diag
                  , mvdPolicy = defaultModuleValuePolicy
                  , mvdFuel = defaultModuleValueFuel
                  }
                acc
            )


adaptImportedDefinitions
  :: ModuleEnv
  -> Text
  -> Text
  -> Text
  -> [Text]
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> Either Text (M.Map Text ModuleTypeDef, M.Map Text ModuleValueDef)
adaptImportedDefinitions _env _label srcDoctrine tgtDoctrine [] tys vals
  | srcDoctrine == tgtDoctrine =
      Right (tys, vals)
adaptImportedDefinitions _env label srcDoctrine tgtDoctrine [] _tys _vals =
  Left
    ( label
        <> ": doctrine mismatch between "
        <> srcDoctrine
        <> " and "
        <> tgtDoctrine
        <> "; add `using <morphism>`"
    )
adaptImportedDefinitions env label srcDoctrine tgtDoctrine adapters tys vals = do
  (docFinal, tys', vals') <- foldM step (srcDoctrine, tys, vals) adapters
  if docFinal == tgtDoctrine
    then Right (tys', vals')
    else
      Left
        ( label
            <> ": adapter chain resolved to doctrine "
            <> docFinal
            <> ", expected "
            <> tgtDoctrine
        )
  where
    step (docName, tys0, vals0) morphName = do
      mor <- lookupMorphism env morphName
      if dName (PolyMorph.morSrc mor) == docName
        then Right ()
        else
          Left
            ( label
                <> ": adapter "
                <> morphName
                <> " has source doctrine "
                <> dName (PolyMorph.morSrc mor)
                <> ", expected "
                <> docName
            )
      tys1 <- traverse (translateModuleTypeDef mor) tys0
      vals1 <- traverse (translateModuleValueDef mor) vals0
      pure (dName (PolyMorph.morTgt mor), tys1, vals1)


translateModuleTypeDef :: PolyMorph.Morphism -> ModuleTypeDef -> Either Text ModuleTypeDef
translateModuleTypeDef mor mtd = do
  body' <- PolyMorph.applyMorphismTy mor (mtdBody mtd)
  pure
    mtd
      { mtdDoctrine = dName (PolyMorph.morTgt mor)
      , mtdMode = objOwnerMode body'
      , mtdBody = body'
      }


translateModuleValueDef :: PolyMorph.Morphism -> ModuleValueDef -> Either Text ModuleValueDef
translateModuleValueDef mor mvd = do
  diag' <- PolyMorph.applyMorphismDiagram mor (mvdDiagram mvd)
  let diag'' =
        mapModuleValueRefsDiagram (adaptModuleValueRef (Just (PolyMorph.morName mor)))
          (mapProviderRefsDiagram (adaptProviderRef (Just (PolyMorph.morName mor))) diag')
  pure
    mvd
      { mvdDoctrine = dName (PolyMorph.morTgt mor)
      , mvdMode = dMode diag''
      , mvdDiagram = diag''
      }


adaptProviderRef :: Maybe Text -> ProviderRef -> ProviderRef
adaptProviderRef mAdapter ref =
  ref { prProvider = appendProviderAdapter mAdapter (prProvider ref) }


adaptModuleValueRef :: Maybe Text -> ModuleValueRef -> ModuleValueRef
adaptModuleValueRef mAdapter =
  appendModuleValueRefAdapter mAdapter


providerRefDiagram :: ModeName -> [Obj] -> [Obj] -> ProviderRef -> Either Text Diagram
providerRefDiagram mode dom cod ref = do
  let (ins, d0) = allocPorts dom (emptyDiagram mode [])
  let (outs, d1) = allocPorts cod d0
  d2 <- addEdgePayload (PProvider ref) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3


moduleValueRefDiagram :: ModeName -> [Obj] -> [Obj] -> ModuleValueRef -> Either Text Diagram
moduleValueRefDiagram mode dom cod ref = do
  let (ins, d0) = allocPorts dom (emptyDiagram mode [])
  let (outs, d1) = allocPorts cod d0
  d2 <- addEdgePayload (PModuleRef ref) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3


mergeImportedScope
  :: ImportedScope
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> [ModuleProvider]
  -> Either Text ImportedScope
mergeImportedScope acc tys vals providers = do
  case M.keys (M.intersection (isTypes acc) tys) of
    [] -> Right ()
    (bad:_) -> Left ("module: duplicate imported type " <> bad)
  case M.keys (M.intersection (isValues acc) vals) of
    [] -> Right ()
    (bad:_) -> Left ("module: duplicate imported value " <> bad)
  pure
    ImportedScope
      { isTypes = M.union (isTypes acc) tys
      , isValues = M.union (isValues acc) vals
      , isProviders = L.nub (isProviders acc <> providers)
      }


localizeImportedTypes :: Maybe Text -> M.Map Text ModuleTypeDef -> M.Map Text ModuleTypeDef
localizeImportedTypes mAlias =
  M.fromList
    . map localizeOne
    . M.toList
  where
    qualifyName name =
      case mAlias of
        Nothing -> name
        Just alias -> alias <> "::" <> name

    localizeOne (name, mt) =
      let localName = qualifyName name
       in (localName, ModuleTypeDef localName (mtdDoctrine mt) (mtdMode mt) (mtdBody mt))


localizeImportedValues :: Maybe Text -> M.Map Text ModuleValueDef -> M.Map Text ModuleValueDef
localizeImportedValues mAlias =
  M.fromList
    . map localizeOne
    . M.toList
  where
    qualifyName name =
      case mAlias of
        Nothing -> name
        Just alias -> alias <> "::" <> name

    localizeOne (name, mv) =
      let localName = qualifyName name
       in (localName, mv { mvdName = localName })


type ModuleDataReprElaborator =
  ModuleSurfaceDef
  -> ModuleEnv
  -> LanguageDef
  -> M.Map Text ScopedType
  -> M.Map Text ScopedValue
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> RawModuleData
  -> Either Text ModuleDataDef


type ModuleDataReprRegistry = M.Map Text ModuleDataReprElaborator


data ResolvedModuleDataRepr
  = RMRDirect Text
  | RMROpaqueConfigured Text Text


standardModuleDataReprRegistry :: ModuleDataReprRegistry
standardModuleDataReprRegistry =
  M.fromList
    [ ( "doctrine_data"
      , \surface env lang importedTypes importedValues localTypes localValues raw ->
          elabDoctrineBackedModuleData
            surface
            env
            lang
            importedTypes
            importedValues
            localTypes
            localValues
            raw
            "doctrine_data"
      )
    , ( "opaque_data"
      , \surface env lang importedTypes importedValues localTypes localValues raw ->
          elabOpaqueModuleData
            surface
            env
            lang
            importedTypes
            importedValues
            localTypes
            localValues
            raw
      )
    ]


elabModuleData
  :: ModuleDataReprRegistry
  -> ModuleSurfaceDef
  -> ModuleEnv
  -> LanguageDef
  -> M.Map Text ScopedType
  -> M.Map Text ScopedValue
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> M.Map Text ModuleDataDef
  -> RawModuleData
  -> Either Text ModuleDataDef
elabModuleData reprRegistry surface env lang importedTypes importedValues localTypes localValues dataPkgs raw = do
  let name = rmdName raw
  if M.member name dataPkgs
    then Left ("Duplicate module data name: " <> name)
    else Right ()
  if M.member name localTypes || M.member name importedTypes
    then Left ("Duplicate module type name: " <> name)
    else Right ()
  if null (rmdCtors raw)
    then Left ("module data " <> name <> ": expected at least one constructor")
    else Right ()
  let reprName = maybe (maybe "doctrine_data" id (msdDefaultDataRepr surface)) id (rmdRepr raw)
  resolvedRepr <- resolveModuleDataReprChoice reprRegistry env reprName
  case resolvedRepr of
    RMRDirect baseName -> do
      reprElab <-
        case M.lookup baseName reprRegistry of
          Nothing -> Left ("module data " <> name <> ": unknown representation " <> reprName)
          Just elabRepr -> Right elabRepr
      pkg <- reprElab surface env lang importedTypes importedValues localTypes localValues raw
      pure pkg { mddRepr = reprName }
    RMROpaqueConfigured providerInterface descriptorPrefix ->
      elabOpaqueModuleDataConfigured
        reprName
        providerInterface
        descriptorPrefix
        surface
        env
        lang
        importedTypes
        importedValues
        localTypes
        localValues
        raw


resolveModuleDataReprChoice
  :: ModuleDataReprRegistry
  -> ModuleEnv
  -> Text
  -> Either Text ResolvedModuleDataRepr
resolveModuleDataReprChoice reprRegistry env =
  go S.empty
  where
    go visiting reprName
      | reprName `S.member` visiting =
          Left ("data_repr cycle involving " <> reprName)
      | reprName == "opaque_data" =
          Right (RMROpaqueConfigured opaqueModuleDataProviderInterface opaqueModuleDataDescriptorPrefix)
      | M.member reprName reprRegistry =
          Right (RMRDirect reprName)
      | otherwise =
          case M.lookup reprName (meModuleDataReprs env) of
            Nothing -> Left ("unknown representation " <> reprName)
            Just def -> do
              baseResolved <- go (S.insert reprName visiting) (mdrBase def)
              applyOverrides reprName def baseResolved

    applyOverrides reprName def resolved =
      case resolved of
        RMROpaqueConfigured providerInterface descriptorPrefix ->
          Right
            ( RMROpaqueConfigured
                (maybe providerInterface id (mdrProviderInterface def))
                (maybe descriptorPrefix id (mdrDescriptorPrefix def))
            )
        RMRDirect baseName ->
          case (mdrProviderInterface def, mdrDescriptorPrefix def) of
            (Nothing, Nothing) -> Right (RMRDirect baseName)
            _ ->
              Left
                ( "data_repr "
                    <> reprName
                    <> ": provider_interface and descriptor_prefix are only supported for opaque_data"
                )


elabDoctrineBackedModuleData
  :: ModuleSurfaceDef
  -> ModuleEnv
  -> LanguageDef
  -> M.Map Text ScopedType
  -> M.Map Text ScopedValue
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> RawModuleData
  -> Text
  -> Either Text ModuleDataDef
elabDoctrineBackedModuleData surface env lang importedTypes importedValues localTypes localValues raw reprName = do
  doc <- lookupDoctrine env (ldDoctrine lang)
  ownerMode <- resolveInterfaceMode doc (msdMode surface) (rmdMode raw)
  ctorTables <- deriveCtorTables doc
  typeRef <-
    case lookupCtorRefForOwnerInTables doc ctorTables ownerMode (ObjName (rmdName raw)) of
      Nothing -> Left ("module data " <> rmdName raw <> ": doctrine is missing type constructor " <> rmdName raw)
      Just ref -> Right ref
  typeParams <- lookupCtorSigForOwnerInTables doc ctorTables ownerMode typeRef
  if null (csParams typeParams)
    then Right ()
    else Left ("module data " <> rmdName raw <> ": doctrine-backed representation only supports nullary type constructors")
  ensureDistinctTexts ("module data " <> rmdName raw <> ": duplicate constructor name") (map rmcName (rmdCtors raw))
  let typeObj =
        Obj
          { objOwnerMode = ownerMode
          , objCode = CTCon typeRef []
          }
      typeDef =
        ModuleTypeDef (rmdName raw) (ldDoctrine lang) ownerMode typeObj
      typeScope =
        M.insert
          (rmdName raw)
          typeObj
          (scopedTypeBodies (M.union (moduleTypesAsScope localTypes) importedTypes))
  ctorDefs <- foldM (elabCtor doc ownerMode typeScope) M.empty (rmdCtors raw)
  pure
    ModuleDataDef
      { mddName = rmdName raw
      , mddDoctrine = ldDoctrine lang
      , mddMode = ownerMode
      , mddRepr = reprName
      , mddTypeDef = typeDef
      , mddCtorDefs = ctorDefs
      , mddCtorNames = map rmcName (rmdCtors raw)
      }
  where
    elabCtor doc ownerMode typeScope acc rawCtor = do
      let ctorName = rmcName rawCtor
      if M.member ctorName acc || M.member ctorName localValues || M.member ctorName importedValues
        then Left ("Duplicate module value name: " <> ctorName)
        else Right ()
      gd <-
        lookupGenDeclInDoctrine
          ("module data " <> rmdName raw <> ": doctrine is missing constructor " <> ctorName)
          doc
          ownerMode
          (GenName ctorName)
      if null (gdParams gd)
        then Right ()
        else Left ("module data " <> rmdName raw <> ": constructor " <> ctorName <> " must not take type or term parameters")
      if all isPortInput (gdDom gd)
        then Right ()
        else Left ("module data " <> rmdName raw <> ": constructor " <> ctorName <> " must not take binder inputs")
      checkDoctrineBackedCtorSig doc ownerMode typeScope raw gd rawCtor
      diag <- genericGenDiagram gd
      pure
        ( M.insert
            ctorName
            ModuleValueDef
              { mvdName = ctorName
              , mvdDoctrine = ldDoctrine lang
              , mvdMode = ownerMode
              , mvdDiagram = diag
              , mvdPolicy = defaultModuleValuePolicy
              , mvdFuel = defaultModuleValueFuel
              }
            acc
        )

    isPortInput sh =
      case sh of
        InPort _ -> True
        InBinder _ -> False


elabOpaqueModuleData
  :: ModuleSurfaceDef
  -> ModuleEnv
  -> LanguageDef
  -> M.Map Text ScopedType
  -> M.Map Text ScopedValue
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> RawModuleData
  -> Either Text ModuleDataDef
elabOpaqueModuleData surface env lang importedTypes importedValues localTypes localValues raw = do
  elabOpaqueModuleDataConfigured
    "opaque_data"
    opaqueModuleDataProviderInterface
    opaqueModuleDataDescriptorPrefix
    surface
    env
    lang
    importedTypes
    importedValues
    localTypes
    localValues
    raw


elabOpaqueModuleDataConfigured
  :: Text
  -> Text
  -> Text
  -> ModuleSurfaceDef
  -> ModuleEnv
  -> LanguageDef
  -> M.Map Text ScopedType
  -> M.Map Text ScopedValue
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> RawModuleData
  -> Either Text ModuleDataDef
elabOpaqueModuleDataConfigured reprName providerInterface descriptorPrefix surface env lang importedTypes importedValues localTypes localValues raw = do
  doc <- lookupDoctrine env (ldDoctrine lang)
  ownerMode <- resolveInterfaceMode doc (msdMode surface) (rmdMode raw)
  ensureDistinctTexts ("module data " <> rmdName raw <> ": duplicate constructor name") (map rmcName (rmdCtors raw))
  meta <- mkTypeMetaVar doc ownerMode (opaqueModuleDataTypeName (rmdName raw))
  let typeObj = Obj { objOwnerMode = ownerMode, objCode = CTMeta meta }
  let typeDef =
        ModuleTypeDef (rmdName raw) (ldDoctrine lang) ownerMode typeObj
      typeScope =
        M.insert
          (rmdName raw)
          typeObj
          (scopedTypeBodies (M.union (moduleTypesAsScope localTypes) importedTypes))
  ctorDefs <- foldM (elabCtor doc ownerMode typeScope) M.empty (rmdCtors raw)
  pure
    ModuleDataDef
      { mddName = rmdName raw
      , mddDoctrine = ldDoctrine lang
      , mddMode = ownerMode
      , mddRepr = reprName
      , mddTypeDef = typeDef
      , mddCtorDefs = ctorDefs
      , mddCtorNames = map rmcName (rmdCtors raw)
      }
  where
    dataProvider =
      ModuleProvider
        { mpName = rmdName raw
        , mpInterface = providerInterface
        , mpDescriptor = opaqueModuleDataProviderDescriptorWithPrefix descriptorPrefix (rmdName raw)
        , mpAdapters = []
        }

    elabCtor doc ownerMode typeScope acc rawCtor = do
      let ctorName = rmcName rawCtor
      if M.member ctorName acc || M.member ctorName localValues || M.member ctorName importedValues
        then Left ("Duplicate module value name: " <> ctorName)
        else Right ()
      sigMode <- resolveInterfaceMode doc (Just (modeNameText ownerMode)) (rvsMode (rmcSig rawCtor))
      if sigMode == ownerMode
        then Right ()
        else Left ("module data " <> rmdName raw <> ": constructor " <> ctorName <> " mode mismatch")
      dom <- mapM (elabObjExprInScope typeScope doc [] [] M.empty ownerMode) (rvsDom (rmcSig rawCtor))
      cod <- mapM (elabObjExprInScope typeScope doc [] [] M.empty ownerMode) (rvsCod (rmcSig rawCtor))
      diag <-
        providerRefDiagram
          ownerMode
          dom
          cod
          ProviderRef
            { prProvider = dataProvider
            , prValueName = ctorName
            }
      pure
        ( M.insert
            ctorName
            ModuleValueDef
              { mvdName = ctorName
              , mvdDoctrine = ldDoctrine lang
              , mvdMode = ownerMode
              , mvdDiagram = diag
              , mvdPolicy = defaultModuleValuePolicy
              , mvdFuel = defaultModuleValueFuel
              }
            acc
        )


checkDoctrineBackedCtorSig
  :: Doctrine
  -> ModeName
  -> M.Map Text Obj
  -> RawModuleData
  -> GenDecl
  -> RawModuleCtor
  -> Either Text ()
checkDoctrineBackedCtorSig doc ownerMode typeScope rawData gd rawCtor = do
  sigMode <- resolveInterfaceMode doc (Just (modeNameText ownerMode)) (rvsMode (rmcSig rawCtor))
  if sigMode == ownerMode
    then Right ()
    else Left ("module data " <> rmdName rawData <> ": constructor " <> rmcName rawCtor <> " mode mismatch")
  dom <- mapM (elabObjExprInScope typeScope doc [] [] M.empty ownerMode) (rvsDom (rmcSig rawCtor))
  cod <- mapM (elabObjExprInScope typeScope doc [] [] M.empty ownerMode) (rvsCod (rmcSig rawCtor))
  if dom == gdPlainDom gd
    then Right ()
    else Left ("module data " <> rmdName rawData <> ": constructor " <> rmcName rawCtor <> " domain mismatch")
  if cod == gdCod gd
    then Right ()
    else Left ("module data " <> rmdName rawData <> ": constructor " <> rmcName rawCtor <> " codomain mismatch")


ensureDistinctTexts :: Text -> [Text] -> Either Text ()
ensureDistinctTexts label names =
  if S.size (S.fromList names) == length names
    then Right ()
    else Left label


firstPrefix :: Text -> Either Text a -> Either Text a
firstPrefix prefix =
  either (Left . (prefix <>)) Right


defaultModuleValuePolicy :: RewritePolicy
defaultModuleValuePolicy = UseStructuralAsBidirectional


defaultModuleValueFuel :: Int
defaultModuleValueFuel = 50


modeNameText :: ModeName -> Text
modeNameText (ModeName name) = name


elabModuleType
  :: ModuleEnv
  -> LanguageDef
  -> ModuleSurfaceDef
  -> M.Map Text ScopedType
  -> M.Map Text ModuleTypeDef
  -> RawModuleType
  -> Either Text (M.Map Text ModuleTypeDef)
elabModuleType env lang surface importedTypes acc raw =
  if M.member (rmtName raw) acc || M.member (rmtName raw) importedTypes
    then Left ("Duplicate module type name: " <> rmtName raw)
    else do
      doc <- lookupDoctrine env (ldDoctrine lang)
      let typeScope = scopedTypeBodies (M.union (moduleTypesAsScope acc) importedTypes)
      body <- elabScopedTypeExpr doc (msdMode surface) (rmtMode raw) typeScope (rmtBody raw)
      let typeDef =
            ModuleTypeDef (rmtName raw) (ldDoctrine lang) (objOwnerMode body) body
      pure (M.insert (rmtName raw) typeDef acc)


elabModuleValue
  :: ModuleEnv
  -> LanguageDef
  -> ModuleSurfaceDef
  -> M.Map Text ScopedValue
  -> M.Map Text ScopedType
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> RawModuleValue
  -> Either Text (M.Map Text ModuleValueDef)
elabModuleValue env lang surface importedTerms importedTypes localTypes acc raw = do
  if M.member (rmvName raw) acc || M.member (rmvName raw) importedTerms
    then Left ("Duplicate module value name: " <> rmvName raw)
    else do
      let sigMode = rmvSig raw >>= rvsMode
      case (sigMode, rmvMode raw) of
        (Just sig, Just declMode)
          | sig /= declMode ->
              Left ("module " <> rmvName raw <> ": conflicting mode annotations")
        _ -> Right ()
      let scopeTerms = moduleValuesAsScope acc
          scopeTypes = moduleTypesAsScope localTypes
          valueScope = M.unions [scopeTerms, importedTerms]
          typeScope = scopedTypeBodies (M.unions [scopeTypes, importedTypes])
          doctrineName = ldDoctrine lang
          uses = dedupe (msdUses surface <> rmvUses raw)
          surfaceName = case rmvSurface raw of
            Just s -> Just s
            Nothing -> msdExprSurface surface
          modeName = chooseModeText sigMode (chooseModeText (rmvMode raw) (msdMode surface))
          fuel = maybe 50 id (rmvFuel raw)
          policyName = maybe "UseStructuralAsBidirectional" id (rmvPolicy raw)
      policy <- parsePolicy policyName
      CompiledDiagramArtifact
        { cdaDoctrine = docFinal
        , cdaNormalizedDiagram = normDiag
        } <-
        case
            compileDiagramArtifact
              valueScope
              typeScope
              env
              doctrineName
              modeName
              surfaceName
              uses
              (rmvMorphisms raw)
              policy
              fuel
              (rmvExprText raw) of
          Left err -> Left ("module " <> rmvName raw <> ": " <> err)
          Right ok -> Right ok
      checkModuleValueSignature docFinal typeScope normDiag raw
      let valueDef =
            ModuleValueDef
              { mvdName = rmvName raw
              , mvdDoctrine = dName docFinal
              , mvdMode = dMode normDiag
              , mvdDiagram = normDiag
              , mvdPolicy = policy
              , mvdFuel = fuel
              }
      pure (M.insert (rmvName raw) valueDef acc)


checkModuleValueSignature :: Doctrine -> M.Map Text Obj -> Diagram -> RawModuleValue -> Either Text ()
checkModuleValueSignature _doc _typeScope _diag raw
  | Nothing <- rmvSig raw = Right ()
checkModuleValueSignature doc typeScope diag raw =
  case rmvSig raw of
    Nothing -> Right ()
    Just sig -> do
      let actualMode = dMode diag
          declaredMode =
            case rvsMode sig of
              Nothing -> actualMode
              Just name -> ModeName name
      if declaredMode == actualMode
        then Right ()
        else Left ("module " <> rmvName raw <> ": signature mode mismatch")
      dom <- mapM (elabObjExprInScope typeScope doc [] [] M.empty declaredMode) (rvsDom sig)
      cod <- mapM (elabObjExprInScope typeScope doc [] [] M.empty declaredMode) (rvsCod sig)
      actualDom <- diagramDom diag
      actualCod <- diagramCod diag
      if dom == actualDom
        then Right ()
        else Left ("module " <> rmvName raw <> ": declared domain does not match elaborated body")
      if cod == actualCod
        then Right ()
        else Left ("module " <> rmvName raw <> ": declared codomain does not match elaborated body")


insertBuild :: ModuleEnv -> RawBuild -> Either Text ModuleEnv
insertBuild env raw = do
  ensureAbsent "build" (rbName raw) (meBuilds env)
  _ <-
    case M.lookup (rbModule raw) (meModules env) of
      Nothing -> Left ("Unknown module: " <> rbModule raw)
      Just _ -> Right ()
  _ <-
    case M.lookup (rbPipeline raw) (mePipelines env) of
      Nothing -> Left ("Unknown pipeline: " <> rbPipeline raw)
      Just _ -> Right ()
  let buildDef :: BuildDef
      buildDef =
        BuildDef
          { bdName = rbName raw
          , bdModule = rbModule raw
          , bdPipeline = rbPipeline raw
          }
  pure env { meBuilds = M.insert (rbName raw) buildDef (meBuilds env) }


lookupInterface :: ModuleEnv -> Text -> Either Text InterfaceDef
lookupInterface env name =
  case M.lookup name (meInterfaces env) of
    Nothing -> Left ("Unknown interface: " <> name)
    Just iface -> Right iface


ensureModuleMatchesInterface
  :: ModuleEnv
  -> Text
  -> M.Map Text ModuleTypeDef
  -> M.Map Text ModuleValueDef
  -> Text
  -> Either Text ()
ensureModuleMatchesInterface env doctrineName types values ifaceName = do
  iface <- lookupInterface env ifaceName
  if idefDoctrine iface /= doctrineName
    then Left ("interface " <> ifaceName <> " doctrine mismatch")
    else do
      doc <- lookupDoctrine env doctrineName
      let checkType doc' iface' (name, sig) =
            case M.lookup name types of
              Nothing -> Left ("interface " <> ifaceName <> ": missing type " <> name)
              Just mt -> ensureModuleTypeMatchesSig doc' iface' types ifaceName mt sig

          checkValue doc' iface' (name, sig0) =
            case M.lookup name values of
              Nothing -> Left ("interface " <> ifaceName <> ": missing value " <> name)
              Just mv -> do
                sig <- instantiateInterfaceValueSig doc' iface' types sig0
                ensureModuleValueMatchesSig ifaceName mv sig
      mapM_ (checkType doc iface) (M.toList (idefTypes iface))
      mapM_ (checkValue doc iface) (M.toList (idefValues iface))


ensureModuleTypeMatchesSig :: Doctrine -> InterfaceDef -> M.Map Text ModuleTypeDef -> Text -> ModuleTypeDef -> InterfaceTypeSig -> Either Text ()
ensureModuleTypeMatchesSig doc iface exportedTypes ifaceName mt sig = do
  if mtdMode mt /= itsMode sig
    then Left ("interface " <> ifaceName <> ": type " <> moduleTypeName mt <> " mode mismatch")
    else Right ()
  case itsBody sig of
    Nothing -> Right ()
    Just expected -> do
      tt <- doctrineTypeTheory doc
      subst <- buildOpaqueTypeSubst tt iface exportedTypes
      expected' <- normalizeObjDeep tt =<< SR.applySubstObj tt subst expected
      actual' <- normalizeObjDeep tt (mtdBody mt)
      if expected' == actual'
        then Right ()
        else Left ("interface " <> ifaceName <> ": type " <> moduleTypeName mt <> " definition mismatch")


moduleTypeName :: ModuleTypeDef -> Text
moduleTypeName (ModuleTypeDef name _ _ _) = name


instantiateInterfaceValueSig
  :: Doctrine
  -> InterfaceDef
  -> M.Map Text ModuleTypeDef
  -> InterfaceValueSig
  -> Either Text InterfaceValueSig
instantiateInterfaceValueSig doc iface exportedTypes sig = do
  tt <- doctrineTypeTheory doc
  subst <- buildOpaqueTypeSubst tt iface exportedTypes
  dom <- mapM (SR.applySubstObj tt subst) (ivsDom sig)
  cod <- mapM (SR.applySubstObj tt subst) (ivsCod sig)
  pure sig { ivsDom = dom, ivsCod = cod }


buildOpaqueTypeSubst
  :: TypeTheory
  -> InterfaceDef
  -> M.Map Text ModuleTypeDef
  -> Either Text US.Subst
buildOpaqueTypeSubst _tt iface exportedTypes =
  US.mkSubst
    [ (v, CAObj (mtdBody mt))
    | (name, sig) <- M.toList (idefTypes iface)
    , Nothing <- [itsBody sig]
    , Just mt <- [M.lookup name exportedTypes]
    , Obj { objCode = CTMeta v } <- [itsRepr sig]
    ]


ensureModuleValueMatchesSig :: Text -> ModuleValueDef -> InterfaceValueSig -> Either Text ()
ensureModuleValueMatchesSig ifaceName mv sig = do
  if mvdMode mv /= ivsMode sig
    then Left ("interface " <> ifaceName <> ": value " <> mvdName mv <> " mode mismatch")
    else Right ()
  dom <- diagramDom (mvdDiagram mv)
  cod <- diagramCod (mvdDiagram mv)
  if dom /= ivsDom sig
    then Left ("interface " <> ifaceName <> ": value " <> mvdName mv <> " domain mismatch")
    else Right ()
  if cod /= ivsCod sig
    then Left ("interface " <> ifaceName <> ": value " <> mvdName mv <> " codomain mismatch")
    else Right ()


elabPipeline :: RawPipeline -> Either Text Pipeline
elabPipeline raw = do
  phases <- mapM elabPhase (rplPhases raw)
  let pipeline = Pipeline { plName = rplName raw, plPhases = phases }
  validatePipeline pipeline
  pure pipeline


elabPhase :: RawPhase -> Either Text Phase
elabPhase raw =
  case raw of
    RPApply name -> Right (ApplyMorph name)
    RPNormalize opts -> do
      policy <- parsePipelinePolicy (rnoPolicy opts)
      let fuel = maybe 50 id (rnoFuel opts)
      Right (Normalize policy fuel)
    RPQuoteInto fragmentName targetName ->
      Right (QuoteInto fragmentName targetName)
    RPLink name ->
      Right (LinkModule name)
    RPBundleAll ->
      Right BundleAll
    RPBundle items ->
      Right
        ( BundleExports
            [ BundleItem
                { biSource = rbiSource item
                , biTarget = rbiTarget item
                }
            | item <- items
            ]
        )
    RPProjectExport name ->
      Right (ProjectExport name)
    RPEmitVia backendName opts ->
      Right
        ( EmitVia
            BackendSpec
              { bsName = backendName
              , bsStdout = rveStdout opts
              , bsRoot = rveRoot opts
              }
        )


parsePipelinePolicy :: Maybe Text -> Either Text RewritePolicy
parsePipelinePolicy mName =
  case maybe "UseStructuralAsBidirectional" id mName of
    "topmost" -> Right UseStructuralAsBidirectional
    "computational_lr" -> Right UseOnlyComputationalLR
    "all_oriented" -> Right UseAllOriented
    other -> parsePolicy other


validatePipeline :: Pipeline -> Either Text ()
validatePipeline pipeline = go PKModule (plPhases pipeline)
  where
    go _ [] = Right ()
    go kind (phase:rest) = do
      next <- phaseTransition phase kind
      go next rest


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


renderGenNameText :: GenName -> Text
renderGenNameText (GenName name) = name


elabImplements :: SearchBudget -> ModuleEnv -> Text -> Text -> Text -> Either Text (((Text, Text), Text), Int)
elabImplements budget env ifaceName tgtName morphName = do
  ifaceDoc <- lookupDoctrine env ifaceName
  tgtDoc <- lookupDoctrine env tgtName
  morph <- lookupMorphism env morphName
  if PolyMorph.morSrc morph /= ifaceDoc
    then Left "Morphism source does not match implements interface"
    else
      if PolyMorph.morTgt morph /= tgtDoc
        then Left "Morphism target does not match implements target"
        else do
          result <- checkImplementsObligationsWithBudget budget env tgtDoc morph ifaceDoc
          proofCount <-
            case result of
              ImplementsCheckProved proofs ->
                Right (length proofs)
              ImplementsCheckUndecided label lim ->
                Left ("implements obligation undecided: " <> label <> " (" <> renderSearchLimit lim <> ")")
          Right (((ifaceName, tgtName), morphName), proofCount)


buildPolyFromBase :: SearchBudget -> Text -> Text -> ModuleEnv -> Doctrine -> Either Text (PolyMorph.Morphism, Int)
buildPolyFromBase budget baseName newName env newDoc = do
  baseDoc <- lookupDoctrine env baseName
  ensureAbsent "morphism" morName (meMorphisms env)
  ctorTables <- deriveCtorTables baseDoc
  genMap <- fmap M.fromList (mapM genImage (allGens baseDoc ctorTables))
  let mor =
        PolyMorph.Morphism
          { PolyMorph.morName = morName
          , PolyMorph.morSrc = baseDoc
          , PolyMorph.morTgt = newDoc
          , PolyMorph.morIsCoercion = True
          , PolyMorph.morModeMap = identityModeMap baseDoc
          , PolyMorph.morModMap = identityModMap baseDoc
          , PolyMorph.morTypeMap = M.empty
          , PolyMorph.morGenMap = genMap
          , PolyMorph.morCheck = PolyMorph.CheckAll
          , PolyMorph.morPolicy = UseStructuralAsBidirectional
          }
  case PolyMorph.checkMorphismResultWithBudget budget mor of
    Left err ->
      Left ("generated morphism " <> morName <> " invalid: " <> err)
    Right checkResult ->
      case checkResult of
        PolyMorph.MorphismCheckProved proofs ->
          Right (mor, length proofs)
        PolyMorph.MorphismCheckUndecided cellName lim ->
          Left
            ( "generated morphism "
                <> morName
                <> " invalid: checkMorphism: equation undecided for "
                <> cellName
                <> " ("
                <> renderSearchLimit lim
                <> ")"
            )
  where
    morName = newName <> ".fromBase"

    allGens doc ctorTables =
      [ (mode, gen)
      | (mode, table) <- M.toList (dGens doc)
      , gen <- M.elems table
      , not (isTypeDeclGenNameInTables doc ctorTables mode (genToObjName (gdName gen)))
      ]

    genImage (mode, gen) = do
      img0 <- genericGenDiagram gen
      let binderSlots = [bs | InBinder bs <- gdDom gen]
      let holes = [BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1]]
      let bargs = map BAMeta holes
      let binderSigs = M.fromList (zip holes binderSlots)
      case IM.toList (dEdges img0) of
        [(_, _)] -> pure ((mode, gdName gen), PolyMorph.GenImage img0 binderSigs)
        _ -> Left "generated morphism image is not a single generator edge"

    identityModeMap doc =
      M.fromList [(m, m) | m <- M.keys (mtModes (dModes doc))]

    identityModMap doc =
      M.fromList
        [ (name, ModExpr {meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name]})
        | (name, decl) <- M.toList (mtDecls (dModes doc))
        ]

    genToObjName (GenName n) = ObjName n
