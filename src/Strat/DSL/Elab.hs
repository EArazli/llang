{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  , elabRawFileWithEnvAndBudget
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Data.Map.Strict (Map)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.AST
import Strat.Frontend.Env
import Strat.Frontend.Compile (compileDiagramArtifact)
import Strat.Pipeline
import Strat.Poly.Attr
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
import Strat.Poly.TypeExpr (TypeExpr(..), TypeArg(..), TypeRef(..), TypeName(..), TyVar(..), TmVar(..), TermDiagram(..))
import Strat.Poly.Diagram (Diagram(..), genDWithAttrs)
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , BinderSig(..)
  , GenDecl(..)
  , InputShape(..)
  , ObligationDecl(..)
  , ParamSig(..)
  , TypeSig(..)
  , doctrineTypeTheory
  , gdPlainDom
  , lookupTypeSig
  , validateDoctrine
  )
import Strat.Poly.Graph (BinderArg(..), BinderMetaVar(..), Edge(..), EdgePayload(..))
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.ModeTheory
  ( ModeTheory(..)
  , ModeInfo(..)
  , ModDecl(..)
  , ModEqn(..)
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
  )
import Strat.Poly.Surface (elabPolySurfaceDecl)
import Strat.Poly.Surface.Spec (ssDoctrine, ssBaseDoctrine)
import Strat.Poly.Proof (SearchBudget, defaultSearchBudget, renderSearchLimit)
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeNormalize (termExprToDiagramChecked)


elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile = elabRawFileWithEnvAndBudget defaultSearchBudget emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv = elabRawFileWithEnvAndBudget defaultSearchBudget

elabRawFileWithEnvAndBudget :: SearchBudget -> ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnvAndBudget budget baseEnv (RawFile decls) = do
  (env, rawTerms, rawRuns) <- foldM step (baseEnv, [], []) decls
  envWithTerms <- elabTerms env rawTerms
  runs <- elabRuns envWithTerms rawRuns
  pure envWithTerms { meRuns = runs }
  where
    step (env, rawTerms, rawRuns) decl =
      case decl of
        DeclImport _ -> Right (env, rawTerms, rawRuns)
        DeclDoctrine raw -> do
          env' <- insertDoctrine budget env raw
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
        DeclDoctrineFunctor functorDecl -> do
          env' <- elabDoctrineFunctor budget env functorDecl
          pure (env', rawTerms, rawRuns)
        DeclDoctrineApply applyDecl -> do
          env' <- elabDoctrineApply env applyDecl
          pure (env', rawTerms, rawRuns)
        DeclDoctrineEffects name base effects -> do
          env' <- elabDoctrineEffects budget env name base effects
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
          (morph, morphCheck) <- elabPolyMorphismWithBudgetResult budget env morphDecl
          let proofCount =
                case morphCheck of
                  PolyMorph.MorphismCheckProved proofs -> length proofs
                  PolyMorph.MorphismCheckUndecided _ _ -> 0
          let env' =
                addMorphismProofCount proofCount
                  (env { meMorphisms = M.insert name morph (meMorphisms env) })
          pure (env', rawTerms, rawRuns)
        DeclImplements iface tgt morphName -> do
          ((key, name), proofCount) <- elabImplements budget env iface tgt morphName
          let defaults = M.findWithDefault [] key (meImplDefaults env)
          let defaults' = if name `elem` defaults then defaults else defaults <> [name]
          let env' =
                addImplementsProofCount proofCount
                  (env { meImplDefaults = M.insert key defaults' (meImplDefaults env) })
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
  mapM_ (\(_, _, schemaDoc) -> validateFunctorSchema schemaDoc) paramsWithSchemas
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


elabDoctrineApply :: ModuleEnv -> RawDoctrineApply -> Either Text ModuleEnv
elabDoctrineApply env raw = do
  ensureAbsent "doctrine" (rdaName raw) (meDoctrines env)
  functorDef <- lookupFunctor env (rdaFunctor raw)
  targetDoc <- lookupDoctrine env (rdaTarget raw)
  implMorphs <- resolveApplyMorphisms env functorDef targetDoc (rdaUsing raw)
  implIface <- buildIfaceImplMorphism raw functorDef targetDoc implMorphs
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
    env
      { meDoctrines = M.insert (rdaName raw) doc (meDoctrines env)
      , meMorphisms = morphisms'
      }


lookupFunctor :: ModuleEnv -> Text -> Either Text DoctrineFunctorDef
lookupFunctor env name =
  case M.lookup name (meFunctors env) of
    Nothing -> Left ("Unknown doctrine_functor: " <> name)
    Just def -> Right def

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
  attrMaps <- mapM (uncurry liftCompletedAttrMap) implMorphs
  attrMap <- mergeDisjoint "attrsort" attrMaps
  typeMaps <- mapM (uncurry liftCompletedTypeMap) implMorphs
  typeMap <- mergeDisjoint "type" typeMaps
  genMap <- mergeDisjoint "generator" [liftGenMap p (PolyMorph.morGenMap mor) | (p, mor) <- implMorphs]
  pure
    PolyMorph.Morphism
      { PolyMorph.morName = rdaName raw <> ".__impl_iface"
      , PolyMorph.morSrc = dfIface functorDef
      , PolyMorph.morTgt = targetDoc
      , PolyMorph.morIsCoercion = False
      , PolyMorph.morModeMap = modeMap
      , PolyMorph.morModMap = modMap
      , PolyMorph.morAttrSortMap = attrMap
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
        { trMode = prefixMode p (trMode ref)
        , trName = TypeName (prefixText p (renderTypeName (trName ref)))
        }
    renderTypeName (TypeName t) = t
    prefixAttr p (AttrSort s) = AttrSort (prefixText p s)
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
    liftAttrMap p mp =
      M.fromList
        [ (prefixAttr p srcSort, tgtSort)
        | (srcSort, tgtSort) <- M.toList mp
        ]
    liftCompletedAttrMap p mor = do
      completed <- completeAttrMap mor
      pure (liftAttrMap p completed)
    liftTypeMap p mp =
      M.fromList
        [ (prefixTypeRef p srcRef, tmpl)
        | (srcRef, tmpl) <- M.toList mp
        ]
    liftCompletedTypeMap p mor = do
      completed <- completeTypeMap mor
      pure (liftTypeMap p completed)
    liftGenMap p mp =
      M.fromList
        [ (prefixGen p srcKey, img)
        | (srcKey, img) <- M.toList mp
        ]

    completeAttrMap mor =
      foldM add M.empty (M.keys (dAttrSorts (PolyMorph.morSrc mor)))
      where
        explicit = PolyMorph.morAttrSortMap mor
        tgtSorts = dAttrSorts (PolyMorph.morTgt mor)
        add mp srcSort =
          case M.lookup srcSort explicit of
            Just tgtSort -> Right (M.insert srcSort tgtSort mp)
            Nothing ->
              if M.member srcSort tgtSorts
                then Right (M.insert srcSort srcSort mp)
                else Left ("apply: morphism " <> PolyMorph.morName mor <> " missing attrsort mapping")

    completeTypeMap mor = do
      tt <- doctrineTypeTheory (PolyMorph.morTgt mor)
      foldM (addType tt) M.empty (allTypeDecls (PolyMorph.morSrc mor))
      where
        explicit = PolyMorph.morTypeMap mor
        addType tt mp (srcRef, sig) =
          case M.lookup srcRef explicit of
            Just tmpl -> Right (M.insert srcRef tmpl mp)
            Nothing -> do
              tmpl <- identityTemplate tt mor srcRef sig
              Right (M.insert srcRef tmpl mp)

    identityTemplate tt mor srcRef sig = do
      tgtMode <- PolyMorph.applyMorphismMode mor (trMode srcRef)
      let tgtRef = srcRef { trMode = tgtMode }
      params <- mapM (mkParam mor) (zip [0 :: Int ..] (tsParams sig))
      args <- mapM (paramArg tt) params
      pure (PolyMorph.TypeTemplate params (TCon tgtRef args))

    mkParam mor (i, param) =
      case param of
        PS_Ty srcMode -> do
          tgtMode <- PolyMorph.applyMorphismMode mor srcMode
          Right (PolyMorph.TPType TyVar { tvName = "a" <> T.pack (show i), tvMode = tgtMode })
        PS_Tm srcSort -> do
          tgtSort <- PolyMorph.applyMorphismTy mor srcSort
          Right (PolyMorph.TPTm TmVar { tmvName = "t" <> T.pack (show i), tmvSort = tgtSort, tmvScope = 0 })

    paramArg tt param =
      case param of
        PolyMorph.TPType v -> Right (TAType (TVar v))
        PolyMorph.TPTm v -> do
          tm <- termExprToDiagramChecked tt [] (tmvSort v) (TMVar v)
          Right (TATm tm)

    allTypeDecls doc =
      [ (TypeRef mode typeName, sig)
      | (mode, table) <- M.toList (dTypes doc)
      , (typeName, sig) <- M.toList table
      ]

    validateApplyCoverage paramName mor = do
      let srcDoc = PolyMorph.morSrc mor
      let tgtDoc = PolyMorph.morTgt mor
      let typeIssues =
            [ (srcRef, issue)
            | (srcRef, srcSig) <- allTypeDecls srcDoc
            , Just issue <- [typeMappingIssue srcRef srcSig tgtDoc mor]
            ]
      let missingTypes = [ srcRef | (srcRef, isMissing) <- typeIssues, isMissing ]
      let incompatibleTypes = [ srcRef | (srcRef, isMissing) <- typeIssues, not isMissing ]
      let allBadTypes = missingTypes <> incompatibleTypes
      let missingGens = [ srcKey | srcKey <- allGenKeys srcDoc, M.notMember srcKey (PolyMorph.morGenMap mor) ]
      let missingAttrSorts = [ srcSort | srcSort <- M.keys (dAttrSorts srcDoc), needsAttrMapping srcSort tgtDoc mor ]
      if null allBadTypes && null missingGens && null missingAttrSorts
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
                <> "; "
                <> renderMissing "attr_sort" (map renderAttrSort missingAttrSorts)
            )

    typeMappingIssue srcRef srcSig tgtDoc mor =
      case M.lookup srcRef (PolyMorph.morTypeMap mor) of
        Just _ -> Nothing
        Nothing ->
          case PolyMorph.applyMorphismMode mor (trMode srcRef) of
            Left _ -> Just True
            Right tgtMode ->
              let tgtRef = srcRef { trMode = tgtMode }
              in case lookupTypeSig tgtDoc tgtRef of
                  Left _ -> Just True
                  Right tgtSig ->
                    if length (tsParams srcSig) == length (tsParams tgtSig)
                      then Nothing
                      else Just False

    needsAttrMapping srcSort tgtDoc mor =
      case M.lookup srcSort (PolyMorph.morAttrSortMap mor) of
        Just _ -> False
        Nothing -> M.notMember srcSort (dAttrSorts tgtDoc)

    allGenKeys doc =
      [ (mode, gdName genDecl)
      | (mode, table) <- M.toList (dGens doc)
      , genDecl <- M.elems table
      ]

    renderMissing label vals =
      label <> "=" <> renderList vals

    renderList [] = "(none)"
    renderList vals = "[" <> T.intercalate ", " vals <> "]"

    renderModeName (ModeName n) = n
    renderTypeRef ref = renderModeName (trMode ref) <> "." <> renderTypeName (trName ref)
    renderAttrSort (AttrSort s) = s
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

validateFunctorSchema :: Doctrine -> Either Text ()
validateFunctorSchema schema = do
  case forbidden of
    [] -> Right ()
    _ ->
      Left
        ( "doctrine_functor: schema "
            <> dName schema
            <> " must be signature-only; forbidden items: "
            <> T.intercalate ", " forbidden
        )
  where
    forbidden =
      concat
        [ [ "actions" | not (M.null (dActions schema)) ]
        , [ "obligations" | not (null (dObligations schema)) ]
        , [ "mod_transforms" | not (M.null (mtTransforms (dModes schema))) ]
        , [ "cells/rules" | not (null (dCells2 schema)) ]
        ]

namespaceDoctrineWithParam :: Text -> Doctrine -> Either Text Doctrine
namespaceDoctrineWithParam param doc = do
  modeTheory' <- renameModeTheory modeRenMap modRenMap (dModes doc)
  types' <- renameTypeTables (dTypes doc)
  gens' <- renameGenTables (dGens doc)
  let attrSorts' =
        M.fromList
          [ (renameSort (asName decl), decl { asName = renameSort (asName decl) })
          | decl <- M.elems (dAttrSorts doc)
          ]
  let acyclic' =
        S.fromList
          [ renameMode mode
          | mode <- S.toList (dAcyclicModes doc)
          ]
  pure
    doc
      { dName = prefix (dName doc)
      , dModes = modeTheory'
      , dAcyclicModes = acyclic'
      , dAttrSorts = attrSorts'
      , dTypes = renameOuterModeMap modeRenMap types'
      , dGens = gens'
      }
  where
    prefix t = param <> "::" <> t
    modeRenMap = M.fromList [ (m, renameMode m) | m <- M.keys (mtModes (dModes doc)) ]
    modRenMap = M.fromList [ (m, renameMod m) | m <- M.keys (mtDecls (dModes doc)) ]
    sortRenMap = M.fromList [ (s, renameSort s) | s <- M.keys (dAttrSorts doc) ]
    typeRenMap =
      M.fromList
        [ (TypeRef mode tname, renameTypeRef (TypeRef mode tname))
        | (mode, table) <- M.toList (dTypes doc)
        , tname <- M.keys table
        ]
    genRenMap =
      M.fromList
        [ ((mode, gdName gd), renameGenName (gdName gd))
        | (mode, table) <- M.toList (dGens doc)
        , gd <- M.elems table
        ]
    renameOuterModeMap ren mp =
      M.fromList [ (M.findWithDefault mode mode ren, table) | (mode, table) <- M.toList mp ]
    renameMode (ModeName t) = ModeName (prefix t)
    renameMod (ModName t) = ModName (prefix t)
    renameSort (AttrSort t) = AttrSort (prefix t)
    renameTypeName (TypeName t) = TypeName (prefix t)
    renameTypeRef ref =
      TypeRef
        { trMode = renameMode (trMode ref)
        , trName = renameTypeName (trName ref)
        }
    renameGenName (GenName t) = GenName (prefix t)

    renameTypeTables tables =
      foldM addType M.empty
        [ (mode, tname, sig)
        | (mode, table) <- M.toList tables
        , (tname, sig) <- M.toList table
        ]
      where
        addType acc (mode, tname, sig) = do
          sig' <- renameTypeSig modeRenMap modRenMap typeRenMap sig
          let mode' = M.findWithDefault mode mode modeRenMap
          let tname' = renameTypeName tname
          let table0 = M.findWithDefault M.empty mode' acc
          let table' = M.insert tname' sig' table0
          Right (M.insert mode' table' acc)

    renameGenTables tables =
      foldM addGen M.empty
        [ (mode, gen)
        | (mode, table) <- M.toList tables
        , gen <- M.elems table
        ]
      where
        addGen acc (mode, gen) = do
          gen' <- renameGenDecl modeRenMap modRenMap typeRenMap sortRenMap genRenMap gen
          let mode' = M.findWithDefault mode mode modeRenMap
          let key' = gdName gen'
          let table0 = M.findWithDefault M.empty mode' acc
          case M.lookup key' table0 of
            Nothing ->
              let table' = M.insert key' gen' table0
              in Right (M.insert mode' table' acc)
            Just existing
              | existing == gen' -> Right acc
              | otherwise -> Left "doctrine_functor: namespaced generator collision"

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
  attrSorts <- unionByEq "attrsort" (dAttrSorts left) (dAttrSorts right)
  types <- mergeModeTables "type" (dTypes left) (dTypes right)
  gens <- mergeModeTables "generator" (dGens left) (dGens right)
  cells <- mergeCellsWithAlphaRename (dCells2 left) (dCells2 right)
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
            }
      , dAcyclicModes = S.union (dAcyclicModes left) (dAcyclicModes right)
      , dAttrSorts = attrSorts
      , dTypes = types
      , dGens = gens
      , dCells2 = cells
      , dActions = actions
      , dObligations = obligations
      }

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

renameModeTheory
  :: Map ModeName ModeName
  -> Map ModName ModName
  -> ModeTheory
  -> Either Text ModeTheory
renameModeTheory modeRen modRen mt =
  Right
    ModeTheory
      { mtModes =
          M.fromList
            [ (mode', info { miName = mode' })
            | (mode, info) <- M.toList (mtModes mt)
            , let mode' = M.findWithDefault mode mode modeRen
            ]
      , mtDecls =
          M.fromList
            [ (name', decl { mdName = name', mdSrc = renMode (mdSrc decl), mdTgt = renMode (mdTgt decl) })
            | (name, decl) <- M.toList (mtDecls mt)
            , let name' = renMod name
            ]
      , mtEqns =
          [ ModEqn
              { meLHS = renExpr (meLHS eqn)
              , meRHS = renExpr (meRHS eqn)
              }
          | eqn <- mtEqns mt
          ]
      , mtTransforms =
          M.fromList
            [ (renTransform name, decl { mtdName = renTransform name, mtdFrom = renExpr (mtdFrom decl), mtdTo = renExpr (mtdTo decl) })
            | (name, decl) <- M.toList (mtTransforms mt)
            ]
      }
  where
    renMode mode = M.findWithDefault mode mode modeRen
    renMod name = M.findWithDefault name name modRen
    renTransform (ModTransformName t) = ModTransformName t
    renExpr me =
      me
        { meSrc = renMode (meSrc me)
        , meTgt = renMode (meTgt me)
        , mePath = map renMod (mePath me)
        }

renameTypeSig
  :: Map ModeName ModeName
  -> Map ModName ModName
  -> Map TypeRef TypeRef
  -> TypeSig
  -> Either Text TypeSig
renameTypeSig modeRen modRen typeRen sig =
  TypeSig <$> mapM renParam (tsParams sig)
  where
    renParam p =
      case p of
        PS_Ty mode -> Right (PS_Ty (M.findWithDefault mode mode modeRen))
        PS_Tm ty -> PS_Tm <$> renameTypeExpr modeRen modRen typeRen ty

renameGenDecl
  :: Map ModeName ModeName
  -> Map ModName ModName
  -> Map TypeRef TypeRef
  -> Map AttrSort AttrSort
  -> Map (ModeName, GenName) GenName
  -> GenDecl
  -> Either Text GenDecl
renameGenDecl modeRen modRen typeRen sortRen genRen gen = do
  let mode0 = gdMode gen
  tyVars' <- mapM renTyVar (gdTyVars gen)
  tmVars' <- mapM renTmVar (gdTmVars gen)
  dom' <- mapM renInput (gdDom gen)
  cod' <- mapM (renameTypeExpr modeRen modRen typeRen) (gdCod gen)
  let attrs' = [ (field, M.findWithDefault sortName sortName sortRen) | (field, sortName) <- gdAttrs gen ]
  let genName' = M.findWithDefault (gdName gen) (mode0, gdName gen) genRen
  pure
    gen
      { gdName = genName'
      , gdMode = M.findWithDefault mode0 mode0 modeRen
      , gdTyVars = tyVars'
      , gdTmVars = tmVars'
      , gdDom = dom'
      , gdCod = cod'
      , gdAttrs = attrs'
      }
  where
    renTyVar tv = Right tv { tvMode = M.findWithDefault (tvMode tv) (tvMode tv) modeRen }
    renTmVar tm = do
      sort' <- renameTypeExpr modeRen modRen typeRen (tmvSort tm)
      Right tm { tmvSort = sort' }
    renInput shape =
      case shape of
        InPort ty -> InPort <$> renameTypeExpr modeRen modRen typeRen ty
        InBinder bs -> do
          tmCtx' <- mapM (renameTypeExpr modeRen modRen typeRen) (bsTmCtx bs)
          dom' <- mapM (renameTypeExpr modeRen modRen typeRen) (bsDom bs)
          cod' <- mapM (renameTypeExpr modeRen modRen typeRen) (bsCod bs)
          Right (InBinder bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' })

renameTypeExpr
  :: Map ModeName ModeName
  -> Map ModName ModName
  -> Map TypeRef TypeRef
  -> TypeExpr
  -> Either Text TypeExpr
renameTypeExpr modeRen modRen typeRen ty =
  case ty of
    TVar tv ->
      Right (TVar tv { tvMode = M.findWithDefault (tvMode tv) (tvMode tv) modeRen })
    TMod me inner -> do
      inner' <- renameTypeExpr modeRen modRen typeRen inner
      pure
        ( TMod
            me
              { meSrc = M.findWithDefault (meSrc me) (meSrc me) modeRen
              , meTgt = M.findWithDefault (meTgt me) (meTgt me) modeRen
              , mePath = map (\m -> M.findWithDefault m m modRen) (mePath me)
              }
            inner'
        )
    TCon ref args -> do
      args' <- mapM renArg args
      let ref' = M.findWithDefault ref ref typeRen
      pure (TCon ref' args')
  where
    renArg arg =
      case arg of
        TAType t -> TAType <$> renameTypeExpr modeRen modRen typeRen t
        TATm tm -> TATm <$> renameTermDiagram modeRen modRen typeRen tm

renameTermDiagram
  :: Map ModeName ModeName
  -> Map ModName ModName
  -> Map TypeRef TypeRef
  -> TermDiagram
  -> Either Text TermDiagram
renameTermDiagram modeRen modRen typeRen (TermDiagram diag) = do
  tmCtx' <- mapM (renameTypeExpr modeRen modRen typeRen) (dTmCtx diag)
  portTy' <- mapM (renameTypeExpr modeRen modRen typeRen) (dPortTy diag)
  edges' <- mapM renEdge (dEdges diag)
  pure
    ( TermDiagram
        diag
          { dMode = M.findWithDefault (dMode diag) (dMode diag) modeRen
          , dTmCtx = tmCtx'
          , dPortTy = portTy'
          , dEdges = edges'
          }
    )
  where
    renEdge edge =
      case ePayload edge of
        PTmMeta tm -> do
          sort' <- renameTypeExpr modeRen modRen typeRen (tmvSort tm)
          pure edge { ePayload = PTmMeta tm { tmvSort = sort' } }
        _ -> pure edge


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
  mt0 <- addMode mode emptyModeTheory
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
            , gdTmVars = []
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
      , dModes = mt0
      , dAcyclicModes = S.singleton mode
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
      , dActions = M.empty
      , dObligations = []
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
    , PolyMorph.morCheck = PolyMorph.CheckNone
    , PolyMorph.morPolicy = UseStructuralAsBidirectional
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


buildPolyFromBase :: SearchBudget -> Text -> Text -> ModuleEnv -> Doctrine -> Either Text (PolyMorph.Morphism, Int)
buildPolyFromBase budget baseName newName env newDoc = do
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
