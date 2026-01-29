{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  , elabPresentation
  ) where

import Strat.Kernel.DSL.AST
import Strat.Poly.DSL.AST (RawPolyDoctrine(..))
import Strat.Kernel.Presentation
import Strat.Kernel.Presentation.Rename (qualifyPresentation)
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Term
import Strat.Kernel.Syntax
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Kernel.Subst (applySubstSort)
import Strat.Kernel.AlphaEq
import Strat.Kernel.Pushout
import Strat.Kernel.Morphism.Util (symbolMapMorphism)
import Strat.Syntax.Spec
import Strat.Model.Spec
import Strat.Frontend.Env (ModuleEnv(..), SyntaxDef)
import qualified Strat.Frontend.Env as Env
import Strat.Frontend.RunSpec
import Strat.Poly.DSL.Elab (elabPolyDoctrine, elabPolyRun, elabPolyMorphism)
import Strat.Poly.Pushout
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Poly.Diagram (genD)
import Strat.Poly.Surface (elabPolySurfaceDecl)
import Strat.Poly.Surface.Spec (ssDoctrine)
import Strat.Poly.RunSpec (PolyRunSpec)
import Strat.Surface2.Elab
import Strat.Surface2.SyntaxSpec
import Strat.Kernel.Morphism
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM)


type VarEnv = M.Map Text (Var, Sort)

elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile = elabRawFileWithEnv Env.emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv baseEnv (RawFile decls) = do
  (env, rawRuns, rawPolyRuns) <- foldM step (baseEnv, [], []) decls
  runs <- elabRuns env rawRuns
  polyRuns <- elabPolyRuns env rawPolyRuns
  pure env { meRuns = runs, mePolyRuns = polyRuns }
  where
    step (env, rawRuns, rawPolyRuns) decl =
      case decl of
        DeclImport _ -> Right (env, rawRuns, rawPolyRuns)
        DeclDoctrineWhere name mExt items -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          rawPres <- case mExt of
            Nothing -> elabPresentation name items
            Just base -> do
              baseRaw <- lookupRawDoctrine env base
              elabPresentationWith name baseRaw items
          pres <- qualifyPresentation name rawPres
          case validatePresentation pres of
            Left err -> Left ("Presentation invalid: " <> err)
            Right () -> do
              env' <- case mExt of
                Nothing -> Right env
                Just base -> do
                  mor <- buildFromBase base name env pres
                  pure env { meMorphisms = M.insert (morName mor) mor (meMorphisms env) }
              let env'' = env'
                    { meDoctrines = M.insert name pres (meDoctrines env')
                    , meRawDoctrines = M.insert name rawPres (meRawDoctrines env')
                    }
              pure (env'', rawRuns, rawPolyRuns)
        DeclDoctrinePushout name leftMor rightMor -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          f <- lookupMorphism env leftMor
          g <- lookupMorphism env rightMor
          PushoutResult pres inl inr glue <- computePushout name f g
          ensureAbsent "morphism" (morName inl) (meMorphisms env)
          ensureAbsent "morphism" (morName inr) (meMorphisms env)
          ensureAbsent "morphism" (morName glue) (meMorphisms env)
          let env' = env
                { meDoctrines = M.insert name pres (meDoctrines env)
                , meRawDoctrines = M.insert name pres (meRawDoctrines env)
                , meMorphisms =
                    M.insert (morName glue) glue
                  (M.insert (morName inl) inl
                  (M.insert (morName inr) inr (meMorphisms env)))
                }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolyDoctrine polyDecl -> do
          let name = rpdName polyDecl
          ensureAbsent "polydoctrine" name (mePolyDoctrines env)
          doc <- elabPolyDoctrine env polyDecl
          env' <- case rpdExtends polyDecl of
            Nothing -> Right env
            Just base -> do
              mor <- buildPolyFromBase base name env doc
              pure env { mePolyMorphisms = M.insert (PolyMorph.morName mor) mor (mePolyMorphisms env) }
          let env'' = env' { mePolyDoctrines = M.insert name doc (mePolyDoctrines env') }
          pure (env'', rawRuns, rawPolyRuns)
        DeclPolyDoctrinePushout name leftMor rightMor -> do
          ensureAbsent "polydoctrine" name (mePolyDoctrines env)
          f <- lookupPolyMorphism env leftMor
          g <- lookupPolyMorphism env rightMor
          PolyPushoutResult doc inl inr glue <- computePolyPushout name f g
          ensureAbsent "polymorphism" (PolyMorph.morName inl) (mePolyMorphisms env)
          ensureAbsent "polymorphism" (PolyMorph.morName inr) (mePolyMorphisms env)
          ensureAbsent "polymorphism" (PolyMorph.morName glue) (mePolyMorphisms env)
          let env' = env
                { mePolyDoctrines = M.insert name doc (mePolyDoctrines env)
                , mePolyMorphisms =
                    M.insert (PolyMorph.morName glue) glue
                    (M.insert (PolyMorph.morName inl) inl
                    (M.insert (PolyMorph.morName inr) inr (mePolyMorphisms env)))
                }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolyDoctrineCoproduct name leftDoc rightDoc -> do
          ensureAbsent "polydoctrine" name (mePolyDoctrines env)
          left <- lookupPolyDoctrine env leftDoc
          right <- lookupPolyDoctrine env rightDoc
          PolyPushoutResult doc inl inr glue <- computePolyCoproduct name left right
          ensureAbsent "polymorphism" (PolyMorph.morName inl) (mePolyMorphisms env)
          ensureAbsent "polymorphism" (PolyMorph.morName inr) (mePolyMorphisms env)
          ensureAbsent "polymorphism" (PolyMorph.morName glue) (mePolyMorphisms env)
          let env' = env
                { mePolyDoctrines = M.insert name doc (mePolyDoctrines env)
                , mePolyMorphisms =
                    M.insert (PolyMorph.morName glue) glue
                    (M.insert (PolyMorph.morName inl) inl
                    (M.insert (PolyMorph.morName inr) inr (mePolyMorphisms env)))
                }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolySurface surfDecl -> do
          let name = rpsName surfDecl
          ensureAbsent "polysurface" name (mePolySurfaces env)
          let spec = rpsSpec surfDecl
          doc <- case M.lookup (ssDoctrine spec) (mePolyDoctrines env) of
            Nothing -> Left ("Unknown polydoctrine: " <> ssDoctrine spec)
            Just d -> Right d
          def <- elabPolySurfaceDecl name doc spec
          let env' = env { mePolySurfaces = M.insert name def (mePolySurfaces env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclSyntaxWhere decl -> do
          let name = rsnName decl
          ensureAbsent "syntax" name (meSyntaxes env)
          spec <- elabSyntaxDecl decl
          let env' = env { meSyntaxes = M.insert name spec (meSyntaxes env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclModelWhere name doc items -> do
          ensureAbsent "model" name (meModels env)
          spec <- elabModelSpec name items
          _ <- lookupDoctrine env doc
          let env' = env { meModels = M.insert name (doc, spec) (meModels env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolyModelWhere name doc items -> do
          ensureAbsent "polymodel" name (mePolyModels env)
          spec <- elabModelSpec name items
          _ <- lookupPolyDoctrine env doc
          let env' = env { mePolyModels = M.insert name (doc, spec) (mePolyModels env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclSurfaceWhere surfDecl -> do
          let name = rsdName surfDecl
          ensureAbsent "surface" name (meSurfaces env)
          def <- elabSurfaceDecl (resolveDoctrine env) surfDecl
          let env' = env { meSurfaces = M.insert name def (meSurfaces env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclMorphismWhere morphDecl -> do
          let name = rmdName morphDecl
          ensureAbsent "morphism" name (meMorphisms env)
          morph <- elabMorphismDecl env morphDecl
          let env' = env { meMorphisms = M.insert name morph (meMorphisms env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolyMorphism morphDecl -> do
          let name = rpmName morphDecl
          ensureAbsent "polymorphism" name (mePolyMorphisms env)
          morph <- elabPolyMorphism env morphDecl
          let env' = env { mePolyMorphisms = M.insert name morph (mePolyMorphisms env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclImplements implDecl -> do
          (key, morphName) <- elabImplements env implDecl
          let defaults = M.findWithDefault [] key (meImplDefaults env)
          let defaults' = if morphName `elem` defaults then defaults else defaults <> [morphName]
          let env' = env { meImplDefaults = M.insert key defaults' (meImplDefaults env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolyImplements implDecl -> do
          (key, morphName) <- elabPolyImplements env implDecl
          let defaults = M.findWithDefault [] key (mePolyImplDefaults env)
          let defaults' = if morphName `elem` defaults then defaults else defaults <> [morphName]
          let env' = env { mePolyImplDefaults = M.insert key defaults' (mePolyImplDefaults env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclRunSpec name rawSpec -> do
          ensureAbsent "run_spec" name (meRunSpecs env)
          let env' = env { meRunSpecs = M.insert name (rrsRun rawSpec) (meRunSpecs env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclPolyRunSpec name rawSpec -> do
          ensureAbsent "polyrun_spec" name (mePolyRunSpecs env)
          let env' = env { mePolyRunSpecs = M.insert name (rprsPolyRun rawSpec) (mePolyRunSpecs env) }
          pure (env', rawRuns, rawPolyRuns)
        DeclRun rawNamed ->
          pure (env, rawRuns <> [rawNamed], rawPolyRuns)
        DeclPolyRun polyRun ->
          pure (env, rawRuns, rawPolyRuns <> [polyRun])

ensureAbsent :: Text -> Text -> M.Map Text v -> Either Text ()
ensureAbsent label name mp =
  if M.member name mp
    then Left ("Duplicate " <> label <> " name: " <> name)
    else Right ()

lookupDoctrine :: ModuleEnv -> Text -> Either Text Presentation
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just pres -> Right pres

lookupRawDoctrine :: ModuleEnv -> Text -> Either Text Presentation
lookupRawDoctrine env name =
  case M.lookup name (meRawDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just pres -> Right pres

resolveDoctrine :: ModuleEnv -> Text -> Either Text Presentation
resolveDoctrine env = lookupDoctrine env

lookupMorphism :: ModuleEnv -> Text -> Either Text Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just mor -> Right mor

lookupPolyDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupPolyDoctrine env name =
  case M.lookup name (mePolyDoctrines env) of
    Nothing -> Left ("Unknown polydoctrine: " <> name)
    Just doc -> Right doc

lookupPolyMorphism :: ModuleEnv -> Text -> Either Text PolyMorph.Morphism
lookupPolyMorphism env name =
  case M.lookup name (mePolyMorphisms env) of
    Nothing -> Left ("Unknown polymorphism: " <> name)
    Just mor -> Right mor

buildPolyFromBase :: Text -> Text -> ModuleEnv -> Doctrine -> Either Text PolyMorph.Morphism
buildPolyFromBase baseName newName env newDoc = do
  baseDoc <- lookupPolyDoctrine env baseName
  ensureAbsent "polymorphism" morName (mePolyMorphisms env)
  genMap <- fmap M.fromList (mapM genImage (allPolyGens baseDoc))
  let mor = PolyMorph.Morphism
        { PolyMorph.morName = morName
        , PolyMorph.morSrc = baseDoc
        , PolyMorph.morTgt = newDoc
        , PolyMorph.morTypeMap = M.empty
        , PolyMorph.morGenMap = genMap
        , PolyMorph.morPolicy = UseStructuralAsBidirectional
        , PolyMorph.morFuel = 50
        }
  case PolyMorph.checkMorphism mor of
    Left err -> Left ("generated polymorphism " <> morName <> " invalid: " <> err)
    Right () -> Right mor
  where
    morName = newName <> ".fromBase"
    allPolyGens doc =
      [ (mode, gen)
      | (mode, table) <- M.toList (dGens doc)
      , gen <- M.elems table
      ]
    genImage (mode, gen) = do
      img <- genD mode (gdDom gen) (gdCod gen) (gdName gen)
      pure ((mode, gdName gen), img)

buildFromBase :: Text -> Text -> ModuleEnv -> Presentation -> Either Text Morphism
buildFromBase baseName newName env newPres = do
  basePres <- lookupDoctrine env baseName
  ensureAbsent "morphism" morName (meMorphisms env)
  let sortMap = M.fromList [ (s, requalifySortName baseName newName s) | s <- M.keys (sigSortCtors (presSig basePres)) ]
  let opMap = M.fromList [ (o, requalifyOpName baseName newName o) | o <- M.keys (sigOps (presSig basePres)) ]
  mor <- symbolMapMorphism basePres newPres sortMap opMap
  let mor' = mor { morName = morName }
  case checkMorphism (mcPolicy (morCheck mor')) (mcFuel (morCheck mor')) mor' of
    Left err -> Left ("generated morphism " <> morName <> " invalid: " <> renderMorphismError err)
    Right () -> Right mor'
  where
    morName = newName <> ".fromBase"

requalifySortName :: Text -> Text -> SortName -> SortName
requalifySortName baseName newName (SortName t) =
  SortName (requalifyName baseName newName t)

requalifyOpName :: Text -> Text -> OpName -> OpName
requalifyOpName baseName newName (OpName t) =
  OpName (requalifyName baseName newName t)

requalifyName :: Text -> Text -> Text -> Text
requalifyName baseName newName t =
  case T.stripPrefix (baseName <> ".") t of
    Just rest -> newName <> "." <> rest
    Nothing -> newName <> "." <> t

elabPresentation :: Text -> [RawItem] -> Either Text Presentation
elabPresentation name items =
  elabPresentationWith name (Presentation name (Signature M.empty M.empty) []) items

elabPresentationWith :: Text -> Presentation -> [RawItem] -> Either Text Presentation
elabPresentationWith name base items = do
  (eqMap0, eqs0) <- foldM insertEq (M.empty, []) (presEqs base)
  (sig, _, eqs) <- foldM step (presSig base, eqMap0, eqs0) items
  pure Presentation { presName = name, presSig = sig, presEqs = eqs }
  where
    step (sig, eqMap, eqs) item =
      case item of
        ItemSort decl -> do
          sig' <- addSortDecl sig decl
          pure (sig', eqMap, eqs)
        ItemOp decl -> do
          sig' <- addOpDecl sig decl
          pure (sig', eqMap, eqs)
        ItemRule rr -> do
          eq <- elabRule sig rr
          (eqMap', eqs') <- insertEq (eqMap, eqs) eq
          pure (sig, eqMap', eqs')

addSortDecl :: Signature -> RawSortDecl -> Either Text Signature
addSortDecl sig decl = do
  let name = SortName (rsName decl)
  if M.member name (sigSortCtors sig)
    then Left ("Duplicate sort ctor: " <> rsName decl)
    else do
      let scope = ScopeId ("sort:" <> rsName decl)
      (tele, _) <- elabBinders sig scope (rsTele decl)
      let ctor = SortCtor { scName = name, scTele = tele }
      pure sig { sigSortCtors = M.insert name ctor (sigSortCtors sig) }

addOpDecl :: Signature -> RawOpDecl -> Either Text Signature
addOpDecl sig decl = do
  let name = OpName (roName decl)
  if M.member name (sigOps sig)
    then Left ("Duplicate op: " <> roName decl)
    else do
      let scope = ScopeId ("op:" <> roName decl)
      (tele, env) <- elabBinders sig scope (roTele decl)
      res <- elabSort sig env (roResult decl)
      let opDecl = OpDecl { opName = name, opTele = tele, opResult = res }
      pure sig { sigOps = M.insert name opDecl (sigOps sig) }

elabRule :: Signature -> RawRule -> Either Text Equation
elabRule sig rr = do
  let scope = ScopeId ("eq:" <> rrName rr)
  (tele, env) <- elabBinders sig scope (rrTele rr)
  lhsTerm <- elabTerm sig env (rrLHS rr)
  rhsTerm <- elabTerm sig env (rrRHS rr)
  pure Equation
    { eqName = rrName rr
    , eqClass = rrClass rr
    , eqOrient = rrOrient rr
    , eqTele = tele
    , eqLHS = lhsTerm
    , eqRHS = rhsTerm
    }

elabSyntaxDecl :: RawSyntaxDecl -> Either Text SyntaxDef
elabSyntaxDecl decl =
  case rsnTarget decl of
    SyntaxDoctrine -> do
      let coreItems = [ i | i <- rsnItems decl, isCoreItem i ]
      if length coreItems /= length (rsnItems decl)
        then Left "surface syntax items not allowed in doctrine syntax"
        else do
          spec <- elabSyntaxSpec (rsnName decl) coreItems
          pure (Env.SyntaxDoctrine spec)
    SyntaxSurface surfName -> do
      let surfItems = [ i | i <- rsnItems decl, isSurfaceItem i ]
      if length surfItems /= length (rsnItems decl)
        then Left "doctrine syntax items not allowed in surface syntax"
        else do
          spec <- elabSurfaceSyntaxSpec (rsnName decl) surfName surfItems
          pure (Env.SyntaxSurface spec)
  where
    isCoreItem item =
      case item of
        RSPrint _ -> True
        RSParse _ -> True
        RSAllowCall -> True
        RSVarPrefix _ -> True
        _ -> False

    isSurfaceItem item =
      case item of
        RSTy _ -> True
        RSTm _ -> True
        _ -> False

elabBinders :: Signature -> ScopeId -> [RawBinder] -> Either Text ([Binder], VarEnv)
elabBinders sig scope binders =
  foldM step ([], M.empty, 0) binders >>= \(bs, env, _) -> pure (bs, env)
  where
    step (acc, env, ix) (RawBinder name sRaw) = do
      if M.member name env
        then Left ("Duplicate binder name: " <> name)
        else do
          let v = Var scope ix
          s <- elabSort sig env sRaw
          let env' = M.insert name (v, s) env
          pure (acc <> [Binder v s], env', ix + 1)

elabTerm :: Signature -> VarEnv -> RawTerm -> Either Text Term
elabTerm sig env tm =
  case tm of
    RVar v ->
      case M.lookup v env of
        Nothing -> Left ("Unknown variable: " <> v)
        Just (var, s) -> Right (mkVar s var)
    RApp name args -> do
      args' <- mapM (elabTerm sig env) args
      case mkOp sig (OpName name) args' of
        Left err -> Left (renderTypeError err)
        Right t -> Right t

elabSort :: Signature -> VarEnv -> RawSort -> Either Text Sort
elabSort sig env (RawSort name idx) = do
  idxTerms <- mapM (elabTerm sig env) idx
  case mkSort sig (SortName name) idxTerms of
    Left err -> Left (renderSortError err)
    Right s -> Right s

type EqAcc = (M.Map Text Equation, [Equation])

insertEq :: EqAcc -> Equation -> Either Text EqAcc
insertEq (eqMap, eqs) eq =
  case M.lookup (eqName eq) eqMap of
    Nothing -> Right (M.insert (eqName eq) eq eqMap, eqs <> [eq])
    Just existing ->
      if alphaEqEquation existing eq
        then Right (eqMap, eqs)
        else Left ("Duplicate equation name: " <> eqName eq)

renderSortName :: SortName -> Text
renderSortName (SortName t) = t

renderOpName :: OpName -> Text
renderOpName (OpName t) = t

resolveSortNameIn :: Presentation -> Text -> Either Text SortName
resolveSortNameIn pres name =
  let direct = SortName name
      pref = SortName (presName pres <> "." <> name)
      sig = presSig pres
  in if M.member direct (sigSortCtors sig)
      then Right direct
      else if M.member pref (sigSortCtors sig)
        then Right pref
        else Left ("Unknown sort name: " <> name)

resolveOpNameIn :: Presentation -> Text -> Either Text OpName
resolveOpNameIn pres name =
  let direct = OpName name
      pref = OpName (presName pres <> "." <> name)
      sig = presSig pres
  in if M.member direct (sigOps sig)
      then Right direct
      else if M.member pref (sigOps sig)
        then Right pref
        else Left ("Unknown op name: " <> name)

elabMorphismDecl :: ModuleEnv -> RawMorphismDecl -> Either Text Morphism
elabMorphismDecl env decl = do
  srcPres <- lookupDoctrine env (rmdSrc decl)
  tgtPres <- lookupDoctrine env (rmdTgt decl)
  sortMap <- buildSortMap srcPres tgtPres (rmdItems decl)
  opMap <- buildOpInterps (rmdName decl) srcPres tgtPres sortMap (rmdItems decl)
  checkCfg <- resolveCheck (rmdCheck decl)
  let mor = Morphism
        { morName = rmdName decl
        , morSrc = srcPres
        , morTgt = tgtPres
        , morSortMap = sortMap
        , morOpMap = opMap
        , morCheck = checkCfg
        }
  case checkMorphism (mcPolicy checkCfg) (mcFuel checkCfg) mor of
    Left err -> Left (renderMorphismError err)
    Right () -> Right mor
  where
    resolveCheck mcheck = do
      let policyName = maybe "UseStructuralAsBidirectional" id (mcheck >>= rmcPolicy)
      policy <- parsePolicy policyName
      let fuel = maybe 200 id (mcheck >>= rmcFuel)
      pure MorphismCheck { mcPolicy = policy, mcFuel = fuel }

buildSortMap :: Presentation -> Presentation -> [RawMorphismItem] -> Either Text (M.Map SortName SortName)
buildSortMap src tgt items = do
  explicit <- mapM (resolveSortPair src tgt) [ (s, t) | RMISort s t <- items ]
  ensureNoDup "sort mapping" (map fst explicit)
  mapM_ (checkSrcSort src) (map fst explicit)
  mapM_ (checkTgtSort tgt) (map snd explicit)
  foldM (fillSort tgt) (M.fromList explicit) (M.keys (sigSortCtors (presSig src)))
  where
    resolveSortPair presSrc presTgt (s, t) = do
      s' <- resolveSortNameIn presSrc s
      t' <- resolveSortNameIn presTgt t
      pure (s', t')
    checkSrcSort pres name =
      if M.member name (sigSortCtors (presSig pres))
        then Right ()
        else Left ("Unknown source sort in morphism: " <> renderSortName name)
    checkTgtSort pres name =
      if M.member name (sigSortCtors (presSig pres))
        then Right ()
        else Left ("Unknown target sort in morphism: " <> renderSortName name)
    fillSort pres acc name =
      if M.member name acc
        then Right acc
        else if M.member name (sigSortCtors (presSig pres))
          then Right (M.insert name name acc)
          else Left ("Missing sort mapping: " <> renderSortName name)

buildOpInterps :: Text -> Presentation -> Presentation -> M.Map SortName SortName -> [RawMorphismItem] -> Either Text (M.Map OpName OpInterp)
buildOpInterps morName src tgt sortMap items = do
  explicit <- mapM (resolveOpItem src) [ i | i@RMIOp{} <- items ]
  ensureNoDup "op mapping" (map fst explicit)
  let explicitMap = M.fromList explicit
  let srcOps = M.keys (sigOps (presSig src))
  let deps = M.fromList [ (op, opDeps (sigOps (presSig src) M.! op)) | op <- srcOps ]
  order <- topoSortOps (S.fromList srcOps) deps
  foldM (buildOne explicitMap) M.empty order
  where
    resolveOpItem pres item = do
      opName <- resolveOpNameIn pres (rmiSrcOp item)
      pure (opName, item)

    buildOne explicitMap acc opName = do
      let decl = sigOps (presSig src) M.! opName
      item <- case M.lookup opName explicitMap of
        Just it -> Right it
        Nothing ->
          let opText = renderOpName opName
          in Right RMIOp { rmiSrcOp = opText, rmiParams = Nothing, rmiRhs = RApp opText [] }
      interp <- elabOpInterp morName src tgt sortMap acc decl item
      pure (M.insert opName interp acc)

    opDeps decl =
      let fromBinder b = opsInSort (bSort b)
      in S.unions (map fromBinder (opTele decl) <> [opsInSort (opResult decl)])

    topoSortOps opSet deps =
      let deps' = M.map (`S.intersection` opSet) deps
      in go deps' []
      where
        go remaining acc
          | M.null remaining = Right (reverse acc)
          | otherwise =
              case [ n | (n, ds) <- M.toList remaining, S.null (S.intersection ds (M.keysSet remaining)) ] of
                [] -> Left ("Cyclic op dependency in morphism: " <> T.intercalate ", " (map renderOpName (M.keys remaining)))
                (n:_) -> go (M.delete n remaining) (n:acc)

elabOpInterp
  :: Text
  -> Presentation
  -> Presentation
  -> M.Map SortName SortName
  -> M.Map OpName OpInterp
  -> OpDecl
  -> RawMorphismItem
  -> Either Text OpInterp
elabOpInterp morName src tgt sortMap opMapKnown decl item = do
  let teleSrc = opTele decl
  let arity = length teleSrc
  let rhsVars = rawTermVars (rmiRhs item)
  paramNames <- case rmiParams item of
    Just names ->
      if length names /= arity
        then Left ("Morphism op mapping arity mismatch for " <> renderOpName (opName decl))
        else if hasDup names
          then Left ("Duplicate parameter name in op mapping for " <> renderOpName (opName decl))
          else Right names
    Nothing ->
      if not (S.null rhsVars)
        then Left ("Morphism op mapping for " <> renderOpName (opName decl) <> " uses variables; provide parameter list")
        else Right [ "x" <> T.pack (show i) | i <- [0 .. arity - 1] ]
  let rhsRaw0 =
        case (rmiParams item, rmiRhs item, arity) of
          (Nothing, RApp name [], n) | n > 0 -> RApp name (map RVar paramNames)
          _ -> rmiRhs item
  rhsRaw1 <- qualifyRawTerm tgt rhsRaw0
  (teleTgt, subst) <- buildTele morName (opName decl) sortMap opMapKnown teleSrc
  let env = M.fromList [ (n, (v, bSort b)) | (n, b@(Binder v _)) <- zip paramNames teleTgt ]
  rhsTerm <- elabTerm (presSig tgt) env rhsRaw1
  resSort <- applySubstSort subst <$> applyMorphismSortPartial sortMap opMapKnown (opResult decl)
  if termSort rhsTerm /= resSort
    then Left ("Morphism op mapping for " <> renderOpName (opName decl) <> " has wrong result sort")
    else Right OpInterp { oiTele = teleTgt, oiRhs = rhsTerm }
  where
    hasDup xs = case findDup xs of
      Nothing -> False
      Just _ -> True
    findDup = go M.empty
    go _ [] = Nothing
    go seen (x:rest)
      | M.member x seen = Just x
      | otherwise = go (M.insert x () seen) rest

buildTele
  :: Text
  -> OpName
  -> M.Map SortName SortName
  -> M.Map OpName OpInterp
  -> [Binder]
  -> Either Text ([Binder], M.Map Var Term)
buildTele morName opName0 sortMap opMap teleSrc =
  foldM step ([], M.empty, 0) teleSrc >>= \(tele, subst, _) -> Right (tele, subst)
  where
    scope = ScopeId ("mor:" <> morName <> ":" <> renderOpName opName0)
    step (acc, subst, ix) (Binder v s) = do
      s0 <- applyMorphismSortPartial sortMap opMap s
      let s1 = applySubstSort subst s0
      let v' = Var scope ix
      let b' = Binder v' s1
      let subst' = M.insert v (mkVar s1 v') subst
      pure (acc <> [b'], subst', ix + 1)

applyMorphismSortPartial
  :: M.Map SortName SortName
  -> M.Map OpName OpInterp
  -> Sort
  -> Either Text Sort
applyMorphismSortPartial sortMap opMap (Sort name idx) = do
  let name' = M.findWithDefault name name sortMap
  idx' <- mapM (applyMorphismTermPartial sortMap opMap) idx
  pure (Sort name' idx')

applyMorphismTermPartial
  :: M.Map SortName SortName
  -> M.Map OpName OpInterp
  -> Term
  -> Either Text Term
applyMorphismTermPartial sortMap opMap tm =
  case termNode tm of
    TVar v -> do
      s' <- applyMorphismSortPartial sortMap opMap (termSort tm)
      pure Term { termSort = s', termNode = TVar v }
    TOp op args -> do
      args' <- mapM (applyMorphismTermPartial sortMap opMap) args
      case M.lookup op opMap of
        Nothing -> Left ("Morphism op dependency missing: " <> renderOpName op)
        Just interp -> Right (applyOpInterp interp args')

qualifyRawTerm :: Presentation -> RawTerm -> Either Text RawTerm
qualifyRawTerm pres tm =
  case tm of
    RVar v -> Right (RVar v)
    RApp name args -> do
      op <- resolveOpNameIn pres name
      args' <- mapM (qualifyRawTerm pres) args
      pure (RApp (renderOpName op) args')

rawTermVars :: RawTerm -> S.Set Text
rawTermVars tm =
  case tm of
    RVar v -> S.singleton v
    RApp _ args -> S.unions (map rawTermVars args)

opsInSort :: Sort -> S.Set OpName
opsInSort (Sort _ idx) = S.unions (map opsInTerm idx)

opsInTerm :: Term -> S.Set OpName
opsInTerm tm =
  let fromSort = opsInSort (termSort tm)
  in case termNode tm of
      TVar _ -> fromSort
      TOp op args -> S.insert op (S.unions (fromSort : map opsInTerm args))

ensureNoDup :: Ord a => Text -> [a] -> Either Text ()
ensureNoDup label xs =
  case findDup xs of
    Nothing -> Right ()
    Just _ -> Left ("Duplicate " <> label)
  where
    findDup = go M.empty
    go _ [] = Nothing
    go seen (x:rest)
      | M.member x seen = Just x
      | otherwise = go (M.insert x () seen) rest

renderMorphismError :: MorphismError -> Text
renderMorphismError = T.pack . show

elabSyntaxSpec :: Text -> [RawSyntaxItem] -> Either Text SyntaxSpec
elabSyntaxSpec name items =
  foldM step initial items
  where
    initial = SyntaxSpec
      { ssName = name
      , ssNotations = []
      , ssAllowCall = False
      , ssVarPrefix = "?"
      , ssAllowQualId = True
      }

    step spec item =
      case item of
        RSAllowCall -> pure spec { ssAllowCall = True }
        RSVarPrefix pfx -> pure spec { ssVarPrefix = pfx }
        RSPrint note -> pure spec { ssNotations = ssNotations spec <> [toNotation True note] }
        RSParse note -> pure spec { ssNotations = ssNotations spec <> [toNotation False note] }
        RSTy _ -> Left "ty notation not allowed in doctrine syntax"
        RSTm _ -> Left "tm notation not allowed in doctrine syntax"

    toNotation printable note =
      case note of
        RNAtom tok op -> NotationSpec NAtom tok op printable
        RNPrefix prec tok op -> NotationSpec (NPrefix prec) tok op printable
        RNPostfix prec tok op -> NotationSpec (NPostfix prec) tok op printable
        RNInfix assoc prec tok op -> NotationSpec (NInfix (toAssoc assoc) prec) tok op printable

    toAssoc a =
      case a of
        AssocL -> LeftAssoc
        AssocR -> RightAssoc
        AssocN -> NonAssoc

elabSurfaceSyntaxSpec :: Text -> Text -> [RawSyntaxItem] -> Either Text SurfaceSyntaxSpec
elabSurfaceSyntaxSpec name surfName items = do
  let tyNotes = [ n | RSTy n <- items ]
  let tmNotes = [ n | RSTm n <- items ]
  if null tyNotes && null tmNotes
    then Left "surface syntax requires ty/tm notations"
    else Right ()
  pure SurfaceSyntaxSpec
    { sssName = name
    , sssSurface = surfName
    , sssTyNotations = map elabSurfaceNote tyNotes
    , sssTmNotations = map elabSurfaceNote tmNotes
    }
  where
    elabSurfaceNote note =
      case note of
        RSNAtom tok con -> SAtom tok con
        RSNPrefix tok con -> SPrefix tok con
        RSNInfix assoc prec tok con -> SInfix (toAssoc assoc) prec tok con
        RSNBinder tok tySep bodySep con -> SBinder tok tySep bodySep con
        RSNApp con -> SApp con
        RSNTuple tok con -> STuple tok con

    toAssoc a =
      case a of
        SurfAssocL -> SLeft
        SurfAssocR -> SRight
        SurfAssocN -> SNon

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

elabRun :: RawRun -> Either Text RunSpec
elabRun raw = do
  doctrine <- maybe (Left "run: missing doctrine") Right (rrDoctrine raw)
  model <- maybe (Right "Symbolic") Right (rrModel raw)
  policy <- maybe (Right UseOnlyComputationalLR) parsePolicy (rrPolicy raw)
  let fuel = maybe 50 id (rrFuel raw)
  let showFlags = if null (rrShowFlags raw) then [ShowNormalized, ShowValue, ShowCat] else map toShow (rrShowFlags raw)
  validateRunFields (rrSurface raw) (rrSurfaceSyntax raw) (rrSyntax raw)
  pure RunSpec
    { runDoctrine = doctrine
    , runSyntax = rrSyntax raw
    , runSurface = rrSurface raw
    , runSurfaceSyntax = rrSurfaceSyntax raw
    , runModel = model
    , runUses = rrUses raw
    , runOpen = rrOpen raw
    , runPolicy = policy
    , runFuel = fuel
    , runShowFlags = showFlags
    , runExprText = rrExprText raw
    }
  where
    toShow s =
      case s of
        RawShowNormalized -> ShowNormalized
        RawShowValue -> ShowValue
        RawShowCat -> ShowCat
        RawShowInput -> ShowInput
        RawShowCoherence -> ShowCoherence

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
            Just specName ->
              case M.lookup specName (meRunSpecs env) of
                Nothing -> Left ("Unknown run_spec: " <> specName)
                Just spec -> Right (Just spec)
          let merged = mergeRawRun base (rnrRun raw)
          spec <- elabRun merged
          pure (M.insert name spec acc)

elabPolyRuns :: ModuleEnv -> [RawPolyNamedRun] -> Either Text (M.Map Text PolyRunSpec)
elabPolyRuns env raws = foldM step M.empty raws
  where
    step acc raw = do
      let name = rprnName raw
      if M.member name acc
        then Left ("Duplicate polyrun name: " <> name)
        else do
          base <- case rprnUsing raw of
            Nothing -> Right Nothing
            Just specName ->
              case M.lookup specName (mePolyRunSpecs env) of
                Nothing -> Left ("Unknown polyrun_spec: " <> specName)
                Just spec -> Right (Just spec)
          let merged = mergeRawPolyRun base (rprnRun raw)
          spec <- elabPolyRun name merged
          pure (M.insert name spec acc)

mergeRawRun :: Maybe RawRun -> RawRun -> RawRun
mergeRawRun base override =
  case base of
    Nothing -> override
    Just b ->
      RawRun
        { rrDoctrine = pick rrDoctrine
        , rrSyntax = pick rrSyntax
        , rrSurface = pick rrSurface
        , rrSurfaceSyntax = pick rrSurfaceSyntax
        , rrModel = pick rrModel
        , rrUses = mergeUses (rrUses b) (rrUses override)
        , rrOpen = rrOpen b <> rrOpen override
        , rrPolicy = pick rrPolicy
        , rrFuel = pick rrFuel
        , rrShowFlags = rrShowFlags b <> rrShowFlags override
        , rrExprText = rrExprText override
        }
      where
        pick f = case f override of
          Just v -> Just v
          Nothing -> f b

mergeRawPolyRun :: Maybe RawPolyRun -> RawPolyRun -> RawPolyRun
mergeRawPolyRun base override =
  case base of
    Nothing -> override
    Just b ->
      RawPolyRun
        { rprDoctrine = pick rprDoctrine
        , rprMode = pick rprMode
        , rprSurface = pick rprSurface
        , rprModel = pick rprModel
        , rprMorphisms = rprMorphisms b <> rprMorphisms override
        , rprUses = rprUses b <> rprUses override
        , rprPolicy = pick rprPolicy
        , rprFuel = pick rprFuel
        , rprShowFlags = rprShowFlags b <> rprShowFlags override
        , rprExprText = rprExprText override
        }
      where
        pick f = case f override of
          Just v -> Just v
          Nothing -> f b

mergeUses :: [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)]
mergeUses base override =
  let baseMap = M.fromList base
      overMap = M.fromList override
  in M.toList (M.union overMap baseMap)

elabImplements :: ModuleEnv -> RawImplementsDecl -> Either Text ((Text, Text), Text)
elabImplements env decl = do
  ifacePres <- lookupDoctrine env (ridInterface decl)
  tgtPres <- lookupDoctrine env (ridTarget decl)
  morph <- case M.lookup (ridMorphism decl) (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> ridMorphism decl)
    Just m -> Right m
  if morSrc morph /= ifacePres
    then Left "Morphism source does not match implements interface"
    else if morTgt morph /= tgtPres
      then Left "Morphism target does not match implements target"
      else Right ((presName ifacePres, presName tgtPres), ridMorphism decl)

elabPolyImplements :: ModuleEnv -> RawPolyImplementsDecl -> Either Text ((Text, Text), Text)
elabPolyImplements env decl = do
  ifaceDoc <- lookupPolyDoctrine env (rpidInterface decl)
  tgtDoc <- lookupPolyDoctrine env (rpidTarget decl)
  morph <- case M.lookup (rpidMorphism decl) (mePolyMorphisms env) of
    Nothing -> Left ("Unknown polymorphism: " <> rpidMorphism decl)
    Just m -> Right m
  if PolyMorph.morSrc morph /= ifaceDoc
    then Left "Polymorphism source does not match polyimplements interface"
    else if PolyMorph.morTgt morph /= tgtDoc
      then Left "Polymorphism target does not match polyimplements target"
      else Right ((rpidInterface decl, rpidTarget decl), rpidMorphism decl)

validateRunFields :: Maybe Text -> Maybe Text -> Maybe Text -> Either Text ()
validateRunFields surf surfSyn syntaxName =
  case surf of
    Nothing ->
      case syntaxName of
        Nothing -> Left "run: missing syntax"
        Just _ -> Right ()
    Just _ -> do
      if surfSyn == Nothing then Left "run: missing surface_syntax" else Right ()

renderTypeError :: TypeError -> Text
renderTypeError = T.pack . show

renderSortError :: SortError -> Text
renderSortError = T.pack . show

parsePolicy :: Text -> Either Text RewritePolicy
parsePolicy name =
  case name of
    "UseOnlyComputationalLR" -> Right UseOnlyComputationalLR
    "UseStructuralAsBidirectional" -> Right UseStructuralAsBidirectional
    "UseAllOriented" -> Right UseAllOriented
    _ -> Left ("Unknown policy: " <> name)
