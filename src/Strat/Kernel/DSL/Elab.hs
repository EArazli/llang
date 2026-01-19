{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  , elabPresentation
  ) where

import Strat.Kernel.DSL.AST
import Strat.Kernel.DoctrineExpr
import Strat.Kernel.Presentation
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Term
import Strat.Kernel.Syntax
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Kernel.Subst (applySubstSort, applySubstTerm)
import Strat.Kernel.AlphaEq
import Strat.Syntax.Spec
import Strat.Model.Spec
import Strat.Frontend.Env (ModuleEnv(..), SyntaxDef)
import qualified Strat.Frontend.Env as Env
import Strat.Frontend.RunSpec
import Strat.Surface2.Elab
import Strat.Surface2.Def
import Strat.Surface2.SyntaxSpec
import Strat.Kernel.Morphism
import Strat.Kernel.Weakening (weakenTermToCtxEither)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM)


data Def = Def
  { defExpr :: DocExpr
  , defRawPresentation :: Maybe Presentation
  }

type DocEnv = M.Map Text Def
type VarEnv = M.Map Text (Var, Sort)

elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile = elabRawFileWithEnv Env.emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv baseEnv (RawFile decls) = do
  let baseDocEnv = docsFromEnv baseEnv
  (docEnv, env, rawRuns) <- foldM step (baseDocEnv, baseEnv, []) decls
  let env' = env { meDoctrines = M.map defExpr docEnv }
  runs <- elabRuns env' rawRuns
  pure env' { meRuns = runs }
  where
    step (docEnv, env, rawRuns) decl =
      case decl of
        DeclImport _ -> Right (docEnv, env, rawRuns)
        DeclWhere name items -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          pres <- elabPresentation docEnv name items
          let def = Def { defExpr = Atom name pres, defRawPresentation = Just pres }
          let docEnv' = M.insert name def docEnv
          pure (docEnv', env
            { meDoctrines = M.insert name (defExpr def) (meDoctrines env)
            , mePresentations = M.insert name pres (mePresentations env)
            }, rawRuns)
        DeclSogatWhere decl -> do
          let name = rsogName decl
          ensureAbsent "doctrine" name (meDoctrines env)
          pres <- elabSogatDecl decl
          let def = Def { defExpr = Atom name pres, defRawPresentation = Just pres }
          let docEnv' = M.insert name def docEnv
          pure (docEnv', env
            { meDoctrines = M.insert name (defExpr def) (meDoctrines env)
            , mePresentations = M.insert name pres (mePresentations env)
            }, rawRuns)
        DeclExpr name expr -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          dexpr <- resolveExpr docEnv expr
          let def = Def { defExpr = dexpr, defRawPresentation = Nothing }
          let docEnv' = M.insert name def docEnv
          pure (docEnv', env { meDoctrines = M.insert name dexpr (meDoctrines env) }, rawRuns)
        DeclSyntaxWhere decl -> do
          let name = rsnName decl
          ensureAbsent "syntax" name (meSyntaxes env)
          spec <- elabSyntaxDecl decl
          let env' = env { meSyntaxes = M.insert name spec (meSyntaxes env) }
          pure (docEnv, env', rawRuns)
        DeclModelWhere name items -> do
          ensureAbsent "model" name (meModels env)
          spec <- elabModelSpec name items
          let env' = env { meModels = M.insert name spec (meModels env) }
          pure (docEnv, env', rawRuns)
        DeclSurfaceWhere surfDecl -> do
          let name = rsdName surfDecl
          ensureAbsent "surface" name (meSurfaces env)
          def <- elabSurfaceDecl (resolvePresentation docEnv) surfDecl
          let env' = env { meSurfaces = M.insert name def (meSurfaces env) }
          pure (docEnv, env', rawRuns)
        DeclMorphismWhere morphDecl -> do
          let name = rmdName morphDecl
          ensureAbsent "morphism" name (meMorphisms env)
          morph <- elabMorphismDecl docEnv morphDecl
          let env' = env { meMorphisms = M.insert name morph (meMorphisms env) }
          pure (docEnv, env', rawRuns)
        DeclImplements implDecl -> do
          (key, morphName) <- elabImplements docEnv env implDecl
          let env' = env { meImplDefaults = M.insert key morphName (meImplDefaults env) }
          pure (docEnv, env', rawRuns)
        DeclRunSpec name rawSpec -> do
          ensureAbsent "run_spec" name (meRunSpecs env)
          let env' = env { meRunSpecs = M.insert name (rrsRun rawSpec) (meRunSpecs env) }
          pure (docEnv, env', rawRuns)
        DeclRun rawNamed ->
          pure (docEnv, env, rawRuns <> [rawNamed])

    docsFromEnv env =
      M.mapWithKey
        (\name expr -> Def { defExpr = expr, defRawPresentation = M.lookup name (mePresentations env) })
        (meDoctrines env)

ensureAbsent :: Text -> Text -> M.Map Text v -> Either Text ()
ensureAbsent label name mp =
  if M.member name mp
    then Left ("Duplicate " <> label <> " name: " <> name)
    else Right ()

elabPresentation :: DocEnv -> Text -> [RawItem] -> Either Text Presentation
elabPresentation docEnv name items = do
  (sig, eqMap, eqs) <- foldM step (Signature M.empty M.empty, M.empty, []) items
  let pres = Presentation { presName = name, presSig = sig, presEqs = eqs }
  case validatePresentation pres of
    Left err -> Left ("Presentation invalid: " <> err)
    Right () -> Right pres
  where
    step (sig, eqMap, eqs) item =
      case item of
        ItemInclude expr -> do
          presInc <- resolveIncludePresentation docEnv expr
          sig' <- mergeSignatures sig (presSig presInc)
          (eqMap', eqs') <- foldM insertEq (eqMap, eqs) (presEqs presInc)
          pure (sig', eqMap', eqs')
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
    SyntaxDoctrine _ -> do
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

mergeSignatures :: Signature -> Signature -> Either Text Signature
mergeSignatures s1 s2 = do
  sortCtors <- mergeSortCtors (M.toList (sigSortCtors s1) <> M.toList (sigSortCtors s2))
  opDecls <- mergeOpDecls (M.toList (sigOps s1) <> M.toList (sigOps s2))
  pure Signature { sigSortCtors = sortCtors, sigOps = opDecls }

mergeSortCtors :: [(SortName, SortCtor)] -> Either Text (M.Map SortName SortCtor)
mergeSortCtors = foldl step (Right M.empty)
  where
    step acc (name, ctor) = do
      m <- acc
      case M.lookup name m of
        Nothing -> pure (M.insert name ctor m)
        Just ctor' ->
          if alphaEqSortCtor ctor' ctor
            then pure m
            else Left ("Duplicate sort ctor: " <> renderSortName name)

mergeOpDecls :: [(OpName, OpDecl)] -> Either Text (M.Map OpName OpDecl)
mergeOpDecls = foldl step (Right M.empty)
  where
    step acc (name, decl) = do
      m <- acc
      case M.lookup name m of
        Nothing -> pure (M.insert name decl m)
        Just decl' ->
          if alphaEqOpDecl decl' decl
            then pure m
            else Left ("Duplicate op decl: " <> renderOpName name)

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

resolveExpr :: DocEnv -> RawExpr -> Either Text DocExpr
resolveExpr env expr =
  case expr of
    ERef name ->
      case M.lookup name env of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just def -> Right (defExpr def)
    EInst base ns ->
      case M.lookup base env of
        Nothing -> Left ("Unknown doctrine: " <> base)
        Just def ->
          case defRawPresentation def of
            Nothing -> Left ("@ requires a where-defined doctrine: " <> base)
            Just pres -> Right (Atom ns pres)
    EAnd a b -> And <$> resolveExpr env a <*> resolveExpr env b
    ERenameOps m e -> RenameOps (mapOpNames m) <$> resolveExpr env e
    ERenameSorts m e -> RenameSorts (mapSortNames m) <$> resolveExpr env e
    ERenameEqs m e -> RenameEqs m <$> resolveExpr env e
    EShareOps pairs e -> ShareOps (mapPair OpName pairs) <$> resolveExpr env e
    EShareSorts pairs e -> ShareSorts (mapPair SortName pairs) <$> resolveExpr env e

resolvePresentation :: DocEnv -> RawExpr -> Either Text Presentation
resolvePresentation env expr = resolveExpr env expr >>= elabDocExpr

resolveIncludePresentation :: DocEnv -> RawExpr -> Either Text Presentation
resolveIncludePresentation env expr =
  case expr of
    ERef name ->
      case M.lookup name env of
        Just def ->
          case defRawPresentation def of
            Just pres -> Right pres
            Nothing -> resolvePresentation env expr
        Nothing -> resolvePresentation env expr
    _ -> resolvePresentation env expr

elabMorphismDecl :: DocEnv -> RawMorphismDecl -> Either Text Morphism
elabMorphismDecl docEnv decl = do
  srcPres <- resolvePresentation docEnv (rmdSrc decl)
  tgtPres <- resolvePresentation docEnv (rmdTgt decl)
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

mapOpNames :: M.Map Text Text -> M.Map OpName OpName
mapOpNames m = M.fromList [(OpName k, OpName v) | (k, v) <- M.toList m]

mapSortNames :: M.Map Text Text -> M.Map SortName SortName
mapSortNames m = M.fromList [(SortName k, SortName v) | (k, v) <- M.toList m]

mapPair :: (Text -> a) -> [(Text, Text)] -> [(a, a)]
mapPair f = map (\(a, b) -> (f a, f b))

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
    , runCoreSyntax = rrCoreSyntax raw
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
        RawShowResult -> ShowResult

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

mergeRawRun :: Maybe RawRun -> RawRun -> RawRun
mergeRawRun base override =
  case base of
    Nothing -> override
    Just b ->
      RawRun
        { rrDoctrine = pick rrDoctrine
        , rrSyntax = pick rrSyntax
        , rrCoreSyntax = pick rrCoreSyntax
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

mergeUses :: [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)]
mergeUses base override =
  let baseMap = M.fromList base
      overMap = M.fromList override
  in M.toList (M.union overMap baseMap)

elabImplements :: DocEnv -> ModuleEnv -> RawImplementsDecl -> Either Text ((Text, Text), Text)
elabImplements docEnv env decl = do
  ifacePres <- resolvePresentation docEnv (ridInterface decl)
  tgtPres <- resolvePresentation docEnv (ridTarget decl)
  morph <- case M.lookup (ridMorphism decl) (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> ridMorphism decl)
    Just m -> Right m
  if morSrc morph /= ifacePres
    then Left "Morphism source does not match implements interface"
    else if morTgt morph /= tgtPres
      then Left "Morphism target does not match implements target"
      else Right ((presName ifacePres, presName tgtPres), ridMorphism decl)

validateRunFields :: Maybe Text -> Maybe Text -> Maybe Text -> Either Text ()
validateRunFields surf surfSyn coreSyn =
  case surf of
    Nothing ->
      case coreSyn of
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


-- SOGAT elaboration

data SogatEnv = SogatEnv
  { seCtxSort :: SortName
  , seSorts :: M.Map Text RawSortDecl
  , seOps :: M.Map Text RawSogatOpDecl
  }

elabSogatDecl :: RawSogatDecl -> Either Text Presentation
elabSogatDecl decl = do
  ctxName <- requireContextSort (rsogItems decl)
  let sortItems = [d | RSSogatSort d <- rsogItems decl]
  let opItems = [d | RSSogatOp d <- rsogItems decl]
  sortMap <- buildSortMap sortItems
  opMap <- buildOpMap opItems
  if M.member ctxName sortMap
    then Right ()
    else Left ("context_sort not declared as sort: " <> ctxName)
  let env = SogatEnv { seCtxSort = SortName ctxName, seSorts = sortMap, seOps = opMap }
  sortCtors <- mapM (elabSogatSortCtor env) sortItems
  opDecls <- mapM (elabSogatOpDecl env) opItems
  let ctxSortCtor = SortCtor { scName = SortName "Ctx", scTele = [] }
  let ctxOps = [emptyDecl, extendDecl env]
  let sig = Signature
        { sigSortCtors = M.fromList ((scName ctxSortCtor, ctxSortCtor) : map (\c -> (scName c, c)) sortCtors)
        , sigOps = M.fromList (map (\o -> (opName o, o)) (ctxOps <> opDecls))
        }
  let pres =
        Presentation
          { presName = rsogName decl
          , presSig = sig
          , presEqs = []
          }
  case validatePresentation pres of
    Left err -> Left ("SOGAT presentation invalid: " <> err)
    Right () -> Right pres
  where
    ctxSort = Sort (SortName "Ctx") []

    requireContextSort items =
      case [ n | RSSogatContextSort n <- items ] of
        [] -> Left "sogat: missing context_sort"
        [n] -> Right n
        _ -> Left "sogat: multiple context_sort declarations"

    buildSortMap decls =
      case dupName [ rsName d | d <- decls ] of
        Just dup -> Left ("Duplicate sort in sogat: " <> dup)
        Nothing -> Right (M.fromList [ (rsName d, d) | d <- decls ])

    buildOpMap decls =
      case dupName [ rsoName d | d <- decls ] of
        Just dup -> Left ("Duplicate op in sogat: " <> dup)
        Nothing -> Right (M.fromList [ (rsoName d, d) | d <- decls ])

    dupName xs = go S.empty xs
      where
        go _ [] = Nothing
        go seen (x:rest)
          | x `S.member` seen = Just x
          | otherwise = go (S.insert x seen) rest

    emptyDecl =
      let name = OpName "empty"
      in OpDecl
          { opName = name
          , opTele = []
          , opResult = ctxSort
          }

    extendDecl env =
      let name = OpName "extend"
          scope = ScopeId "op:extend"
          gammaVar = Var scope 0
          aVar = Var scope 1
          ctxTerm = mkVar ctxSort gammaVar
          tySort = Sort (seCtxSort env) [ctxTerm]
      in OpDecl
          { opName = name
          , opTele =
              [ Binder gammaVar ctxSort
              , Binder aVar tySort
              ]
          , opResult = ctxSort
          }

    elabSogatSortCtor env rawDecl = do
      let name = rsName rawDecl
      let scope = ScopeId ("sort:" <> name)
      let needsCtx = name /= "Ctx"
      let gammaVar = Var scope 0
      let ctxTerm = mkVar ctxSort gammaVar
      let mCtxTerm = if needsCtx then Just ctxTerm else Nothing
      let startIx = if needsCtx then 1 else 0
      (binders, _, _) <- foldM (stepSortBinder env mCtxTerm scope) ([], M.empty, startIx) (rsTele rawDecl)
      pure SortCtor
        { scName = SortName name
        , scTele =
            if needsCtx
              then Binder gammaVar ctxSort : binders
              else binders
        }

    stepSortBinder env mCtxTerm scope (acc, termEnv, idx) rb = do
      srt <- elabRawSort env mCtxTerm termEnv (rbSort rb)
      let v = Var scope idx
      let termEnv' = M.insert (rbName rb) (mkVar srt v) termEnv
      pure (acc <> [Binder v srt], termEnv', idx + 1)

    elabSogatOpDecl env rawDecl = do
      let name = rsoName rawDecl
      let scope = ScopeId ("op:" <> name)
      let hasCtx = rawSortName (rsoResult rawDecl) /= "Ctx"
      let gammaVar = Var scope 0
      let ctxTerm = mkVar ctxSort gammaVar
      let mCtxTerm = if hasCtx then Just ctxTerm else Nothing
      let startIx = if hasCtx then 1 else 0
      (binders, termEnv, _) <- foldM (stepOpArg env mCtxTerm scope) ([], M.empty, startIx) (rsoArgs rawDecl)
      resultSort <- elabRawSort env mCtxTerm termEnv (rsoResult rawDecl)
      pure OpDecl
        { opName = OpName name
        , opTele =
            if hasCtx
              then Binder gammaVar ctxSort : binders
              else binders
        , opResult = resultSort
        }

    stepOpArg env mCtxTerm scope (acc, termEnv, idx) arg = do
      mCtxTerm' <-
        case (mCtxTerm, rsgaBinders arg) of
          (Nothing, []) -> Right Nothing
          (Nothing, _ : _) ->
            Left "SOGAT binders require a context parameter"
          (Just ctx, binders) -> Just <$> extendCtx env ctx termEnv binders
      srt <- elabRawSort env mCtxTerm' termEnv (rsgaSort arg)
      let v = Var scope idx
      let termEnv' = M.insert (rsgaName arg) (mkVar srt v) termEnv
      pure (acc <> [Binder v srt], termEnv', idx + 1)

    extendCtx env ctxTerm termEnv binders =
      foldM step ctxTerm binders
      where
        step ctx (RawSogatBinder bName bType) = do
          tyTerm <- elabRawTerm env (Just ctx) termEnv bType
          let expected = Sort (seCtxSort env) [ctx]
          tyTerm' <-
            if termSort tyTerm == expected
              then Right tyTerm
              else weakenTermToExpected tyTerm expected
          if termSort tyTerm' /= expected
            then Left ("SOGAT binder type is not in context_sort: " <> bName)
            else Right (extendCtxTerm ctx tyTerm')

    extendCtxTerm ctxTerm tyTerm =
      Term
        { termSort = ctxSort
        , termNode = TOp (OpName "extend") [ctxTerm, tyTerm]
        }

    coerceTerm errMsg expected term =
      if termSort term == expected
        then Right term
        else case weakenTermToExpected term expected of
          Right t -> Right t
          Left _ -> Left errMsg

    weakenTermToExpected term expected =
      case ctxIndex expected of
        Nothing -> Left "no context index for expected sort"
        Just ctxNew -> do
          term' <- weakenTermToCtxEither term ctxNew
          if termSort term' == expected
            then Right term'
            else Left "unable to weaken term to expected sort"

    ctxIndex (Sort (SortName "Ctx") _) = Nothing
    ctxIndex (Sort _ (ctx:_)) = Just ctx
    ctxIndex _ = Nothing


    elabRawTerm env mCtxTerm termEnv tm =
      case tm of
        RVar name ->
          case M.lookup name termEnv of
            Nothing -> Left ("Unknown variable in SOGAT term: " <> name)
            Just t -> Right t
        RApp name args -> do
          case (args, M.lookup name termEnv) of
            ([], Just t) -> Right t
            _ -> do
              opDecl <- lookupOp name
              let hasCtx = rawSortName (rsoResult opDecl) /= "Ctx"
              case (hasCtx, mCtxTerm) of
                (True, Nothing) -> Left ("SOGAT term requires context for op: " <> name)
                _ -> Right ()
              (tele, resSort) <- opSignature env opDecl
              args' <- mapM (elabRawTerm env mCtxTerm termEnv) args
              let allArgs =
                    case (hasCtx, mCtxTerm) of
                      (True, Just ctx) -> ctx : args'
                      _ -> args'
              if length allArgs /= length tele
                then Left ("SOGAT op arity mismatch in term: " <> name)
                else Right ()
              (args', subst) <- checkArgs name tele allArgs M.empty
              let resSort' = applySubstSort subst resSort
              pure Term
                { termSort = resSort'
                , termNode = TOp (OpName name) args'
                }
      where
        lookupOp n =
          case M.lookup n (seOps env) of
            Nothing -> Left ("Unknown op in SOGAT term: " <> n)
            Just d -> Right d

        checkArgs _ [] [] subst = Right ([], subst)
        checkArgs n (Binder v s : bs) (a:as) subst = do
          let expected = applySubstSort subst s
          a' <- coerceTerm ("SOGAT term sort mismatch for op: " <> n) expected a
          let subst' = M.insert v a' subst
          (rest, subst'') <- checkArgs n bs as subst'
          Right (a' : rest, subst'')
        checkArgs n _ _ _ = Left ("SOGAT internal arity mismatch for op: " <> n)

    opSignature env opDecl = do
      let name = rsoName opDecl
      let scope = ScopeId ("op:" <> name)
      let hasCtx = rawSortName (rsoResult opDecl) /= "Ctx"
      let gammaVar = Var scope 0
      let ctxTerm = mkVar ctxSort gammaVar
      let mCtxTerm = if hasCtx then Just ctxTerm else Nothing
      let startIx = if hasCtx then 1 else 0
      (binders, termEnv, _) <- foldM (stepOpArg env mCtxTerm scope) ([], M.empty, startIx) (rsoArgs opDecl)
      resultSort <- elabRawSort env mCtxTerm termEnv (rsoResult opDecl)
      let tele =
            if hasCtx
              then Binder gammaVar ctxSort : binders
              else binders
      pure (tele, resultSort)

    elabRawSort env mCtxTerm termEnv (RawSort name idx) =
      if name == "Ctx"
        then
          if null idx
            then Right ctxSort
            else Left "Ctx sort does not take indices"
        else do
          rawDecl <- lookupSort name
          let tele = rsTele rawDecl
          if length idx /= length tele
            then Left ("Sort index arity mismatch: " <> name)
            else Right ()
          let mCtxTerm' = mCtxTerm
          case mCtxTerm' of
            Nothing -> Left ("SOGAT sort requires context: " <> name)
            Just _ -> Right ()
          let startIx = 1
          (binders, _, _) <- foldM (stepSortBinder env mCtxTerm' (ScopeId ("sort:" <> name))) ([], termEnv, startIx) tele
          let binderVars = map bVar binders
          let binderSorts = map bSort binders
          terms <- mapM (elabRawTerm env mCtxTerm' termEnv) idx
          (terms', subst) <- checkSortArgs name (zip3 binderVars binderSorts terms) M.empty
          let idx' = map (applySubstTerm subst) terms'
          let allIdx =
                case mCtxTerm' of
                  Just ctx -> ctx : idx'
                  Nothing -> idx'
          pure (Sort (SortName name) allIdx)
      where
        lookupSort n =
          case M.lookup n (seSorts env) of
            Nothing -> Left ("Unknown sort in SOGAT: " <> n)
            Just d -> Right d

        checkSortArgs _ [] subst = Right ([], subst)
        checkSortArgs n ((v, s, t):rest) subst = do
          let expected = applySubstSort subst s
          t' <- coerceTerm ("Sort parameter sort mismatch in " <> n) expected t
          let subst' = M.insert v t' subst
          (restTerms, subst'') <- checkSortArgs n rest subst'
          Right (t' : restTerms, subst'')

    rawSortName (RawSort n _) = n
