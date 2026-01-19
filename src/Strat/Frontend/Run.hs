{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Run
  ( RunResult(..)
  , runFile
  , buildMorphismEnv
  , renderRunResult
  ) where

import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.RunSpec
import Strat.Kernel.DSL.AST (RawExpr(..))
import Strat.Kernel.DoctrineExpr (DocExpr(..), elabDocExpr)
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.RewriteSystem (compileRewriteSystem, RewritePolicy(..), RewriteSystem)
import Strat.Kernel.Rewrite (normalize)
import Strat.Kernel.Syntax (OpName(..), SortName(..), Term(..), TermNode(..), Var(..), ScopeId(..), Binder(..))
import Strat.Kernel.Term (mkOp, mkVar)
import Strat.Kernel.Signature (sigSortCtors, sigOps, opTele, opResult)
import Strat.Kernel.Morphism
import Strat.Surface (defaultInstance, elaborate)
import Strat.Syntax.Spec (SyntaxSpec, SyntaxInstance(..), instantiateSyntax)
import Strat.Model.Spec (ModelSpec(..), DefaultBehavior(..), instantiateModel)
import Strat.Backend (Value(..), RuntimeError(..), evalTerm)
import Strat.Backend.Concat (CatExpr(..), compileTerm)
import Strat.Surface2.Def
import Strat.Surface2.Elab ()
import Strat.Surface2.Syntax (SurfaceSyntaxInstance(..), instantiateSurfaceSyntax)
import Strat.Surface2.SyntaxSpec (SurfaceSyntaxSpec)
import Strat.Surface2.Engine
import Strat.Surface2.CoreEval
import Strat.Surface2.Term (STerm(..), Ix(..), JudgName(..), Con2Name(..))
import Strat.Surface2.Pattern (MVar(..), MatchSubst(..), MetaSubst(..), instantiateMeta, resolvePlaceholders)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Monad (foldM)


data RunResult = RunResult
  { rrPresentation :: Presentation
  , rrInputTerm :: Term
  , rrNormalized :: Term
  , rrPrintedNormalized :: Text
  , rrCatExpr :: CatExpr
  , rrValue :: Value
  , rrPrintedInput :: Maybe Text
  , rrResult :: Maybe Text
  , rrOutput :: Text
  }
  deriving (Eq, Show)

runFile :: FilePath -> Maybe Text -> IO (Either Text RunResult)
runFile path mRunName = do
  envResult <- loadModule path
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case selectRun env mRunName of
        Left err -> pure (Left err)
        Right spec -> pure (runWithEnv env spec)

selectRun :: ModuleEnv -> Maybe Text -> Either Text RunSpec
selectRun env mName =
  case mName of
    Just name ->
      case M.lookup name (meRuns env) of
        Nothing -> Left ("Unknown run: " <> name <> available)
        Just spec -> Right spec
    Nothing ->
      case M.lookup "main" (meRuns env) of
        Just spec -> Right spec
        Nothing ->
          case M.toList (meRuns env) of
            [] -> Left "No runs found"
            [(name, spec)] -> Right spec
            _ -> Left ("Multiple runs found; specify --run. Available: " <> T.intercalate ", " (M.keys (meRuns env)))
  where
    available =
      if M.null (meRuns env)
        then ""
        else " (available: " <> T.intercalate ", " (M.keys (meRuns env)) <> ")"

runWithEnv :: ModuleEnv -> RunSpec -> Either Text RunResult
runWithEnv env spec = do
  docExpr <- resolveRunExpr env (runDoctrine spec)
  pres <- elabDocExpr docExpr
  rs <- compileRewriteSystem (runPolicy spec) pres
  modelSpec <- lookupModel env (runModel spec)
  (term, printedInput, printedNorm, surfInfo) <- case runSurface spec of
    Nothing -> do
      syntaxName <- maybe (Left "run: missing syntax") Right (runSyntax spec)
      syntaxSpec <- lookupDoctrineSyntax env syntaxName
      syntaxInstance <- instantiateSyntax pres (runOpen spec) syntaxSpec
      comb <- siParse syntaxInstance (runExprText spec)
      t <-
        case elaborate (defaultInstance pres) comb of
          Left err -> Left ("Elaboration error: " <> T.pack (show err))
          Right t' -> Right t'
      let normText = siPrint syntaxInstance (normalize (runFuel spec) rs t)
      pure (t, Just (siPrint syntaxInstance t), normText, Nothing)
    Just surfName -> do
      surf <- lookupSpec "surface" surfName (meSurfaces env)
      surfSynName <- maybe (Left "run: missing surface_syntax") Right (runSurfaceSyntax spec)
      surfSynSpec <- lookupSurfaceSyntax env surfSynName
      morphs <- buildMorphismEnv env pres surf (runUses spec)
      surfSyntax <- instantiateSurfaceSyntax surf surfSynSpec
      surfaceTerm <- ssiParseTm surfSyntax (runExprText spec)
      let goalArgs = buildSurfaceGoal surf surfaceTerm
      solveRes <-
        case solveJudgment surf (JudgName "HasType") goalArgs (runFuel spec) of
          Left err -> Left (renderSolveError err)
          Right res -> Right res
      let coreExpr =
            case srOutputs solveRes of
              (c:_) -> c
              _ -> CoreVar "e"
      coreEnv <- buildCoreEnv pres surf morphs (srEnv solveRes)
      coreVal <- evalCoreExpr pres surf morphs coreEnv coreExpr
      coreTerm <- case coreVal of
        CVCore t -> Right t
        _ -> Left "surface elaboration did not produce core term"
      let normText =
            case chooseCoreSyntax env spec pres of
              Just coreSyn -> coreSyn (normalize (runFuel spec) rs coreTerm)
              Nothing -> T.pack (show (normalize (runFuel spec) rs coreTerm))
      let inputText = ssiPrintTm surfSyntax surfaceTerm
      pure (coreTerm, Just inputText, normText, Just (surf, surfSyntax, morphs, srEnv solveRes, goalArgs))
  let norm = normalize (runFuel spec) rs term
  resultTxt <-
    if ShowResult `elem` runShowFlags spec
      then case surfInfo of
        Nothing -> Right Nothing
        Just info -> fmap Just (readbackResult spec rs norm info)
      else Right Nothing
  let cat = compileTerm norm
  model <- instantiateModel pres (runOpen spec) modelSpec
  val <-
    case evalTerm model norm of
      Left err -> Left ("Evaluation error: " <> renderRuntimeError err)
      Right v -> Right v
  let output = renderRunResult spec printedNorm cat val printedInput resultTxt
  pure RunResult
    { rrPresentation = pres
    , rrInputTerm = term
    , rrNormalized = norm
    , rrPrintedNormalized = printedNorm
    , rrCatExpr = cat
    , rrValue = val
    , rrPrintedInput = printedInput
    , rrResult = resultTxt
    , rrOutput = output
    }

lookupSpec :: Text -> Text -> M.Map Text a -> Either Text a
lookupSpec label name mp =
  case M.lookup name mp of
    Nothing -> Left ("Unknown " <> label <> ": " <> name)
    Just v -> Right v

lookupDoctrineSyntax :: ModuleEnv -> Text -> Either Text SyntaxSpec
lookupDoctrineSyntax env name =
  case M.lookup name (meSyntaxes env) of
    Nothing -> Left ("Unknown syntax: " <> name)
    Just def ->
      case def of
        SyntaxDoctrine spec -> Right spec
        SyntaxSurface _ -> Left ("Syntax is for surface, not doctrine: " <> name)

lookupSurfaceSyntax :: ModuleEnv -> Text -> Either Text SurfaceSyntaxSpec
lookupSurfaceSyntax env name =
  case M.lookup name (meSyntaxes env) of
    Nothing -> Left ("Unknown syntax: " <> name)
    Just def ->
      case def of
        SyntaxSurface spec -> Right spec
        SyntaxDoctrine _ -> Left ("Syntax is for doctrine, not surface: " <> name)

lookupModel :: ModuleEnv -> Text -> Either Text ModelSpec
lookupModel env name =
  case M.lookup name (meModels env) of
    Nothing ->
      if name == "Symbolic"
        then Right ModelSpec { msName = "Symbolic", msClauses = [], msDefault = DefaultSymbolic }
        else Left ("Unknown model: " <> name)
    Just spec -> Right spec

buildMorphismEnv :: ModuleEnv -> Presentation -> SurfaceDef -> [(Text, Text)] -> Either Text (M.Map Text Morphism)
buildMorphismEnv env pres surf uses = do
  explicit <- ensureNoDupUses uses
  let reqs = sdRequires surf
  let reqAliases = map srAlias reqs
  case filter (`notElem` reqAliases) (M.keys explicit) of
    (bad:_) -> Left ("Unknown required alias in run: " <> bad)
    [] -> pure ()
  morphs <- mapM (resolveRequirement explicit) reqs
  pure (M.fromList morphs)
  where
    ensureNoDupUses pairs =
      case dupKey pairs of
        Just k -> Left ("Duplicate implements alias: " <> k)
        Nothing -> Right (M.fromList pairs)
    dupKey = go M.empty
      where
        go _ [] = Nothing
        go seen ((k,_):rest)
          | M.member k seen = Just k
          | otherwise = go (M.insert k () seen) rest

    resolveRequirement explicit req = do
      let alias = srAlias req
      case M.lookup alias explicit of
        Just name -> do
          mor <- lookupMorphism name
          ensureMorphMatch alias req mor
        Nothing ->
          case M.lookup (presName (srPres req), presName pres) (meImplDefaults env) of
            Just name -> do
              mor <- lookupMorphism name
              ensureMorphMatch alias req mor
            Nothing ->
              if presName (srPres req) == presName pres
                then do
                  mor <- identityMorphism pres
                  case checkMorphism (mcPolicy (morCheck mor)) (mcFuel (morCheck mor)) mor of
                    Left err -> Left ("identity morphism check failed: " <> T.pack (show err))
                    Right () -> Right (alias, mor)
                else do
                  let candidates =
                        [ m
                        | m <- M.elems (meMorphisms env)
                        , morSrc m == srPres req
                        , morTgt m == pres
                        ]
                  case candidates of
                    [m] -> Right (alias, m)
                    [] -> Left ("Missing implementation for alias: " <> alias)
                    _ -> Left ("Ambiguous implementation for alias: " <> alias)

    lookupMorphism name =
      case M.lookup name (meMorphisms env) of
        Nothing -> Left ("Unknown morphism: " <> name)
        Just m -> Right m

    ensureMorphMatch alias req mor =
      if morSrc mor /= srPres req
        then Left ("Morphism source does not match required interface for alias: " <> alias)
        else if morTgt mor /= pres
          then Left ("Morphism target does not match run doctrine for alias: " <> alias)
          else Right (alias, mor)

identityMorphism :: Presentation -> Either Text Morphism
identityMorphism pres =
  let sorts = M.keys (sigSortCtors (presSig pres))
      ops = M.keys (sigOps (presSig pres))
      sortMap = M.fromList [ (s, s) | s <- sorts ]
      mkInterp op =
        let decl = sigOps (presSig pres) M.! op
            tele = opTele decl
            args = [ mkVar (bSort b) v | b@(Binder v _) <- tele ]
        in case mkOp (presSig pres) op args of
          Left err -> Left ("identity morphism failed to construct op: " <> T.pack (show err))
          Right rhs -> Right OpInterp { oiTele = tele, oiRhs = rhs }
  in do
    opMapList <- mapM (\o -> fmap (\i -> (o, i)) (mkInterp o)) ops
    let opMap = M.fromList opMapList
    pure Morphism
      { morName = "identity"
      , morSrc = pres
      , morTgt = pres
      , morSortMap = sortMap
      , morOpMap = opMap
      , morCheck = MorphismCheck { mcPolicy = UseStructuralAsBidirectional, mcFuel = 200 }
      }

renderRunResult :: RunSpec -> Text -> CatExpr -> Value -> Maybe Text -> Maybe Text -> Text
renderRunResult spec norm cat val inputTxt resultTxt =
  T.unlines (concat [inputOut, normOut, valOut, catOut, resultOut])
  where
    inputOut = if ShowInput `elem` runShowFlags spec then maybe [] (\t -> ["input: " <> t]) inputTxt else []
    normOut = if ShowNormalized `elem` runShowFlags spec then ["normalized: " <> norm] else []
    valOut = if ShowValue `elem` runShowFlags spec then ["value: " <> T.pack (show val)] else []
    catOut = if ShowCat `elem` runShowFlags spec then ["cat: " <> T.pack (show cat)] else []
    resultOut =
      if ShowResult `elem` runShowFlags spec
        then case resultTxt of
          Nothing -> ["result: (unavailable)"]
          Just t -> ["result: " <> t]
        else []

buildSurfaceGoal :: SurfaceDef -> STerm -> [GoalArg]
buildSurfaceGoal surf tm =
  case M.lookup (JudgName "HasType") (sdJudgments surf) of
    Nothing -> [GCtx (emptyCtxFor (sdCtxDisc surf)), GSurf tm, GSurf (SFree (holeName 0))]
    Just decl ->
      let params = jdParams decl
          surfArgs = [ tm ]
          (args, _, _) = foldl build ([], surfArgs, 0 :: Int) params
      in args
  where
    holeName :: Int -> Text
    holeName i = "_h" <> T.pack (show i)
    build (acc, surfArgs, holeIdx) param =
      case jpSort param of
        PCtx -> (acc <> [GCtx (emptyCtxFor (sdCtxDisc surf))], surfArgs, holeIdx)
        PSurf _ ->
          case surfArgs of
            (x:xs) -> (acc <> [GSurf x], xs, holeIdx)
            [] -> (acc <> [GSurf (SFree (holeName holeIdx))], [], holeIdx + 1)
        PNat -> (acc <> [GNat 0], surfArgs, holeIdx)
        PCore -> (acc, surfArgs, holeIdx)

readbackResult :: RunSpec -> RewriteSystem -> Term -> (SurfaceDef, SurfaceSyntaxInstance, M.Map Text Morphism, SolveEnv, [GoalArg]) -> Either Text Text
readbackResult spec rs norm (surf, surfSyntax, morphs, env, goalArgs) = do
  tyTerm <- inferTypeTerm surf env goalArgs
  if isBoolTy tyTerm
    then do
      coreBool <- readbackCoreBool surf morphs rs spec norm
      case coreBool of
        Nothing -> pure "result not in canonical Bool form"
        Just tm -> pure (ssiPrintTm surfSyntax tm)
    else pure "result not in canonical Bool form"
  where
    isBoolTy tm =
      case tm of
        SCon (Con2Name "BoolTy") [] -> True
        _ -> False

inferTypeTerm :: SurfaceDef -> SolveEnv -> [GoalArg] -> Either Text STerm
inferTypeTerm surf env goalArgs =
  case M.lookup (JudgName "HasType") (sdJudgments surf) of
    Nothing -> Left "missing HasType judgment"
    Just decl -> do
      let params = jdParams decl
      case lastSurfParam params goalArgs of
        Nothing -> Left "no surface type argument"
        Just tm -> resolvePlaceholders (seMatch env) tm
  where
    lastSurfParam params args =
      let indexed = zip params args
          surfArgs = [ tm | (p, GSurf tm) <- indexed, isSurfParam p ]
      in case surfArgs of
          [] -> Nothing
          xs -> Just (last xs)

    isSurfParam p =
      case jpSort p of
        PSurf _ -> True
        _ -> False

readbackCoreBool :: SurfaceDef -> M.Map Text Morphism -> RewriteSystem -> RunSpec -> Term -> Either Text (Maybe STerm)
readbackCoreBool surf morphs rs spec tm =
  case candidates of
    [] -> Right Nothing
    ((mor, tInterp, fInterp):_) -> do
      let tTerm = applyOpInterp tInterp []
      let fTerm = applyOpInterp fInterp []
      let normT = normalize (runFuel spec) rs tTerm
      let normF = normalize (runFuel spec) rs fTerm
      let ctxTerms =
            either (const Nothing) Just
              (buildCtxBoolTerms (runFuel spec) rs mor tInterp fInterp)
      let isT =
            tm == normT
              || maybe False (\(tCtx, _) -> tm == tCtx) ctxTerms
              || joinableWithin (runFuel spec) rs tm tTerm
      let isF =
            tm == normF
              || maybe False (\(_, fCtx) -> tm == fCtx) ctxTerms
              || joinableWithin (runFuel spec) rs tm fTerm
      if isT && not isF
        then Right (Just (SCon (Con2Name "True") []))
        else if isF && not isT
          then Right (Just (SCon (Con2Name "False") []))
          else Right Nothing
  where
    candidates =
      [ (mor, tInterp, fInterp)
      | req <- sdRequires surf
      , Just mor <- [M.lookup (srAlias req) morphs]
      , Right tKey <- [resolveOpNameIn (morSrc mor) "T"]
      , Right fKey <- [resolveOpNameIn (morSrc mor) "F"]
      , Right tInterp <- [lookupInterp mor tKey]
      , Right fInterp <- [lookupInterp mor fKey]
      ]

    buildCtxBoolTerms fuel rs mor tInterp0 fInterp0 = do
      unitInterp <- resolveInterp mor "Unit"
      boolInterp <- resolveInterp mor "Bool"
      terminalInterp <- resolveInterp mor "terminal"
      compInterp <- resolveInterp mor "comp"
      let unitTerm = applyOpInterp unitInterp []
      let boolTerm = applyOpInterp boolInterp []
      let termT = applyOpInterp tInterp0 []
      let termF = applyOpInterp fInterp0 []
      let termTerminal = applyOpInterp terminalInterp [unitTerm]
      let termTrue = applyOpInterp compInterp [unitTerm, unitTerm, boolTerm, termT, termTerminal]
      let termFalse = applyOpInterp compInterp [unitTerm, unitTerm, boolTerm, termF, termTerminal]
      pure (normalize fuel rs termTrue, normalize fuel rs termFalse)

    resolveInterp mor name = do
      key <- resolveOpNameIn (morSrc mor) name
      lookupInterp mor key

resolveOpNameIn :: Presentation -> Text -> Either Text OpName
resolveOpNameIn pres name =
  let direct = OpName name
      pref = OpName (presName pres <> "." <> name)
      sig = presSig pres
  in if M.member direct (sigOps sig)
      then Right direct
      else if M.member pref (sigOps sig)
        then Right pref
        else Left ("unknown core op: " <> name)

chooseCoreSyntax :: ModuleEnv -> RunSpec -> Presentation -> Maybe (Term -> Text)
chooseCoreSyntax env spec pres =
  case runCoreSyntax spec of
    Nothing -> Nothing
    Just name ->
      case lookupDoctrineSyntax env name of
        Left _ -> Nothing
        Right syn ->
          case instantiateSyntax pres (runOpen spec) syn of
            Left _ -> Nothing
            Right inst -> Just (siPrint inst)

buildCoreEnv :: Presentation -> SurfaceDef -> M.Map Text Morphism -> SolveEnv -> Either Text CoreEnv
buildCoreEnv pres surf morphs env = do
  envSurf <- buildSurfEnv
  let envNats = M.fromList [ (k, CVNat v) | (k, v) <- M.toList (msNats (seMatch env)) ]
  let envCtx = M.map CVCtx (seCtxs env)
  let envPlace = M.map CVSurf (seSurfVars env)
  let base = M.unions [envSurf, envNats, envCtx, envPlace]
  evalCoreBindings base (seCore env)
  where
    renderMVar (MVar t) = t
    buildSurfEnv = do
      pairs <- mapM toPair (M.toList (msTerms (seMatch env)))
      pure (M.fromList pairs)
    toPair (mv, ms) = do
      tm <- instantiateMeta ms (map Ix [0 .. msArity ms - 1])
      tm' <- resolvePlaceholders (seMatch env) tm
      pure (renderMVar mv, CVSurf tm')

    evalCoreBindings env0 pending0 = go env0 pending0
      where
        go envAcc pending
          | M.null pending = Right envAcc
          | otherwise = do
              (env', pending', progressed) <- foldM (step pending) (envAcc, pending, False) (M.toList pending)
              if progressed
                then go env' pending'
                else Left "core binding dependency cycle or unresolved reference"

        step pending (envAcc, pendingAcc, progressed) (name, expr) =
          case evalCoreBinding pres surf morphs envAcc (name, expr) of
            Right env' -> Right (env', M.delete name pendingAcc, True)
            Left err ->
              case missingCoreVar err of
                Just var | M.member var pending -> Right (envAcc, pendingAcc, progressed)
                _ -> Left err

        missingCoreVar msg = T.stripPrefix "unknown core var: " msg

evalCoreBinding :: Presentation -> SurfaceDef -> M.Map Text Morphism -> CoreEnv -> (Text, CoreExpr) -> Either Text CoreEnv
evalCoreBinding pres surf morphs env (name, expr) = do
  val <- evalCoreExpr pres surf morphs env expr
  case val of
    CVCore t -> Right (M.insert name (CVCore t) env)
    _ -> Right (M.insert name val env)

resolveRunExpr :: ModuleEnv -> RawExpr -> Either Text DocExpr
resolveRunExpr env expr =
  case expr of
    ERef name ->
      case M.lookup name (meDoctrines env) of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just d -> Right d
    EInst base ns ->
      case M.lookup base (mePresentations env) of
        Nothing -> Left ("@ requires a where-defined doctrine: " <> base)
        Just pres -> Right (Atom ns pres)
    EAnd a b -> And <$> resolveRunExpr env a <*> resolveRunExpr env b
    ERenameOps m e -> RenameOps (mapOpNames m) <$> resolveRunExpr env e
    ERenameSorts m e -> RenameSorts (mapSortNames m) <$> resolveRunExpr env e
    ERenameEqs m e -> RenameEqs m <$> resolveRunExpr env e
    EShareOps pairs e -> ShareOps (mapPair OpName pairs) <$> resolveRunExpr env e
    EShareSorts pairs e -> ShareSorts (mapPair SortName pairs) <$> resolveRunExpr env e

mapOpNames :: M.Map Text Text -> M.Map OpName OpName
mapOpNames m = M.fromList [(OpName k, OpName v) | (k, v) <- M.toList m]

mapSortNames :: M.Map Text Text -> M.Map SortName SortName
mapSortNames m = M.fromList [(SortName k, SortName v) | (k, v) <- M.toList m]

mapPair :: (Text -> a) -> [(Text, Text)] -> [(a, a)]
mapPair f = map (\(a, b) -> (f a, f b))

renderRuntimeError :: RuntimeError -> Text
renderRuntimeError (RuntimeError msg) = msg
