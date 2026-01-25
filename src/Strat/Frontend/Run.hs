{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Run
  ( RunResult(..)
  , runFile
  , runWithEnv
  , selectRun
  , buildMorphismEnv
  , renderRunResult
  ) where

import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.RunSpec
import Strat.Kernel.Morphism.Util (identityMorphism)
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.RewriteSystem (compileRewriteSystem, RewriteSystem)
import Strat.Kernel.Syntax (Term(..))
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
import Strat.Surface2.Term (STerm(..), Ix(..), JudgName(..))
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
            [(_, spec)] -> Right spec
            _ -> Left ("Multiple runs found; specify --run. Available: " <> T.intercalate ", " (M.keys (meRuns env)))
  where
    available =
      if M.null (meRuns env)
        then ""
        else " (available: " <> T.intercalate ", " (M.keys (meRuns env)) <> ")"

runWithEnv :: ModuleEnv -> RunSpec -> Either Text RunResult
runWithEnv env spec = do
  pres <- lookupDoctrine env (runDoctrine spec)
  rs <- compileRewriteSystem (runPolicy spec) pres
  (modelDocName, modelSpec) <- lookupModel env (runModel spec) (runDoctrine spec)
  (term, printedInput, printNorm) <- case runSurface spec of
    Nothing -> do
      syntaxName <- maybe (Left "run: missing syntax") Right (runSyntax spec)
      syntaxSpec <- lookupDoctrineSyntax env syntaxName
      syntaxInstance <- instantiateSyntax pres (runOpen spec) syntaxSpec
      comb <- siParse syntaxInstance (runExprText spec)
      t <-
        case elaborate (defaultInstance pres) comb of
          Left err -> Left ("Elaboration error: " <> T.pack (show err))
          Right t' -> Right t'
      let printNorm = siPrint syntaxInstance
      pure (t, Just (siPrint syntaxInstance t), printNorm)
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
      let printNorm =
            case chooseCoreSyntax env spec pres of
              Just coreSyn -> coreSyn
              Nothing -> T.pack . show
      let inputText = ssiPrintTm surfSyntax surfaceTerm
      pure (coreTerm, Just inputText, printNorm)
  let (norm, _ok) = normalizeStatus (runFuel spec) rs term
  let printedNorm = printNorm norm
  let cat = compileTerm norm
  modelPres <- lookupDoctrine env modelDocName
  model <- instantiateModel modelPres (runOpen spec) modelSpec
  evalTerm' <- resolveModelTerm env pres modelPres norm
  val <-
    case evalTerm model evalTerm' of
      Left err -> Left ("Evaluation error: " <> renderRuntimeError err)
      Right v -> Right v
  let output = renderRunResult spec printedNorm cat val printedInput
  pure RunResult
    { rrPresentation = pres
    , rrInputTerm = term
    , rrNormalized = norm
    , rrPrintedNormalized = printedNorm
    , rrCatExpr = cat
    , rrValue = val
    , rrPrintedInput = printedInput
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

lookupModel :: ModuleEnv -> Text -> Text -> Either Text (Text, ModelSpec)
lookupModel env name runDocName =
  case M.lookup name (meModels env) of
    Nothing ->
      if name == "Symbolic"
        then Right (runDocName, ModelSpec { msName = "Symbolic", msClauses = [], msDefault = DefaultSymbolic })
        else Left ("Unknown model: " <> name)
    Just spec -> Right spec

lookupDoctrine :: ModuleEnv -> Text -> Either Text Presentation
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just pres -> Right pres

resolveModelTerm :: ModuleEnv -> Presentation -> Presentation -> Term -> Either Text Term
resolveModelTerm env runPres modelPres term =
  if runPres == modelPres
    then Right term
    else do
      mor <- findUniqueMorphism env runPres modelPres
      Right (applyMorphismTerm mor term)

findUniqueMorphism :: ModuleEnv -> Presentation -> Presentation -> Either Text Morphism
findUniqueMorphism env src tgt =
  case [ m | m <- M.elems (meMorphisms env), morSrc m == src, morTgt m == tgt ] of
    [m] -> Right m
    [] -> Left ("Model restriction requires morphism from " <> presName src <> " to " <> presName tgt <> "; none found")
    ms -> Left ("Model restriction ambiguous: multiple morphisms from " <> presName src <> " to " <> presName tgt <> " (" <> T.intercalate ", " (map morName ms) <> ")")

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
        Nothing -> do
          mDefault <- resolveDefault alias req
          case mDefault of
            Just pair -> Right pair
            Nothing ->
              if srPres req == pres
                then do
                  let mor = identityMorphism pres
                  pair <- ensureMorphMatch alias req mor
                  case checkMorphism (mcPolicy (morCheck mor)) (mcFuel (morCheck mor)) mor of
                    Left err -> Left ("identity morphism check failed: " <> T.pack (show err))
                    Right () -> Right pair
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
      where
        resolveDefault alias req' =
          case M.lookup (presName (srPres req'), presName pres) (meImplDefaults env) of
            Nothing -> Right Nothing
            Just names -> do
              mors <- mapM lookupMorphism names
              let matches = [ pair | mor <- mors, Right pair <- [ensureMorphMatch alias req' mor] ]
              case matches of
                [] -> Right Nothing
                [pair] -> Right (Just pair)
                _ -> Left ("Ambiguous default implements for alias: " <> alias)

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

renderRunResult :: RunSpec -> Text -> CatExpr -> Value -> Maybe Text -> Text
renderRunResult spec norm cat val inputTxt =
  T.unlines (concat [inputOut, normOut, valOut, catOut])
  where
    inputOut = if ShowInput `elem` runShowFlags spec then maybe [] (\t -> ["input: " <> t]) inputTxt else []
    normOut = if ShowNormalized `elem` runShowFlags spec then ["normalized: " <> norm] else []
    valOut = if ShowValue `elem` runShowFlags spec then ["value: " <> T.pack (show val)] else []
    catOut = if ShowCat `elem` runShowFlags spec then ["cat: " <> T.pack (show cat)] else []

buildSurfaceGoal :: SurfaceDef -> STerm -> [GoalArg]
buildSurfaceGoal surf tm =
  case M.lookup (JudgName "HasType") (sdJudgments surf) of
    Nothing -> [GCtx emptyCtx, GSurf tm, GSurf (SFree (holeName 0))]
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
        PCtx -> (acc <> [GCtx emptyCtx], surfArgs, holeIdx)
        PSurf _ ->
          case surfArgs of
            (x:xs) -> (acc <> [GSurf x], xs, holeIdx)
            [] -> (acc <> [GSurf (SFree (holeName holeIdx))], [], holeIdx + 1)
        PNat -> (acc <> [GNat 0], surfArgs, holeIdx)
        PCore -> (acc, surfArgs, holeIdx)

chooseCoreSyntax :: ModuleEnv -> RunSpec -> Presentation -> Maybe (Term -> Text)
chooseCoreSyntax env spec pres =
  case runSyntax spec of
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

renderRuntimeError :: RuntimeError -> Text
renderRuntimeError (RuntimeError msg) = msg
