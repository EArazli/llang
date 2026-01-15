{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Run
  ( RunResult(..)
  , runFile
  , renderRunResult
  ) where

import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.RunSpec
import Strat.Kernel.DSL.AST (RawExpr(..))
import Strat.Kernel.DoctrineExpr (DocExpr(..), elabDocExpr)
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.RewriteSystem (compileRewriteSystem)
import Strat.Kernel.Rewrite (normalize)
import Strat.Kernel.Syntax (OpName(..), SortName(..), Term(..))
import Strat.Surface (defaultInstance, elaborate)
import Strat.Syntax.Spec (SyntaxInstance(..), instantiateSyntax)
import Strat.Model.Spec (instantiateModel)
import Strat.Backend (Value(..), RuntimeError(..), evalTerm)
import Strat.Backend.Concat (CatExpr(..), compileTerm)
import Strat.Surface2.Def
import Strat.Surface2.Elab ()
import Strat.Surface2.Syntax (SurfaceSyntaxInstance(..), instantiateSurfaceSyntax)
import Strat.Surface2.Engine
import Strat.Surface2.Interface
import Strat.Surface2.InterfaceInst
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

runFile :: FilePath -> IO (Either Text RunResult)
runFile path = do
  envResult <- loadModule path
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case meRun env of
        Nothing -> pure (Left "No run block found")
        Just spec -> pure (runWithEnv env spec)

runWithEnv :: ModuleEnv -> RunSpec -> Either Text RunResult
runWithEnv env spec = do
  docExpr <- resolveRunExpr env (runDoctrine spec)
  pres <- elabDocExpr docExpr
  rs <- compileRewriteSystem (runPolicy spec) pres
  modelSpec <- lookupSpec "model" (runModel spec) (meModels env)
  (term, printedInput, printedNorm) <- case runSurface spec of
    Nothing -> do
      syntaxName <- maybe (Left "run: missing syntax") Right (runSyntax spec)
      syntaxSpec <- lookupSpec "syntax" syntaxName (meSyntaxes env)
      syntaxInstance <- instantiateSyntax pres (runOpen spec) syntaxSpec
      comb <- siParse syntaxInstance (runExprText spec)
      t <-
        case elaborate (defaultInstance pres) comb of
          Left err -> Left ("Elaboration error: " <> T.pack (show err))
          Right t' -> Right t'
      let normText = siPrint syntaxInstance (normalize (runFuel spec) rs t)
      pure (t, Just (siPrint syntaxInstance t), normText)
    Just surfName -> do
      surf <- lookupSpec "surface" surfName (meSurfaces env)
      surfSynName <- maybe (Left "run: missing surface_syntax") Right (runSurfaceSyntax spec)
      surfSynSpec <- lookupSpec "surface_syntax" surfSynName (meSurfaceSyntaxes env)
      ifaceName <- maybe (Left "run: missing interface") Right (runInterface spec)
      ifaceSpec <- lookupSpec "interface" ifaceName (meInterfaces env)
      ifaceKind <- maybe (Left "Unknown interface kind") Right (lookupInterfaceKind (sdRequires surf))
      ifacePres <- elabDocExpr =<< resolveRunExpr env (isDoctrine ifaceSpec)
      if presSig ifacePres /= presSig pres
        then Left "interface doctrine does not match run doctrine"
        else Right ()
      ifaceInst <- instantiateInterface pres (runOpen spec) ifaceSpec ifaceKind
      surfSyntax <- instantiateSurfaceSyntax surf surfSynSpec
      surfaceTerm <- ssiParseTm surfSyntax (runExprText spec)
      let goalArgs = buildSurfaceGoal surf surfaceTerm
      solveRes <- solveJudgment surf (JudgName "HasType") goalArgs (runFuel spec)
      let coreExpr =
            case srOutputs solveRes of
              (c:_) -> c
              _ -> CoreVar "e"
      coreEnv <- buildCoreEnv pres surf ifaceInst (srEnv solveRes)
      coreVal <- evalCoreExpr pres surf ifaceInst coreEnv coreExpr
      coreTerm <- case coreVal of
        CVCore t -> Right t
        _ -> Left "surface elaboration did not produce core term"
      let normText =
            case chooseCoreSyntax env spec pres of
              Just coreSyn -> coreSyn (normalize (runFuel spec) rs coreTerm)
              Nothing -> T.pack (show (normalize (runFuel spec) rs coreTerm))
      let inputText = ssiPrintTm surfSyntax surfaceTerm
      pure (coreTerm, Just inputText, normText)
  let norm = normalize (runFuel spec) rs term
  let cat = compileTerm norm
  model <- instantiateModel pres (runOpen spec) modelSpec
  val <-
    case evalTerm model norm of
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
    Nothing -> [GCtx emptyCtx, GSurf tm, GSurf (SFree "_A")]
    Just decl ->
      let params = jdParams decl
          surfArgs = [ tm ]
          (args, _) = foldl build ([], surfArgs) params
      in args
  where
    build (acc, surfArgs) param =
      case jpSort param of
        PCtx -> (acc <> [GCtx emptyCtx], surfArgs)
        PSurf _ ->
          case surfArgs of
            (x:xs) -> (acc <> [GSurf x], xs)
            [] -> (acc <> [GSurf (SFree "_A")], [])
        PNat -> (acc <> [GNat 0], surfArgs)
        PCore -> (acc, surfArgs)

chooseCoreSyntax :: ModuleEnv -> RunSpec -> Presentation -> Maybe (Term -> Text)
chooseCoreSyntax env spec pres =
  case runCoreSyntax spec of
    Nothing -> Nothing
    Just name ->
      case M.lookup name (meSyntaxes env) of
        Nothing -> Nothing
        Just syn ->
          case instantiateSyntax pres (runOpen spec) syn of
            Left _ -> Nothing
            Right inst -> Just (siPrint inst)

buildCoreEnv :: Presentation -> SurfaceDef -> InterfaceInstance -> SolveEnv -> Either Text CoreEnv
buildCoreEnv pres surf iface env = do
  let envSurf = M.fromList [ (renderMVar mv, CVSurf (metaToTerm mv ms)) | (mv, ms) <- M.toList (msTerms (seMatch env)) ]
  let envNats = M.fromList [ (k, CVNat v) | (k, v) <- M.toList (msNats (seMatch env)) ]
  let envCtx = M.map CVCtx (seCtxs env)
  let envPlace = M.map CVSurf (seSurfVars env)
  let base = M.unions [envSurf, envNats, envCtx, envPlace]
  foldM (evalCoreBinding pres surf iface) base (M.toList (seCore env))
  where
    renderMVar (MVar t) = t
    metaToTerm mv ms =
      case instantiateMeta ms (map Ix [0 .. msArity ms - 1]) of
        Just tm -> resolvePlaceholders (seMatch env) tm
        Nothing -> SFree (renderMVar mv)

evalCoreBinding :: Presentation -> SurfaceDef -> InterfaceInstance -> CoreEnv -> (Text, CoreExpr) -> Either Text CoreEnv
evalCoreBinding pres surf iface env (name, expr) = do
  val <- evalCoreExpr pres surf iface env expr
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
