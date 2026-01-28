{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.RunPoly
  ( PolyRunResult(..)
  , runPolyFile
  , runPolyWithEnv
  , selectPolyRun
  , renderPolyRunResult
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad (foldM)
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Poly.RunSpec
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Normalize (NormalizationStatus(..), normalize)
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Pretty (renderDiagram)
import Strat.Frontend.RunSpec (RunShow(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Surface (PolySurfaceDef(..), PolySurfaceKind(..))
import Strat.Poly.Surface.SSA (elabSSA)
import qualified Strat.Poly.Surface.CartTerm as CartTerm
import qualified Strat.Poly.Surface.STLC as STLC
import Strat.Poly.Surface.CoreTerm (elabCoreTerm)
import Strat.Poly.Eval (evalDiagram)
import Strat.Poly.Morphism (Morphism(..), applyMorphismDiagram)
import Strat.Model.Spec (ModelSpec)
import Strat.Backend (Value(..))
import Strat.Frontend.Run (buildMorphismEnv)
import Strat.Kernel.Presentation (Presentation)
import qualified Strat.Kernel.Morphism as KMorph
import Strat.Kernel.Syntax (Term(..))
import Strat.Surface2.Def
import Strat.Surface2.Syntax (SurfaceSyntaxInstance(..), instantiateSurfaceSyntax)
import Strat.Surface2.SyntaxSpec (SurfaceSyntaxSpec)
import Strat.Surface2.Engine (GoalArg(..), SolveEnv(..), SolveResult(..), solveJudgment, renderSolveError, emptyCtx)
import Strat.Surface2.CoreEval (CoreVal(..), CoreEnv, evalCoreExpr)
import Strat.Surface2.Term (STerm(..), Ix(..), JudgName(..))
import Strat.Surface2.Pattern (MVar(..), MatchSubst(..), MetaSubst(..), instantiateMeta, resolvePlaceholders)


data PolyRunResult = PolyRunResult
  { prDoctrineDef :: Doctrine
  , prInput :: Diagram
  , prNormalized :: Diagram
  , prOutput :: Text
  } deriving (Eq, Show)

runPolyFile :: FilePath -> Maybe Text -> IO (Either Text PolyRunResult)
runPolyFile path mRunName = do
  envResult <- loadModule path
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case selectPolyRun env mRunName of
        Left err -> pure (Left err)
        Right spec -> pure (runPolyWithEnv env spec)

selectPolyRun :: ModuleEnv -> Maybe Text -> Either Text PolyRunSpec
selectPolyRun env mName =
  case mName of
    Just name ->
      case M.lookup name (mePolyRuns env) of
        Nothing -> Left ("Unknown polyrun: " <> name <> available)
        Just spec -> Right spec
    Nothing ->
      case M.lookup "main" (mePolyRuns env) of
        Just spec -> Right spec
        Nothing ->
          case M.toList (mePolyRuns env) of
            [] -> Left "No polyruns found"
            [(_, spec)] -> Right spec
            _ -> Left ("Multiple polyruns found; specify --run. Available: " <> T.intercalate ", " (M.keys (mePolyRuns env)))
  where
    available =
      if M.null (mePolyRuns env)
        then ""
        else " (available: " <> T.intercalate ", " (M.keys (mePolyRuns env)) <> ")"

runPolyWithEnv :: ModuleEnv -> PolyRunSpec -> Either Text PolyRunResult
runPolyWithEnv env spec = do
  docTarget <- lookupPolyDoctrine env (prDoctrine spec)
  (docSurface, mode, diag) <- case prSurface spec of
    Nothing -> do
      mode <- resolveMode docTarget spec Nothing
      rawExpr <- parseDiagExpr (prExprText spec)
      diag <- elabDiagExpr docTarget mode [] rawExpr
      pure (docTarget, mode, diag)
    Just name -> do
      mPolySurf <- lookupPolySurface env name
      case mPolySurf of
        Just surf -> do
          (docSurface, mode) <- resolveSurfaceDocMode env docTarget spec (Just surf)
          diag <- case psKind surf of
            SurfaceSSA -> elabSSA docSurface mode (prExprText spec)
            SurfaceCartTerm -> CartTerm.elabCartTerm docTarget mode (prExprText spec)
            SurfaceSTLC -> STLC.elabSTLC docTarget mode (prExprText spec)
          pure (docSurface, mode, diag)
        Nothing -> do
          surf <- lookupLegacySurface env name
          corePres <- lookupCoreDoctrine env spec
          surfSynName <- maybe (Left "polyrun: missing surface_syntax") Right (prSurfaceSyntax spec)
          surfSynSpec <- lookupSurfaceSyntax env surfSynName
          mode <- resolveMode docTarget spec Nothing
          coreTerm <- elabLegacySurfaceTerm env corePres surf surfSynSpec (prExprText spec) (prFuel spec)
          diag <- elabCoreTerm docTarget mode coreTerm
          pure (docTarget, mode, diag)
  morphsFromUses <- resolveUses env (prDoctrine spec) (prUses spec)
  (docUsed, diagUsed) <- applyMorphisms env docSurface diag morphsFromUses
  if not (null (prUses spec)) && dName docUsed /= dName docTarget
    then Left "polyrun: uses did not reach target doctrine"
    else Right ()
  (doc', diag') <- applyMorphisms env docUsed diagUsed (prMorphisms spec)
  if null (prMorphisms spec) && dName doc' /= dName docTarget
    then Left "polyrun: morphism chain did not reach target doctrine"
    else Right ()
  -- TODO: cartesian surface handled by builtin in resolveSurface below
  if S.null (freeTyVarsDiagram diag')
    then Right ()
    else Left "polyrun: unresolved type variables in diagram"
  let rules = rulesFromPolicy (prPolicy spec) (dCells2 doc')
  status <- normalize (prFuel spec) rules diag'
  let norm =
        case status of
          Finished d -> d
          OutOfFuel d -> d
  mValue <- case prModel spec of
    Nothing -> Right Nothing
    Just name -> do
      (docName, modelSpec) <- lookupPolyModel env name
      (docModel, diagModel) <- resolvePolyModelDiagram env doc' norm docName
      if null (dIn diagModel)
        then do
          vals <- evalDiagram docModel modelSpec diagModel []
          pure (Just vals)
        else Left "polyrun: value requires closed diagram"
  output <- renderPolyRunResult spec diag' norm mValue
  pure PolyRunResult
    { prDoctrineDef = doc'
    , prInput = diag'
    , prNormalized = norm
    , prOutput = output
    }

renderPolyRunResult :: PolyRunSpec -> Diagram -> Diagram -> Maybe [Value] -> Either Text Text
renderPolyRunResult spec input norm mValue = do
  inputTxt <- if ShowInput `elem` prShowFlags spec
    then fmap ("input:\n" <>) (renderDiagram input)
    else Right ""
  normTxt <- if ShowNormalized `elem` prShowFlags spec
    then fmap ("normalized:\n" <>) (renderDiagram norm)
    else Right ""
  valueTxt <- if ShowValue `elem` prShowFlags spec
    then case mValue of
      Nothing -> Left "polyrun: show value requires model"
      Just vals -> Right ("value:\n" <> renderValues vals)
    else Right ""
  catTxt <- if ShowCat `elem` prShowFlags spec
    then fmap ("cat:\n" <>) (renderDiagram norm)
    else Right ""
  pure (T.intercalate "\n" (filter (not . T.null) [inputTxt, normTxt, valueTxt, catTxt]))

lookupPolyDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupPolyDoctrine env name =
  case M.lookup name (mePolyDoctrines env) of
    Nothing -> Left ("Unknown polydoctrine: " <> name)
    Just doc -> Right doc

resolveMode :: Doctrine -> PolyRunSpec -> Maybe PolySurfaceDef -> Either Text ModeName
resolveMode doc spec mSurface =
  case mSurface of
    Just surf ->
      case psKind surf of
        SurfaceCartTerm -> resolveModeDefault doc spec
        SurfaceSTLC -> resolveModeDefault doc spec
        SurfaceSSA ->
          case prMode spec of
            Nothing -> Right (psMode surf)
            Just name ->
              let mode = ModeName name
              in if mode == psMode surf
                then Right mode
                else Left "polyrun: mode does not match surface"
    Nothing -> resolveModeDefault doc spec
  where
    resolveModeDefault d s =
      case prMode s of
        Just name ->
          let mode = ModeName name
          in if mode `S.member` mtModes (dModes d)
            then Right mode
            else Left ("polyrun: unknown mode " <> name)
        Nothing ->
          case S.toList (mtModes (dModes d)) of
            [m] -> Right m
            [] -> Left "polyrun: doctrine has no modes"
            _ -> Left "polyrun: multiple modes; specify mode"

lookupPolySurface :: ModuleEnv -> Text -> Either Text (Maybe PolySurfaceDef)
lookupPolySurface _ "CartTermSurface" = Right (Just CartTerm.builtinSurface)
lookupPolySurface _ "STLCSurface" = Right (Just STLC.builtinSurface)
lookupPolySurface env name = Right (M.lookup name (mePolySurfaces env))

resolveSurfaceDocMode :: ModuleEnv -> Doctrine -> PolyRunSpec -> Maybe PolySurfaceDef -> Either Text (Doctrine, ModeName)
resolveSurfaceDocMode env docTarget spec mSurface =
  case mSurface of
    Nothing -> do
      mode <- resolveMode docTarget spec Nothing
      pure (docTarget, mode)
    Just surf ->
      case psKind surf of
        SurfaceCartTerm -> do
          mode <- resolveMode docTarget spec (Just surf)
          pure (docTarget, mode)
        SurfaceSTLC -> do
          mode <- resolveMode docTarget spec (Just surf)
          pure (docTarget, mode)
        SurfaceSSA -> do
          docSurface <- lookupPolyDoctrine env (psDoctrine surf)
          mode <- resolveMode docSurface spec (Just surf)
          pure (docSurface, mode)

lookupPolyModel :: ModuleEnv -> Text -> Either Text (Text, ModelSpec)
lookupPolyModel env name =
  case M.lookup name (mePolyModels env) of
    Nothing -> Left ("Unknown polymodel: " <> name)
    Just spec -> Right spec

resolvePolyModelDiagram :: ModuleEnv -> Doctrine -> Diagram -> Text -> Either Text (Doctrine, Diagram)
resolvePolyModelDiagram env doc diag modelDocName =
  if dName doc == modelDocName
    then Right (doc, diag)
    else do
      target <- lookupPolyDoctrine env modelDocName
      mor <- findUniquePolyMorphism env doc target
      diag' <- applyMorphismDiagram mor diag
      pure (morTgt mor, diag')

findUniquePolyMorphism :: ModuleEnv -> Doctrine -> Doctrine -> Either Text Morphism
findUniquePolyMorphism env src tgt =
  case [ m | m <- M.elems (mePolyMorphisms env), dName (morSrc m) == dName src, dName (morTgt m) == dName tgt ] of
    [m] -> Right m
    [] -> Left ("Model restriction requires polymorphism from " <> dName src <> " to " <> dName tgt <> "; none found")
    ms -> Left ("Model restriction ambiguous: multiple polymorphisms from " <> dName src <> " to " <> dName tgt <> " (" <> T.intercalate ", " (map morName ms) <> ")")

lookupLegacySurface :: ModuleEnv -> Text -> Either Text SurfaceDef
lookupLegacySurface env name =
  case M.lookup name (meSurfaces env) of
    Nothing -> Left ("Unknown surface: " <> name)
    Just surf -> Right surf

lookupSurfaceSyntax :: ModuleEnv -> Text -> Either Text SurfaceSyntaxSpec
lookupSurfaceSyntax env name =
  case M.lookup name (meSyntaxes env) of
    Nothing -> Left ("Unknown surface_syntax: " <> name)
    Just def ->
      case def of
        SyntaxSurface spec -> Right spec
        SyntaxDoctrine _ -> Left ("Syntax is for doctrine, not surface: " <> name)

lookupCoreDoctrine :: ModuleEnv -> PolyRunSpec -> Either Text Presentation
lookupCoreDoctrine env spec =
  let name = maybe (prDoctrine spec) id (prCoreDoctrine spec)
  in case M.lookup name (meDoctrines env) of
      Nothing -> Left ("Unknown doctrine: " <> name)
      Just pres -> Right pres

elabLegacySurfaceTerm :: ModuleEnv -> Presentation -> SurfaceDef -> SurfaceSyntaxSpec -> Text -> Int -> Either Text Term
elabLegacySurfaceTerm env pres surf surfSynSpec src fuel = do
  morphs <- buildMorphismEnv env pres surf []
  surfSyntax <- instantiateSurfaceSyntax surf surfSynSpec
  surfaceTerm <- ssiParseTm surfSyntax src
  let goalArgs = buildSurfaceGoal surf surfaceTerm
  solveRes <-
    case solveJudgment surf (JudgName "HasType") goalArgs fuel of
      Left err -> Left (renderSolveError err)
      Right res -> Right res
  let coreExpr =
        case srOutputs solveRes of
          (c:_) -> c
          _ -> CoreVar "e"
  coreEnv <- buildCoreEnv pres surf morphs (srEnv solveRes)
  coreVal <- evalCoreExpr pres surf morphs coreEnv coreExpr
  case coreVal of
    CVCore t -> Right t
    _ -> Left "surface elaboration did not produce core term"

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

buildCoreEnv :: Presentation -> SurfaceDef -> M.Map Text KMorph.Morphism -> SolveEnv -> Either Text CoreEnv
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

evalCoreBinding :: Presentation -> SurfaceDef -> M.Map Text KMorph.Morphism -> CoreEnv -> (Text, CoreExpr) -> Either Text CoreEnv
evalCoreBinding pres surf morphs env (name, expr) = do
  val <- evalCoreExpr pres surf morphs env expr
  case val of
    CVCore t -> Right (M.insert name (CVCore t) env)
    CVNat n -> Right (M.insert name (CVNat n) env)
    CVCtx c -> Right (M.insert name (CVCtx c) env)
    CVSurf s -> Right (M.insert name (CVSurf s) env)

applyMorphisms :: ModuleEnv -> Doctrine -> Diagram -> [Text] -> Either Text (Doctrine, Diagram)
applyMorphisms env doc diag names =
  foldl step (Right (doc, diag)) names
  where
    step acc name = do
      (doc0, diag0) <- acc
      mor <- lookupPolyMorphism env name
      if dName (morSrc mor) /= dName doc0
        then Left ("polyrun: morphism source mismatch for " <> name)
        else do
          diag' <- applyMorphismDiagram mor diag0
          pure (morTgt mor, diag')

lookupPolyMorphism :: ModuleEnv -> Text -> Either Text Morphism
lookupPolyMorphism env name =
  case M.lookup name (mePolyMorphisms env) of
    Nothing -> Left ("Unknown polymorphism: " <> name)
    Just mor -> Right mor

resolveUses :: ModuleEnv -> Text -> [Text] -> Either Text [Text]
resolveUses env target uses =
  foldl step (Right []) uses
  where
    step acc iface = do
      names <- acc
      case M.lookup (iface, target) (mePolyImplDefaults env) of
        Nothing -> Left ("Missing polyimplements for interface: " <> iface)
        Just [name] -> Right (names <> [name])
        Just [] -> Left ("Missing polyimplements for interface: " <> iface)
        Just _ -> Left ("Ambiguous polyimplements for interface: " <> iface)

renderValues :: [Value] -> Text
renderValues vals =
  case vals of
    [v] -> T.pack (show v)
    _ -> T.pack (show vals)
