{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Run
  ( RunResult(..)
  , runFile
  , runWithEnv
  , selectRun
  , renderRunResult
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.RunSpec
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Normalize (NormalizationStatus(..), normalize)
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Coherence (checkCoherence, renderCoherenceReport)
import Strat.Poly.CriticalPairs (CPMode(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Surface (PolySurfaceDef(..))
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Eval (evalDiagram)
import Strat.Poly.Morphism (Morphism(..), applyMorphismDiagram)
import Strat.Model.Spec (ModelSpec)
import Strat.Backend (Value(..))


data RunResult = RunResult
  { prDoctrineDef :: Doctrine
  , prInput :: Diagram
  , prNormalized :: Diagram
  , prOutput :: Text
  } deriving (Eq, Show)

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
  docTarget <- lookupDoctrine env (prDoctrine spec)
  (docSurface, mode, diag) <- case prSurface spec of
    Nothing -> do
      mode <- resolveMode docTarget spec Nothing
      rawExpr <- parseDiagExpr (prExprText spec)
      diag <- elabDiagExpr docTarget mode [] rawExpr
      pure (docTarget, mode, diag)
    Just name -> do
      surf <- lookupSurface env name
      docSurface <- lookupDoctrine env (psDoctrine surf)
      mode <- resolveMode docSurface spec (Just surf)
      diag <- elabSurfaceExpr docSurface surf (prExprText spec)
      pure (docSurface, mode, diag)
  morphsFromUses <- resolveUses env (prDoctrine spec) (prUses spec)
  (docUsed, diagUsed) <- applyMorphisms env docSurface diag morphsFromUses
  if not (null (prUses spec)) && dName docUsed /= dName docTarget
    then Left "run: uses did not reach target doctrine"
    else Right ()
  (doc', diag') <- applyMorphisms env docUsed diagUsed (prMorphisms spec)
  if null (prMorphisms spec) && dName doc' /= dName docTarget
    then Left "run: morphism chain did not reach target doctrine"
    else Right ()
  if S.null (freeTyVarsDiagram diag')
    then Right ()
    else Left "run: unresolved type variables in diagram"
  let rules = rulesFromPolicy (prPolicy spec) (dCells2 doc')
  status <- normalize (prFuel spec) rules diag'
  let norm =
        case status of
          Finished d -> d
          OutOfFuel d -> d
  mValue <- if ShowValue `elem` prShowFlags spec
    then case prModel spec of
      Nothing -> Left "run: show value requires model"
      Just name -> do
        (docName, modelSpec) <- lookupModel env name
        (docModel, diagModel) <- resolveModelDiagram env doc' norm docName
        if null (dIn diagModel)
          then do
            vals <- evalDiagram docModel modelSpec diagModel []
            pure (Just vals)
          else Left "run: value requires closed diagram"
    else Right Nothing
  coherenceTxt <- if ShowCoherence `elem` prShowFlags spec
    then do
      results <- checkCoherence CP_StructuralVsComputational (prPolicy spec) (prFuel spec) doc'
      renderCoherenceReport results
    else Right ""
  output <- renderRunResult spec diag' norm mValue coherenceTxt
  pure RunResult
    { prDoctrineDef = doc'
    , prInput = diag'
    , prNormalized = norm
    , prOutput = output
    }

renderRunResult :: RunSpec -> Diagram -> Diagram -> Maybe [Value] -> Text -> Either Text Text
renderRunResult spec input norm mValue coherenceTxt = do
  inputTxt <- if ShowInput `elem` prShowFlags spec
    then fmap ("input:\n" <>) (renderDiagram input)
    else Right ""
  normTxt <- if ShowNormalized `elem` prShowFlags spec
    then fmap ("normalized:\n" <>) (renderDiagram norm)
    else Right ""
  valueTxt <- if ShowValue `elem` prShowFlags spec
    then case mValue of
      Nothing -> Left "run: show value requires model"
      Just vals -> Right ("value:\n" <> renderValues vals)
    else Right ""
  catTxt <- if ShowCat `elem` prShowFlags spec
    then Left "run: show cat is not supported"
    else Right ""
  let cohTxt = if ShowCoherence `elem` prShowFlags spec
        then coherenceTxt
        else ""
  pure (T.intercalate "\n" (filter (not . T.null) [inputTxt, normTxt, valueTxt, catTxt, cohTxt]))

lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc

resolveMode :: Doctrine -> RunSpec -> Maybe PolySurfaceDef -> Either Text ModeName
resolveMode doc spec mSurface =
  case mSurface of
    Just surf ->
      case prMode spec of
        Nothing -> Right (psMode surf)
        Just name ->
          let mode = ModeName name
          in if mode == psMode surf
            then Right mode
            else Left "run: mode does not match surface"
    Nothing -> resolveModeDefault doc spec
  where
    resolveModeDefault d s =
      case prMode s of
        Just name ->
          let mode = ModeName name
          in if mode `S.member` mtModes (dModes d)
            then Right mode
            else Left ("run: unknown mode " <> name)
        Nothing ->
          case S.toList (mtModes (dModes d)) of
            [m] -> Right m
            [] -> Left "run: doctrine has no modes"
            _ -> Left "run: multiple modes; specify mode"

lookupSurface :: ModuleEnv -> Text -> Either Text PolySurfaceDef
lookupSurface env name =
  case M.lookup name (meSurfaces env) of
    Nothing -> Left ("Unknown surface: " <> name)
    Just surf -> Right surf

lookupModel :: ModuleEnv -> Text -> Either Text (Text, ModelSpec)
lookupModel env name =
  case M.lookup name (meModels env) of
    Nothing -> Left ("Unknown model: " <> name)
    Just spec -> Right spec

resolveModelDiagram :: ModuleEnv -> Doctrine -> Diagram -> Text -> Either Text (Doctrine, Diagram)
resolveModelDiagram env doc diag modelDocName =
  if dName doc == modelDocName
    then Right (doc, diag)
    else do
      target <- lookupDoctrine env modelDocName
      mor <- findUniqueMorphism env doc target
      diag' <- applyMorphismDiagram mor diag
      pure (morTgt mor, diag')

findUniqueMorphism :: ModuleEnv -> Doctrine -> Doctrine -> Either Text Morphism
findUniqueMorphism env src tgt =
  case [ m | m <- M.elems (meMorphisms env), dName (morSrc m) == dName src, dName (morTgt m) == dName tgt ] of
    [m] -> Right m
    [] -> Left ("Model restriction requires morphism from " <> dName src <> " to " <> dName tgt <> "; none found")
    ms -> Left ("Model restriction ambiguous: multiple morphisms from " <> dName src <> " to " <> dName tgt <> " (" <> T.intercalate ", " (map morName ms) <> ")")

applyMorphisms :: ModuleEnv -> Doctrine -> Diagram -> [Text] -> Either Text (Doctrine, Diagram)
applyMorphisms env doc diag names =
  foldl step (Right (doc, diag)) names
  where
    step acc name = do
      (doc0, diag0) <- acc
      mor <- lookupMorphism env name
      if dName (morSrc mor) /= dName doc0
        then Left ("run: morphism source mismatch for " <> name)
        else do
          diag' <- applyMorphismDiagram mor diag0
          pure (morTgt mor, diag')

lookupMorphism :: ModuleEnv -> Text -> Either Text Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just mor -> Right mor

resolveUses :: ModuleEnv -> Text -> [Text] -> Either Text [Text]
resolveUses env target uses =
  foldl step (Right []) uses
  where
    step acc iface = do
      names <- acc
      case M.lookup (iface, target) (meImplDefaults env) of
        Nothing -> Left ("Missing implements for interface: " <> iface)
        Just [name] -> Right (names <> [name])
        Just [] -> Left ("Missing implements for interface: " <> iface)
        Just _ -> Left ("Ambiguous implements for interface: " <> iface)

renderValues :: [Value] -> Text
renderValues vals =
  case vals of
    [v] -> T.pack (show v)
    _ -> T.pack (show vals)
