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
import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.Compile (compileDiagramArtifact)
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.RunSpec
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Pretty (renderDiagram)
import Strat.Poly.Coherence (checkCoherence, renderCoherenceReport)
import Strat.Poly.CriticalPairs (CPMode(..))
import Strat.Poly.Eval (evalDiagram)
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
  (doc', diag', norm) <-
    case compileDiagramArtifact
      env
      (prDoctrine spec)
      (prMode spec)
      (prSurface spec)
      (prUses spec)
      (prMorphisms spec)
      (prPolicy spec)
      (prFuel spec)
      (prExprText spec) of
        Left err -> Left ("run: " <> err)
        Right ok -> Right ok
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
      case coerceDiagramTo env doc diag modelDocName of
        Left err -> Left ("run: " <> err)
        Right ok -> Right ok

renderValues :: [Value] -> Text
renderValues vals =
  case vals of
    [v] -> T.pack (show v)
    _ -> T.pack (show vals)
