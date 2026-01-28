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
import Strat.Poly.Surface.LegacyAdapter (elabLegacySurfaceDiagram)
import Strat.Poly.Eval (evalDiagram)
import Strat.Poly.Morphism (Morphism(..), applyMorphismDiagram)
import Strat.Model.Spec (ModelSpec)
import Strat.Backend (Value(..))


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
          pure (docSurface, mode, diag)
        Nothing -> do
          mode <- resolveMode docTarget spec Nothing
          diag <- elabLegacySurfaceDiagram env spec docTarget mode name (prExprText spec)
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
