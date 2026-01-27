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
import qualified Data.IntMap.Strict as IM
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
import Strat.Poly.TypeExpr (TyVar(..), TypeExpr(..))
import Strat.Poly.Surface (PolySurfaceDef(..), PolySurfaceKind(..))
import Strat.Poly.Surface.SSA (elabSSA)
import qualified Strat.Poly.Surface.CartTerm as CartTerm
import Strat.Poly.Eval (evalDiagram)
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
  doc <- lookupPolyDoctrine env (prDoctrine spec)
  mSurface <- lookupSurface env (prSurface spec)
  mode <- resolveMode doc spec mSurface
  diag <- case mSurface of
    Nothing -> do
      rawExpr <- parseDiagExpr (prExprText spec)
      elabDiagExpr doc mode [] rawExpr
    Just surf -> do
      ensureSurfaceDoc (prDoctrine spec) surf
      case psKind surf of
        SurfaceSSA -> elabSSA doc mode (prExprText spec)
        SurfaceCartTerm -> CartTerm.elabCartTerm doc mode (prExprText spec)
  -- TODO: cartesian surface handled by builtin in resolveSurface below
  if S.null (freeVars diag)
    then Right ()
    else Left "polyrun: unresolved type variables in diagram"
  let rules = rulesFromPolicy (prPolicy spec) (dCells2 doc)
  status <- normalize (prFuel spec) rules diag
  let norm =
        case status of
          Finished d -> d
          OutOfFuel d -> d
  mValue <- case prModel spec of
    Nothing -> Right Nothing
    Just name -> do
      (docName, modelSpec) <- lookupPolyModel env name
      if docName /= prDoctrine spec
        then Left "polyrun: model doctrine mismatch"
        else do
          if null (dIn norm)
            then do
              vals <- evalDiagram doc modelSpec norm []
              pure (Just vals)
            else Left "polyrun: value requires closed diagram"
  output <- renderPolyRunResult spec diag norm mValue
  pure PolyRunResult
    { prDoctrineDef = doc
    , prInput = diag
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
  pure (T.intercalate "\n" (filter (not . T.null) [inputTxt, normTxt, valueTxt]))

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

lookupSurface :: ModuleEnv -> Maybe Text -> Either Text (Maybe PolySurfaceDef)
lookupSurface _ Nothing = Right Nothing
lookupSurface env (Just name)
  | name == "CartTermSurface" = Right (Just CartTerm.builtinSurface)
  | otherwise =
      case M.lookup name (mePolySurfaces env) of
        Nothing -> Left ("Unknown polysurface: " <> name)
        Just def -> Right (Just def)

ensureSurfaceDoc :: Text -> PolySurfaceDef -> Either Text ()
ensureSurfaceDoc docName surf =
  case psKind surf of
    SurfaceCartTerm -> Right ()
    _ ->
      if psDoctrine surf == docName
        then Right ()
        else Left "polyrun: surface doctrine mismatch"

lookupPolyModel :: ModuleEnv -> Text -> Either Text (Text, ModelSpec)
lookupPolyModel env name =
  case M.lookup name (mePolyModels env) of
    Nothing -> Left ("Unknown polymodel: " <> name)
    Just spec -> Right spec

renderValues :: [Value] -> Text
renderValues vals =
  case vals of
    [v] -> T.pack (show v)
    _ -> T.pack (show vals)

freeVars :: Diagram -> S.Set TyVar
freeVars diag = S.fromList (concatMap varsInTy (IM.elems (dPortTy diag)))

varsInTy :: TypeExpr -> [TyVar]
varsInTy ty =
  case ty of
    TVar v -> [v]
    TCon _ args -> concatMap varsInTy args
