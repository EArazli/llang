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
import Strat.Poly.Rewrite (rulesFromDoctrine)
import Strat.Poly.Pretty (renderDiagram)
import Strat.Frontend.RunSpec (RunShow(..))
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import Strat.Poly.TypeExpr (TyVar(..), TypeExpr(..))


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
  mode <- inferMode doc
  rawExpr <- parseDiagExpr (prExprText spec)
  diag <- elabDiagExpr doc mode [] rawExpr
  if S.null (freeVars diag)
    then Right ()
    else Left "polyrun: unresolved type variables in diagram"
  let rules = rulesFromDoctrine doc
  status <- normalize (prFuel spec) rules diag
  let norm =
        case status of
          Finished d -> d
          OutOfFuel d -> d
  let output = renderPolyRunResult spec diag norm
  pure PolyRunResult
    { prDoctrineDef = doc
    , prInput = diag
    , prNormalized = norm
    , prOutput = output
    }

renderPolyRunResult :: PolyRunSpec -> Diagram -> Diagram -> Text
renderPolyRunResult spec input norm =
  T.intercalate "\n" (filter (not . T.null) [inputOut, normOut])
  where
    inputOut =
      if ShowInput `elem` prShowFlags spec
        then "input:\n" <> renderDiagram input
        else ""
    normOut =
      if ShowNormalized `elem` prShowFlags spec
        then "normalized:\n" <> renderDiagram norm
        else ""

lookupPolyDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupPolyDoctrine env name =
  case M.lookup name (mePolyDoctrines env) of
    Nothing -> Left ("Unknown polydoctrine: " <> name)
    Just doc -> Right doc

inferMode :: Doctrine -> Either Text ModeName
inferMode doc =
  case S.toList (mtModes (dModes doc)) of
    [m] -> Right m
    [] -> Left "polyrun: doctrine has no modes"
    _ -> Left "polyrun: multiple modes; please reduce to a single mode"

freeVars :: Diagram -> S.Set TyVar
freeVars diag = S.fromList (concatMap varsInTy (IM.elems (dPortTy diag)))

varsInTy :: TypeExpr -> [TyVar]
varsInTy ty =
  case ty of
    TVar v -> [v]
    TCon _ args -> concatMap varsInTy args
