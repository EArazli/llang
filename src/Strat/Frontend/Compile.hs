{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Compile
  ( compileDiagramArtifact
  , compileSourceDiagram
  , applyMorphisms
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.Doctrine (Doctrine(..), doctrineTypeTheory)
import Strat.Poly.Diagram (Diagram, freeTyVarsDiagram, freeIxVarsDiagram)
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Normalize (NormalizationStatus(..), normalize)
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Surface (PolySurfaceDef(..))
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Morphism (Morphism(..), applyMorphismDiagram)


compileDiagramArtifact
  :: ModuleEnv
  -> Text        -- target doctrine name
  -> Maybe Text  -- mode override
  -> Maybe Text  -- surface
  -> [Text]      -- uses
  -> [Text]      -- morphisms
  -> RewritePolicy
  -> Int
  -> Text        -- expr text
  -> Either Text (Doctrine, Diagram, Diagram)
compileDiagramArtifact env targetName mMode mSurface uses morphs policy fuel exprText = do
  (docUsed, diagUsed) <- compileSourceDiagram env targetName mMode mSurface uses exprText
  (docApplied, diagApplied) <- applyMorphisms env docUsed diagUsed morphs
  (docFinal, diagFinal) <-
    if dName docApplied == targetName
      then Right (docApplied, diagApplied)
      else do
        case coerceDiagramTo env docApplied diagApplied targetName of
          Right ok -> Right ok
          Left err -> Left ("morphism chain did not reach target doctrine; " <> err)
  let rules = rulesFromPolicy policy (dCells2 docFinal)
  status <- normalize (doctrineTypeTheory docFinal) fuel rules diagFinal
  let norm =
        case status of
          Finished d -> d
          OutOfFuel d -> d
  pure (docFinal, diagFinal, norm)

compileSourceDiagram
  :: ModuleEnv
  -> Text
  -> Maybe Text
  -> Maybe Text
  -> [Text]
  -> Text
  -> Either Text (Doctrine, Diagram)
compileSourceDiagram env targetName mMode mSurface uses exprText = do
  docTarget <- lookupDoctrine env targetName
  (docSurface, _mode, diag0) <- case mSurface of
    Nothing -> do
      mode <- resolveMode docTarget mMode Nothing
      rawExpr <- parseDiagExpr exprText
      diag <- elabDiagExpr env docTarget mode [] rawExpr
      pure (docTarget, mode, diag)
    Just name -> do
      surf <- lookupSurface env name
      docSurface <- lookupDoctrine env (psDoctrine surf)
      mode <- resolveMode docSurface mMode (Just surf)
      (docOut, diagOut) <- elabSurfaceExpr env docSurface surf exprText
      pure (docOut, mode, diagOut)
  morphsFromUses <- resolveUses env targetName uses
  (docUsed, diagUsed) <- applyMorphisms env docSurface diag0 morphsFromUses
  let usesMismatch = (not (null uses)) && dName docUsed /= targetName
  (docFinal, diagFinal) <-
    if dName docUsed == targetName
      then Right (docUsed, diagUsed)
      else do
        case coerceDiagramTo env docUsed diagUsed targetName of
          Right ok -> Right ok
          Left err -> Left (renderMismatch usesMismatch err)
  if S.null (freeTyVarsDiagram diagFinal)
    then Right ()
  else Left "unresolved type variables in diagram"
  if S.null (freeIxVarsDiagram diagFinal)
    then Right ()
  else Left "unresolved index variables in diagram"
  pure (docFinal, diagFinal)
  where
    renderMismatch usesMismatch err =
      let label =
            if usesMismatch
              then "uses did not reach target doctrine"
              else "morphism chain did not reach target doctrine"
      in label <> "; " <> err

resolveMode :: Doctrine -> Maybe Text -> Maybe PolySurfaceDef -> Either Text ModeName
resolveMode doc mMode mSurface =
  case mSurface of
    Just surf ->
      case mMode of
        Nothing -> Right (psMode surf)
        Just name ->
          let mode = ModeName name
          in if mode == psMode surf
            then Right mode
            else Left "mode does not match surface"
    Nothing -> resolveModeDefault doc mMode
  where
    resolveModeDefault d mName =
      case mName of
        Just name ->
          let mode = ModeName name
          in if M.member mode (mtModes (dModes d))
            then Right mode
            else Left ("unknown mode " <> name)
        Nothing ->
          case M.keys (mtModes (dModes d)) of
            [m] -> Right m
            [] -> Left "doctrine has no modes"
            _ -> Left "multiple modes; specify mode"

lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc

lookupSurface :: ModuleEnv -> Text -> Either Text PolySurfaceDef
lookupSurface env name =
  case M.lookup name (meSurfaces env) of
    Nothing -> Left ("Unknown surface: " <> name)
    Just surf -> Right surf

lookupMorphism :: ModuleEnv -> Text -> Either Text Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just mor -> Right mor

applyMorphisms :: ModuleEnv -> Doctrine -> Diagram -> [Text] -> Either Text (Doctrine, Diagram)
applyMorphisms env doc diag names =
  foldl step (Right (doc, diag)) names
  where
    step acc name = do
      (doc0, diag0) <- acc
      mor <- lookupMorphism env name
      if dName (morSrc mor) /= dName doc0
        then Left ("morphism source mismatch for " <> name)
        else do
          diag' <- applyMorphismDiagram mor diag0
          pure (morTgt mor, diag')

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
