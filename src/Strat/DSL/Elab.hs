{-# LANGUAGE OverloadedStrings #-}
module Strat.DSL.Elab
  ( elabRawFile
  , elabRawFileWithEnv
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Map.Strict as M
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.AST
import Strat.Frontend.Env
import Strat.Model.Spec (ModelSpec(..), DefaultBehavior(..), OpClause(..))
import Strat.Poly.DSL.Elab (elabPolyDoctrine, elabPolyMorphism, elabPolyRun)
import Strat.Poly.DSL.AST (rpdExtends, rpdName)
import Strat.Poly.Diagram (genD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..))
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Poly.Pushout (PolyPushoutResult(..), computePolyPushout, computePolyCoproduct)
import Strat.Poly.Surface (elabPolySurfaceDecl)
import Strat.Poly.Surface.Spec (ssDoctrine)
import Strat.RunSpec (RunSpec)


elabRawFile :: RawFile -> Either Text ModuleEnv
elabRawFile = elabRawFileWithEnv emptyEnv

elabRawFileWithEnv :: ModuleEnv -> RawFile -> Either Text ModuleEnv
elabRawFileWithEnv baseEnv (RawFile decls) = do
  (env, rawRuns) <- foldM step (baseEnv, []) decls
  runs <- elabRuns env rawRuns
  pure env { meRuns = runs }
  where
    step (env, rawRuns) decl =
      case decl of
        DeclImport _ -> Right (env, rawRuns)
        DeclDoctrine raw -> do
          let name = rpdName raw
          ensureAbsent "doctrine" name (meDoctrines env)
          doc <- elabPolyDoctrine env raw
          env' <- case rpdExtends raw of
            Nothing -> Right env
            Just base -> do
              mor <- buildPolyFromBase base (rpdName raw) env doc
              pure env { meMorphisms = M.insert (PolyMorph.morName mor) mor (meMorphisms env) }
          let env'' = env' { meDoctrines = M.insert (rpdName raw) doc (meDoctrines env') }
          pure (env'', rawRuns)
        DeclDoctrinePushout name leftMor rightMor -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          f <- lookupMorphism env leftMor
          g <- lookupMorphism env rightMor
          PolyPushoutResult doc inl inr glue <- computePolyPushout name f g
          ensureAbsent "morphism" (PolyMorph.morName inl) (meMorphisms env)
          ensureAbsent "morphism" (PolyMorph.morName inr) (meMorphisms env)
          ensureAbsent "morphism" (PolyMorph.morName glue) (meMorphisms env)
          let env' = env
                { meDoctrines = M.insert name doc (meDoctrines env)
                , meMorphisms =
                    M.insert (PolyMorph.morName glue) glue
                    (M.insert (PolyMorph.morName inl) inl
                    (M.insert (PolyMorph.morName inr) inr (meMorphisms env)))
                }
          pure (env', rawRuns)
        DeclDoctrineCoproduct name leftDoc rightDoc -> do
          ensureAbsent "doctrine" name (meDoctrines env)
          left <- lookupDoctrine env leftDoc
          right <- lookupDoctrine env rightDoc
          PolyPushoutResult doc inl inr glue <- computePolyCoproduct name left right
          ensureAbsent "morphism" (PolyMorph.morName inl) (meMorphisms env)
          ensureAbsent "morphism" (PolyMorph.morName inr) (meMorphisms env)
          ensureAbsent "morphism" (PolyMorph.morName glue) (meMorphisms env)
          let env' = env
                { meDoctrines = M.insert name doc (meDoctrines env)
                , meMorphisms =
                    M.insert (PolyMorph.morName glue) glue
                    (M.insert (PolyMorph.morName inl) inl
                    (M.insert (PolyMorph.morName inr) inr (meMorphisms env)))
                }
          pure (env', rawRuns)
        DeclSurface name spec -> do
          ensureAbsent "surface" name (meSurfaces env)
          doc <- lookupDoctrine env (ssDoctrine spec)
          def <- elabPolySurfaceDecl name doc spec
          let env' = env { meSurfaces = M.insert name def (meSurfaces env) }
          pure (env', rawRuns)
        DeclModel name doc items -> do
          ensureAbsent "model" name (meModels env)
          spec <- elabModelSpec name items
          _ <- lookupDoctrine env doc
          let env' = env { meModels = M.insert name (doc, spec) (meModels env) }
          pure (env', rawRuns)
        DeclMorphism morphDecl -> do
          let name = rpmName morphDecl
          ensureAbsent "morphism" name (meMorphisms env)
          morph <- elabPolyMorphism env morphDecl
          let env' = env { meMorphisms = M.insert name morph (meMorphisms env) }
          pure (env', rawRuns)
        DeclImplements iface tgt morphName -> do
          (key, name) <- elabImplements env iface tgt morphName
          let defaults = M.findWithDefault [] key (meImplDefaults env)
          let defaults' = if name `elem` defaults then defaults else defaults <> [name]
          let env' = env { meImplDefaults = M.insert key defaults' (meImplDefaults env) }
          pure (env', rawRuns)
        DeclRunSpec name rawSpec -> do
          ensureAbsent "run_spec" name (meRunSpecs env)
          let env' = env { meRunSpecs = M.insert name rawSpec (meRunSpecs env) }
          pure (env', rawRuns)
        DeclRun rawRun ->
          pure (env, rawRuns <> [rawRun])


ensureAbsent :: Text -> Text -> M.Map Text v -> Either Text ()
ensureAbsent label name mp =
  if M.member name mp
    then Left ("Duplicate " <> label <> " name: " <> name)
    else Right ()

lookupDoctrine :: ModuleEnv -> Text -> Either Text Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> Left ("Unknown doctrine: " <> name)
    Just doc -> Right doc

lookupMorphism :: ModuleEnv -> Text -> Either Text PolyMorph.Morphism
lookupMorphism env name =
  case M.lookup name (meMorphisms env) of
    Nothing -> Left ("Unknown morphism: " <> name)
    Just mor -> Right mor

elabImplements :: ModuleEnv -> Text -> Text -> Text -> Either Text ((Text, Text), Text)
elabImplements env ifaceName tgtName morphName = do
  ifaceDoc <- lookupDoctrine env ifaceName
  tgtDoc <- lookupDoctrine env tgtName
  morph <- lookupMorphism env morphName
  if PolyMorph.morSrc morph /= ifaceDoc
    then Left "Morphism source does not match implements interface"
    else if PolyMorph.morTgt morph /= tgtDoc
      then Left "Morphism target does not match implements target"
      else Right ((ifaceName, tgtName), morphName)

elabRuns :: ModuleEnv -> [RawNamedRun] -> Either Text (M.Map Text RunSpec)
elabRuns env raws = foldM step M.empty raws
  where
    step acc raw = do
      let name = rnrName raw
      if M.member name acc
        then Left ("Duplicate run name: " <> name)
        else do
          base <- case rnrUsing raw of
            Nothing -> Right Nothing
            Just specName ->
              case M.lookup specName (meRunSpecs env) of
                Nothing -> Left ("Unknown run_spec: " <> specName)
                Just spec -> Right (Just (rrsRun spec))
          let merged = mergeRawRun base (rnrRun raw)
          spec <- elabPolyRun name merged
          pure (M.insert name spec acc)

mergeRawRun :: Maybe RawRun -> RawRun -> RawRun
mergeRawRun base override =
  case base of
    Nothing -> override
    Just b ->
      RawRun
        { rrDoctrine = pick rrDoctrine
        , rrMode = pick rrMode
        , rrSurface = pick rrSurface
        , rrModel = pick rrModel
        , rrMorphisms = rrMorphisms b <> rrMorphisms override
        , rrUses = rrUses b <> rrUses override
        , rrPolicy = pick rrPolicy
        , rrFuel = pick rrFuel
        , rrShowFlags = rrShowFlags b <> rrShowFlags override
        , rrExprText = rrExprText override
        }
      where
        pick f = case f override of
          Just v -> Just v
          Nothing -> f b

elabModelSpec :: Text -> [RawModelItem] -> Either Text ModelSpec
elabModelSpec name items = do
  let defaults = [ d | RMDefault d <- items ]
  def <-
    case defaults of
      [] -> Right DefaultSymbolic
      [RawDefaultSymbolic] -> Right DefaultSymbolic
      [RawDefaultError msg] -> Right (DefaultError msg)
      _ -> Left "Multiple default clauses in model"
  let clauses = [ c | RMOp c <- items ]
  let opNames = map rmcOp clauses
  case findDup opNames of
    Just dup -> Left ("Duplicate op clause in model: " <> dup)
    Nothing -> pure ()
  let ops = map (\c -> OpClause (rmcOp c) (rmcArgs c) (rmcExpr c)) clauses
  pure ModelSpec
    { msName = name
    , msClauses = ops
    , msDefault = def
    }
  where
    findDup xs = go M.empty xs
    go _ [] = Nothing
    go seen (x:rest)
      | M.member x seen = Just x
      | otherwise = go (M.insert x () seen) rest

buildPolyFromBase :: Text -> Text -> ModuleEnv -> Doctrine -> Either Text PolyMorph.Morphism
buildPolyFromBase baseName newName env newDoc = do
  baseDoc <- lookupDoctrine env baseName
  ensureAbsent "morphism" morName (meMorphisms env)
  genMap <- fmap M.fromList (mapM genImage (allGens baseDoc))
  let mor = PolyMorph.Morphism
        { PolyMorph.morName = morName
        , PolyMorph.morSrc = baseDoc
        , PolyMorph.morTgt = newDoc
        , PolyMorph.morTypeMap = M.empty
        , PolyMorph.morGenMap = genMap
        , PolyMorph.morPolicy = UseStructuralAsBidirectional
        , PolyMorph.morFuel = 50
        }
  case PolyMorph.checkMorphism mor of
    Left err -> Left ("generated morphism " <> morName <> " invalid: " <> err)
    Right () -> Right mor
  where
    morName = newName <> ".fromBase"
    allGens doc =
      [ (mode, gen)
      | (mode, table) <- M.toList (dGens doc)
      , gen <- M.elems table
      ]
    genImage (mode, gen) = do
      img <- genD mode (gdDom gen) (gdCod gen) (gdName gen)
      pure ((mode, gdName gen), img)
