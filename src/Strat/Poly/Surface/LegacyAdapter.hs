{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Surface.LegacyAdapter
  ( elabLegacySurfaceDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Control.Monad (foldM)
import Strat.Frontend.Env
import Strat.Poly.RunSpec (PolyRunSpec(..))
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Surface.CoreTerm (elabCoreTerm)
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


elabLegacySurfaceDiagram :: ModuleEnv -> PolyRunSpec -> Doctrine -> ModeName -> Text -> Text -> Either Text Diagram
elabLegacySurfaceDiagram env spec docTarget mode surfaceName src = do
  surf <- lookupLegacySurface env surfaceName
  corePres <- lookupCoreDoctrine env spec
  surfSynName <- maybe (Left "polyrun: missing surface_syntax") Right (prSurfaceSyntax spec)
  surfSynSpec <- lookupSurfaceSyntax env surfSynName
  coreTerm <- elabLegacySurfaceTerm env corePres surf surfSynSpec src (prFuel spec)
  elabCoreTerm docTarget mode coreTerm

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
