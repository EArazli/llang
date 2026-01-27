{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Env
  ( ModuleEnv(..)
  , SyntaxDef(..)
  , emptyEnv
  , mergeEnv
  ) where

import Strat.Kernel.Presentation (Presentation)
import Strat.Syntax.Spec (SyntaxSpec)
import Strat.Model.Spec (ModelSpec)
import Strat.Frontend.RunSpec (RunSpec)
import Strat.Kernel.DSL.AST (RawRun, RawPolyRun)
import Strat.Surface2.Def (SurfaceDef)
import Strat.Surface2.SyntaxSpec (SurfaceSyntaxSpec)
import Strat.Kernel.Morphism (Morphism)
import Strat.Poly.Doctrine (Doctrine)
import qualified Strat.Poly.Morphism as PolyMorph
import Strat.Poly.Surface (PolySurfaceDef)
import Strat.Poly.RunSpec (PolyRunSpec)
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S


data SyntaxDef
  = SyntaxDoctrine SyntaxSpec
  | SyntaxSurface SurfaceSyntaxSpec
  deriving (Eq, Show)

data ModuleEnv = ModuleEnv
  { meDoctrines     :: M.Map Text Presentation
  , meRawDoctrines  :: M.Map Text Presentation
  , mePolyDoctrines :: M.Map Text Doctrine
  , mePolyMorphisms :: M.Map Text PolyMorph.Morphism
  , mePolySurfaces  :: M.Map Text PolySurfaceDef
  , mePolyModels    :: M.Map Text (Text, ModelSpec)
  , meSyntaxes      :: M.Map Text SyntaxDef
  , meSurfaces      :: M.Map Text SurfaceDef
  , meMorphisms     :: M.Map Text Morphism
  , meModels        :: M.Map Text (Text, ModelSpec)
  , meImplDefaults  :: M.Map (Text, Text) [Text]
  , mePolyImplDefaults :: M.Map (Text, Text) [Text]
  , meRunSpecs      :: M.Map Text RawRun
  , mePolyRunSpecs  :: M.Map Text RawPolyRun
  , meRuns          :: M.Map Text RunSpec
  , mePolyRuns      :: M.Map Text PolyRunSpec
  }
  deriving (Eq, Show)

emptyEnv :: ModuleEnv
emptyEnv = ModuleEnv
  { meDoctrines = M.empty
  , meRawDoctrines = M.empty
  , mePolyDoctrines = M.empty
  , mePolyMorphisms = M.empty
  , mePolySurfaces = M.empty
  , mePolyModels = M.empty
  , meSyntaxes = M.empty
  , meSurfaces = M.empty
  , meMorphisms = M.empty
  , meModels = M.empty
  , meImplDefaults = M.empty
  , mePolyImplDefaults = M.empty
  , meRunSpecs = M.empty
  , mePolyRunSpecs = M.empty
  , meRuns = M.empty
  , mePolyRuns = M.empty
  }

mergeEnv :: ModuleEnv -> ModuleEnv -> Either Text ModuleEnv
mergeEnv a b = do
  docs <- mergeMap "doctrine" meDoctrines
  rawDocs <- mergeMap "raw doctrine" meRawDoctrines
  polyDocs <- mergeMap "polydoctrine" mePolyDoctrines
  polyMorphs <- mergeMap "polymorphism" mePolyMorphisms
  polySurfs <- mergeMap "polysurface" mePolySurfaces
  polyModels <- mergeMap "polymodel" mePolyModels
  syns <- mergeMap "syntax" meSyntaxes
  surfs <- mergeMap "surface" meSurfaces
  morphs <- mergeMap "morphism" meMorphisms
  mods <- mergeMap "model" meModels
  let impls = mergeImplDefaults (meImplDefaults a) (meImplDefaults b)
  let polyImpls = mergeImplDefaults (mePolyImplDefaults a) (mePolyImplDefaults b)
  specs <- mergeMap "run_spec" meRunSpecs
  polySpecs <- mergeMap "polyrun_spec" mePolyRunSpecs
  runs <- mergeMap "run" meRuns
  polyRuns <- mergeMap "polyrun" mePolyRuns
  pure ModuleEnv
    { meDoctrines = docs
    , meRawDoctrines = rawDocs
    , mePolyDoctrines = polyDocs
    , mePolyMorphisms = polyMorphs
    , mePolySurfaces = polySurfs
    , mePolyModels = polyModels
    , meSyntaxes = syns
    , meSurfaces = surfs
    , meMorphisms = morphs
    , meModels = mods
    , meImplDefaults = impls
    , mePolyImplDefaults = polyImpls
    , meRunSpecs = specs
    , mePolyRunSpecs = polySpecs
    , meRuns = runs
    , mePolyRuns = polyRuns
    }
  where
    mergeMap label f = mergeNamed label id (f a) (f b)
    mergeImplDefaults left right = M.unionWith mergeDefaults left right
    mergeDefaults xs ys = dedupe (xs <> ys)

dedupe :: Ord a => [a] -> [a]
dedupe = go S.empty
  where
    go _ [] = []
    go seen (x:xs)
      | x `S.member` seen = go seen xs
      | otherwise = x : go (S.insert x seen) xs

mergeNamed :: (Ord k, Eq v) => Text -> (k -> Text) -> M.Map k v -> M.Map k v -> Either Text (M.Map k v)
mergeNamed label renderKey left right =
  case conflicts of
    [] -> Right (M.union left right)
    (k:_) -> Left ("Duplicate " <> label <> " name: " <> renderKey k)
  where
    conflicts =
      [ k
      | k <- M.keys (M.intersection left right)
      , M.lookup k left /= M.lookup k right
      ]
