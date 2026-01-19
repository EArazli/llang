{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Env
  ( ModuleEnv(..)
  , SyntaxDef(..)
  , emptyEnv
  , mergeEnv
  ) where

import Strat.Kernel.DoctrineExpr (DocExpr)
import Strat.Kernel.Presentation (Presentation)
import Strat.Syntax.Spec (SyntaxSpec)
import Strat.Model.Spec (ModelSpec)
import Strat.Frontend.RunSpec (RunSpec)
import Strat.Kernel.DSL.AST (RawRun)
import Strat.Surface2.Def (SurfaceDef)
import Strat.Surface2.SyntaxSpec (SurfaceSyntaxSpec)
import Strat.Kernel.Morphism (Morphism)
import Data.Text (Text)
import qualified Data.Map.Strict as M


data SyntaxDef
  = SyntaxDoctrine SyntaxSpec
  | SyntaxSurface SurfaceSyntaxSpec
  deriving (Eq, Show)

data ModuleEnv = ModuleEnv
  { meDoctrines     :: M.Map Text DocExpr
  , mePresentations :: M.Map Text Presentation
  , meSyntaxes      :: M.Map Text SyntaxDef
  , meSurfaces      :: M.Map Text SurfaceDef
  , meMorphisms     :: M.Map Text Morphism
  , meModels        :: M.Map Text ModelSpec
  , meImplDefaults  :: M.Map (Text, Text) Text
  , meRunSpecs      :: M.Map Text RawRun
  , meRuns          :: M.Map Text RunSpec
  }
  deriving (Eq, Show)

emptyEnv :: ModuleEnv
emptyEnv = ModuleEnv
  { meDoctrines = M.empty
  , mePresentations = M.empty
  , meSyntaxes = M.empty
  , meSurfaces = M.empty
  , meMorphisms = M.empty
  , meModels = M.empty
  , meImplDefaults = M.empty
  , meRunSpecs = M.empty
  , meRuns = M.empty
  }

mergeEnv :: ModuleEnv -> ModuleEnv -> Either Text ModuleEnv
mergeEnv a b = do
  docs <- mergeMap "doctrine" meDoctrines
  pres <- mergeMap "presentation" mePresentations
  syns <- mergeMap "syntax" meSyntaxes
  surfs <- mergeMap "surface" meSurfaces
  morphs <- mergeMap "morphism" meMorphisms
  mods <- mergeMap "model" meModels
  impls <- mergeNamed "implements default" renderImplKey (meImplDefaults a) (meImplDefaults b)
  specs <- mergeMap "run_spec" meRunSpecs
  runs <- mergeMap "run" meRuns
  pure ModuleEnv
    { meDoctrines = docs
    , mePresentations = pres
    , meSyntaxes = syns
    , meSurfaces = surfs
    , meMorphisms = morphs
    , meModels = mods
    , meImplDefaults = impls
    , meRunSpecs = specs
    , meRuns = runs
    }
  where
    mergeMap label f = mergeNamed label id (f a) (f b)
    renderImplKey (i, t) = i <> " -> " <> t

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
