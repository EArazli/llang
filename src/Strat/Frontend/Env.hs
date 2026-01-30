{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Env
  ( ModuleEnv(..)
  , emptyEnv
  , mergeEnv
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.DSL.AST (RawRunSpec)
import Strat.Model.Spec (ModelSpec)
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.Morphism (Morphism)
import Strat.Poly.Surface (PolySurfaceDef)
import Strat.RunSpec (RunSpec)


data ModuleEnv = ModuleEnv
  { meDoctrines :: M.Map Text Doctrine
  , meMorphisms :: M.Map Text Morphism
  , meSurfaces :: M.Map Text PolySurfaceDef
  , meModels :: M.Map Text (Text, ModelSpec)
  , meImplDefaults :: M.Map (Text, Text) [Text]
  , meRunSpecs :: M.Map Text RawRunSpec
  , meRuns :: M.Map Text RunSpec
  }
  deriving (Eq, Show)

emptyEnv :: ModuleEnv
emptyEnv = ModuleEnv
  { meDoctrines = M.empty
  , meMorphisms = M.empty
  , meSurfaces = M.empty
  , meModels = M.empty
  , meImplDefaults = M.empty
  , meRunSpecs = M.empty
  , meRuns = M.empty
  }

mergeEnv :: ModuleEnv -> ModuleEnv -> Either Text ModuleEnv
mergeEnv a b = do
  docs <- mergeMap "doctrine" meDoctrines
  morphs <- mergeMap "morphism" meMorphisms
  surfs <- mergeMap "surface" meSurfaces
  mods <- mergeMap "model" meModels
  let impls = mergeImplDefaults (meImplDefaults a) (meImplDefaults b)
  specs <- mergeMap "run_spec" meRunSpecs
  runs <- mergeMap "run" meRuns
  pure ModuleEnv
    { meDoctrines = docs
    , meMorphisms = morphs
    , meSurfaces = surfs
    , meModels = mods
    , meImplDefaults = impls
    , meRunSpecs = specs
    , meRuns = runs
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
