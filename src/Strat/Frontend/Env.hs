{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Env
  ( ModuleEnv(..)
  , DoctrineFunctorDef(..)
  , FunctorParamDef(..)
  , ProofStats(..)
  , emptyProofStats
  , addProofStats
  , subProofStats
  , proofStatsTotal
  , ScopedType(..)
  , ScopedValue(..)
  , emptyEnv
  , mergeEnv
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Strat.Pipeline (Pipeline, DerivedDoctrine, FragmentDecl)
import Strat.Frontend.Model
  ( LanguageDef
  , ModuleElaboratorDef
  , ModuleDataReprDef
  , ModuleSurfaceDef
  , InterfaceDef
  , ModuleDef
  , BuildDef
  )
import Strat.Poly.Kernel (Doctrine)
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Obj (Obj)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Morphism (Morphism)
import Strat.Poly.Surface (PolySurfaceDef)
import Strat.Util.List (dedupe)


data ProofStats = ProofStats
  { psMorphismProofs :: Int
  , psActionProofs :: Int
  , psImplementsProofs :: Int
  }
  deriving (Eq, Read, Show)

emptyProofStats :: ProofStats
emptyProofStats =
  ProofStats
    { psMorphismProofs = 0
    , psActionProofs = 0
    , psImplementsProofs = 0
    }

addProofStats :: ProofStats -> ProofStats -> ProofStats
addProofStats a b =
  ProofStats
    { psMorphismProofs = psMorphismProofs a + psMorphismProofs b
    , psActionProofs = psActionProofs a + psActionProofs b
    , psImplementsProofs = psImplementsProofs a + psImplementsProofs b
    }

subProofStats :: ProofStats -> ProofStats -> ProofStats
subProofStats a b =
  ProofStats
    { psMorphismProofs = max 0 (psMorphismProofs a - psMorphismProofs b)
    , psActionProofs = max 0 (psActionProofs a - psActionProofs b)
    , psImplementsProofs = max 0 (psImplementsProofs a - psImplementsProofs b)
    }

proofStatsTotal :: ProofStats -> Int
proofStatsTotal ps =
  psMorphismProofs ps + psActionProofs ps + psImplementsProofs ps


data ScopedType = ScopedType
  { stDoctrine :: Text
  , stMode :: ModeName
  , stBody :: Obj
  } deriving (Eq, Read, Show)


data ScopedValue = ScopedValue
  { svDoctrine :: Text
  , svMode :: ModeName
  , svDiagram :: Diagram
  } deriving (Eq, Read, Show)

data FunctorParamDef = FunctorParamDef
  { fpdName :: Text
  , fpdSchemaName :: Text
  } deriving (Eq, Read, Show)

data DoctrineFunctorDef = DoctrineFunctorDef
  { dfName :: Text
  , dfParams :: [FunctorParamDef]
  , dfIface :: Doctrine
  , dfBody :: Doctrine
  , dfIncl :: Morphism
  } deriving (Eq, Read, Show)


data ModuleEnv = ModuleEnv
  { meDoctrines :: M.Map Text Doctrine
  , meMorphisms :: M.Map Text Morphism
  , meSurfaces :: M.Map Text PolySurfaceDef
  , meModuleElaborators :: M.Map Text ModuleElaboratorDef
  , meModuleDataReprs :: M.Map Text ModuleDataReprDef
  , meModuleSurfaces :: M.Map Text ModuleSurfaceDef
  , mePipelines :: M.Map Text Pipeline
  , meLanguages :: M.Map Text LanguageDef
  , meInterfaces :: M.Map Text InterfaceDef
  , meModules :: M.Map Text ModuleDef
  , meBuilds :: M.Map Text BuildDef
  , meFragments :: M.Map Text FragmentDecl
  , meDerivedDoctrines :: M.Map Text DerivedDoctrine
  , meImplDefaults :: M.Map (Text, Text) [Text]
  , meFunctors :: M.Map Text DoctrineFunctorDef
  , meProofStats :: ProofStats
  }
  deriving (Eq, Read, Show)


emptyEnv :: ModuleEnv
emptyEnv =
  ModuleEnv
    { meDoctrines = M.empty
    , meMorphisms = M.empty
    , meSurfaces = M.empty
    , meModuleElaborators = M.empty
    , meModuleDataReprs = M.empty
    , meModuleSurfaces = M.empty
    , mePipelines = M.empty
    , meLanguages = M.empty
    , meInterfaces = M.empty
    , meModules = M.empty
    , meBuilds = M.empty
    , meFragments = M.empty
    , meDerivedDoctrines = M.empty
    , meImplDefaults = M.empty
    , meFunctors = M.empty
    , meProofStats = emptyProofStats
    }


mergeEnv :: ModuleEnv -> ModuleEnv -> Either Text ModuleEnv
mergeEnv a b = do
  docs <- mergeMap "doctrine" meDoctrines
  morphs <- mergeMap "morphism" meMorphisms
  surfs <- mergeMap "surface" meSurfaces
  moduleElaborators <- mergeMap "module_elaborator" meModuleElaborators
  moduleDataReprs <- mergeMap "data_repr" meModuleDataReprs
  moduleSurfaces <- mergeMap "module_surface" meModuleSurfaces
  pipelines <- mergeMap "pipeline" mePipelines
  languages <- mergeMap "language" meLanguages
  interfaces <- mergeMap "interface" meInterfaces
  modules_ <- mergeMap "module" meModules
  builds <- mergeMap "build" meBuilds
  fragments <- mergeMap "fragment" meFragments
  derived <- mergeMap "derived doctrine" meDerivedDoctrines
  let impls = mergeImplDefaults (meImplDefaults a) (meImplDefaults b)
  functors <- mergeMap "doctrine_functor" meFunctors
  pure
    ModuleEnv
      { meDoctrines = docs
      , meMorphisms = morphs
      , meSurfaces = surfs
      , meModuleElaborators = moduleElaborators
      , meModuleDataReprs = moduleDataReprs
      , meModuleSurfaces = moduleSurfaces
      , mePipelines = pipelines
      , meLanguages = languages
      , meInterfaces = interfaces
      , meModules = modules_
      , meBuilds = builds
      , meFragments = fragments
      , meDerivedDoctrines = derived
      , meImplDefaults = impls
      , meFunctors = functors
      , meProofStats = addProofStats (meProofStats a) (meProofStats b)
      }
  where
    mergeMap label f = mergeNamed label id (f a) (f b)
    mergeImplDefaults left right = M.unionWith mergeDefaults left right
    mergeDefaults xs ys = dedupe (xs <> ys)

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
