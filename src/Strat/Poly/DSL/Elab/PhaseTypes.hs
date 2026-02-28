module Strat.Poly.DSL.Elab.PhaseTypes
  ( UniverseSpec(..)
  , ClassificationDeclRaw(..)
  ) where

import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (Obj)
import Strat.Poly.DSL.AST (RawPolyObjExpr)


data UniverseSpec
  = UniverseResolved Obj
  | UniverseRaw RawPolyObjExpr
  deriving (Eq, Show)

data ClassificationDeclRaw = ClassificationDeclRaw
  { cdrClassifier :: ModeName
  , cdrUniverse :: UniverseSpec
  } deriving (Eq, Show)

