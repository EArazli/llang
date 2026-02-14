{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , lookupTmFunSig
  , defaultTmFuel
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.ModeTheory (ModeName, ModeTheory)
import Strat.Poly.TypeExpr


data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttTypeParams :: M.Map TypeRef [TypeParamSig]
  , ttTmFuns :: M.Map ModeName (M.Map TmFunName TmFunSig)
  , ttTmRules :: M.Map ModeName [TmRule]
  , ttTmFuel :: Int
  , ttTmPolicy :: RewritePolicy
  } deriving (Eq, Show)

data TypeParamSig
  = TPS_Ty ModeName
  | TPS_Tm TypeExpr
  deriving (Eq, Ord, Show)

data TmFunSig = TmFunSig
  { tfsArgs :: [TypeExpr]
  , tfsRes :: TypeExpr
  } deriving (Eq, Ord, Show)

data TmRule = TmRule
  { trVars :: [TmVar]
  , trLHS :: TermDiagram
  , trRHS :: TermDiagram
  } deriving (Eq, Ord, Show)

defaultTmFuel :: Int
defaultTmFuel = 200

modeOnlyTypeTheory :: ModeTheory -> TypeTheory
modeOnlyTypeTheory mt =
  TypeTheory
    { ttModes = mt
    , ttTypeParams = M.empty
    , ttTmFuns = M.empty
    , ttTmRules = M.empty
    , ttTmFuel = defaultTmFuel
    , ttTmPolicy = UseOnlyComputationalLR
    }

lookupTmFunSig :: TypeTheory -> ModeName -> TmFunName -> Maybe TmFunSig
lookupTmFunSig tt mode f =
  M.lookup mode (ttTmFuns tt) >>= M.lookup f
