{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , lookupTmFunSig
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName, ModeTheory)
import Strat.Poly.TypeExpr


data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttTypeParams :: M.Map TypeRef [TypeParamSig]
  , ttTmFuns :: M.Map ModeName (M.Map TmFunName TmFunSig)
  , ttTmRules :: M.Map ModeName [TmRule]
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

modeOnlyTypeTheory :: ModeTheory -> TypeTheory
modeOnlyTypeTheory mt =
  TypeTheory
    { ttModes = mt
    , ttTypeParams = M.empty
    , ttTmFuns = M.empty
    , ttTmRules = M.empty
    }

lookupTmFunSig :: TypeTheory -> ModeName -> TmFunName -> Maybe TmFunSig
lookupTmFunSig tt mode f =
  M.lookup mode (ttTmFuns tt) >>= M.lookup f
