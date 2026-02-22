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
import Strat.Poly.Term.RewriteSystem (TRS)
import Strat.Poly.Obj


data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttObjParams :: M.Map ObjRef [TypeParamSig]
  , ttTmFuns :: M.Map ModeName (M.Map TmFunName TmFunSig)
  , ttTmRules :: M.Map ModeName [TmRule]
  , ttTmTRS :: M.Map ModeName TRS
  } deriving (Eq, Show)

data TypeParamSig
  = TPS_Ty ModeName
  | TPS_Tm Obj
  deriving (Eq, Ord, Show)

data TmFunSig = TmFunSig
  { tfsArgs :: [Obj]
  , tfsRes :: Obj
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
    , ttObjParams = M.empty
    , ttTmFuns = M.empty
    , ttTmRules = M.empty
    , ttTmTRS = M.empty
    }

lookupTmFunSig :: TypeTheory -> ModeName -> TmFunName -> Maybe TmFunSig
lookupTmFunSig tt mode f =
  M.lookup mode (ttTmFuns tt) >>= M.lookup f
