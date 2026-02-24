{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , DefFragment(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , emptyDefFragment
  , setDefFragment
  , setModeTermFuns
  , setModeTermRules
  , setModeTermTRS
  , defFragmentForMode
  , termFunsForMode
  , termRulesForMode
  , termTRSForMode
  , lookupTmFunSig
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)
import Strat.Poly.Obj


data DefFragment = DefFragment
  { dfMode :: ModeName
  , dfFuns :: M.Map TmFunName TmFunSig
  , dfRules :: [TmRule]
  , dfTRS :: TRS
  } deriving (Eq, Show)

data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttCtorTables :: M.Map ModeName (M.Map ObjName [TypeParamSig])
  , ttObjParams :: M.Map ObjRef [TypeParamSig]
  , ttDefFragments :: M.Map ModeName DefFragment
  , ttStrictCtorLookup :: Bool
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
  let fragments =
        M.fromList
          [ (mode, emptyDefFragment mode)
          | mode <- M.keys (mtModes mt)
          ]
   in
  TypeTheory
    { ttModes = mt
    , ttCtorTables = M.empty
    , ttObjParams = M.empty
    , ttDefFragments = fragments
    , ttStrictCtorLookup = False
    }

emptyDefFragment :: ModeName -> DefFragment
emptyDefFragment mode =
  DefFragment
    { dfMode = mode
    , dfFuns = M.empty
    , dfRules = []
    , dfTRS = mkTRS mode []
    }

setDefFragment :: DefFragment -> TypeTheory -> TypeTheory
setDefFragment fragment tt =
  tt
    { ttDefFragments = M.insert mode fragment (ttDefFragments tt) }
  where
    mode = dfMode fragment

setModeTermFuns :: ModeName -> M.Map TmFunName TmFunSig -> TypeTheory -> TypeTheory
setModeTermFuns mode funs tt =
  setDefFragment fragment tt
  where
    fragment = baseFragment { dfFuns = funs }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

setModeTermRules :: ModeName -> [TmRule] -> TypeTheory -> TypeTheory
setModeTermRules mode rules tt =
  setDefFragment fragment tt
  where
    fragment = baseFragment { dfRules = rules }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

setModeTermTRS :: ModeName -> TRS -> TypeTheory -> TypeTheory
setModeTermTRS mode trs tt =
  setDefFragment fragment tt
  where
    fragment = baseFragment { dfTRS = trs }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

defFragmentForMode :: TypeTheory -> ModeName -> Maybe DefFragment
defFragmentForMode tt mode =
  M.lookup mode (ttDefFragments tt)

termFunsForMode :: TypeTheory -> ModeName -> M.Map TmFunName TmFunSig
termFunsForMode tt mode =
  case defFragmentForMode tt mode of
    Just fragment -> dfFuns fragment
    Nothing -> M.empty

termRulesForMode :: TypeTheory -> ModeName -> [TmRule]
termRulesForMode tt mode =
  case defFragmentForMode tt mode of
    Just fragment -> dfRules fragment
    Nothing -> []

termTRSForMode :: TypeTheory -> ModeName -> TRS
termTRSForMode tt mode =
  case defFragmentForMode tt mode of
    Just fragment -> dfTRS fragment
    Nothing -> mkTRS mode []

lookupTmFunSig :: TypeTheory -> ModeName -> TmFunName -> Maybe TmFunSig
lookupTmFunSig tt mode f =
  M.lookup f (termFunsForMode tt mode)
