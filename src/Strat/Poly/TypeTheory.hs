{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , CtorSigEnv
  , UniverseCtors
  , ttCtorTablesByOwner
  , DefFragment(..)
  , TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , emptyDefFragment
  , setDefFragment
  , setModeTermFuns
  , setModeTermRules
  , setModeTermTRS
  , setModeNBEConfig
  , defFragmentForMode
  , defEqEngineForMode
  , termFunsForMode
  , termRulesForMode
  , termTRSForMode
  , nbeConfigForMode
  , lookupTmFunSig
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..), DefEqEngine(..), modeDefEqEngine)
import Strat.Poly.Names (GenName)
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)
import Strat.Poly.Term.NBE.Config (NbeConfig, defaultNbeConfig)
import Strat.Poly.Obj

type CtorSigEnv = M.Map ModeName (M.Map ObjName [TypeParamSig])
type UniverseCtors = M.Map ModeName (S.Set ObjName)


data DefFragment
  = DefFragmentTRS
      { dfMode :: ModeName
      , dfFuns :: M.Map GenName TmFunSig
      , dfRules :: [TmRule]
      , dfTRS :: TRS
      }
  | DefFragmentNBE
      { dfMode :: ModeName
      , dfFuns :: M.Map GenName TmFunSig
      , dfRules :: [TmRule]
      , dfNBE :: NbeConfig
      }
  deriving (Eq, Show)

data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttCtorSigs :: CtorSigEnv
  , ttUniverseCtors :: UniverseCtors
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
          [ ( mode
            , case modeDefEqEngine mt mode of
                DefEqTRS -> emptyDefFragment mode
                DefEqNBE -> emptyNBEDefFragment mode
            )
          | mode <- M.keys (mtModes mt)
          ]
   in
  TypeTheory
    { ttModes = mt
    , ttCtorSigs = M.empty
    , ttUniverseCtors = M.empty
    , ttDefFragments = fragments
    , ttStrictCtorLookup = False
    }

ttCtorTablesByOwner :: TypeTheory -> CtorSigEnv
ttCtorTablesByOwner tt =
  M.fromList
    [ (ownerMode, tableForOwner ownerMode)
    | ownerMode <- M.keys (mtModes (ttModes tt))
    ]
  where
    tableForOwner ownerMode =
      let classifierMode = modeClassifierMode (ttModes tt) ownerMode
          sigs = M.findWithDefault M.empty classifierMode (ttCtorSigs tt)
          eligible = M.findWithDefault S.empty ownerMode (ttUniverseCtors tt)
       in M.filterWithKey (\name _ -> S.member name eligible) sigs

emptyDefFragment :: ModeName -> DefFragment
emptyDefFragment mode =
  DefFragmentTRS
    { dfMode = mode
    , dfFuns = M.empty
    , dfRules = []
    , dfTRS = mkTRS mode []
    }

emptyNBEDefFragment :: ModeName -> DefFragment
emptyNBEDefFragment mode =
  DefFragmentNBE
    { dfMode = mode
    , dfFuns = M.empty
    , dfRules = []
    , dfNBE = defaultNbeConfig
    }

setDefFragment :: DefFragment -> TypeTheory -> TypeTheory
setDefFragment fragment tt =
  tt
    { ttDefFragments = M.insert mode fragment (ttDefFragments tt) }
  where
    mode = dfMode fragment

setModeTermFuns :: ModeName -> M.Map GenName TmFunSig -> TypeTheory -> TypeTheory
setModeTermFuns mode funs tt =
  setDefFragment fragment tt
  where
    fragment =
      case baseFragment of
        trs@DefFragmentTRS {} -> trs { dfFuns = funs }
        nbe@DefFragmentNBE {} -> nbe { dfFuns = funs }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing ->
          case defEqEngineForMode tt mode of
            DefEqNBE -> emptyNBEDefFragment mode
            DefEqTRS -> emptyDefFragment mode

setModeTermRules :: ModeName -> [TmRule] -> TypeTheory -> TypeTheory
setModeTermRules mode rules tt =
  setDefFragment fragment tt
  where
    fragment =
      case baseFragment of
        trs@DefFragmentTRS {} -> trs { dfRules = rules }
        nbe@DefFragmentNBE {} -> nbe { dfRules = rules }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing ->
          case defEqEngineForMode tt mode of
            DefEqNBE -> emptyNBEDefFragment mode
            DefEqTRS -> emptyDefFragment mode

setModeTermTRS :: ModeName -> TRS -> TypeTheory -> TypeTheory
setModeTermTRS mode trs tt =
  setDefFragment fragment tt
  where
    fragment =
      case baseFragment of
        trsFrag@DefFragmentTRS {} ->
          trsFrag { dfTRS = trs }
        nbeFrag@DefFragmentNBE {} ->
          DefFragmentTRS
            { dfMode = dfMode nbeFrag
            , dfFuns = dfFuns nbeFrag
            , dfRules = dfRules nbeFrag
            , dfTRS = trs
            }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

setModeNBEConfig :: ModeName -> NbeConfig -> TypeTheory -> TypeTheory
setModeNBEConfig mode cfg tt =
  setDefFragment fragment tt
  where
    fragment =
      case baseFragment of
        trsFrag@DefFragmentTRS {} ->
          DefFragmentNBE
            { dfMode = dfMode trsFrag
            , dfFuns = dfFuns trsFrag
            , dfRules = dfRules trsFrag
            , dfNBE = cfg
            }
        nbeFrag@DefFragmentNBE {} ->
          nbeFrag { dfNBE = cfg }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyNBEDefFragment mode

defFragmentForMode :: TypeTheory -> ModeName -> Maybe DefFragment
defFragmentForMode tt mode =
  M.lookup mode (ttDefFragments tt)

defEqEngineForMode :: TypeTheory -> ModeName -> DefEqEngine
defEqEngineForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragmentTRS {} -> DefEqTRS
    Just DefFragmentNBE {} -> DefEqNBE
    Nothing -> modeDefEqEngine (ttModes tt) mode

termFunsForMode :: TypeTheory -> ModeName -> M.Map GenName TmFunSig
termFunsForMode tt mode =
  case defFragmentForMode tt mode of
    Just fragment -> dfFuns fragment
    Nothing -> M.empty

termRulesForMode :: TypeTheory -> ModeName -> [TmRule]
termRulesForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragmentTRS { dfRules = rules } -> rules
    Just DefFragmentNBE {} -> []
    Nothing -> []

termTRSForMode :: TypeTheory -> ModeName -> TRS
termTRSForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragmentTRS { dfTRS = trs } -> trs
    Just DefFragmentNBE {} -> mkTRS mode []
    Nothing -> mkTRS mode []

nbeConfigForMode :: TypeTheory -> ModeName -> Maybe NbeConfig
nbeConfigForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragmentNBE { dfNBE = cfg } -> Just cfg
    _ -> Nothing

lookupTmFunSig :: TypeTheory -> ModeName -> GenName -> Maybe TmFunSig
lookupTmFunSig tt mode f =
  M.lookup f (termFunsForMode tt mode)
