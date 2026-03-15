{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , CtorSigEnv
  , UniverseCtors
  , ttCtorTablesByOwner
  , literalKindForObj
  , DefFragment(..)
  , CtorSig(..)
  , TmHeadSig(..)
  , GenArgSig(..)
  , TmRule(..)
  , emptyDefFragment
  , setDefFragment
  , setModeTermHeads
  , setModeTermRules
  , setModeTermTRS
  , setModeNBEConfig
  , defFragmentForMode
  , defEqEngineForMode
  , termHeadsForMode
  , termRulesForMode
  , termTRSForMode
  , nbeConfigForMode
  , lookupTmHeadSig
  , lookupGenArgSig
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Literal (LiteralKind)
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..), DefEqEngine(..), modeDefEqEngine)
import Strat.Poly.Names (GenName)
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)
import Strat.Poly.Term.NBE.Config (NbeConfig, defaultNbeConfig)
import Strat.Poly.Obj
import Strat.Poly.Tele (CtorSig(..), GenParam)

type CtorSigEnv = M.Map ModeName (M.Map ObjName CtorSig)
type UniverseCtors = M.Map ModeName (S.Set ObjName)


data DefFragment
  = DefFragmentTRS
      { dfMode :: ModeName
      , dfHeads :: M.Map GenName TmHeadSig
      , dfRules :: [TmRule]
      , dfTRS :: TRS
      }
  | DefFragmentNBE
      { dfMode :: ModeName
      , dfHeads :: M.Map GenName TmHeadSig
      , dfRules :: [TmRule]
      , dfNBE :: NbeConfig
      }
  deriving (Eq, Show)

data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttCtorSigs :: CtorSigEnv
  , ttUniverseCtors :: UniverseCtors
  , ttLiteralKinds :: M.Map ModeName (M.Map ObjName LiteralKind)
  , ttGenArgSigs :: M.Map ModeName (M.Map GenName GenArgSig)
  , ttDefFragments :: M.Map ModeName DefFragment
  , ttStrictCtorLookup :: Bool
  } deriving (Eq, Show)

data TmHeadSig = TmHeadSig
  { thsParams :: [GenParam]
  , thsInputs :: [Obj]
  , thsRes :: Obj
  } deriving (Eq, Ord, Show)

data GenArgSig = GenArgSig
  { gasParams :: [GenParam]
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
    , ttLiteralKinds = M.empty
    , ttGenArgSigs = M.empty
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
    , dfHeads = M.empty
    , dfRules = []
    , dfTRS = mkTRS mode []
    }

emptyNBEDefFragment :: ModeName -> DefFragment
emptyNBEDefFragment mode =
  DefFragmentNBE
    { dfMode = mode
    , dfHeads = M.empty
    , dfRules = []
    , dfNBE = defaultNbeConfig
    }

setDefFragment :: DefFragment -> TypeTheory -> TypeTheory
setDefFragment fragment tt =
  tt
    { ttDefFragments = M.insert mode fragment (ttDefFragments tt) }
  where
    mode = dfMode fragment

setModeTermHeads :: ModeName -> M.Map GenName TmHeadSig -> TypeTheory -> TypeTheory
setModeTermHeads mode heads tt =
  setDefFragment fragment tt
  where
    fragment =
      case baseFragment of
        trs@DefFragmentTRS {} -> trs { dfHeads = heads }
        nbe@DefFragmentNBE {} -> nbe { dfHeads = heads }
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
            , dfHeads = dfHeads nbeFrag
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
            , dfHeads = dfHeads trsFrag
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

termHeadsForMode :: TypeTheory -> ModeName -> M.Map GenName TmHeadSig
termHeadsForMode tt mode =
  case defFragmentForMode tt mode of
    Just fragment -> dfHeads fragment
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

lookupTmHeadSig :: TypeTheory -> ModeName -> GenName -> Maybe TmHeadSig
lookupTmHeadSig tt mode f =
  M.lookup f (termHeadsForMode tt mode)

lookupGenArgSig :: TypeTheory -> ModeName -> GenName -> Maybe GenArgSig
lookupGenArgSig tt mode g =
  M.lookup g (M.findWithDefault M.empty mode (ttGenArgSigs tt))

literalKindForObj :: TypeTheory -> Obj -> Maybe LiteralKind
literalKindForObj tt obj =
  case objCode obj of
    CTCon ref [] ->
      M.lookup (orName ref) =<< M.lookup (objOwnerMode obj) (ttLiteralKinds tt)
    _ -> Nothing
