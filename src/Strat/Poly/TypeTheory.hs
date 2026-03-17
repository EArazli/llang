{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , CtorSigEnv
  , UniverseCtors
  , ttCtorTablesByOwner
  , literalKindForObj
  , DefFragment(..)
  , BinderSig(..)
  , BuiltinHeadRole(..)
  , FunctionBuiltin(..)
  , ExtensionalBuiltin(..)
  , RecursiveHeadArgSource(..)
  , BranchInputSource(..)
  , ElimBranchBuiltin(..)
  , InductiveElimBuiltin(..)
  , EliminatorBuiltin(..)
  , BuiltinHeads(..)
  , CtorSig(..)
  , TmHeadSig(..)
  , GenArgSig(..)
  , TmRule(..)
  , setModeDiagramRules
  , emptyBuiltinHeads
  , emptyDefFragment
  , setDefFragment
  , setModeTermHeads
  , setModeTermRules
  , setModeCompiledRules
  , setModeBuiltins
  , setModeTermTRS
  , defFragmentForMode
  , termHeadsForMode
  , termRulesForMode
  , diagramRulesForMode
  , compiledRulesForMode
  , builtinHeadsForMode
  , functionBuiltinForMode
  , extensionalBuiltinForMode
  , eliminatorBuiltinForMode
  , termTRSForMode
  , lookupTmHeadSig
  , lookupGenArgSig
  , modeOnlyTypeTheory
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Cell2 (Cell2)
import Strat.Poly.Literal (LiteralKind)
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import Strat.Poly.Names (GenName)
import Strat.Poly.ObjClassifier (modeClassifierMode)
import Strat.Poly.Term.RewriteSystem (TRS, mkTRS)
import Strat.Poly.Obj
import Strat.Poly.Tele (CtorSig(..), GenParam)

type CtorSigEnv = M.Map ModeName (M.Map ObjName CtorSig)
type UniverseCtors = M.Map ModeName (S.Set ObjName)

data BuiltinHeadRole
  = BuiltinExtensional
  | BuiltinEliminator
  deriving (Eq, Ord, Read, Show)

data BinderSig = BinderSig
  { bsTmCtx :: [Obj]
  , bsDom :: Context
  , bsCod :: Context
  } deriving (Eq, Ord, Read, Show)

data FunctionBuiltin = FunctionBuiltin
  { fbLamGen :: GenName
  , fbAppGen :: GenName
  , fbArrTyCon :: ObjName
  , fbAllowEta :: Bool
  } deriving (Eq, Ord, Read, Show)

data ExtensionalBuiltin
  = BuiltinTransport
  deriving (Eq, Ord, Read, Show)

data RecursiveHeadArgSource
  = RHOuterHeadArg Int
  | RHCtorArg Int
  deriving (Eq, Ord, Read, Show)

data BranchInputSource
  = BISOuterHeadTmParam Int
  | BISCtorHeadTmParam Int
  | BISOuterInput Int
  | BISCtorField Int
  | BISRecursiveResult Int [RecursiveHeadArgSource]
  deriving (Eq, Ord, Read, Show)

data ElimBranchBuiltin = ElimBranchBuiltin
  { ebbCtorGen :: GenName
  , ebbTmCtxInputs :: [BranchInputSource]
  , ebbInputs :: [BranchInputSource]
  } deriving (Eq, Ord, Read, Show)

data InductiveElimBuiltin = InductiveElimBuiltin
  { iebScrutineeIndex :: Int
  , iebScrutineeTyCon :: ObjRef
  , iebBranches :: [ElimBranchBuiltin]
  } deriving (Eq, Ord, Read, Show)

data EliminatorBuiltin
  = BuiltinInductiveElim InductiveElimBuiltin
  deriving (Eq, Ord, Read, Show)

data BuiltinHeads = BuiltinHeads
  { bhFunctionSpace :: Maybe FunctionBuiltin
  , bhExtensionalHeads :: M.Map GenName ExtensionalBuiltin
  , bhEliminators :: M.Map GenName EliminatorBuiltin
  , bhHeadRoles :: M.Map GenName BuiltinHeadRole
  } deriving (Eq, Read, Show)

data DefFragment
  = DefFragment
      { dfMode :: ModeName
      , dfHeads :: M.Map GenName TmHeadSig
      , dfRules :: [TmRule]
      , dfDiagramRules :: [Cell2]
      , dfCompiledRules :: TRS
      , dfBuiltins :: BuiltinHeads
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
  , thsBinders :: [BinderSig]
  , thsRes :: Obj
  } deriving (Eq, Ord, Show)

data GenArgSig = GenArgSig
  { gasParams :: [GenParam]
  } deriving (Eq, Ord, Show)

data TmRule = TmRule
  { trTyVars :: [TmVar]
  , trVars :: [TmVar]
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

emptyBuiltinHeads :: BuiltinHeads
emptyBuiltinHeads =
  BuiltinHeads
    { bhFunctionSpace = Nothing
    , bhExtensionalHeads = M.empty
    , bhEliminators = M.empty
    , bhHeadRoles = M.empty
    }

emptyDefFragment :: ModeName -> DefFragment
emptyDefFragment mode =
  DefFragment
    { dfMode = mode
    , dfHeads = M.empty
    , dfRules = []
    , dfDiagramRules = []
    , dfCompiledRules = mkTRS mode []
    , dfBuiltins = emptyBuiltinHeads
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
    fragment = baseFragment { dfHeads = heads }
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

setModeDiagramRules :: ModeName -> [Cell2] -> TypeTheory -> TypeTheory
setModeDiagramRules mode rules tt =
  setDefFragment fragment tt
  where
    fragment = baseFragment { dfDiagramRules = rules }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

setModeCompiledRules :: ModeName -> TRS -> TypeTheory -> TypeTheory
setModeCompiledRules mode compiled tt =
  setDefFragment fragment tt
  where
    fragment = baseFragment { dfCompiledRules = compiled }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

setModeBuiltins :: ModeName -> BuiltinHeads -> TypeTheory -> TypeTheory
setModeBuiltins mode builtins tt =
  setDefFragment fragment tt
  where
    fragment = baseFragment { dfBuiltins = builtins }
    baseFragment =
      case defFragmentForMode tt mode of
        Just existing -> existing
        Nothing -> emptyDefFragment mode

setModeTermTRS :: ModeName -> TRS -> TypeTheory -> TypeTheory
setModeTermTRS = setModeCompiledRules

defFragmentForMode :: TypeTheory -> ModeName -> Maybe DefFragment
defFragmentForMode tt mode =
  M.lookup mode (ttDefFragments tt)

termHeadsForMode :: TypeTheory -> ModeName -> M.Map GenName TmHeadSig
termHeadsForMode tt mode =
  case defFragmentForMode tt mode of
    Just fragment -> dfHeads fragment
    Nothing -> M.empty

termRulesForMode :: TypeTheory -> ModeName -> [TmRule]
termRulesForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragment { dfRules = rules } -> rules
    Nothing -> []

diagramRulesForMode :: TypeTheory -> ModeName -> [Cell2]
diagramRulesForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragment { dfDiagramRules = rules } -> rules
    Nothing -> []

compiledRulesForMode :: TypeTheory -> ModeName -> TRS
compiledRulesForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragment { dfCompiledRules = trs } -> trs
    Nothing -> mkTRS mode []

termTRSForMode :: TypeTheory -> ModeName -> TRS
termTRSForMode = compiledRulesForMode

builtinHeadsForMode :: TypeTheory -> ModeName -> BuiltinHeads
builtinHeadsForMode tt mode =
  case defFragmentForMode tt mode of
    Just DefFragment { dfBuiltins = builtins } -> builtins
    Nothing -> emptyBuiltinHeads

functionBuiltinForMode :: TypeTheory -> ModeName -> Maybe FunctionBuiltin
functionBuiltinForMode tt mode =
  bhFunctionSpace (builtinHeadsForMode tt mode)

extensionalBuiltinForMode :: TypeTheory -> ModeName -> GenName -> Maybe ExtensionalBuiltin
extensionalBuiltinForMode tt mode g =
  M.lookup g (bhExtensionalHeads (builtinHeadsForMode tt mode))

eliminatorBuiltinForMode :: TypeTheory -> ModeName -> GenName -> Maybe EliminatorBuiltin
eliminatorBuiltinForMode tt mode g =
  M.lookup g (bhEliminators (builtinHeadsForMode tt mode))

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
