{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Morphism
  ( Morphism(..)
  , OpInterp(..)
  , MorphismCheck(..)
  , MorphismError(..)
  , applyMorphismSort
  , applyMorphismTerm
  , applyOpInterp
  , lookupInterp
  , checkMorphism
  , joinableWithin
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.AlphaEq
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Subst (applySubstSort, applySubstTerm)
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)


data OpInterp = OpInterp
  { oiTele :: [Binder]
  , oiRhs  :: Term
  }
  deriving (Eq, Show)

data Morphism = Morphism
  { morName    :: Text
  , morSrc     :: Presentation
  , morTgt     :: Presentation
  , morSortMap :: M.Map SortName SortName
  , morOpMap   :: M.Map OpName OpInterp
  , morCheck   :: MorphismCheck
  }
  deriving (Eq, Show)


data MorphismCheck = MorphismCheck
  { mcPolicy :: RewritePolicy
  , mcFuel   :: Int
  }
  deriving (Eq, Show)


data MorphismError
  = MorphismMissingSort SortName
  | MorphismMissingOp OpName
  | MorphismUnknownSort SortName
  | MorphismUnknownOp OpName
  | MorphismSortMismatch SortName SortName
  | MorphismOpMismatch OpName OpName
  | MorphismCompileError Text
  | MorphismEqViolation Text Term Term
  | MorphismEqUndecided Text RewritePolicy Int
  deriving (Eq, Show)


applyMorphismSort :: Morphism -> Sort -> Sort
applyMorphismSort mor (Sort name idx) =
  let name' = M.findWithDefault name name (morSortMap mor)
  in Sort name' (map (applyMorphismTerm mor) idx)

applyMorphismTerm :: Morphism -> Term -> Term
applyMorphismTerm mor tm =
  case termNode tm of
    TVar v ->
      Term { termSort = applyMorphismSort mor (termSort tm), termNode = TVar v }
    TOp op args ->
      let args' = map (applyMorphismTerm mor) args
      in case M.lookup op (morOpMap mor) of
          Nothing ->
            Term { termSort = applyMorphismSort mor (termSort tm)
                 , termNode = TOp op args'
                 }
          Just interp ->
            applyOpInterp interp args'

applyOpInterp :: OpInterp -> [Term] -> Term
applyOpInterp interp args =
  let tele = oiTele interp
      subst =
        M.fromList
          [ (v, arg)
          | (Binder v _, arg) <- zip tele args
          ]
  in applySubstTerm subst (oiRhs interp)

lookupInterp :: Morphism -> OpName -> Either Text OpInterp
lookupInterp mor op =
  case M.lookup op (morOpMap mor) of
    Nothing -> Left ("Unknown op in morphism: " <> renderOpName op)
    Just interp -> Right interp


checkMorphism :: RewritePolicy -> Int -> Morphism -> Either MorphismError ()
checkMorphism pol fuel mor = do
  checkSortMappings
  checkOpMappings
  checkEquations
  where
    sigSrc = presSig (morSrc mor)
    sigTgt = presSig (morTgt mor)
    checkSortMappings =
      mapM_ (checkSortCtor pol) (M.toList (sigSortCtors sigSrc))

    checkSortCtor _ (sName, ctor) =
      case M.lookup sName (morSortMap mor) of
        Nothing -> Left (MorphismMissingSort sName)
        Just tgtName ->
          case M.lookup tgtName (sigSortCtors sigTgt) of
            Nothing -> Left (MorphismUnknownSort tgtName)
            Just tgtCtor ->
              let mapped = mapSortCtor mor ctor
              in if alphaEqSortCtor mapped tgtCtor
                   then Right ()
                   else Left (MorphismSortMismatch sName tgtName)

    checkOpMappings =
      mapM_ checkOpDecl (M.toList (sigOps sigSrc))

    checkOpDecl (opName, decl) =
      case M.lookup opName (morOpMap mor) of
        Nothing -> Left (MorphismMissingOp opName)
        Just interp -> checkOpInterp decl interp

    checkOpInterp decl interp = do
      let teleSrc = opTele decl
      let teleTgt = oiTele interp
      if length teleSrc /= length teleTgt
        then Left (MorphismOpMismatch (opName decl) (opName decl))
        else do
          let subst =
                M.fromList
                  [ (v, mkVar (bSort bTgt) vTgt)
                  | (Binder v _, bTgt@(Binder vTgt _)) <- zip teleSrc teleTgt
                  ]
          let checkBinder (Binder _ sSrc) (Binder _ sTgt) = do
                let sSrc' = applySubstSort subst (applyMorphismSort mor sSrc)
                if sSrc' == sTgt then Right () else Left (MorphismOpMismatch (opName decl) (opName decl))
          mapM_ (uncurry checkBinder) (zip teleSrc teleTgt)
          let res' = applySubstSort subst (applyMorphismSort mor (opResult decl))
          let rhsSort = termSort (oiRhs interp)
          if res' == rhsSort
            then Right ()
            else Left (MorphismOpMismatch (opName decl) (opName decl))
    checkEquations = do
      rsTgt <-
        case compileRewriteSystem pol (morTgt mor) of
          Left err -> Left (MorphismCompileError err)
          Right rs -> Right rs
      mapM_ (checkEquation rsTgt) (presEqs (morSrc mor))

    checkEquation rs eq = do
      let lhs' = applyMorphismTerm mor (eqLHS eq)
      let rhs' = applyMorphismTerm mor (eqRHS eq)
      let (nfL, okL) = normalizeStatus fuel rs lhs'
      let (nfR, okR) = normalizeStatus fuel rs rhs'
      if okL && okR
        then if nfL == nfR
          then Right ()
          else Left (MorphismEqViolation (eqName eq) nfL nfR)
        else
          if joinableWithin fuel rs lhs' rhs'
            then Right ()
            else Left (MorphismEqUndecided (eqName eq) pol fuel)


mapSortCtor :: Morphism -> SortCtor -> SortCtor
mapSortCtor mor ctor =
  ctor { scTele = map (mapBinderSort mor) (scTele ctor) }

mapBinderSort :: Morphism -> Binder -> Binder
mapBinderSort mor b = b { bSort = applyMorphismSort mor (bSort b) }

renderOpName :: OpName -> Text
renderOpName (OpName t) = t


normalizeStatus :: Int -> RewriteSystem -> Term -> (Term, Bool)
normalizeStatus fuel rs t0 = go fuel t0
  where
    go n t
      | n <= 0 =
          if null (rewriteOnce rs t)
            then (t, True)
            else (t, False)
      | otherwise =
          case rewriteOnce rs t of
            [] -> (t, True)
            reds ->
              case chooseRedex reds of
                Nothing -> (t, True)
                Just r  -> go (n - 1) (redexTo r)

joinableWithin :: Int -> RewriteSystem -> Term -> Term -> Bool
joinableWithin fuel rs t1 t2 =
  let reach1 = reachable fuel rs t1
      reach2 = reachable fuel rs t2
  in not (S.null (S.intersection reach1 reach2))

reachable :: Int -> RewriteSystem -> Term -> S.Set Term
reachable fuel rs t0 = go fuel (S.singleton t0) (S.singleton t0)
  where
    go n frontier seen
      | n <= 0 = seen
      | S.null frontier = seen
      | otherwise =
          let next = S.fromList [ redexTo r | t <- S.toList frontier, r <- rewriteOnce rs t ]
              newFrontier = S.difference next seen
              seen' = S.union seen next
          in go (n - 1) newFrontier seen'
