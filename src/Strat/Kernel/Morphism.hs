{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Morphism
  ( Morphism(..)
  , MorphismCheck(..)
  , MorphismError(..)
  , applyMorphismSort
  , applyMorphismTerm
  , checkMorphism
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Subst (applySubstSort)
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)


data Morphism = Morphism
  { morName    :: Text
  , morSrc     :: Presentation
  , morTgt     :: Presentation
  , morSortMap :: M.Map SortName SortName
  , morOpMap   :: M.Map OpName OpName
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
  Term
    { termSort = applyMorphismSort mor (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar v
          TOp op args ->
            let op' = M.findWithDefault op op (morOpMap mor)
            in TOp op' (map (applyMorphismTerm mor) args)
    }


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
        Just tgtName ->
          case M.lookup tgtName (sigOps sigTgt) of
            Nothing -> Left (MorphismUnknownOp tgtName)
            Just tgtDecl ->
              let mapped = mapOpDecl mor decl
              in if alphaEqOpDecl mapped tgtDecl
                   then Right ()
                   else Left (MorphismOpMismatch opName tgtName)

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

mapOpDecl :: Morphism -> OpDecl -> OpDecl
mapOpDecl mor decl =
  decl
    { opTele = map (mapBinderSort mor) (opTele decl)
    , opResult = applyMorphismSort mor (opResult decl)
    }

mapBinderSort :: Morphism -> Binder -> Binder
mapBinderSort mor b = b { bSort = applyMorphismSort mor (bSort b) }


alphaEqSortCtor :: SortCtor -> SortCtor -> Bool
alphaEqSortCtor c1 c2 =
  let tele1 = scTele c1
      tele2 = scTele c2
  in length tele1 == length tele2
      && and (zipWith alphaEqBinder tele1 tele2)
  where
    subst =
      M.fromList
        [ (v2, mkVar s1 v1)
        | (Binder v1 s1, Binder v2 _) <- zip (scTele c1) (scTele c2)
        ]
    alphaEqBinder (Binder _ s1) (Binder _ s2) =
      let s2' = applySubstSort subst s2
      in s1 == s2'

alphaEqOpDecl :: OpDecl -> OpDecl -> Bool
alphaEqOpDecl d1 d2 =
  let tele1 = opTele d1
      tele2 = opTele d2
  in length tele1 == length tele2
      && and (zipWith alphaEqBinder tele1 tele2)
      && opResult d1 == applySubstSort subst (opResult d2)
  where
    subst =
      M.fromList
        [ (v2, mkVar s1 v1)
        | (Binder v1 s1, Binder v2 _) <- zip (opTele d1) (opTele d2)
        ]
    alphaEqBinder (Binder _ s1) (Binder _ s2) =
      let s2' = applySubstSort subst s2
      in s1 == s2'


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
