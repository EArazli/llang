{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Attr
  ( AttrSort(..)
  , AttrLitKind(..)
  , AttrSortDecl(..)
  , AttrVar(..)
  , AttrLit(..)
  , AttrTerm(..)
  , AttrSubst
  , AttrName
  , AttrMap
  , freeAttrVarsTerm
  , freeAttrVarsMap
  , applyAttrSubstTerm
  , applyAttrSubstMap
  , composeAttrSubst
  , unifyAttrFlex
  , renderAttrSort
  , renderAttrVar
  , renderAttrTerm
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S


newtype AttrSort = AttrSort Text
  deriving (Eq, Ord, Show)

data AttrLitKind = LKInt | LKString | LKBool
  deriving (Eq, Ord, Show)

data AttrSortDecl = AttrSortDecl
  { asName :: AttrSort
  , asLitKind :: Maybe AttrLitKind
  } deriving (Eq, Show)

data AttrVar = AttrVar
  { avName :: Text
  , avSort :: AttrSort
  } deriving (Eq, Ord, Show)

data AttrLit
  = ALInt Int
  | ALString Text
  | ALBool Bool
  deriving (Eq, Ord, Show)

data AttrTerm
  = ATVar AttrVar
  | ATLit AttrLit
  deriving (Eq, Ord, Show)

type AttrSubst = M.Map AttrVar AttrTerm
type AttrName = Text
type AttrMap = M.Map AttrName AttrTerm

freeAttrVarsTerm :: AttrTerm -> S.Set AttrVar
freeAttrVarsTerm term =
  case term of
    ATVar v -> S.singleton v
    ATLit _ -> S.empty

freeAttrVarsMap :: AttrMap -> S.Set AttrVar
freeAttrVarsMap mp = S.unions (map freeAttrVarsTerm (M.elems mp))

applyAttrSubstTerm :: AttrSubst -> AttrTerm -> AttrTerm
applyAttrSubstTerm subst = go S.empty
  where
    go seen term =
      case term of
        ATLit _ -> term
        ATVar v ->
          case M.lookup v subst of
            Nothing -> term
            Just t ->
              if v `S.member` seen
                then ATVar v
                else go (S.insert v seen) t

applyAttrSubstMap :: AttrSubst -> AttrMap -> AttrMap
applyAttrSubstMap subst = M.map (applyAttrSubstTerm subst)

composeAttrSubst :: AttrSubst -> AttrSubst -> AttrSubst
composeAttrSubst s2 s1 =
  normalizeAttrSubst (M.union s1' s2)
  where
    s1' = M.map (applyAttrSubstTerm s2) s1

unifyAttrFlex :: S.Set AttrVar -> AttrSubst -> AttrTerm -> AttrTerm -> Either Text AttrSubst
unifyAttrFlex flex subst t1 t2 =
  case (applyAttrSubstTerm subst t1, applyAttrSubstTerm subst t2) of
    (ATLit l1, ATLit l2) ->
      if l1 == l2
        then Right subst
        else Left ("unifyAttrFlex: literal mismatch " <> renderAttrTerm (ATLit l1) <> " vs " <> renderAttrTerm (ATLit l2))
    (ATVar v, t) -> unifyVar v t
    (t, ATVar v) -> unifyVar v t
  where
    unifyVar v t
      | v `S.member` flex = bindVar subst v t
      | otherwise =
          case t of
            ATVar v' | v' == v -> Right subst
            _ ->
              Left ("unifyAttrFlex: rigid variable mismatch " <> renderAttrVar v <> " with " <> renderAttrTerm t)

bindVar :: AttrSubst -> AttrVar -> AttrTerm -> Either Text AttrSubst
bindVar subst v t = do
  let t' = applyAttrSubstTerm subst t
  case t' of
    ATVar v'
      | avSort v /= avSort v' ->
          Left ("unifyAttrFlex: sort mismatch " <> renderAttrVar v <> " with " <> renderAttrVar v')
      | otherwise -> bindNormalized t'
    ATLit _ -> bindNormalized t'
  where
    bindNormalized t'
      | t' == ATVar v = Right subst
      | otherwise =
          let one = M.singleton v t'
              subst' = M.insert v t' (M.map (applyAttrSubstTerm one) subst)
          in Right (normalizeAttrSubst subst')

normalizeAttrSubst :: AttrSubst -> AttrSubst
normalizeAttrSubst subst =
  M.fromList
    [ (v, t')
    | (v, t) <- M.toList subst
    , let t' = applyAttrSubstTerm subst t
    , t' /= ATVar v
    ]

renderAttrSort :: AttrSort -> Text
renderAttrSort (AttrSort name) = name

renderAttrVar :: AttrVar -> Text
renderAttrVar v = avName v <> ":" <> renderAttrSort (avSort v)

renderAttrTerm :: AttrTerm -> Text
renderAttrTerm term =
  case term of
    ATVar v -> renderAttrVar v
    ATLit lit ->
      case lit of
        ALInt n -> T.pack (show n)
        ALString s -> T.pack (show s)
        ALBool True -> "true"
        ALBool False -> "false"
