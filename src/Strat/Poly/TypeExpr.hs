{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeExpr
  ( TyVar(..)
  , TypeName(..)
  , TypeRef(..)
  , TypeExpr(..)
  , Context
  , typeMode
  , normalizeTypeExpr
  ) where

import Data.Text (Text)
import Strat.Poly.ModeTheory (ModeName, ModExpr(..), ModeTheory, composeMod, normalizeModExpr)


newtype TypeName = TypeName Text deriving (Eq, Ord, Show)

data TypeRef = TypeRef
  { trMode :: ModeName
  , trName :: TypeName
  } deriving (Eq, Ord, Show)

data TyVar = TyVar
  { tvName :: Text
  , tvMode :: ModeName
  } deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeRef [TypeExpr]
  | TMod ModExpr TypeExpr
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

typeMode :: TypeExpr -> ModeName
typeMode ty =
  case ty of
    TVar v -> tvMode v
    TCon r _ -> trMode r
    TMod me _ -> meTgt me

normalizeTypeExpr :: ModeTheory -> TypeExpr -> Either Text TypeExpr
normalizeTypeExpr mt ty =
  case ty of
    TVar _ -> Right ty
    TCon ref args -> do
      args' <- mapM (normalizeTypeExpr mt) args
      Right (TCon ref args')
    TMod me inner0 -> do
      inner <- normalizeTypeExpr mt inner0
      (meComposed, innerBase) <-
        case inner of
          TMod me2 inner2 -> do
            me' <- composeMod mt me2 me
            Right (me', inner2)
          _ -> Right (me, inner)
      if typeMode innerBase /= meSrc meComposed
        then Left "normalizeTypeExpr: modality source does not match inner type mode"
        else do
          let meNorm = normalizeModExpr mt meComposed
          if null (mePath meNorm)
            then Right innerBase
            else Right (TMod meNorm innerBase)
