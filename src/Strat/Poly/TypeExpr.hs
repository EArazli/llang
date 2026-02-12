{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeExpr
  ( TyVar(..)
  , TypeName(..)
  , TypeRef(..)
  , IxFunName(..)
  , IxVar(..)
  , IxTerm(..)
  , TypeArg(..)
  , TypeExpr(..)
  , Context
  , mapIxTerm
  , mapTypeExpr
  , freeTyVarsType
  , freeIxVarsType
  , freeIxVarsIx
  , boundIxIndicesType
  , boundIxIndicesIx
  , typeMode
  , normalizeTypeExpr
  ) where

import Data.Text (Text)
import qualified Data.Set as S
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

newtype IxFunName = IxFunName Text deriving (Eq, Ord, Show)

data IxVar = IxVar
  { ixvName :: Text
  , ixvSort :: TypeExpr
  , ixvScope :: Int
  } deriving (Eq, Ord, Show)

data IxTerm
  = IXVar IxVar
  | IXBound Int
  | IXFun IxFunName [IxTerm]
  deriving (Eq, Ord, Show)

data TypeArg
  = TAType TypeExpr
  | TAIndex IxTerm
  deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeRef [TypeArg]
  | TMod ModExpr TypeExpr
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

mapIxTerm :: (IxTerm -> IxTerm) -> IxTerm -> IxTerm
mapIxTerm f = go
  where
    go tm =
      f $
        case tm of
          IXVar _ -> tm
          IXBound _ -> tm
          IXFun name args -> IXFun name (map go args)

mapTypeExpr :: (TypeExpr -> TypeExpr) -> (IxTerm -> IxTerm) -> TypeExpr -> TypeExpr
mapTypeExpr fTy fIx = goTy
  where
    goTy ty =
      fTy $
        case ty of
          TVar _ -> ty
          TCon ref args -> TCon ref (map goArg args)
          TMod me inner -> TMod me (goTy inner)
    goArg arg =
      case arg of
        TAType ty -> TAType (goTy ty)
        TAIndex ix -> TAIndex (mapIxTerm fIx ix)

freeTyVarsType :: TypeExpr -> S.Set TyVar
freeTyVarsType ty =
  case ty of
    TVar v -> S.singleton v
    TCon _ args -> S.unions (map freeTyVarsArg args)
    TMod _ inner -> freeTyVarsType inner
  where
    freeTyVarsArg arg =
      case arg of
        TAType innerTy -> freeTyVarsType innerTy
        TAIndex ix -> S.unions (map (freeTyVarsType . ixvSort) (S.toList (freeIxVarsIx ix)))

freeIxVarsIx :: IxTerm -> S.Set IxVar
freeIxVarsIx tm =
  case tm of
    IXVar v -> S.singleton v
    IXBound _ -> S.empty
    IXFun _ args -> S.unions (map freeIxVarsIx args)

freeIxVarsType :: TypeExpr -> S.Set IxVar
freeIxVarsType ty =
  case ty of
    TVar _ -> S.empty
    TCon _ args -> S.unions (map freeIxVarsArg args)
    TMod _ inner -> freeIxVarsType inner
  where
    freeIxVarsArg arg =
      case arg of
        TAType innerTy -> freeIxVarsType innerTy
        TAIndex ix -> freeIxVarsIx ix

boundIxIndicesIx :: IxTerm -> S.Set Int
boundIxIndicesIx tm =
  case tm of
    IXVar _ -> S.empty
    IXBound i -> S.singleton i
    IXFun _ args -> S.unions (map boundIxIndicesIx args)

boundIxIndicesType :: TypeExpr -> S.Set Int
boundIxIndicesType ty =
  case ty of
    TVar _ -> S.empty
    TCon _ args -> S.unions (map boundIxIndicesArg args)
    TMod _ inner -> boundIxIndicesType inner
  where
    boundIxIndicesArg arg =
      case arg of
        TAType innerTy -> boundIxIndicesType innerTy
        TAIndex ix -> boundIxIndicesIx ix

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
      args' <- mapM normalizeArg args
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
  where
    normalizeArg arg =
      case arg of
        TAType innerTy -> TAType <$> normalizeTypeExpr mt innerTy
        TAIndex ix -> Right (TAIndex ix)
