{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeExpr
  ( TyVar(..)
  , TypeName(..)
  , TypeRef(..)
  , TmFunName(..)
  , TmVar(..)
  , TermDiagram(..)
  , TypeArg(..)
  , TypeExpr(..)
  , Context
  , mapTermDiagram
  , mapTypeExpr
  , freeTyVarsType
  , freeTyVarsTerm
  , freeTmVarsType
  , freeTmVarsTerm
  , boundTmIndicesType
  , boundTmIndicesTerm
  , tmCtxForMode
  , typeMode
  , normalizeTypeExpr
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Strat.Poly.ModeTheory (ModeName, ModExpr(..), ModeTheory, composeMod, normalizeModExpr)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..), getPortLabel, unPortId)


newtype TypeName = TypeName Text deriving (Eq, Ord, Show)

data TypeRef = TypeRef
  { trMode :: ModeName
  , trName :: TypeName
  } deriving (Eq, Ord, Show)

data TyVar = TyVar
  { tvName :: Text
  , tvMode :: ModeName
  } deriving (Eq, Ord, Show)

newtype TmFunName = TmFunName Text deriving (Eq, Ord, Show)

data TmVar = TmVar
  { tmvName :: Text
  , tmvSort :: TypeExpr
  , tmvScope :: Int
  } deriving (Eq, Ord, Show)

newtype TermDiagram = TermDiagram { unTerm :: Diagram }
  deriving (Eq, Ord, Show)

data TypeArg
  = TAType TypeExpr
  | TATm TermDiagram
  deriving (Eq, Ord, Show)

data TypeExpr
  = TVar TyVar
  | TCon TypeRef [TypeArg]
  | TMod ModExpr TypeExpr
  deriving (Eq, Ord, Show)

type Context = [TypeExpr]

mapTermDiagram :: (TermDiagram -> TermDiagram) -> TermDiagram -> TermDiagram
mapTermDiagram f tm = f tm

mapTypeExpr :: (TypeExpr -> TypeExpr) -> (TermDiagram -> TermDiagram) -> TypeExpr -> TypeExpr
mapTypeExpr fTy fTm = goTy
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
        TATm tm -> TATm (mapTermDiagram fTm tm)

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
        TATm tm -> freeTyVarsTerm tm

freeTyVarsTerm :: TermDiagram -> S.Set TyVar
freeTyVarsTerm (TermDiagram diag) =
  S.unions
    [ S.unions (map freeTyVarsType (IM.elems (dPortTy diag)))
    , S.unions (map freeTyVarsType (dTmCtx diag))
    , S.unions (map edgeTyVars (IM.elems (dEdges diag)))
    ]
  where
    edgeTyVars edge =
      case ePayload edge of
        PTmMeta v -> freeTyVarsType (tmvSort v)
        _ -> S.empty

freeTmVarsTerm :: TermDiagram -> S.Set TmVar
freeTmVarsTerm (TermDiagram diag) =
  S.unions
    [ S.unions (map freeTmVarsType (IM.elems (dPortTy diag)))
    , S.unions (map freeTmVarsType (dTmCtx diag))
    , S.unions (map edgeTmVars (IM.elems (dEdges diag)))
    ]
  where
    edgeTmVars edge =
      case ePayload edge of
        PTmMeta v -> S.singleton v
        _ -> S.empty

freeTmVarsType :: TypeExpr -> S.Set TmVar
freeTmVarsType ty =
  case ty of
    TVar _ -> S.empty
    TCon _ args -> S.unions (map freeTmVarsArg args)
    TMod _ inner -> freeTmVarsType inner
  where
    freeTmVarsArg arg =
      case arg of
        TAType innerTy -> freeTmVarsType innerTy
        TATm tm -> freeTmVarsTerm tm

boundTmIndicesTerm :: TermDiagram -> S.Set Int
boundTmIndicesTerm (TermDiagram diag) =
  S.fromList
    [ globalTm
    | (localPos, pid) <- zip [0 :: Int ..] (dIn diag)
    , inputIsUsed pid
    , let globalTm = resolveGlobal localPos pid
    ]
  where
    inputIsUsed pid =
      pid `elem` dOut diag
        || case IM.lookup (unPortId pid) (dCons diag) of
             Just (Just _) -> True
             _ -> False

    resolveGlobal localPos pid =
      case getPortLabel diag pid >>= decodeTmCtxLabel of
        Just globalTm -> globalTm
        Nothing ->
          case drop localPos globals of
            (globalTm:_) -> globalTm
            [] -> localPos

    globals =
      [ i
      | (i, ty) <- zip [0 :: Int ..] (dTmCtx diag)
      , typeMode ty == dMode diag
      ]

    decodeTmCtxLabel lbl =
      case T.stripPrefix "tmctx:" lbl of
        Nothing -> Nothing
        Just raw ->
          case reads (T.unpack raw) of
            [(n, "")] -> Just n
            _ -> Nothing

boundTmIndicesType :: TypeExpr -> S.Set Int
boundTmIndicesType ty =
  case ty of
    TVar _ -> S.empty
    TCon _ args -> S.unions (map boundTmIndicesArg args)
    TMod _ inner -> boundTmIndicesType inner
  where
    boundTmIndicesArg arg =
      case arg of
        TAType innerTy -> boundTmIndicesType innerTy
        TATm tm -> boundTmIndicesTerm tm

tmCtxForMode :: [TypeExpr] -> ModeName -> [TypeExpr]
tmCtxForMode tele mode =
  [ ty
  | ty <- tele
  , typeMode ty == mode
  ]

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
        TATm tm -> Right (TATm tm)
