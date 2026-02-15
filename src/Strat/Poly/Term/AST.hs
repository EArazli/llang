module Strat.Poly.Term.AST
  ( TermExpr(..)
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  , sameTmMetaId
  ) where

import qualified Data.Set as S
import Strat.Poly.TypeExpr (TmFunName, TmVar(..))


data TermExpr
  = TMVar TmVar
  | TMBound Int
  | TMFun TmFunName [TermExpr]
  deriving (Eq, Ord, Show)

freeTmVarsExpr :: TermExpr -> S.Set TmVar
freeTmVarsExpr tm =
  case tm of
    TMVar v -> S.singleton v
    TMBound _ -> S.empty
    TMFun _ args -> S.unions (map freeTmVarsExpr args)

boundGlobalsExpr :: TermExpr -> S.Set Int
boundGlobalsExpr tm =
  case tm of
    TMVar _ -> S.empty
    TMBound i -> S.singleton i
    TMFun _ args -> S.unions (map boundGlobalsExpr args)

maxTmScopeExpr :: TermExpr -> Int
maxTmScopeExpr tm =
  case tm of
    TMVar v -> tmvScope v
    TMBound _ -> 0
    TMFun _ args -> maximum (0 : map maxTmScopeExpr args)

isPureMetaExpr :: TermExpr -> Bool
isPureMetaExpr tm =
  case tm of
    TMVar _ -> True
    TMBound _ -> False
    TMFun _ _ -> False

sameTmMetaId :: TmVar -> TmVar -> Bool
sameTmMetaId a b = tmvName a == tmvName b && tmvScope a == tmvScope b
