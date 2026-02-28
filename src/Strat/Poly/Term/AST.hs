module Strat.Poly.Term.AST
  ( TermExpr(..)
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  , sameTmMetaId
  ) where

import qualified Data.Set as S
import Strat.Poly.Syntax (TmFunName, TmVar(..), TmMeta(..), tmMetaToTmVar)


data TermExpr
  = TMVar TmVar
  | TMBound Int
  | TMMeta TmMeta [Int]
  | TMFun TmFunName [TermExpr]
  deriving (Eq, Ord, Show)

freeTmVarsExpr :: TermExpr -> S.Set TmVar
freeTmVarsExpr tm =
  case tm of
    TMVar v -> S.singleton v
    TMBound _ -> S.empty
    TMMeta v _ -> S.singleton (tmMetaToTmVar v)
    TMFun _ args -> S.unions (map freeTmVarsExpr args)

boundGlobalsExpr :: TermExpr -> S.Set Int
boundGlobalsExpr tm =
  case tm of
    TMVar _ -> S.empty
    TMBound i -> S.singleton i
    TMMeta _ args -> S.fromList args
    TMFun _ args -> S.unions (map boundGlobalsExpr args)

maxTmScopeExpr :: TermExpr -> Int
maxTmScopeExpr tm =
  case tm of
    TMVar v -> tmvScope v
    TMBound _ -> 0
    TMMeta v _ -> tmmScope v
    TMFun _ args -> maximum (0 : map maxTmScopeExpr args)

isPureMetaExpr :: TermExpr -> Bool
isPureMetaExpr tm =
  case tm of
    TMVar _ -> True
    TMMeta _ _ -> True
    TMBound _ -> False
    TMFun _ _ -> False

sameTmMetaId :: TmMeta -> TmMeta -> Bool
sameTmMetaId a b =
  let a' = tmMetaToTmVar a
      b' = tmMetaToTmVar b
   in tmvName a' == tmvName b' && tmvScope a' == tmvScope b'
