module Strat.Poly.Term.AST
  ( TermExpr(..)
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  ) where

import qualified Data.Set as S
import Strat.Poly.Syntax (TmFunName, TmVar(..))


data TermExpr
  = TMBound Int
  | TMMeta TmVar [Int]
  | TMFun TmFunName [TermExpr]
  deriving (Eq, Ord, Show)

freeTmVarsExpr :: TermExpr -> S.Set TmVar
freeTmVarsExpr tm =
  case tm of
    TMBound _ -> S.empty
    TMMeta v _ -> S.singleton v
    TMFun _ args -> S.unions (map freeTmVarsExpr args)

boundGlobalsExpr :: TermExpr -> S.Set Int
boundGlobalsExpr tm =
  case tm of
    TMBound i -> S.singleton i
    TMMeta _ args -> S.fromList args
    TMFun _ args -> S.unions (map boundGlobalsExpr args)

maxTmScopeExpr :: TermExpr -> Int
maxTmScopeExpr tm =
  case tm of
    TMBound _ -> 0
    TMMeta v _ -> tmvScope v
    TMFun _ args -> maximum (0 : map maxTmScopeExpr args)

isPureMetaExpr :: TermExpr -> Bool
isPureMetaExpr tm =
  case tm of
    TMMeta _ _ -> True
    TMBound _ -> False
    TMFun _ _ -> False
