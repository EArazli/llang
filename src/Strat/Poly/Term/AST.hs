module Strat.Poly.Term.AST
  ( TermHeadArg(..)
  , TermExpr(..)
  , freeTmVarsExpr
  , boundGlobalsExpr
  , maxTmScopeExpr
  , isPureMetaExpr
  ) where

import qualified Data.Set as S
import Strat.Poly.Literal (Literal)
import Strat.Poly.Names (GenName)
import Strat.Poly.Syntax (Obj, TmVar(..))


data TermHeadArg
  = THAObj Obj
  | THATm TermExpr
  deriving (Eq, Ord, Show)

data TermExpr
  = TMBound Int
  | TMMeta TmVar [Int]
  | TMGen GenName [TermHeadArg]
  | TMLit Literal
  deriving (Eq, Ord, Show)

freeTmVarsExpr :: TermExpr -> S.Set TmVar
freeTmVarsExpr tm =
  case tm of
    TMBound _ -> S.empty
    TMMeta v _ -> S.singleton v
    TMGen _ args -> S.unions (map freeHeadArg args)
    TMLit _ -> S.empty
  where
    freeHeadArg arg =
      case arg of
        THAObj _ -> S.empty
        THATm inner -> freeTmVarsExpr inner

boundGlobalsExpr :: TermExpr -> S.Set Int
boundGlobalsExpr tm =
  case tm of
    TMBound i -> S.singleton i
    TMMeta _ args -> S.fromList args
    TMGen _ args -> S.unions (map boundHeadArg args)
    TMLit _ -> S.empty
  where
    boundHeadArg arg =
      case arg of
        THAObj _ -> S.empty
        THATm inner -> boundGlobalsExpr inner

maxTmScopeExpr :: TermExpr -> Int
maxTmScopeExpr tm =
  case tm of
    TMBound _ -> 0
    TMMeta v _ -> tmvScope v
    TMGen _ args -> maximum (0 : map maxHeadArg args)
    TMLit _ -> 0
  where
    maxHeadArg arg =
      case arg of
        THAObj _ -> 0
        THATm inner -> maxTmScopeExpr inner

isPureMetaExpr :: TermExpr -> Bool
isPureMetaExpr tm =
  case tm of
    TMMeta _ _ -> True
    TMBound _ -> False
    TMGen _ _ -> False
    TMLit _ -> False
