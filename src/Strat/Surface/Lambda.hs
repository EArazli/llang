{-# LANGUAGE OverloadedStrings #-}
module Strat.Surface.Lambda
  ( LamTerm(..)
  , toCombTerm
  ) where

import Strat.Surface.Combinator
import Data.Text (Text)
import qualified Data.Set as S


data LamTerm
  = LVar Text
  | LLam Text LamTerm
  | LApp LamTerm LamTerm
  deriving (Eq, Show)

-- Internal combinator expression for abstraction
data CombExpr
  = CV Text
  | CS
  | CK
  | CI
  | CApp CombExpr CombExpr
  deriving (Eq, Show)


toCombTerm :: LamTerm -> CombTerm
toCombTerm = combExprToCombTerm . toCombExpr


toCombExpr :: LamTerm -> CombExpr
toCombExpr term =
  case term of
    LVar x -> CV x
    LApp t u -> CApp (toCombExpr t) (toCombExpr u)
    LLam x t -> abstract x (toCombExpr t)

abstract :: Text -> CombExpr -> CombExpr
abstract x expr =
  case expr of
    CV y | y == x -> CI
    _ | x `S.notMember` freeVars expr -> CApp CK expr
    CApp a b -> CApp (CApp CS (abstract x a)) (abstract x b)
    _ -> CApp CK expr

freeVars :: CombExpr -> S.Set Text
freeVars expr =
  case expr of
    CV x -> S.singleton x
    CS -> S.empty
    CK -> S.empty
    CI -> S.empty
    CApp a b -> freeVars a `S.union` freeVars b

combExprToCombTerm :: CombExpr -> CombTerm
combExprToCombTerm expr =
  case expr of
    CV x -> COp x []
    CS -> COp "S" []
    CK -> COp "K" []
    CI -> COp "I" []
    CApp a b -> COp "app" [combExprToCombTerm a, combExprToCombTerm b]
