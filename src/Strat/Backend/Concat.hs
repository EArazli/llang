module Strat.Backend.Concat
  ( CatExpr(..)
  , compileTerm
  ) where

import Strat.Kernel.Syntax
import Data.Text (Text)
import qualified Data.Text as T

data CatExpr
  = CatVar Text
  | CatOp OpName [CatExpr]
  deriving (Eq, Show)

compileTerm :: Term -> CatExpr
compileTerm tm =
  case termNode tm of
    TVar v -> CatVar (renderVar v)
    TOp op args -> CatOp op (map compileTerm args)

renderVar :: Var -> Text
renderVar v =
  case vScope v of
    ScopeId s -> s <> T.singleton ':' <> T.pack (show (vLocal v))
