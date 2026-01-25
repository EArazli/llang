{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Compat
  ( compilePresentationToDoctrine2
  , compileTermToDiagram
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (findIndex)
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.Rule (Equation(..))
import Strat.Kernel.Syntax (Binder(..), Term(..), TermNode(..), Var)
import Strat.Kernel.Signature (Signature)
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr (Context, TypeExpr(..))
import Strat.Poly.Diagram
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Doctrine (Doctrine2(..), StructuralLib(..), cartMode)
import Strat.Poly.CartLib


compilePresentationToDoctrine2 :: Presentation -> Either Text Doctrine2
compilePresentationToDoctrine2 pres = do
  let modeTheory = ModeTheory (S.singleton cartMode) M.empty []
  let structByMode = M.fromList [(cartMode, StructCartesian)]
  cells <- mapM (compileEq (presSig pres)) (presEqs pres)
  pure Doctrine2
    { d2Name = presName pres
    , d2ModeTheory = modeTheory
    , d2Sig = presSig pres
    , d2StructByMode = structByMode
    , d2Cells2 = cells
    }

compileEq :: Signature -> Equation -> Either Text Cell2
compileEq sig eq = do
  lhs <- compileTermToDiagram sig cartMode (eqTele eq) (eqLHS eq)
  rhs <- compileTermToDiagram sig cartMode (eqTele eq) (eqRHS eq)
  pure Cell2
    { c2Name = eqName eq
    , c2Class = eqClass eq
    , c2Orient = eqOrient eq
    , c2LHS = lhs
    , c2RHS = rhs
    }


compileTermToDiagram
  :: Signature
  -> ModeName
  -> [Binder]
  -> Term
  -> Either Text Diagram
compileTermToDiagram _sig mode tele term =
  case termNode term of
    TVar v -> do
      idx <- findVarIndex v tele
      let ctx = teleCtx tele
      projWire mode ctx idx
    TOp op args -> do
      let ctx = teleCtx tele
      argDiags <- mapM (compileTermToDiagram _sig mode tele) args
      argsDia <- pairArgs mode ctx argDiags
      let dom = map (TySort . termSort) args
      let cod = [TySort (termSort term)]
      let gen = genD mode dom cod (GLUser op)
      compD gen argsDia


teleCtx :: [Binder] -> Context
teleCtx tele = map (TySort . bSort) tele

findVarIndex :: Var -> [Binder] -> Either Text Int
findVarIndex v tele =
  case findIndex ((== v) . bVar) tele of
    Nothing -> Left "compileTermToDiagram: variable not in telescope"
    Just ix -> Right ix
