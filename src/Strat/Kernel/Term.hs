module Strat.Kernel.Term where

import Strat.Kernel.Signature
import Strat.Kernel.Subst
import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M

data TypeError
  = UnknownOp OpName
  | ArityMismatch OpName Int Int
  | ArgSortMismatch OpName Int Sort Sort
  deriving (Eq, Show)

mkVar :: Sort -> Var -> Term
mkVar s v = Term { termSort = s, termNode = TVar v }

mkOp :: Signature -> OpName -> [Term] -> Either TypeError Term
mkOp sig name args =
  case M.lookup name (sigOps sig) of
    Nothing -> Left (UnknownOp name)
    Just decl ->
      let tele = opTele decl
          expected = length tele
          actual = length args
      in if expected /= actual
           then Left (ArityMismatch name expected actual)
           else do
             subst <- foldl step (Right M.empty) (zip3 [0 ..] tele args)
             let resSort = applySubstSort subst (opResult decl)
             pure Term { termSort = resSort, termNode = TOp name args }
  where
    step acc (ix, Binder v s, arg) = do
      subst <- acc
      let expectedSort = applySubstSort subst s
      let actualSort = applySubstSort subst (termSort arg)
      if expectedSort == actualSort
        then pure (M.insert v arg subst)
        else Left (ArgSortMismatch name ix expectedSort actualSort)
