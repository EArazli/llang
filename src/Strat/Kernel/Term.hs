module Strat.Kernel.Term where

import Strat.Kernel.Signature
import Strat.Kernel.Subst
import Strat.Kernel.Syntax
import Strat.Kernel.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S

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
      let actualSort = termSort arg
      if expectedSort == actualSort
        then pure (M.insert v arg subst)
        else Left (ArgSortMismatch name ix expectedSort actualSort)

isVar :: Term -> Bool
isVar t =
  case termNode t of
    TVar _ -> True
    _ -> False

asVar :: Term -> Maybe Var
asVar t =
  case termNode t of
    TVar v -> Just v
    _ -> Nothing

positions :: Term -> [Pos]
positions t =
  [] : case termNode t of
    TVar _ -> []
    TOp _ args ->
      concat
        [ map (i :) (positions arg)
        | (i, arg) <- zip [0 ..] args
        ]

subtermAt :: Term -> Pos -> Maybe Term
subtermAt t [] = Just t
subtermAt t (i : is) =
  case termNode t of
    TOp _ args
      | i >= 0 && i < length args -> subtermAt (args !! i) is
      | otherwise -> Nothing
    _ -> Nothing

replaceAt :: Term -> Pos -> Term -> Maybe Term
replaceAt _ [] newTerm = Just newTerm
replaceAt t (i : is) newTerm =
  case termNode t of
    TOp op args
      | i >= 0 && i < length args ->
          case splitAt i args of
            (before, target : after) -> do
              target' <- replaceAt target is newTerm
              let args' = before ++ (target' : after)
              pure Term { termSort = termSort t, termNode = TOp op args' }
            _ -> Nothing
      | otherwise -> Nothing
    _ -> Nothing

renameScope :: ScopeId -> ScopeId -> Term -> Term
renameScope old new tm =
  Term
    { termSort = renameScopeSort old new (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar (renameScopeVar old new v)
          TOp op args -> TOp op (map (renameScope old new) args)
    }

renameScopeVar :: ScopeId -> ScopeId -> Var -> Var
renameScopeVar old new v =
  if vScope v == old
    then v { vScope = new }
    else v

renameScopeSort :: ScopeId -> ScopeId -> Sort -> Sort
renameScopeSort old new (Sort name idx) =
  Sort name (map (renameScope old new) idx)

renameScopeBinder :: ScopeId -> ScopeId -> Binder -> Binder
renameScopeBinder old new b =
  Binder
    { bVar = renameScopeVar old new (bVar b)
    , bSort = renameScopeSort old new (bSort b)
    }

scopesInTerm :: Term -> S.Set ScopeId
scopesInTerm term =
  S.map vScope (varsTerm term)

varsTerm :: Term -> S.Set Var
varsTerm term =
  varsInTerm term `S.union` varsInSort (termSort term)
  where
    varsInTerm t =
      case termNode t of
        TVar v -> S.singleton v
        TOp _ args -> S.unions (map varsTerm args)

varsInSort :: Sort -> S.Set Var
varsInSort (Sort _ idx) = S.unions (map varsTerm idx)
