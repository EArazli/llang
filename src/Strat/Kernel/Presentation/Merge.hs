{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Presentation.Merge
  ( mergePresentations
  , mergeSignatures
  , mergeSortCtors
  , mergeOpDecls
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.Rule (Equation(..))
import Strat.Kernel.Signature
import Strat.Kernel.AlphaEq
import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Control.Monad (foldM)

mergePresentations :: Presentation -> Presentation -> Either Text Presentation
mergePresentations a b = do
  let presName' = presName a <> "+" <> presName b
  sig' <- mergeSignatures (presSig a) (presSig b)
  (_, eqs') <- foldM insertEq (M.empty, []) (presEqs a <> presEqs b)
  pure Presentation { presName = presName', presSig = sig', presEqs = eqs' }
  where
    insertEq (eqMap, eqs) eq =
      case M.lookup (eqName eq) eqMap of
        Nothing -> Right (M.insert (eqName eq) eq eqMap, eqs <> [eq])
        Just existing ->
          if alphaEqEquation existing eq
            then Right (eqMap, eqs)
            else Left ("Duplicate equation name: " <> eqName eq)

mergeSignatures :: Signature -> Signature -> Either Text Signature
mergeSignatures s1 s2 = do
  sortCtors <- mergeSortCtors (M.toList (sigSortCtors s1) <> M.toList (sigSortCtors s2))
  opDecls <- mergeOpDecls (M.toList (sigOps s1) <> M.toList (sigOps s2))
  pure Signature { sigSortCtors = sortCtors, sigOps = opDecls }

mergeSortCtors :: [(SortName, SortCtor)] -> Either Text (M.Map SortName SortCtor)
mergeSortCtors = foldl step (Right M.empty)
  where
    step acc (name, ctor) = do
      m <- acc
      case M.lookup name m of
        Nothing -> pure (M.insert name ctor m)
        Just ctor' ->
          if alphaEqSortCtor ctor' ctor
            then pure m
            else Left ("Duplicate sort ctor: " <> renderSortName name)

mergeOpDecls :: [(OpName, OpDecl)] -> Either Text (M.Map OpName OpDecl)
mergeOpDecls = foldl step (Right M.empty)
  where
    step acc (name, decl) = do
      m <- acc
      case M.lookup name m of
        Nothing -> pure (M.insert name decl m)
        Just decl' ->
          if alphaEqOpDecl decl' decl
            then pure m
            else Left ("Duplicate op decl: " <> renderOpName name)

renderOpName :: OpName -> Text
renderOpName (OpName t) = t

renderSortName :: SortName -> Text
renderSortName (SortName t) = t
