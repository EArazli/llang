{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Presentation.Rename
  ( qualifyPresentation
  , renameSortsPresentation
  , renameOpsPresentation
  , renameEqsPresentation
  , renameEqsWith
  , qualifyEqName
  , qualifyOpName
  , qualifySortName
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.Rule (Equation(..))
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Presentation.Merge (mergeOpDecls, mergeSortCtors)
import qualified Data.Map.Strict as M
import Data.Text (Text)

qualifyPresentation :: Text -> Presentation -> Either Text Presentation
qualifyPresentation ns pres = do
  pres1 <- renameSortsPresentation (qualifySortName ns) pres
  pres2 <- renameOpsPresentation (qualifyOpName ns) pres1
  let pres3 = renameEqsWith (qualifyEqName ns) pres2
  pure pres3 { presName = ns }

qualifyEqName :: Text -> Text -> Text
qualifyEqName ns name = ns <> "." <> name

qualifyOpName :: Text -> OpName -> OpName
qualifyOpName ns (OpName t) = OpName (qualifyEqName ns t)

qualifySortName :: Text -> SortName -> SortName
qualifySortName ns (SortName t) = SortName (qualifyEqName ns t)

renameOpsPresentation :: (OpName -> OpName) -> Presentation -> Either Text Presentation
renameOpsPresentation f pres = do
  sig' <- renameOpsSignature f (presSig pres)
  let eqs' = map (renameOpsEquation f) (presEqs pres)
  pure pres { presSig = sig', presEqs = eqs' }

renameSortsPresentation :: (SortName -> SortName) -> Presentation -> Either Text Presentation
renameSortsPresentation f pres = do
  sig' <- renameSortsSignature f (presSig pres)
  let eqs' = map (renameSortsEquation f) (presEqs pres)
  pure pres { presSig = sig', presEqs = eqs' }

renameEqsPresentation :: (Text -> Text) -> Presentation -> Presentation
renameEqsPresentation = renameEqsWith

renameOpsSignature :: (OpName -> OpName) -> Signature -> Either Text Signature
renameOpsSignature f sig = do
  let sortCtors' = M.fromList
        [ (name, ctor { scTele = map (renameOpsBinder f) (scTele ctor) })
        | (name, ctor) <- M.toList (sigSortCtors sig)
        ]
  let opDecls = map (renameOpsDecl f) (M.elems (sigOps sig))
  opDecls' <- mergeOpDecls [(opName d, d) | d <- opDecls]
  pure Signature { sigSortCtors = sortCtors', sigOps = opDecls' }

renameSortsSignature :: (SortName -> SortName) -> Signature -> Either Text Signature
renameSortsSignature f sig = do
  let sortDecls =
        [ let oldName = name
              newName = f name
              oldScope = ScopeId ("sort:" <> renderSortName oldName)
              newScope = ScopeId ("sort:" <> renderSortName newName)
              tele' = map (renameScopeBinder oldScope newScope) (scTele ctor)
              tele'' = map (renameSortsBinder f) tele'
              ctor' = ctor { scName = newName, scTele = tele'' }
          in (newName, ctor')
        | (name, ctor) <- M.toList (sigSortCtors sig)
        ]
  sortCtors' <- mergeSortCtors sortDecls
  let opDecls = map (renameSortsDecl f) (M.elems (sigOps sig))
  opDecls' <- mergeOpDecls [(opName d, d) | d <- opDecls]
  pure Signature { sigSortCtors = sortCtors', sigOps = opDecls' }

renameOpsDecl :: (OpName -> OpName) -> OpDecl -> OpDecl
renameOpsDecl f decl =
  let oldName = opName decl
      newName = f oldName
      oldScope = ScopeId ("op:" <> renderOpName oldName)
      newScope = ScopeId ("op:" <> renderOpName newName)
      tele' = map (renameScopeBinder oldScope newScope) (opTele decl)
      res' = renameScopeSort oldScope newScope (opResult decl)
  in decl
      { opName = newName
      , opTele = map (renameOpsBinder f) tele'
      , opResult = renameOpsSort f res'
      }

renameSortsDecl :: (SortName -> SortName) -> OpDecl -> OpDecl
renameSortsDecl f decl =
  decl
    { opTele = map (renameSortsBinder f) (opTele decl)
    , opResult = renameSortsSort f (opResult decl)
    }

renameOpsEquation :: (OpName -> OpName) -> Equation -> Equation
renameOpsEquation f eq =
  eq
    { eqTele = map (renameOpsBinder f) (eqTele eq)
    , eqLHS = renameOpsTerm f (eqLHS eq)
    , eqRHS = renameOpsTerm f (eqRHS eq)
    }

renameSortsEquation :: (SortName -> SortName) -> Equation -> Equation
renameSortsEquation f eq =
  eq
    { eqTele = map (renameSortsBinder f) (eqTele eq)
    , eqLHS = renameSortsTerm f (eqLHS eq)
    , eqRHS = renameSortsTerm f (eqRHS eq)
    }

renameEqsWith :: (Text -> Text) -> Presentation -> Presentation
renameEqsWith f pres =
  pres { presEqs = map renameEq (presEqs pres) }
  where
    renameEq eq =
      let old = eqName eq
          new = f old
          eq' = eq { eqName = new }
      in renameEquationScope old new eq'

renameEquationScope :: Text -> Text -> Equation -> Equation
renameEquationScope old new eq =
  let oldScope = ScopeId ("eq:" <> old)
      newScope = ScopeId ("eq:" <> new)
      tele' = map (renameScopeBinder oldScope newScope) (eqTele eq)
      lhs' = renameScope oldScope newScope (eqLHS eq)
      rhs' = renameScope oldScope newScope (eqRHS eq)
  in eq { eqTele = tele', eqLHS = lhs', eqRHS = rhs' }

renameOpsTerm :: (OpName -> OpName) -> Term -> Term
renameOpsTerm f tm =
  Term
    { termSort = renameOpsSort f (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar v
          TOp op args -> TOp (f op) (map (renameOpsTerm f) args)
    }

renameOpsSort :: (OpName -> OpName) -> Sort -> Sort
renameOpsSort f (Sort name idx) = Sort name (map (renameOpsTerm f) idx)

renameSortsTerm :: (SortName -> SortName) -> Term -> Term
renameSortsTerm f tm =
  Term
    { termSort = renameSortsSort f (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar v
          TOp op args -> TOp op (map (renameSortsTerm f) args)
    }

renameSortsSort :: (SortName -> SortName) -> Sort -> Sort
renameSortsSort f (Sort name idx) = Sort (f name) (map (renameSortsTerm f) idx)

renameOpsBinder :: (OpName -> OpName) -> Binder -> Binder
renameOpsBinder f b =
  b { bSort = renameOpsSort f (bSort b) }

renameSortsBinder :: (SortName -> SortName) -> Binder -> Binder
renameSortsBinder f b =
  b { bSort = renameSortsSort f (bSort b) }

renderOpName :: OpName -> Text
renderOpName (OpName t) = t

renderSortName :: SortName -> Text
renderSortName (SortName t) = t
