{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Presentation
  ( Presentation(..)
  , validateEquation
  , validatePresentation
  ) where

import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term (TypeError, mkOp)
import Data.Text (Text)
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Text as T

data Presentation = Presentation
  { presName :: Text
  , presSig  :: Signature
  , presEqs  :: [Equation]
  }
  deriving (Eq, Show)

validateEquation :: Signature -> Equation -> Either Text ()
validateEquation sig eq = do
  let lhsSort = termSort (eqLHS eq)
  let rhsSort = termSort (eqRHS eq)
  if lhsSort /= rhsSort
    then Left ("Equation sort mismatch: " <> eqName eq)
    else
      let allowed = S.fromList (map bVar (eqTele eq))
          used = varsTerm (eqLHS eq) `S.union` varsTerm (eqRHS eq)
          bad = used `S.difference` allowed
      in if S.null bad
           then do
             validateEqScopes eq
             validateTerm sig (eqLHS eq)
             validateTerm sig (eqRHS eq)
           else Left ("Equation has out-of-scope vars: " <> eqName eq)

validatePresentation :: Presentation -> Either Text ()
validatePresentation pres = mapM_ (validateEquation (presSig pres)) (presEqs pres)

validateEqScopes :: Equation -> Either Text ()
validateEqScopes eq = do
  let expectedScope = ScopeId ("eq:" <> eqName eq)
  let vars = map bVar (eqTele eq)
  case filter (\v -> vScope v /= expectedScope) vars of
    (v : _) -> Left ("Equation has invalid binder scope: " <> eqName eq <> " (" <> renderScope (vScope v) <> ")")
    [] ->
      let locals = map vLocal vars
          expected = [0 .. length vars - 1]
      in if L.sort locals == expected
           then Right ()
           else Left ("Equation has non-contiguous locals: " <> eqName eq)

renderScope :: ScopeId -> Text
renderScope (ScopeId t) = t

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

validateTerm :: Signature -> Term -> Either Text ()
validateTerm sig tm = do
  inferred <- inferSort sig tm
  if inferred == termSort tm
    then Right ()
    else Left ("Term sort mismatch: " <> renderSort inferred <> " vs " <> renderSort (termSort tm))

inferSort :: Signature -> Term -> Either Text Sort
inferSort sig tm =
  case termNode tm of
    TVar _ -> do
      validateSort sig (termSort tm)
      pure (termSort tm)
    TOp op args -> do
      mapM_ (validateTerm sig) args
      case mkOp sig op args of
        Left err -> Left ("Term not well-typed: " <> renderTypeError err)
        Right t ->
          if termSort t == termSort tm
            then pure (termSort tm)
            else Left ("Term sort mismatch: " <> renderSort (termSort t) <> " vs " <> renderSort (termSort tm))

validateSort :: Signature -> Sort -> Either Text ()
validateSort sig (Sort name idx) = do
  mapM_ (validateTerm sig) idx
  case mkSort sig name idx of
    Left err -> Left ("Sort not well-formed: " <> renderSortError err)
    Right _ -> Right ()

renderTypeError :: TypeError -> Text
renderTypeError = T.pack . show

renderSortError :: SortError -> Text
renderSortError = T.pack . show

renderSort :: Sort -> Text
renderSort = T.pack . show
