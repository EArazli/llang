{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Presentation
  ( Presentation(..)
  , validateEquation
  , validatePresentation
  ) where

import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Data.Text (Text)
import qualified Data.List as L
import qualified Data.Set as S

data Presentation = Presentation
  { presName :: Text
  , presSig  :: Signature
  , presEqs  :: [Equation]
  }
  deriving (Eq, Show)

validateEquation :: Equation -> Either Text ()
validateEquation eq = do
  let lhsSort = termSort (eqLHS eq)
  let rhsSort = termSort (eqRHS eq)
  if lhsSort /= rhsSort
    then Left ("Equation sort mismatch: " <> eqName eq)
    else
      let allowed = S.fromList (map bVar (eqTele eq))
          used = varsTerm (eqLHS eq) `S.union` varsTerm (eqRHS eq)
          bad = used `S.difference` allowed
      in if S.null bad
           then validateEqScopes eq
           else Left ("Equation has out-of-scope vars: " <> eqName eq)

validatePresentation :: Presentation -> Either Text ()
validatePresentation pres = mapM_ validateEquation (presEqs pres)

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
