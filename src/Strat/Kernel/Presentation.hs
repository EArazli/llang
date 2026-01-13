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
           then Right ()
           else Left ("Equation has out-of-scope vars: " <> eqName eq)

validatePresentation :: Presentation -> Either Text ()
validatePresentation pres = mapM_ validateEquation (presEqs pres)

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
