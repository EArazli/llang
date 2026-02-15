module Strat.Poly.Term.Normalize
  ( normalizeTermExpr
  ) where

import qualified Data.Map.Strict as M
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.Term.RewriteSystem (TRS(..), TRule(..), TermSubst, applyTermSubst, matchPattern, rootKey)


normalizeTermExpr :: TRS -> TermExpr -> TermExpr
normalizeTermExpr trs tm = fst (normalizeWithMemo M.empty tm)
  where
    normalizeWithMemo memo term =
      case M.lookup term memo of
        Just out -> (out, memo)
        Nothing ->
          let (term1, memo1) = normalizeChildren memo term
              (term2, memo2) = rewriteToFixpoint memo1 term1
              memo3 = M.insert term term2 memo2
           in (term2, memo3)

    normalizeChildren memo term =
      case term of
        TMFun f args ->
          let (args', memo') = normalizeList memo args
           in (TMFun f args', memo')
        _ -> (term, memo)

    normalizeList memo [] = ([], memo)
    normalizeList memo (x:xs) =
      let (x', memo1) = normalizeWithMemo memo x
          (xs', memo2) = normalizeList memo1 xs
       in (x' : xs', memo2)

    rewriteToFixpoint memo term =
      case rewriteRootOnce term of
        Nothing -> (term, memo)
        Just term' -> normalizeWithMemo memo term'

    rewriteRootOnce term =
      let candidates =
            M.findWithDefault [] (rootKey term) (trsIndex trs)
              <> M.findWithDefault [] Nothing (trsIndex trs)
       in firstRewrite candidates term

    firstRewrite [] _ = Nothing
    firstRewrite (rule:rest) term =
      case rewriteByRule rule term of
        Just out -> Just out
        Nothing -> firstRewrite rest term

rewriteByRule :: TRule -> TermExpr -> Maybe TermExpr
rewriteByRule rule term = do
  subst <- matchPattern (trLHS rule) term
  pure (applySubstClosed subst (trRHS rule))

applySubstClosed :: TermSubst -> TermExpr -> TermExpr
applySubstClosed subst = applyTermSubst subst
