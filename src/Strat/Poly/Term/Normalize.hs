module Strat.Poly.Term.Normalize
  ( normalizeTermExpr
  ) where

import qualified Data.Map.Strict as M
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))
import Strat.Poly.Term.RewriteSystem (TRS(..), TRule(..), TermSubst, applyTermSubstOnce, matchPattern, rootKey)


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
        TMGen f args ->
          let (args', memo') = normalizeArgList memo args
           in (TMGen f args', memo')
        _ -> (term, memo)

    normalizeArgList memo [] = ([], memo)
    normalizeArgList memo (x:xs) =
      let (x', memo1) = normalizeHeadArg memo x
          (xs', memo2) = normalizeArgList memo1 xs
       in (x' : xs', memo2)

    normalizeHeadArg memo arg =
      case arg of
        THAObj _ -> (arg, memo)
        THATm tm0 ->
          let (tm1, memo1) = normalizeWithMemo memo tm0
           in (THATm tm1, memo1)

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
  pure (applySubstOnce subst (trRHS rule))

applySubstOnce :: TermSubst -> TermExpr -> TermExpr
applySubstOnce subst = applyTermSubstOnce subst
