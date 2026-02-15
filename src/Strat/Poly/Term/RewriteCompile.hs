{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RewriteCompile
  ( compileTermRules
  , compileAllTermRules
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph (Diagram(..))
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import qualified Strat.Poly.TypeTheory as TT
import Strat.Poly.TypeExpr (TmVar(..), unTerm)
import Strat.Poly.TermExpr (TermExpr(..), diagramGraphToTermExprUnchecked, sameTmMetaId)
import Strat.Poly.Term.RewriteSystem (TRS, TRule(..), mkTRS, boundVarSet)


compileTermRules :: TT.TypeTheory -> ModeName -> Either Text TRS
compileTermRules tt mode = do
  rules <- mapM compileOne (zip [0 :: Int ..] raw)
  pure (mkTRS mode rules)
  where
    raw = M.findWithDefault [] mode (TT.ttTmRules tt)

    compileOne (i, rule) = do
      let vars = TT.trVars rule
      let varCtx = map tmvSort vars
      lhs0 <- toExpr varCtx (TT.trLHS rule)
      rhs0 <- toExpr varCtx (TT.trRHS rule)
      lhs <- abstractVars vars lhs0
      rhs <- abstractVars vars rhs0
      ensureFirstOrder "lhs" lhs
      ensureFirstOrder "rhs" rhs
      ensureLHSShape lhs
      ensureRHSVarsSubsetLHS i lhs rhs
      pure
        TRule
          { trName = "tmrule." <> T.pack (show i)
          , trLHS = lhs
          , trRHS = rhs
          }

    toExpr varCtx tm =
      let d0 = unTerm tm
          d = d0 { dTmCtx = varCtx }
       in diagramGraphToTermExprUnchecked d


compileAllTermRules :: TT.TypeTheory -> Either Text (M.Map ModeName TRS)
compileAllTermRules tt = do
  let modeNames = M.keysSet (mtModes (TT.ttModes tt))
  let withRuleModes = M.keysSet (TT.ttTmRules tt)
  let allModes = S.toList (S.union modeNames withRuleModes)
  trs <- mapM (\mode -> do t <- compileTermRules tt mode; pure (mode, t)) allModes
  pure (M.fromList trs)


abstractVars :: [TmVar] -> TermExpr -> Either Text TermExpr
abstractVars vars tm =
  case tm of
    TMVar v ->
      case findVarIndex v vars 0 of
        Nothing -> Left "compileTermRules: rule contains undeclared term metavariable"
        Just i -> Right (TMBound i)
    TMBound i -> Right (TMBound i)
    TMFun f args -> TMFun f <$> mapM (abstractVars vars) args

findVarIndex :: TmVar -> [TmVar] -> Int -> Maybe Int
findVarIndex _ [] _ = Nothing
findVarIndex v (x:xs) i
  | sameTmMetaId v x = Just i
  | otherwise = findVarIndex v xs (i + 1)

ensureFirstOrder :: Text -> TermExpr -> Either Text ()
ensureFirstOrder side tm =
  case tm of
    TMVar _ -> Left ("compileTermRules: unexpected TMVar in " <> side)
    TMBound _ -> Right ()
    TMFun _ args -> mapM_ (ensureFirstOrder side) args

ensureLHSShape :: TermExpr -> Either Text ()
ensureLHSShape lhs =
  case lhs of
    TMFun _ _ -> Right ()
    _ -> Left "compileTermRules: left-hand side must be a function application"

ensureRHSVarsSubsetLHS :: Int -> TermExpr -> TermExpr -> Either Text ()
ensureRHSVarsSubsetLHS ruleIx lhs rhs =
  let lhsVars = boundVarSet lhs
      rhsVars = boundVarSet rhs
      bad = S.toList (S.difference rhsVars lhsVars)
   in if null bad
        then Right ()
        else
          Left
            ( "compileTermRules: rhs introduces fresh variables in rule tmrule."
                <> T.pack (show ruleIx)
                <> " (indices: "
                <> T.intercalate ", " (map (T.pack . show) bad)
                <> ")"
            )
