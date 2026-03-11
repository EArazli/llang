{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RewriteCompile
  ( compileTermRules
  , compileAllTermRules
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph (Diagram(..), diagramPortObj)
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import qualified Strat.Poly.TypeTheory as TT
import Strat.Poly.Obj (Obj, TmVar(..), defaultMetaArgs, sameTmVarId, unTerm)
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , TermConvEnv(..)
  , diagramGraphToTermExprWith
  )
import Strat.Poly.Term.RewriteSystem (TRS, TRule(..), mkTRS, boundVarSet)


compileTermRules :: TT.TypeTheory -> ModeName -> Either Text TRS
compileTermRules tt mode = do
  rules <- mapM compileOne (zip [0 :: Int ..] raw)
  pure (mkTRS mode rules)
  where
    raw = TT.termRulesForMode tt mode

    compileOne (i, rule) = do
      let vars = TT.trVars rule
      let varCtx = map tmvSort vars
      lhs0 <- toExpr varCtx (TT.trLHS rule)
      rhs0 <- toExpr varCtx (TT.trRHS rule)
      lhs <- abstractVars mode varCtx vars lhs0
      rhs <- abstractVars mode varCtx vars rhs0
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
       in do
            expectedSort <- expectedOutSort d
            diagramGraphToTermExprWith convEnv varCtx expectedSort d

    convEnv =
      TermConvEnv
        { tcLookupSig = \m f -> TT.lookupTmFunSig tt m f
        , tcSortEq = \_ tyA tyB -> Right (tyA == tyB)
        , tcLiteralKindForSort = \_ sortTy -> Right (TT.literalKindForObj tt sortTy)
        }

    expectedOutSort d =
      case dOut d of
        [pid] ->
          case diagramPortObj d pid of
            Just sortTy -> Right sortTy
            Nothing -> Left "compileTermRules: rule diagram output is missing a sort"
        _ -> Left "compileTermRules: rule diagram must have exactly one output"


compileAllTermRules :: TT.TypeTheory -> Either Text (M.Map ModeName TRS)
compileAllTermRules tt = do
  let modeNames = M.keysSet (mtModes (TT.ttModes tt))
  let withRuleModes = M.keysSet (TT.ttDefFragments tt)
  let allModes = S.toList (S.union modeNames withRuleModes)
  trs <- mapM (\mode -> do t <- compileTermRules tt mode; pure (mode, t)) allModes
  pure (M.fromList trs)


abstractVars :: ModeName -> [Obj] -> [TmVar] -> TermExpr -> Either Text TermExpr
abstractVars _mode varCtx vars tm =
  case tm of
    TMMeta v metaArgs ->
      case findVarIndex v vars 0 of
        Nothing -> Right (TMMeta v metaArgs)
        Just i ->
          if metaArgs == defaultMetaArgs varCtx v
            then Right (TMBound i)
            else Left ("Can't use term variable with non-canonical arguments in TRS compilation: " <> tmvName v)
    TMBound i -> Right (TMBound i)
    TMFun f args -> TMFun f <$> mapM (abstractVars _mode varCtx vars) args
    TMLit lit -> Right (TMLit lit)

findVarIndex :: TmVar -> [TmVar] -> Int -> Maybe Int
findVarIndex _ [] _ = Nothing
findVarIndex v (x:xs) i
  | sameTmVarId v x = Just i
  | otherwise = findVarIndex v xs (i + 1)

ensureFirstOrder :: Text -> TermExpr -> Either Text ()
ensureFirstOrder side tm =
  case tm of
    TMMeta _ _ -> Left ("compileTermRules: unexpected TMMeta in " <> side)
    TMBound _ -> Right ()
    TMFun _ args -> mapM_ (ensureFirstOrder side) args
    TMLit _ -> Right ()

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
