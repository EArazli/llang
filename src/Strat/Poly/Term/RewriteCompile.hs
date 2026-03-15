{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RewriteCompile
  ( compileTermRules
  , compileAllTermRules
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Graph (Diagram(..), diagramPortObj, weakenDiagramTmCtxTo)
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import qualified Strat.Poly.TypeTheory as TT
import Strat.Poly.Obj (Obj, TmVar(..), defaultMetaArgs, sameTmVarId, unTerm)
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , diagramGraphToTermExpr
  , normalizeCtxStructurally
  , structuralConvEnv
  )
import Strat.Poly.Term.AST (TermHeadArg(..))
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
      lhs0 <- toExpr "lhs" i varCtx (TT.trLHS rule)
      rhs0 <- toExpr "rhs" i varCtx (TT.trRHS rule)
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

    toExpr side ruleIx varCtx tm =
      let d0 = unTerm tm
       in do
            varCtx' <- normalizeCtxStructurally tt (structuralConvEnv tt) varCtx
            dTmCtx' <- normalizeCtxStructurally tt (structuralConvEnv tt) (dTmCtx d0)
            let d1 = d0 { dTmCtx = dTmCtx' }
            d <- weakenDiagramTmCtxTo varCtx' d1
            expectedSort <- expectedOutSort d
            mapLeft
              ( \err ->
                  "compileTermRules: "
                    <> side
                    <> " of rule tmrule."
                    <> T.pack (show ruleIx)
                    <> " failed (expectedSort="
                    <> T.pack (show expectedSort)
                    <> ", inArity="
                    <> T.pack (show (length (dIn d)))
                    <> ", outArity="
                    <> T.pack (show (length (dOut d)))
                    <> "): "
                    <> err
              )
              (diagramGraphToTermExpr tt varCtx' expectedSort d)

    expectedOutSort d =
      case dOut d of
        [pid] ->
          case diagramPortObj d pid of
            Just sortTy -> Right sortTy
            Nothing -> Left "compileTermRules: rule diagram output is missing a sort"
        _ -> Left "compileTermRules: rule diagram must have exactly one output"

mapLeft :: (e -> f) -> Either e a -> Either f a
mapLeft f mv =
  case mv of
    Left err -> Left (f err)
    Right v -> Right v


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
    TMGen f args -> TMGen f <$> mapM abstractHeadArg args
    TMLit lit -> Right (TMLit lit)
  where
    abstractHeadArg arg =
      case arg of
        THAObj obj -> Right (THAObj obj)
        THATm tm0 -> THATm <$> abstractVars _mode varCtx vars tm0

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
    TMGen _ args -> mapM_ ensureHeadArg args
    TMLit _ -> Right ()
  where
    ensureHeadArg arg =
      case arg of
        THAObj _ -> Right ()
        THATm tm0 -> ensureFirstOrder side tm0

ensureLHSShape :: TermExpr -> Either Text ()
ensureLHSShape lhs =
  case lhs of
    TMGen _ _ -> Right ()
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
