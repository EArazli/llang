{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RewriteCompile
  ( compileTermRules
  , compileAllTermRules
  ) where

import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..), diagramPortObj, weakenDiagramTmCtxTo)
import Strat.Poly.ModeTheory (ModeName, ModeTheory(..))
import qualified Strat.Poly.TypeTheory as TT
import Strat.Poly.Obj (Obj, TermDiagram(..), TmVar(..), defaultMetaArgs, sameTmVarId, unTerm)
import Strat.Poly.ObjNormalize (normalizeObjDeepWithCtx)
import Strat.Poly.Syntax (BinderMetaVar)
import Strat.Poly.Term.RuleDiagram (sameModeSpliceMapper)
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , diagramGraphToRuleExprWith
  , mkNormalizingConvEnv
  , normalizeDiagramStructurally
  , normalizeCtxStructurally
  , structuralConvEnv
  )
import Strat.Poly.Term.AST (TermBinderArg(..), TermHeadArg(..))
import Strat.Poly.Term.RewriteSystem (TRS, TRule(..), mkTRS, boundVarSet)


compileTermRules :: TT.TypeTheory -> ModeName -> Either Text TRS
compileTermRules tt mode =
  mkTRS mode <$> mapM (compileRule tt mode) (zip [0 :: Int ..] (TT.termRulesForMode tt mode))

mapLeft :: (e -> f) -> Either e a -> Either f a
mapLeft f mv =
  case mv of
    Left err -> Left (f err)
    Right v -> Right v


compileAllTermRules :: TT.TypeTheory -> Either Text (M.Map ModeName TRS)
compileAllTermRules tt = do
  ttProvisional <- seedRuleCompileTheory tt
  let modeNames = M.keysSet (mtModes (TT.ttModes tt))
  let withRuleModes = M.keysSet (TT.ttDefFragments tt)
  let allModes = S.toList (S.union modeNames withRuleModes)
  trs <- mapM (\mode -> do t <- compileTermRules ttProvisional mode; pure (mode, t)) allModes
  pure (M.fromList trs)

seedRuleCompileTheory :: TT.TypeTheory -> Either Text TT.TypeTheory
seedRuleCompileTheory tt0 = loop initialTRSByMode (install initialTRSByMode)
  where
    modeNames = M.keysSet (mtModes (TT.ttModes tt0))
    withRuleModes = M.keysSet (TT.ttDefFragments tt0)
    allModes = S.toList (S.union modeNames withRuleModes)
    initialTRSByMode = M.fromList [ (mode, mkTRS mode []) | mode <- allModes ]

    loop prevByMode ttCur = do
      nextByMode <- M.fromList <$> mapM (compileMode ttCur) allModes
      if nextByMode == prevByMode
        then pure (install nextByMode)
        else loop nextByMode (install nextByMode)

    install trsByMode =
      foldl'
        (\acc (mode, trs) -> TT.setModeCompiledRules mode trs acc)
        tt0
        (M.toList trsByMode)

    compileMode ttCur mode =
      pure (mode, mkTRS mode (mapMaybe (compileRuleMaybe ttCur mode) (zip [0 :: Int ..] (TT.termRulesForMode tt0 mode))))

compileRuleMaybe :: TT.TypeTheory -> ModeName -> (Int, TT.TmRule) -> Maybe TRule
compileRuleMaybe tt mode entry =
  case compileRule tt mode entry of
    Left _ -> Nothing
    Right rule -> Just rule

compileRule :: TT.TypeTheory -> ModeName -> (Int, TT.TmRule) -> Either Text TRule
compileRule tt mode (i, rule) = do
  lhsDiagram <- prepareDiagram (TT.trLHS rule)
  rhsDiagram <- prepareDiagram (TT.trRHS rule)
  lhs0 <- compileExpr "lhs" lhsDiagram
  lhs <- abstractVars mode ruleVarCtx vars lhs0
  ensureTrustedRuleExpr "lhs" lhs
  ensureLHSShape lhs
  rhs <- compileRHS ruleVarCtx vars lhs rhsDiagram
  pure
    TRule
      { trName = "tmrule." <> T.pack (show i)
      , trVars = vars
      , trLHS = lhs
      , trRHS = rhs
      , trRHSDiagram = Just (TermDiagram rhsDiagram)
      }
  where
    vars = TT.trVars rule
    ruleVarCtx = map tmvSort vars
    ruleCompileTheory = tt { TT.ttStrictCtorLookup = False }

    prepareDiagram tm =
      let d0 = unTerm tm
       in do
            varCtx' <- normalizeCtxStructurally tt (structuralConvEnv tt) ruleVarCtx
            dTmCtx' <- normalizeCtxStructurally tt (structuralConvEnv tt) (dTmCtx d0)
            let d1 = d0 { dTmCtx = dTmCtx' }
            d <- weakenDiagramTmCtxTo varCtx' d1
            d' <- normalizeDiagramStructurally tt (structuralConvEnv tt) d
            _ <- expectedOutSort d'
            pure d'

    compileExpr side d = do
      varCtx' <- normalizeCtxStructurally tt (structuralConvEnv tt) ruleVarCtx
      expectedSort <- expectedOutSort d
      mapLeft
        ( \err ->
            "compileTermRules: "
              <> side
              <> " of rule tmrule."
              <> T.pack (show i)
              <> " failed (expectedSort="
              <> T.pack (show expectedSort)
              <> ", inArity="
              <> T.pack (show (length (dIn d)))
              <> ", outArity="
              <> T.pack (show (length (dOut d)))
              <> "): "
              <> err
        )
        (diagramGraphToRuleExprWith ruleCompileTheory ruleConvEnv varCtx' expectedSort d)

    ruleConvEnv =
      mkNormalizingConvEnv ruleCompileTheory (sameModeSpliceMapper "rule-compile") (normalizeObjDeepWithCtx ruleCompileTheory)

    compileRHS varCtx0 vars0 lhs rhsDiagram =
      case compileExpr "rhs" rhsDiagram of
        Right rhs0 -> do
          rhs' <- abstractVars mode varCtx0 vars0 rhs0
          case ensureTrustedRuleExpr "rhs" rhs' of
            Right () -> do
              ensureRHSVarsSubsetLHS i lhs rhs'
              ensureRHSHolesSubsetLHS i lhs rhs'
              pure (Just rhs')
            Left err
              | rhsCanFallBackDiagram rhsDiagram -> do
                  ensureRHSVarsSubsetLHS i lhs rhs'
                  ensureRHSHolesSubsetLHS i lhs rhs'
                  Right Nothing
              | otherwise ->
                  Left err
        Left err
          | rhsCanFallBackDiagram rhsDiagram ->
              Right Nothing
          | otherwise ->
              Left err

    rhsCanFallBackDiagram d =
      isStructuralRuleRHS d

    isStructuralRuleRHS d =
      any structuralEdge (IM.elems (dEdges d))
      where
        structuralEdge edge =
          case ePayload edge of
            PGen g args bargs ->
              case TT.lookupTmHeadSig tt (dMode d) g of
                Just sig ->
                  length (TT.thsParams sig) /= length args
                    || length (TT.thsInputs sig) /= length (eIns edge)
                    || length (TT.thsBinders sig) /= length bargs
                    || length (eOuts edge) /= 1
                Nothing ->
                  True
            PSplice _ _ ->
              False
            PTmMeta _ ->
              False
            PTmLit _ ->
              False
            PInternalDrop ->
              True
            _ ->
              True

    expectedOutSort d =
      case dOut d of
        [pid] ->
          case diagramPortObj d pid of
            Just sortTy -> Right sortTy
            Nothing -> Left "compileTermRules: rule diagram output is missing a sort"
        _ -> Left "compileTermRules: rule diagram must have exactly one output"


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
    TMHead f args bargs ->
      (\args' bargs' -> TMHead f args' bargs') <$> mapM abstractHeadArg args <*> mapM abstractBinderArg bargs
    TMSplice hole me args ->
      TMSplice hole me <$> mapM (abstractVars _mode varCtx vars) args
    TMLit lit -> Right (TMLit lit)
  where
    abstractHeadArg arg =
      case arg of
        THAObj obj -> Right (THAObj obj)
        THATm tm0 -> THATm <$> abstractVars _mode varCtx vars tm0

    abstractBinderArg barg =
      case barg of
        TBABody inner -> Right (TBABody inner)
        TBAHole hole -> Right (TBAHole hole)

findVarIndex :: TmVar -> [TmVar] -> Int -> Maybe Int
findVarIndex _ [] _ = Nothing
findVarIndex v (x:xs) i
  | sameTmVarId v x = Just i
  | otherwise = findVarIndex v xs (i + 1)

ensureTrustedRuleExpr :: Text -> TermExpr -> Either Text ()
ensureTrustedRuleExpr side tm =
  case tm of
    TMMeta _ _ -> Left ("compileTermRules: unexpected TMMeta in " <> side)
    TMBound _ -> Right ()
    TMHead _ args bargs -> do
      mapM_ ensureHeadArg args
      mapM_ ensureBinderArg bargs
    TMSplice _ _ args -> do
      mapM_ (ensureTrustedRuleExpr side) args
    TMLit _ -> Right ()
  where
    ensureHeadArg arg =
      case arg of
        THAObj _ -> Right ()
        THATm tm0 -> ensureTrustedRuleExpr side tm0

    ensureBinderArg barg =
      case barg of
        TBABody _ -> Right ()
        TBAHole _ -> Right ()

ensureLHSShape :: TermExpr -> Either Text ()
ensureLHSShape lhs =
  case lhs of
    TMHead _ args bargs -> do
      mapM_ ensureLHSArg args
      mapM_ ensureLHSBinder bargs
      Right ()
    _ -> Left "compileTermRules: left-hand side must be a function application"
  where
    ensureLHSArg arg =
      case arg of
        THAObj _ -> Right ()
        THATm tm -> ensureLHSSubterm tm

    ensureLHSSubterm tm =
      case tm of
        TMHead _ args bargs -> do
          mapM_ ensureLHSArg args
          mapM_ ensureLHSBinder bargs
          Right ()
        TMBound _ -> Right ()
        TMLit _ -> Right ()
        TMMeta _ _ -> Left "compileTermRules: unexpected TMMeta in lhs"
        TMSplice _ _ _ -> Left "compileTermRules: splice terms are not allowed in lhs"

    ensureLHSBinder barg =
      case barg of
        TBABody _ -> Right ()
        TBAHole _ -> Right ()

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

ensureRHSHolesSubsetLHS :: Int -> TermExpr -> TermExpr -> Either Text ()
ensureRHSHolesSubsetLHS ruleIx lhs rhs =
  let lhsHoles = binderHoleSet lhs
      rhsHoles = binderHoleSet rhs
      bad = S.toList (S.difference rhsHoles lhsHoles)
   in if null bad
        then Right ()
        else
          Left
            ( "compileTermRules: rhs introduces fresh binder holes in rule tmrule."
                <> T.pack (show ruleIx)
                <> " (holes: "
                <> T.intercalate ", " (map (T.pack . show) bad)
                <> ")"
            )

binderHoleSet :: TermExpr -> S.Set BinderMetaVar
binderHoleSet tm =
  case tm of
    TMBound _ -> S.empty
    TMMeta _ _ -> S.empty
    TMHead _ args bargs ->
      S.unions (map headArgHoles args <> map binderArgHoles bargs)
    TMSplice hole _ args ->
      S.insert hole (S.unions (map binderHoleSet args))
    TMLit _ -> S.empty
  where
    headArgHoles arg =
      case arg of
        THAObj _ -> S.empty
        THATm inner -> binderHoleSet inner

    binderArgHoles barg =
      case barg of
        TBABody _ -> S.empty
        TBAHole hole -> S.singleton hole
