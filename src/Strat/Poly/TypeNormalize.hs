{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.TypeNormalize
  ( normalizeTypeDeep
  , normalizeTypeDeepWithCtx
  , normalizeTermDiagram
  , termToDiagram
  , diagramToTerm
  , validateTermDiagram
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Diagram (freeTyVarsDiagram)
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , diagramPortType
  , validateDiagram
  )
import Strat.Poly.ModeTheory (ModeName, composeMod, normalizeModExpr, meSrc, mePath)
import Strat.Poly.Normalize (NormalizationStatus(..), normalize)
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.TypeExpr
  ( TermDiagram(..)
  , TmVar(..)
  , TypeArg(..)
  , TypeExpr(..)
  , typeMode
  )
import Strat.Poly.TypeTheory
  ( TypeParamSig(..)
  , TmFunSig(..)
  , TmRule(..)
  , TypeTheory(..)
  )
import Strat.Poly.TermExpr
  ( TermExpr(..)
  , diagramGraphToTermExpr
  , termExprToDiagram
  , validateTermGraph
  , sameTmMetaId
  )


normalizeTypeDeep :: TypeTheory -> TypeExpr -> Either Text TypeExpr
normalizeTypeDeep tt = normalizeTypeDeepWithCtx tt []

normalizeTypeDeepWithCtx :: TypeTheory -> [TypeExpr] -> TypeExpr -> Either Text TypeExpr
normalizeTypeDeepWithCtx tt tmCtx ty = do
  ty' <- go ty
  normalizeTypeExpr0 ty'
  where
    go expr =
      case expr of
        TVar _ -> Right expr
        TMod me inner -> TMod me <$> go inner
        TCon ref args ->
          case M.lookup ref (ttTypeParams tt) of
            Just params ->
              if length params /= length args
                then Left "normalizeTypeDeep: type constructor arity mismatch"
                else TCon ref <$> mapM normalizeArg (zip params args)
            Nothing ->
              if null args
                then Right (TCon ref [])
                else Left "normalizeTypeDeep: unknown type constructor"

    normalizeArg (TPS_Ty _, TAType tyArg) = TAType <$> go tyArg
    normalizeArg (TPS_Tm sortTy, TATm tm) = do
      sortTy' <- go sortTy
      tm' <- normalizeTermDiagram tt tmCtx sortTy' tm
      Right (TATm tm')
    normalizeArg (TPS_Ty _, TATm _) =
      Left "normalizeTypeDeep: expected type argument"
    normalizeArg (TPS_Tm _, TAType _) =
      Left "normalizeTypeDeep: expected term argument"

    normalizeTypeExpr0 expr =
      case expr of
        TVar _ -> Right expr
        TCon ref args -> do
          args' <- mapM normalizeArg0 args
          Right (TCon ref args')
        TMod me inner0 -> do
          inner <- normalizeTypeExpr0 inner0
          (meComposed, innerBase) <-
            case inner of
              TMod me2 inner2 -> do
                me' <- composeMod0 me2 me
                Right (me', inner2)
              _ -> Right (me, inner)
          if typeMode innerBase /= meSrc meComposed
            then Left "normalizeTypeExpr: modality source does not match inner type mode"
            else do
              let meNorm = normalizeModExpr0 meComposed
              if null (mePath meNorm)
                then Right innerBase
                else Right (TMod meNorm innerBase)

    normalizeArg0 arg =
      case arg of
        TAType innerTy -> TAType <$> normalizeTypeExpr0 innerTy
        TATm tm -> Right (TATm tm)

    composeMod0 = composeMod (ttModes tt)
    normalizeModExpr0 = normalizeModExpr (ttModes tt)

normalizeTermDiagram
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text TermDiagram
normalizeTermDiagram tt tmCtx expectedSort term = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  src <- termToDiagram tt tmCtx expectedSort' term
  rules <- termRulesForMode tt tmCtx (typeMode expectedSort')
  status <- normalize tt (ttTmFuel tt) rules src
  out <-
    case status of
      Finished d -> Right d
      OutOfFuel _ -> Left "normalizeTermDiagram: fuel exhausted"
  validateTermGraph out
  ensureOutputSort tt tmCtx expectedSort' out
  -- Canonicalize labels/port ordering for stable equality after rewriting.
  expr <- diagramGraphToTermExpr tt tmCtx expectedSort' out
  termExprToDiagram tt tmCtx expectedSort' expr

termToDiagram
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> TermDiagram
  -> Either Text Diagram
termToDiagram tt tmCtx expectedSort (TermDiagram term0) = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  let term = term0 { dTmCtx = tmCtx }
  validateTermGraph term
  if dMode term == typeMode expectedSort'
    then Right ()
    else Left "termToDiagram: mode mismatch"
  ensureOutputSort tt tmCtx expectedSort' term
  pure term

diagramToTerm
  :: TypeTheory
  -> [TypeExpr]
  -> TypeExpr
  -> Diagram
  -> Either Text TermDiagram
diagramToTerm tt tmCtx expectedSort term0 = do
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  let term = term0 { dTmCtx = tmCtx }
  validateTermGraph term
  if dMode term == typeMode expectedSort'
    then Right ()
    else Left "diagramToTerm: mode mismatch"
  ensureOutputSort tt tmCtx expectedSort' term
  pure (TermDiagram term)

validateTermDiagram :: Diagram -> Either Text ()
validateTermDiagram = validateTermGraph

termRulesForMode :: TypeTheory -> [TypeExpr] -> ModeName -> Either Text [RewriteRule]
termRulesForMode tt tmCtx mode =
  mapM toRewriteRule (zip [0 :: Int ..] tmRules)
  where
    tmRules = M.findWithDefault [] mode (ttTmRules tt)

    toRewriteRule (i, rule) = do
      let vars = trVars rule
      let varCtx = map tmvSort vars
      lhsSort <- outputSort varCtx (unTerm (trLHS rule))
      rhsSort <- outputSort varCtx (unTerm (trRHS rule))
      lhsExpr0 <- diagramGraphToTermExpr tt varCtx lhsSort ((unTerm (trLHS rule)) { dTmCtx = varCtx })
      rhsExpr0 <- diagramGraphToTermExpr tt varCtx rhsSort ((unTerm (trRHS rule)) { dTmCtx = varCtx })
      lhsExpr <- abstractVars vars lhsExpr0
      rhsExpr <- abstractVars vars rhsExpr0
      sortTy <- inferSort varCtx lhsExpr
      lhs0 <- unTerm <$> termExprToDiagram tt varCtx sortTy lhsExpr
      rhs0 <- unTerm <$> termExprToDiagram tt varCtx sortTy rhsExpr
      lhs <- alignCtx lhs0
      rhs <- alignCtx rhs0
      let tyVars = S.toList (freeTyVarsDiagram lhs `S.union` freeTyVarsDiagram rhs)
      pure
        RewriteRule
          { rrName = "tmrule." <> fromStringShow i
          , rrLHS = lhs
          , rrRHS = rhs
          , rrTyVars = tyVars
          , rrTmVars = []
          }

    alignCtx d = do
      let d' = d { dTmCtx = tmCtx }
      validateDiagram d'
      if dMode d' == mode
        then Right d'
        else Left "termRulesForMode: rule term mode mismatch"

    outputSort ctx d =
      case dOut d of
        [pid] ->
          case diagramPortType d pid of
            Nothing -> Left "termRulesForMode: missing output port type"
            Just ty -> normalizeTypeDeepWithCtx tt ctx ty
        _ -> Left "termRulesForMode: rule term must have exactly one output"

    inferSort ctx tm =
      case tm of
        TMVar v -> normalizeTypeDeepWithCtx tt ctx (tmvSort v)
        TMBound i ->
          case nth ctx i of
            Nothing -> Left "termRulesForMode: abstracted bound variable out of scope"
            Just ty -> normalizeTypeDeepWithCtx tt ctx ty
        TMFun f args -> do
          sig <- chooseFunSig f (length args)
          normalizeTypeDeepWithCtx tt ctx (tfsRes sig)

    chooseFunSig funName arity =
      case [ sig
           | table <- M.elems (ttTmFuns tt)
           , (name, sig) <- M.toList table
           , name == funName
           , length (tfsArgs sig) == arity
           ] of
        [] -> Left "termRulesForMode: unknown term function in rule"
        (sig:_) -> Right sig

    abstractVars vars tm =
      case tm of
        TMVar v ->
          case findVarIndex vars v of
            Just idx -> Right (TMBound idx)
            Nothing -> Right tm
        TMBound i -> Right (TMBound i)
        TMFun f args -> TMFun f <$> mapM (abstractVars vars) args

    findVarIndex vars v = elemIndexBy (sameTmMetaId v) vars 0

    elemIndexBy _ [] _ = Nothing
    elemIndexBy p (x:xs) i
      | p x = Just i
      | otherwise = elemIndexBy p xs (i + 1)

    nth xs i
      | i < 0 = Nothing
      | otherwise =
          case drop i xs of
            (y:_) -> Just y
            [] -> Nothing

ensureOutputSort :: TypeTheory -> [TypeExpr] -> TypeExpr -> Diagram -> Either Text ()
ensureOutputSort tt tmCtx expectedSort term = do
  out <- requireSingleOut term
  outSort <-
    case diagramPortType term out of
      Nothing -> Left "termToDiagram: missing output port type"
      Just ty -> normalizeTypeDeepWithCtx tt tmCtx ty
  expectedSort' <- normalizeTypeDeepWithCtx tt tmCtx expectedSort
  if outSort == expectedSort'
    then Right ()
    else Left "termToDiagram: output sort mismatch"

requireSingleOut :: Diagram -> Either Text PortId
requireSingleOut term =
  case dOut term of
    [pid] -> Right pid
    _ -> Left "termToDiagram: term diagram must have exactly one output"

fromStringShow :: Show a => a -> Text
fromStringShow = fromString . show

fromString :: String -> Text
fromString = T.pack
