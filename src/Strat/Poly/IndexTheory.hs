{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.IndexTheory
  ( TypeTheory(..)
  , TypeParamSig(..)
  , IxTheory(..)
  , IxFunSig(..)
  , IxRule(..)
  , normalizeTypeDeep
  , normalizeIx
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName, ModeTheory)
import Strat.Poly.TypeExpr


data TypeTheory = TypeTheory
  { ttModes :: ModeTheory
  , ttIndex :: M.Map ModeName IxTheory
  , ttTypeParams :: M.Map TypeRef [TypeParamSig]
  , ttIxFuel :: Int
  } deriving (Eq, Show)

data TypeParamSig
  = TPS_Ty ModeName
  | TPS_Ix TypeExpr
  deriving (Eq, Ord, Show)


data IxTheory = IxTheory
  { itFuns :: M.Map IxFunName IxFunSig
  , itRules :: [IxRule]
  } deriving (Eq, Ord, Show)

data IxFunSig = IxFunSig
  { ifArgs :: [TypeExpr]
  , ifRes :: TypeExpr
  } deriving (Eq, Ord, Show)

data IxRule = IxRule
  { irVars :: [IxVar]
  , irLHS :: IxTerm
  , irRHS :: IxTerm
  } deriving (Eq, Ord, Show)

normalizeTypeDeep :: TypeTheory -> TypeExpr -> Either Text TypeExpr
normalizeTypeDeep tt ty = do
  ty' <- go ty
  normalizeTypeExpr (ttModes tt) ty'
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
    normalizeArg (TPS_Ix sortTy, TAIndex ix) = do
      sortTy' <- go sortTy
      ix' <- normalizeIx tt sortTy' ix
      Right (TAIndex ix')
    normalizeArg (TPS_Ty _, TAIndex _) =
      Left "normalizeTypeDeep: expected type argument"
    normalizeArg (TPS_Ix _, TAType _) =
      Left "normalizeTypeDeep: expected index argument"

sortsDefEq :: TypeTheory -> TypeExpr -> TypeExpr -> Either Text Bool
sortsDefEq tt lhs rhs = do
  lhs' <- normalizeTypeDeep tt lhs
  rhs' <- normalizeTypeDeep tt rhs
  pure (lhs' == rhs')

normalizeIx :: TypeTheory -> TypeExpr -> IxTerm -> Either Text IxTerm
normalizeIx tt expectedSort tm = do
  expectedSort' <- normalizeTypeDeep tt expectedSort
  _ <- requireTheoryForSort tt expectedSort'
  normalizeLoop (ttIxFuel tt) tt expectedSort' tm
  where
    requireTheoryForSort theory sortTy =
      let mode = typeMode sortTy
       in case M.lookup mode (ttIndex theory) of
            Just ixTheory -> Right ixTheory
            Nothing -> Left "normalizeIx: expected sort is not in an index mode"

normalizeLoop :: Int -> TypeTheory -> TypeExpr -> IxTerm -> Either Text IxTerm
normalizeLoop fuel tt expectedSort tm
  | fuel < 0 = Left "normalizeIx: negative fuel"
  | fuel == 0 = Left "normalizeIx: fuel exhausted"
  | otherwise = do
      mStep <- rewriteOnceIx tt expectedSort tm
      case mStep of
        Nothing -> Right tm
        Just tm' -> normalizeLoop (fuel - 1) tt expectedSort tm'

rewriteOnceIx :: TypeTheory -> TypeExpr -> IxTerm -> Either Text (Maybe IxTerm)
rewriteOnceIx tt expectedSort tm = do
  expectedSort' <- normalizeTypeDeep tt expectedSort
  ixTheory <- requireTheoryForSort tt expectedSort'
  case firstJust (map (\rule -> applyRuleAt tt expectedSort' rule tm) (itRules ixTheory)) of
    Just tm' -> Right (Just tm')
    Nothing ->
      case tm of
        IXFun f args -> do
          sig <- requireFunSig expectedSort' ixTheory f args
          rewritten <- rewriteArgsBySort (zip (ifArgs sig) args)
          pure (fmap (IXFun f) rewritten)
        _ -> Right Nothing
  where
    requireTheoryForSort theory sortTy =
      let mode = typeMode sortTy
       in case M.lookup mode (ttIndex theory) of
            Just ixTheory -> Right ixTheory
            Nothing -> Left "normalizeIx: expected sort is not in an index mode"

    requireFunSig sortTy ixTheory f args =
      case M.lookup f (itFuns ixTheory) of
        Nothing -> Left "normalizeIx: unknown index function"
        Just sig ->
          if length (ifArgs sig) /= length args
            then Left "normalizeIx: index function arity mismatch"
            else do
              sameSort <- sortsDefEq tt (ifRes sig) sortTy
              if sameSort
                then Right sig
                else Left "normalizeIx: index function result sort mismatch"

    rewriteArgsBySort [] = Right Nothing
    rewriteArgsBySort ((argSort, arg):rest) = do
      argSort' <- normalizeTypeDeep tt argSort
      mHead <- rewriteOnceIx tt argSort' arg
      case mHead of
        Just arg' -> Right (Just (arg' : map snd rest))
        Nothing -> do
          mTail <- rewriteArgsBySort rest
          pure (fmap (arg :) mTail)

applyRuleAt :: TypeTheory -> TypeExpr -> IxRule -> IxTerm -> Maybe IxTerm
applyRuleAt tt expectedSort rule tm = do
  sub <- matchPattern tt expectedSort (S.fromList (irVars rule)) (irLHS rule) tm M.empty
  pure (instantiate sub (irRHS rule))

type IxPatternSubst = M.Map IxVar IxTerm

matchPattern :: TypeTheory -> TypeExpr -> S.Set IxVar -> IxTerm -> IxTerm -> IxPatternSubst -> Maybe IxPatternSubst
matchPattern tt expectedSort patternVars lhs rhs sub =
  case lhs of
    IXVar v
      | v `S.member` patternVars ->
          if not (sortEqMaybe (ixvSort v) expectedSort)
            then Nothing
            else
              case M.lookup v sub of
                Nothing -> Just (M.insert v rhs sub)
                Just rhs0 ->
                  if rhs0 == rhs
                    then Just sub
                    else Nothing
      | otherwise ->
          if sortEqMaybe (ixvSort v) expectedSort && lhs == rhs
            then Just sub
            else Nothing
    IXBound i ->
      case rhs of
        IXBound j | i == j -> Just sub
        _ -> Nothing
    IXFun f xs ->
      case rhs of
        IXFun g ys
          | f == g && length xs == length ys ->
              case lookupFunSig expectedSort f xs of
                Nothing -> Nothing
                Just sig ->
                  foldl step (Just sub) (zip3 (ifArgs sig) xs ys)
        _ -> Nothing
  where
    step acc (argSort, x, y) = do
      sub' <- acc
      matchPattern tt argSort patternVars x y sub'

    lookupFunSig sortTy fname args =
      case M.lookup (typeMode sortTy) (ttIndex tt) of
        Nothing -> Nothing
        Just ixTheory ->
          case M.lookup fname (itFuns ixTheory) of
            Nothing -> Nothing
            Just sig ->
              if length (ifArgs sig) /= length args
                then Nothing
                else
                  if sortEqMaybe (ifRes sig) sortTy
                    then Just sig
                    else Nothing

    sortEqMaybe a b =
      case sortsDefEq tt a b of
        Right True -> True
        _ -> False

instantiate :: IxPatternSubst -> IxTerm -> IxTerm
instantiate sub tm =
  case tm of
    IXVar v -> M.findWithDefault tm v sub
    IXBound _ -> tm
    IXFun name args -> IXFun name (map (instantiate sub) args)

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (x:xs) =
  case x of
    Just _ -> x
    Nothing -> firstJust xs
