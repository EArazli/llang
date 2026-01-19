{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Presentation
  ( Presentation(..)
  , validateEquation
  , validatePresentation
  ) where

import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term (TypeError, mkOp)
import Strat.Kernel.Weakening (isCtxExtension, weakenTermToCtxMaybe)
import Data.Text (Text)
import qualified Data.List as L
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Map.Strict as M

data Presentation = Presentation
  { presName :: Text
  , presSig  :: Signature
  , presEqs  :: [Equation]
  }
  deriving (Eq, Show)

validateEquation :: Signature -> Equation -> Either Text ()
validateEquation sig eq = do
  let lhsSort = termSort (eqLHS eq)
  let rhsSort = termSort (eqRHS eq)
  if lhsSort /= rhsSort
    then Left ("Equation sort mismatch: " <> eqName eq)
    else
      let allowed = S.fromList (map bVar (eqTele eq))
          used = varsTerm (eqLHS eq) `S.union` varsTerm (eqRHS eq)
          bad = used `S.difference` allowed
      in if S.null bad
           then do
             validateEqScopes eq
             env <- validateTele sig (eqName eq) (eqTele eq)
             checkVarSorts (eqName eq) env (eqLHS eq)
             checkVarSorts (eqName eq) env (eqRHS eq)
             validateTerm sig (eqLHS eq)
             validateTerm sig (eqRHS eq)
           else Left ("Equation has out-of-scope vars: " <> eqName eq)

validatePresentation :: Presentation -> Either Text ()
validatePresentation pres = do
  validateSignature (presSig pres)
  mapM_ (validateEquation (presSig pres)) (presEqs pres)

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

validateSignature :: Signature -> Either Text ()
validateSignature sig = do
  mapM_ (validateSortCtor sig) (M.elems (sigSortCtors sig))
  mapM_ (validateOpDecl sig) (M.elems (sigOps sig))

validateSortCtor :: Signature -> SortCtor -> Either Text ()
validateSortCtor sig ctor = do
  let scope = ScopeId ("sort:" <> renderSortName (scName ctor))
  validateSortBinderScopes scope (scName ctor) (scTele ctor)
  _ <- validateTele sig (renderSortName (scName ctor)) (scTele ctor)
  pure ()

validateClosedSort :: Signature -> Sort -> Either Text ()
validateClosedSort sig s = do
  validateSort sig s
  if S.null (varsInSort s)
    then Right ()
    else Left ("Sort has free vars: " <> renderSort s)

validateOpDecl :: Signature -> OpDecl -> Either Text ()
validateOpDecl sig decl = do
  let scope = ScopeId ("op:" <> renderOpName (opName decl))
  validateOpBinderScopes scope (opName decl) (opTele decl)
  env <- validateTele sig (renderOpName (opName decl)) (opTele decl)
  let used = varsInSort (opResult decl)
  let allowed = S.fromList (M.keys env)
  if S.isSubsetOf used allowed
    then do
      checkSort (renderOpName (opName decl)) env (opResult decl)
      validateSort sig (opResult decl)
    else Left ("Op result sort has out-of-scope vars: " <> renderOpName (opName decl))

validateOpBinderScopes :: ScopeId -> OpName -> [Binder] -> Either Text ()
validateOpBinderScopes expected opName0 binders =
  case filter (\v -> vScope v /= expected) (map bVar binders) of
    (v : _) -> Left ("Op binder has invalid scope: " <> renderOpName opName0 <> " (" <> renderScope (vScope v) <> ")")
    [] ->
      let locals = map vLocal (map bVar binders)
          expectedLocals = [0 .. length binders - 1]
      in if L.sort locals == expectedLocals
           then Right ()
           else Left ("Op binder locals not contiguous: " <> renderOpName opName0)

validateSortBinderScopes :: ScopeId -> SortName -> [Binder] -> Either Text ()
validateSortBinderScopes expected sortName0 binders =
  case filter (\v -> vScope v /= expected) (map bVar binders) of
    (v : _) -> Left ("Sort binder has invalid scope: " <> renderSortName sortName0 <> " (" <> renderScope (vScope v) <> ")")
    [] ->
      let locals = map vLocal (map bVar binders)
          expectedLocals = [0 .. length binders - 1]
      in if L.sort locals == expectedLocals
           then Right ()
           else Left ("Sort binder locals not contiguous: " <> renderSortName sortName0)

validateTele :: Signature -> Text -> [Binder] -> Either Text (M.Map Var Sort)
validateTele sig eqName0 = go M.empty
  where
    go env [] = Right env
    go env (Binder v s : rest) = do
      validateSort sig s
      checkSort eqName0 env s
      let used = varsInSort s
      let bad = used `S.difference` S.fromList (M.keys env)
      if S.null bad
        then go (M.insert v s env) rest
        else Left ("Binder sort has out-of-scope vars: " <> eqName0)

checkVarSorts :: Text -> M.Map Var Sort -> Term -> Either Text ()
checkVarSorts eqName0 env tm = do
  checkSort eqName0 env (termSort tm)
  case termNode tm of
    TVar v ->
      case M.lookup v env of
        Nothing -> Right ()
        Just decl ->
          if termSort tm == decl
            then Right ()
            else
              if sortIsWeakening decl (termSort tm)
                then Right ()
                else Left ("Variable sort mismatch in equation: " <> eqName0)
    TOp _ args -> mapM_ (checkVarSorts eqName0 env) args

checkSort :: Text -> M.Map Var Sort -> Sort -> Either Text ()
checkSort eqName0 env (Sort _ idx) = mapM_ (checkVarSorts eqName0 env) idx

sortIsWeakening :: Sort -> Sort -> Bool
sortIsWeakening src tgt =
  case (src, tgt) of
    (Sort s (ctxOld:idxOld), Sort s' (ctxNew:idxNew))
      | s == s' && length idxOld == length idxNew ->
          if isCtxExtension ctxOld ctxNew
            then case traverse (\t -> weakenTermToCtxMaybe t ctxNew) idxOld of
              Just idxOld' -> idxOld' == idxNew
              Nothing -> False
            else False
    _ -> False

validateTerm :: Signature -> Term -> Either Text ()
validateTerm sig tm = do
  inferred <- inferSort sig tm
  if inferred == termSort tm
    then Right ()
    else Left ("Term sort mismatch: " <> renderSort inferred <> " vs " <> renderSort (termSort tm))

inferSort :: Signature -> Term -> Either Text Sort
inferSort sig tm =
  case termNode tm of
    TVar _ -> do
      validateSort sig (termSort tm)
      pure (termSort tm)
    TOp op args -> do
      mapM_ (validateTerm sig) args
      case mkOp sig op args of
        Left err -> Left ("Term not well-typed: " <> renderTypeError err)
        Right t ->
          if termSort t == termSort tm
            then pure (termSort tm)
            else Left ("Term sort mismatch: " <> renderSort (termSort t) <> " vs " <> renderSort (termSort tm))

validateSort :: Signature -> Sort -> Either Text ()
validateSort sig (Sort name idx) = do
  mapM_ (validateTerm sig) idx
  case mkSort sig name idx of
    Left err -> Left ("Sort not well-formed: " <> renderSortError err)
    Right _ -> Right ()

renderTypeError :: TypeError -> Text
renderTypeError = T.pack . show

renderSortError :: SortError -> Text
renderSortError = T.pack . show

renderSort :: Sort -> Text
renderSort = T.pack . show

renderSortName :: SortName -> Text
renderSortName (SortName t) = t

renderOpName :: OpName -> Text
renderOpName (OpName t) = t
