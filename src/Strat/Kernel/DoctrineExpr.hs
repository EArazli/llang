{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DoctrineExpr
  ( DocExpr(..)
  , elabDocExpr
  , compileDocExpr
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Subst
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

data DocExpr
  = Atom Text Presentation
  | And DocExpr DocExpr
  | RenameEqs (M.Map Text Text) DocExpr
  | RenameOps (M.Map OpName OpName) DocExpr
  | RenameSorts (M.Map SortName SortName) DocExpr
  | ShareOps [(OpName, OpName)] DocExpr
  | ShareSorts [(SortName, SortName)] DocExpr
  deriving (Eq, Show)

elabDocExpr :: DocExpr -> Either Text Presentation
elabDocExpr expr =
  case expr of
    Atom ns pres -> qualifyPresentation ns pres
    And a b -> do
      pa <- elabDocExpr a
      pb <- elabDocExpr b
      mergePresentations pa pb
    RenameEqs m e -> do
      p <- elabDocExpr e
      let p' = renameEqsWith (renameEqName m) p
      checkUniqueEqNames p'
      pure p'
    RenameOps m e -> do
      p <- elabDocExpr e
      renameOpsPresentation (renameOpName m) p
    RenameSorts m e -> do
      p <- elabDocExpr e
      renameSortsPresentation (renameSortName m) p
    ShareOps pairs e -> do
      p <- elabDocExpr e
      shareOps pairs p
    ShareSorts pairs e -> do
      p <- elabDocExpr e
      shareSorts pairs p

compileDocExpr :: RewritePolicy -> DocExpr -> Either Text RewriteSystem
compileDocExpr pol expr = elabDocExpr expr >>= compileRewriteSystem pol

qualifyPresentation :: Text -> Presentation -> Either Text Presentation
qualifyPresentation ns pres = do
  pres1 <- renameSortsPresentation (qualifySortName ns) pres
  pres2 <- renameOpsPresentation (qualifyOpName ns) pres1
  let pres3 = renameEqsWith (qualifyEqName ns) pres2
  pure pres3 { presName = ns }

qualifyEqName :: Text -> Text -> Text
qualifyEqName ns name = ns <> "." <> name

qualifyOpName :: Text -> OpName -> OpName
qualifyOpName ns (OpName t) = OpName (qualifyEqName ns t)

qualifySortName :: Text -> SortName -> SortName
qualifySortName ns (SortName t) = SortName (qualifyEqName ns t)

renameEqName :: M.Map Text Text -> Text -> Text
renameEqName m name = M.findWithDefault name name m

renameOpName :: M.Map OpName OpName -> OpName -> OpName
renameOpName m name = M.findWithDefault name name m

renameSortName :: M.Map SortName SortName -> SortName -> SortName
renameSortName m name = M.findWithDefault name name m

mergePresentations :: Presentation -> Presentation -> Either Text Presentation
mergePresentations a b = do
  let presName' = presName a <> "+" <> presName b
  sig' <- mergeSignatures (presSig a) (presSig b)
  let eqs' = presEqs a <> presEqs b
  let pres' = Presentation { presName = presName', presSig = sig', presEqs = eqs' }
  checkUniqueEqNames pres'
  pure pres'

checkUniqueEqNames :: Presentation -> Either Text ()
checkUniqueEqNames pres =
  case findDuplicate (map eqName (presEqs pres)) of
    Nothing -> Right ()
    Just dup -> Left ("Duplicate equation name: " <> dup)
  where
    findDuplicate names = go S.empty names
    go _ [] = Nothing
    go seen (n : ns)
      | n `S.member` seen = Just n
      | otherwise = go (S.insert n seen) ns

mergeSignatures :: Signature -> Signature -> Either Text Signature
mergeSignatures s1 s2 = do
  sortCtors <- mergeSortCtors (M.toList (sigSortCtors s1) <> M.toList (sigSortCtors s2))
  opDecls <- mergeOpDecls (M.toList (sigOps s1) <> M.toList (sigOps s2))
  pure Signature { sigSortCtors = sortCtors, sigOps = opDecls }

mergeSortCtors :: [(SortName, SortCtor)] -> Either Text (M.Map SortName SortCtor)
mergeSortCtors = foldl step (Right M.empty)
  where
    step acc (name, ctor) = do
      m <- acc
      case M.lookup name m of
        Nothing -> pure (M.insert name ctor m)
        Just ctor' ->
          if ctor' == ctor
            then pure m
            else Left ("Duplicate sort ctor: " <> renderSortName name)

mergeOpDecls :: [(OpName, OpDecl)] -> Either Text (M.Map OpName OpDecl)
mergeOpDecls = foldl step (Right M.empty)
  where
    step acc (name, decl) = do
      m <- acc
      case M.lookup name m of
        Nothing -> pure (M.insert name decl m)
        Just decl' ->
          if alphaEqOpDecl decl' decl
            then pure m
            else Left ("Duplicate op decl: " <> renderOpName name)

shareOps :: [(OpName, OpName)] -> Presentation -> Either Text Presentation
shareOps pairs pres = do
  let allOps = M.keysSet (sigOps (presSig pres))
  case unknownNames allOps (concatMap (\(a, b) -> [a, b]) pairs) of
    Just unknown -> Left ("Unknown op in share: " <> renderOpName unknown)
    Nothing -> do
      let mapping = buildClassMap pairs
      renameOpsPresentation (renameOpName mapping) pres

shareSorts :: [(SortName, SortName)] -> Presentation -> Either Text Presentation
shareSorts pairs pres = do
  let allSorts = M.keysSet (sigSortCtors (presSig pres))
  case unknownNames allSorts (concatMap (\(a, b) -> [a, b]) pairs) of
    Just unknown -> Left ("Unknown sort in share: " <> renderSortName unknown)
    Nothing -> do
      let mapping = buildClassMap pairs
      renameSortsPresentation (renameSortName mapping) pres

unknownNames :: Ord a => S.Set a -> [a] -> Maybe a
unknownNames known names = go names
  where
    go [] = Nothing
    go (n : ns)
      | n `S.member` known = go ns
      | otherwise = Just n

buildClassMap :: Ord a => [(a, a)] -> M.Map a a
buildClassMap pairs =
  let nodes = S.fromList (concatMap (\(a, b) -> [a, b]) pairs)
      adj = foldl addEdge M.empty pairs
      components = componentsFrom nodes adj
  in M.fromList
      [ (n, rep)
      | comp <- components
      , let rep = S.findMin comp
      , n <- S.toList comp
      ]
  where
    addEdge m (a, b) =
      M.insertWith S.union a (S.singleton b) (M.insertWith S.union b (S.singleton a) m)

componentsFrom :: Ord a => S.Set a -> M.Map a (S.Set a) -> [S.Set a]
componentsFrom nodes adj = go nodes []
  where
    go remaining acc =
      case S.minView remaining of
        Nothing -> acc
        Just (n, rest) ->
          let comp = dfs adj S.empty [n]
              rest' = rest `S.difference` comp
          in go rest' (comp : acc)

dfs :: Ord a => M.Map a (S.Set a) -> S.Set a -> [a] -> S.Set a
dfs _ visited [] = visited
dfs adj visited (x : xs)
  | x `S.member` visited = dfs adj visited xs
  | otherwise =
      let neigh = M.findWithDefault S.empty x adj
      in dfs adj (S.insert x visited) (S.toList neigh <> xs)

renameOpsPresentation :: (OpName -> OpName) -> Presentation -> Either Text Presentation
renameOpsPresentation f pres = do
  sig' <- renameOpsSignature f (presSig pres)
  let eqs' = map (renameOpsEquation f) (presEqs pres)
  pure pres { presSig = sig', presEqs = eqs' }

renameSortsPresentation :: (SortName -> SortName) -> Presentation -> Either Text Presentation
renameSortsPresentation f pres = do
  sig' <- renameSortsSignature f (presSig pres)
  let eqs' = map (renameSortsEquation f) (presEqs pres)
  pure pres { presSig = sig', presEqs = eqs' }

renameOpsSignature :: (OpName -> OpName) -> Signature -> Either Text Signature
renameOpsSignature f sig = do
  let sortCtors' = M.fromList
        [ (name, ctor { scParamSort = map (renameOpsSort f) (scParamSort ctor) })
        | (name, ctor) <- M.toList (sigSortCtors sig)
        ]
  let opDecls = map (renameOpsDecl f) (M.elems (sigOps sig))
  opDecls' <- mergeOpDecls [(opName d, d) | d <- opDecls]
  pure Signature { sigSortCtors = sortCtors', sigOps = opDecls' }

renameSortsSignature :: (SortName -> SortName) -> Signature -> Either Text Signature
renameSortsSignature f sig = do
  let sortDecls =
        [ (f name, ctor { scName = f (scName ctor), scParamSort = map (renameSortsSort f) (scParamSort ctor) })
        | (name, ctor) <- M.toList (sigSortCtors sig)
        ]
  sortCtors' <- mergeSortCtors sortDecls
  let opDecls = map (renameSortsDecl f) (M.elems (sigOps sig))
  opDecls' <- mergeOpDecls [(opName d, d) | d <- opDecls]
  pure Signature { sigSortCtors = sortCtors', sigOps = opDecls' }

renameOpsDecl :: (OpName -> OpName) -> OpDecl -> OpDecl
renameOpsDecl f decl =
  let oldName = opName decl
      newName = f oldName
      oldScope = ScopeId ("op:" <> renderOpName oldName)
      newScope = ScopeId ("op:" <> renderOpName newName)
      tele' = map (renameScopeBinder oldScope newScope) (opTele decl)
      res' = renameScopeSort oldScope newScope (opResult decl)
  in decl
      { opName = newName
      , opTele = map (renameOpsBinder f) tele'
      , opResult = renameOpsSort f res'
      }

renameSortsDecl :: (SortName -> SortName) -> OpDecl -> OpDecl
renameSortsDecl f decl =
  decl
    { opTele = map (renameSortsBinder f) (opTele decl)
    , opResult = renameSortsSort f (opResult decl)
    }

renameOpsEquation :: (OpName -> OpName) -> Equation -> Equation
renameOpsEquation f eq =
  eq
    { eqTele = map (renameOpsBinder f) (eqTele eq)
    , eqLHS = renameOpsTerm f (eqLHS eq)
    , eqRHS = renameOpsTerm f (eqRHS eq)
    }

renameSortsEquation :: (SortName -> SortName) -> Equation -> Equation
renameSortsEquation f eq =
  eq
    { eqTele = map (renameSortsBinder f) (eqTele eq)
    , eqLHS = renameSortsTerm f (eqLHS eq)
    , eqRHS = renameSortsTerm f (eqRHS eq)
    }

renameEqsWith :: (Text -> Text) -> Presentation -> Presentation
renameEqsWith f pres =
  pres { presEqs = map renameEq (presEqs pres) }
  where
    renameEq eq =
      let old = eqName eq
          new = f old
          eq' = eq { eqName = new }
      in renameEquationScope old new eq'

renameEquationScope :: Text -> Text -> Equation -> Equation
renameEquationScope old new eq =
  let oldScope = ScopeId ("eq:" <> old)
      newScope = ScopeId ("eq:" <> new)
      tele' = map (renameScopeBinder oldScope newScope) (eqTele eq)
      lhs' = renameScope oldScope newScope (eqLHS eq)
      rhs' = renameScope oldScope newScope (eqRHS eq)
  in eq { eqTele = tele', eqLHS = lhs', eqRHS = rhs' }

renameOpsTerm :: (OpName -> OpName) -> Term -> Term
renameOpsTerm f tm =
  Term
    { termSort = renameOpsSort f (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar v
          TOp op args -> TOp (f op) (map (renameOpsTerm f) args)
    }

renameOpsSort :: (OpName -> OpName) -> Sort -> Sort
renameOpsSort f (Sort name idx) = Sort name (map (renameOpsTerm f) idx)

renameSortsTerm :: (SortName -> SortName) -> Term -> Term
renameSortsTerm f tm =
  Term
    { termSort = renameSortsSort f (termSort tm)
    , termNode =
        case termNode tm of
          TVar v -> TVar v
          TOp op args -> TOp op (map (renameSortsTerm f) args)
    }

renameSortsSort :: (SortName -> SortName) -> Sort -> Sort
renameSortsSort f (Sort name idx) = Sort (f name) (map (renameSortsTerm f) idx)

renameOpsBinder :: (OpName -> OpName) -> Binder -> Binder
renameOpsBinder f b =
  b { bSort = renameOpsSort f (bSort b) }

renameSortsBinder :: (SortName -> SortName) -> Binder -> Binder
renameSortsBinder f b =
  b { bSort = renameSortsSort f (bSort b) }

alphaEqOpDecl :: OpDecl -> OpDecl -> Bool
alphaEqOpDecl d1 d2 =
  let tele1 = opTele d1
      tele2 = opTele d2
  in length tele1 == length tele2
      && and (zipWith alphaEqBinder tele1 tele2)
      && opResult d1 == applySubstSort subst (opResult d2)
  where
    subst =
      M.fromList
        [ (v2, mkVar s1 v1)
        | (Binder v1 s1, Binder v2 _) <- zip (opTele d1) (opTele d2)
        ]
    alphaEqBinder (Binder _ s1) (Binder _ s2) =
      let s2' = applySubstSort subst s2
      in s1 == s2'

renderOpName :: OpName -> Text
renderOpName (OpName t) = t

renderSortName :: SortName -> Text
renderSortName (SortName t) = t
