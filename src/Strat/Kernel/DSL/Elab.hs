{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.DSL.Elab
  ( loadDoctrines
  , elabRawFile
  , elabPresentation
  ) where

import Strat.Kernel.DSL.AST
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DoctrineExpr
import Strat.Kernel.Presentation
import Strat.Kernel.Rule
import Strat.Kernel.Signature
import Strat.Kernel.Term
import Strat.Kernel.Syntax
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM)

data Def = Def
  { defExpr :: DocExpr
  , defRawPresentation :: Maybe Presentation
  }

type Env = M.Map Text Def
type VarEnv = M.Map Text (Var, Sort)

loadDoctrines :: Text -> Either Text (M.Map Text DocExpr)
loadDoctrines input = do
  rf <- parseRawFile input
  elabRawFile rf

elabRawFile :: RawFile -> Either Text (M.Map Text DocExpr)
elabRawFile (RawFile decls) = do
  env <- foldM step M.empty decls
  pure (M.map defExpr env)
  where
    step env decl =
      case decl of
        DeclWhere name items -> do
          if M.member name env
            then Left ("Duplicate doctrine name: " <> name)
            else do
              pres <- elabPresentation name items
              let def = Def { defExpr = Atom name pres, defRawPresentation = Just pres }
              pure (M.insert name def env)
        DeclExpr name expr -> do
          if M.member name env
            then Left ("Duplicate doctrine name: " <> name)
            else do
              dexpr <- resolveExpr env expr
              let def = Def { defExpr = dexpr, defRawPresentation = Nothing }
              pure (M.insert name def env)

elabPresentation :: Text -> [RawItem] -> Either Text Presentation
elabPresentation name items = do
  (sig, eqs) <- foldM step (Signature M.empty M.empty, []) items
  pure Presentation { presName = name, presSig = sig, presEqs = eqs }
  where
    step (sig, eqs) item =
      case item of
        ItemSort decl -> do
          sig' <- addSortDecl sig decl
          pure (sig', eqs)
        ItemOp decl -> do
          sig' <- addOpDecl sig decl
          pure (sig', eqs)
        ItemRule rr -> do
          eq <- elabRule sig rr
          pure (sig, eqs <> [eq])

addSortDecl :: Signature -> RawSortDecl -> Either Text Signature
addSortDecl sig decl = do
  let name = SortName (rsName decl)
  if M.member name (sigSortCtors sig)
    then Left ("Duplicate sort ctor: " <> rsName decl)
    else do
      params <- mapM (elabSort sig M.empty) (rsParams decl)
      let ctor = SortCtor { scName = name, scParamSort = params }
      pure sig { sigSortCtors = M.insert name ctor (sigSortCtors sig) }

addOpDecl :: Signature -> RawOpDecl -> Either Text Signature
addOpDecl sig decl = do
  let name = OpName (roName decl)
  if M.member name (sigOps sig)
    then Left ("Duplicate op: " <> roName decl)
    else do
      let scope = ScopeId ("op:" <> roName decl)
      (tele, env) <- elabBinders sig scope (roTele decl)
      res <- elabSort sig env (roResult decl)
      let opDecl = OpDecl { opName = name, opTele = tele, opResult = res }
      pure sig { sigOps = M.insert name opDecl (sigOps sig) }

elabRule :: Signature -> RawRule -> Either Text Equation
elabRule sig rr = do
  let scope = ScopeId ("eq:" <> rrName rr)
  (tele, env) <- elabBinders sig scope (rrTele rr)
  lhsTerm <- elabTerm sig env (rrLHS rr)
  rhsTerm <- elabTerm sig env (rrRHS rr)
  pure Equation
    { eqName = rrName rr
    , eqClass = rrClass rr
    , eqOrient = rrOrient rr
    , eqTele = tele
    , eqLHS = lhsTerm
    , eqRHS = rhsTerm
    }

elabBinders :: Signature -> ScopeId -> [RawBinder] -> Either Text ([Binder], VarEnv)
elabBinders sig scope binders =
  foldM step ([], M.empty, 0) binders >>= \(bs, env, _) -> pure (bs, env)
  where
    step (acc, env, ix) (RawBinder name sRaw) = do
      let v = Var scope ix
      s <- elabSort sig env sRaw
      let env' = M.insert name (v, s) env
      pure (acc <> [Binder v s], env', ix + 1)

elabTerm :: Signature -> VarEnv -> RawTerm -> Either Text Term
elabTerm sig env tm =
  case tm of
    RVar v ->
      case M.lookup v env of
        Nothing -> Left ("Unknown variable: " <> v)
        Just (var, s) -> Right (mkVar s var)
    RApp name args -> do
      args' <- mapM (elabTerm sig env) args
      case mkOp sig (OpName name) args' of
        Left err -> Left (renderTypeError err)
        Right t -> Right t

elabSort :: Signature -> VarEnv -> RawSort -> Either Text Sort
elabSort sig env (RawSort name idx) = do
  idxTerms <- mapM (elabTerm sig env) idx
  case mkSort sig (SortName name) idxTerms of
    Left err -> Left (renderSortError err)
    Right s -> Right s

resolveExpr :: Env -> RawExpr -> Either Text DocExpr
resolveExpr env expr =
  case expr of
    ERef name ->
      case M.lookup name env of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just def -> Right (defExpr def)
    EInst base ns ->
      case M.lookup base env of
        Nothing -> Left ("Unknown doctrine: " <> base)
        Just def ->
          case defRawPresentation def of
            Nothing -> Left ("@ requires a where-defined doctrine: " <> base)
            Just pres -> Right (Atom ns pres)
    EAnd a b -> And <$> resolveExpr env a <*> resolveExpr env b
    ERenameOps m e -> RenameOps (mapOpNames m) <$> resolveExpr env e
    ERenameSorts m e -> RenameSorts (mapSortNames m) <$> resolveExpr env e
    ERenameEqs m e -> RenameEqs m <$> resolveExpr env e
    EShareOps pairs e -> ShareOps (mapPair OpName pairs) <$> resolveExpr env e
    EShareSorts pairs e -> ShareSorts (mapPair SortName pairs) <$> resolveExpr env e

mapOpNames :: M.Map Text Text -> M.Map OpName OpName
mapOpNames m = M.fromList [(OpName k, OpName v) | (k, v) <- M.toList m]

mapSortNames :: M.Map Text Text -> M.Map SortName SortName
mapSortNames m = M.fromList [(SortName k, SortName v) | (k, v) <- M.toList m]

mapPair :: (Text -> a) -> [(Text, Text)] -> [(a, a)]
mapPair f = map (\(a, b) -> (f a, f b))

renderTypeError :: TypeError -> Text
renderTypeError = T.pack . show

renderSortError :: SortError -> Text
renderSortError = T.pack . show
