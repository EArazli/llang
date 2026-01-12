{-# LANGUAGE OverloadedStrings #-}
module Strat.Meta.DSL.Elab.FO where

import Strat.Meta.DSL.AST
import Strat.Meta.DSL.Parse (parseRawFile)
import Strat.Meta.DoctrineExpr
import Strat.Meta.Presentation
import Strat.Meta.Rule
import Strat.Meta.Term.FO
import Strat.Meta.Types
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Control.Monad (foldM)
import qualified Data.List as L

data Def = Def
  { defExpr :: DocExpr Term
  , defRawPresentation :: Maybe (Presentation Term)
  }

type Env = M.Map Text Def

loadDoctrinesFO :: Text -> Either Text (M.Map Text (DocExpr Term))
loadDoctrinesFO input = do
  rf <- parseRawFile input
  elabRawFileFO rf

elabRawFileFO :: RawFile -> Either Text (M.Map Text (DocExpr Term))
elabRawFileFO (RawFile decls) = do
  env <- foldM step M.empty decls
  pure (M.map defExpr env)
  where
    step env decl =
      case decl of
        DeclWhere name rules -> do
          if M.member name env
            then Left ("Duplicate doctrine name: " <> name)
            else do
              pres <- elabPresentationFO name rules
              let def = Def { defExpr = Atom name pres, defRawPresentation = Just pres }
              pure (M.insert name def env)
        DeclExpr name expr -> do
          if M.member name env
            then Left ("Duplicate doctrine name: " <> name)
            else do
              dexpr <- resolveExpr env expr
              let def = Def { defExpr = dexpr, defRawPresentation = Nothing }
              pure (M.insert name def env)

elabPresentationFO :: Text -> [RawRule] -> Either Text (Presentation Term)
elabPresentationFO name rules = do
  eqs <- mapM elabRuleFO rules
  pure Presentation { presName = name, presEqs = eqs }

elabRuleFO :: RawRule -> Either Text (Equation Term)
elabRuleFO rr = do
  let varMap = buildVarMap (rrLHS rr) (rrRHS rr)
  lhs <- elabTerm varMap (rrName rr) (rrLHS rr)
  rhs <- elabTerm varMap (rrName rr) (rrRHS rr)
  pure Equation
    { eqName = rrName rr
    , eqClass = rrClass rr
    , eqOrient = rrOrient rr
    , eqLHS = lhs
    , eqRHS = rhs
    }

elabTerm :: M.Map Text Int -> Text -> RawTerm -> Either Text Term
elabTerm varMap ruleName term =
  case term of
    RVar v ->
      case M.lookup v varMap of
        Nothing -> Left ("Unknown variable: " <> v)
        Just ix -> Right (TVar (V (Ns (RuleId ruleName DirLR) 0) ix))
    RApp s args -> do
      args' <- mapM (elabTerm varMap ruleName) args
      pure (TApp (Sym s) args')

buildVarMap :: RawTerm -> RawTerm -> M.Map Text Int
buildVarMap lhs rhs =
  snd (scanTerm rhs (scanTerm lhs (0, M.empty)))
  where
    scanTerm t st =
      case t of
        RVar v ->
          let (n, m) = st
          in if M.member v m then st else (n + 1, M.insert v n m)
        RApp _ args -> L.foldl' (flip scanTerm) st args

resolveExpr :: Env -> RawExpr -> Either Text (DocExpr Term)
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
    ERenameSyms m e -> RenameSyms m <$> resolveExpr env e
    ERenameEqs m e -> RenameEqs m <$> resolveExpr env e
    EShareSyms pairs e -> ShareSyms pairs <$> resolveExpr env e
