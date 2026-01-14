{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Run
  ( RunResult(..)
  , runFile
  , renderRunResult
  ) where

import Strat.Frontend.Loader (loadModule)
import Strat.Frontend.Env
import Strat.Frontend.RunSpec
import Strat.Kernel.DSL.AST (RawExpr(..))
import Strat.Kernel.DoctrineExpr (DocExpr(..), elabDocExpr)
import Strat.Kernel.Presentation (Presentation(..))
import Strat.Kernel.RewriteSystem (compileRewriteSystem)
import Strat.Kernel.Rewrite (normalize)
import Strat.Kernel.Syntax (OpName(..), SortName(..), Term(..))
import Strat.Surface (defaultInstance, elaborate)
import Strat.Syntax.Spec (SyntaxInstance(..), instantiateSyntax)
import Strat.Model.Spec (instantiateModel)
import Strat.Backend (Value(..), RuntimeError(..), evalTerm)
import Strat.Backend.Concat (CatExpr(..), compileTerm)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M


data RunResult = RunResult
  { rrPresentation :: Presentation
  , rrInputTerm :: Term
  , rrNormalized :: Term
  , rrPrintedNormalized :: Text
  , rrCatExpr :: CatExpr
  , rrValue :: Value
  , rrOutput :: Text
  }
  deriving (Eq, Show)

runFile :: FilePath -> IO (Either Text RunResult)
runFile path = do
  envResult <- loadModule path
  case envResult of
    Left err -> pure (Left err)
    Right env ->
      case meRun env of
        Nothing -> pure (Left "No run block found")
        Just spec -> pure (runWithEnv env spec)

runWithEnv :: ModuleEnv -> RunSpec -> Either Text RunResult
runWithEnv env spec = do
  docExpr <- resolveRunExpr env (runDoctrine spec)
  pres <- elabDocExpr docExpr
  rs <- compileRewriteSystem (runPolicy spec) pres
  syntaxSpec <- lookupSpec "syntax" (runSyntax spec) (meSyntaxes env)
  modelSpec <- lookupSpec "model" (runModel spec) (meModels env)
  syntaxInstance <- instantiateSyntax pres (runOpen spec) syntaxSpec
  comb <- siParse syntaxInstance (runExprText spec)
  term <-
    case elaborate (defaultInstance pres) comb of
      Left err -> Left ("Elaboration error: " <> T.pack (show err))
      Right t -> Right t
  let norm = normalize (runFuel spec) rs term
  let printedNorm = siPrint syntaxInstance norm
  let cat = compileTerm norm
  model <- instantiateModel pres (runOpen spec) modelSpec
  val <-
    case evalTerm model norm of
      Left err -> Left ("Evaluation error: " <> renderRuntimeError err)
      Right v -> Right v
  let output = renderRunResult spec printedNorm cat val
  pure RunResult
    { rrPresentation = pres
    , rrInputTerm = term
    , rrNormalized = norm
    , rrPrintedNormalized = printedNorm
    , rrCatExpr = cat
    , rrValue = val
    , rrOutput = output
    }

lookupSpec :: Text -> Text -> M.Map Text a -> Either Text a
lookupSpec label name mp =
  case M.lookup name mp of
    Nothing -> Left ("Unknown " <> label <> ": " <> name)
    Just v -> Right v

renderRunResult :: RunSpec -> Text -> CatExpr -> Value -> Text
renderRunResult spec norm cat val =
  T.unlines (concat [normOut, valOut, catOut])
  where
    normOut = if ShowNormalized `elem` runShowFlags spec then ["normalized: " <> norm] else []
    valOut = if ShowValue `elem` runShowFlags spec then ["value: " <> T.pack (show val)] else []
    catOut = if ShowCat `elem` runShowFlags spec then ["cat: " <> T.pack (show cat)] else []

resolveRunExpr :: ModuleEnv -> RawExpr -> Either Text DocExpr
resolveRunExpr env expr =
  case expr of
    ERef name ->
      case M.lookup name (meDoctrines env) of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just d -> Right d
    EInst base ns ->
      case M.lookup base (mePresentations env) of
        Nothing -> Left ("@ requires a where-defined doctrine: " <> base)
        Just pres -> Right (Atom ns pres)
    EAnd a b -> And <$> resolveRunExpr env a <*> resolveRunExpr env b
    ERenameOps m e -> RenameOps (mapOpNames m) <$> resolveRunExpr env e
    ERenameSorts m e -> RenameSorts (mapSortNames m) <$> resolveRunExpr env e
    ERenameEqs m e -> RenameEqs m <$> resolveRunExpr env e
    EShareOps pairs e -> ShareOps (mapPair OpName pairs) <$> resolveRunExpr env e
    EShareSorts pairs e -> ShareSorts (mapPair SortName pairs) <$> resolveRunExpr env e

mapOpNames :: M.Map Text Text -> M.Map OpName OpName
mapOpNames m = M.fromList [(OpName k, OpName v) | (k, v) <- M.toList m]

mapSortNames :: M.Map Text Text -> M.Map SortName SortName
mapSortNames m = M.fromList [(SortName k, SortName v) | (k, v) <- M.toList m]

mapPair :: (Text -> a) -> [(Text, Text)] -> [(a, a)]
mapPair f = map (\(a, b) -> (f a, f b))

renderRuntimeError :: RuntimeError -> Text
renderRuntimeError (RuntimeError msg) = msg
