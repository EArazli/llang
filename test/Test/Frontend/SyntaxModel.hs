{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.SyntaxModel
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Kernel.DoctrineExpr (elabDocExpr)
import Strat.Kernel.Presentation (presSig)
import Strat.Kernel.Signature (Signature)
import Strat.Kernel.Term (mkOp)
import Strat.Kernel.Syntax (OpName(..), Term)
import Strat.Surface (defaultInstance, elaborate)
import Strat.Syntax.Spec (SyntaxInstance(..), instantiateSyntax)
import Strat.Model.Spec (instantiateModel)
import Strat.Frontend.Env
import Strat.Backend (Value(..), evalTerm)
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "Frontend.SyntaxModel"
    [ testCase "syntax roundtrip" testSyntaxRoundtrip
    , testCase "model evaluation" testModelEval
    ]

loadEnvFromFile :: FilePath -> IO ModuleEnv
loadEnvFromFile path = do
  txt <- TIO.readFile path
  case parseRawFile txt of
    Left err -> assertFailure (T.unpack err) >> pure emptyEnv
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err) >> pure emptyEnv
        Right env -> pure env

mergeEnvs :: ModuleEnv -> ModuleEnv -> IO ModuleEnv
mergeEnvs a b =
  case mergeEnv a b of
    Left err -> assertFailure (T.unpack err) >> pure emptyEnv
    Right env -> pure env


testSyntaxRoundtrip :: Assertion
testSyntaxRoundtrip = do
  presEnv <- getDataFileName "examples/monoid.llang" >>= loadEnvFromFile
  synEnv <- getDataFileName "examples/monoid.syntax.llang" >>= loadEnvFromFile
  env <- mergeEnvs presEnv synEnv
  expr <-
    case M.lookup "Combined" (meDoctrines env) of
      Nothing -> assertFailure "missing Combined" >> pure (error "missing")
      Just e -> pure e
  pres <-
    case elabDocExpr expr of
      Left err -> assertFailure (T.unpack err) >> pure (error "bad")
      Right p -> pure p
  spec <-
    case M.lookup "MonoidSyntax" (meSyntaxes env) of
      Nothing -> assertFailure "missing MonoidSyntax" >> pure (error "missing")
      Just s -> pure s
  inst <-
    case instantiateSyntax pres ["C"] spec of
      Left err -> assertFailure (T.unpack err) >> pure (error "bad")
      Right i -> pure i
  let input = "k(e * e)"
  comb <-
    case siParse inst input of
      Left err -> assertFailure (T.unpack err) >> pure (error "bad")
      Right c -> pure c
  term <-
    case elaborate (defaultInstance pres) comb of
      Left err -> assertFailure (show err) >> pure (error "bad")
      Right t -> pure t
  let printed = siPrint inst term
  comb2 <-
    case siParse inst printed of
      Left err -> assertFailure (T.unpack err) >> pure (error "bad")
      Right c -> pure c
  term2 <-
    case elaborate (defaultInstance pres) comb2 of
      Left err -> assertFailure (show err) >> pure (error "bad")
      Right t -> pure t
  term2 @?= term


testModelEval :: Assertion
testModelEval = do
  presEnv <- getDataFileName "examples/monoid.llang" >>= loadEnvFromFile
  modelEnv <- getDataFileName "examples/monoid.models.llang" >>= loadEnvFromFile
  env <- mergeEnvs presEnv modelEnv
  expr <-
    case M.lookup "Combined" (meDoctrines env) of
      Nothing -> assertFailure "missing Combined" >> pure (error "missing")
      Just e -> pure e
  pres <-
    case elabDocExpr expr of
      Left err -> assertFailure (T.unpack err) >> pure (error "bad")
      Right p -> pure p
  spec <-
    case M.lookup "StringMonoid" (meModels env) of
      Nothing -> assertFailure "missing StringMonoid" >> pure (error "missing")
      Just s -> pure s
  model <-
    case instantiateModel pres ["C"] spec of
      Left err -> assertFailure (T.unpack err) >> pure (error "bad")
      Right m -> pure m
  term <-
    case mkOp (presSig pres) (OpName "C.m") [mkTerm (presSig pres) "C.x" [], mkTerm (presSig pres) "C.y" []] of
      Left err -> assertFailure (show err) >> pure (error "bad")
      Right t -> pure t
  case evalTerm model term of
    Left err -> assertFailure (show err)
    Right v -> v @?= VString "xy"

mkTerm :: Signature -> T.Text -> [Term] -> Term
mkTerm sig name args =
  case mkOp sig (OpName name) args of
    Left err -> error (show err)
    Right t -> t
