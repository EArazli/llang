{-# LANGUAGE OverloadedStrings #-}
module Strat.CLI
  ( CLIOptions(..)
  , CLIResult(..)
  , Lang(..)
  , ModelChoice(..)
  , parseArgs
  , runCLI
  , runPipelineText
  , renderResult
  ) where

import Strat.Kernel.DSL.Elab (loadDoctrines)
import Strat.Kernel.DoctrineExpr (elabDocExpr)
import Strat.Kernel.RewriteSystem (RewritePolicy(..), compileRewriteSystem)
import Strat.Kernel.Rewrite (normalize)
import Strat.Kernel.Presentation (Presentation, presSig)
import Strat.Kernel.Signature (Signature(..))
import Strat.Kernel.Syntax (OpName(..), Sort(..), SortName(..), Term, termSort)
import Strat.Surface
import Strat.Surface.Combinator (CombTerm(..))
import Strat.Surface.Combinator.Parse (parseCombTerm)
import Strat.Surface.Lambda (toCombTerm)
import Strat.Surface.Lambda.Parse (parseLamTerm)
import Strat.Backend (Model, Value(..), RuntimeError(..), evalTerm)
import Strat.Backend.Models (symbolicModel, natModel, stringMonoidModel)
import Strat.Backend.Concat (CatExpr(..), compileTerm)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M


data Lang
  = LangComb
  | LangLambda
  deriving (Eq, Show)

data ModelChoice
  = ModelSymbolic
  | ModelNat
  | ModelString
  deriving (Eq, Show)

data CLIOptions = CLIOptions
  { optFile     :: FilePath
  , optDoctrine :: Text
  , optTerm     :: Text
  , optFuel     :: Int
  , optPolicy   :: RewritePolicy
  , optLang     :: Lang
  , optModel    :: ModelChoice
  }
  deriving (Eq, Show)

data CLIResult = CLIResult
  { crDoctrine     :: Text
  , crPresentation :: Presentation
  , crInputTerm    :: Term
  , crNormalized   :: Term
  , crCatExpr      :: CatExpr
  , crValue        :: Value
  }
  deriving (Eq, Show)

parseArgs :: [String] -> Either Text CLIOptions
parseArgs args =
  case args of
    ["--help"] -> Left usage
    ["-h"] -> Left usage
    (flag : _) | "-" `T.isPrefixOf` T.pack flag -> parseFlags args
    _ -> parsePositional args

parsePositional :: [String] -> Either Text CLIOptions
parsePositional args =
  case args of
    [file, doctrine, term] ->
      Right (mkDefault file doctrine term)
    [file, doctrine, term, fuelStr] ->
      case reads fuelStr of
        [(fuel, "")] -> Right (mkDefault file doctrine term) { optFuel = fuel }
        _ -> Left ("Invalid fuel: " <> T.pack fuelStr)
    _ -> Left usage

parseFlags :: [String] -> Either Text CLIOptions
parseFlags args = do
  let defaults =
        CLIOptions
          { optFile = ""
          , optDoctrine = ""
          , optTerm = ""
          , optFuel = 5
          , optPolicy = UseOnlyComputationalLR
          , optLang = LangComb
          , optModel = ModelSymbolic
          }
  opts <- go defaults args
  if null (optFile opts) || T.null (optDoctrine opts) || T.null (optTerm opts)
    then Left "Missing required flags --file --doctrine --term"
    else Right opts
  where
    go opts [] = Right opts
    go opts ("--file" : path : rest) = go (opts { optFile = path }) rest
    go opts ("--doctrine" : name : rest) = go (opts { optDoctrine = T.pack name }) rest
    go opts ("--term" : term : rest) = go (opts { optTerm = T.pack term }) rest
    go opts ("--fuel" : n : rest) =
      case reads n of
        [(fuel, "")] -> go (opts { optFuel = fuel }) rest
        _ -> Left ("Invalid fuel: " <> T.pack n)
    go opts ("--lang" : lang : rest) =
      case lang of
        "comb" -> go (opts { optLang = LangComb }) rest
        "lambda" -> go (opts { optLang = LangLambda }) rest
        _ -> Left ("Unknown language: " <> T.pack lang)
    go opts ("--model" : model : rest) =
      case model of
        "symbolic" -> go (opts { optModel = ModelSymbolic }) rest
        "nat" -> go (opts { optModel = ModelNat }) rest
        "string" -> go (opts { optModel = ModelString }) rest
        _ -> Left ("Unknown model: " <> T.pack model)
    go _ (flag : _) = Left ("Unknown flag: " <> T.pack flag)

mkDefault :: FilePath -> String -> String -> CLIOptions
mkDefault file doctrine term =
  CLIOptions
    { optFile = file
    , optDoctrine = T.pack doctrine
    , optTerm = T.pack term
    , optFuel = 5
    , optPolicy = UseOnlyComputationalLR
    , optLang = LangComb
    , optModel = ModelSymbolic
    }

runCLI :: CLIOptions -> IO (Either Text CLIResult)
runCLI opts = do
  input <- TIO.readFile (optFile opts)
  pure (runPipelineText opts input)

runPipelineText :: CLIOptions -> Text -> Either Text CLIResult
runPipelineText opts input = do
  docs <- loadDoctrines input
  expr <-
    case M.lookup (optDoctrine opts) docs of
      Nothing -> Left ("Unknown doctrine: " <> optDoctrine opts)
      Just d -> Right d
  pres <- elabDocExpr expr
  rs <- compileRewriteSystem (optPolicy opts) pres
  comb <- parseSurface (optLang opts) (optTerm opts)
  let comb' = qualifyCombTerm pres (optDoctrine opts) comb
  term <-
    case elaborate (defaultInstance pres) comb' of
      Left err -> Left ("Elaboration error: " <> T.pack (show err))
      Right t -> Right t
  let norm = normalize (optFuel opts) rs term
  let cat = compileTerm norm
  val <-
    case evalTerm (selectModel (optModel opts)) norm of
      Left err -> Left ("Evaluation error: " <> renderRuntimeError err)
      Right v -> Right v
  pure CLIResult
    { crDoctrine = optDoctrine opts
    , crPresentation = pres
    , crInputTerm = term
    , crNormalized = norm
    , crCatExpr = cat
    , crValue = val
    }

renderResult :: CLIResult -> Text
renderResult res =
  T.unlines
    [ "doctrine: " <> crDoctrine res
    , "sort: " <> renderSort (termSort (crNormalized res))
    , "input: " <> T.pack (show (crInputTerm res))
    , "normalized: " <> T.pack (show (crNormalized res))
    , "cat: " <> T.pack (show (crCatExpr res))
    , "value: " <> T.pack (show (crValue res))
    ]

renderSort :: Sort -> Text
renderSort (Sort (SortName name) _) = name

renderRuntimeError :: RuntimeError -> Text
renderRuntimeError err = T.pack (show err)

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE DOCTRINE TERM [FUEL]"
    , "   or: llang-exe --file FILE --doctrine NAME --term TERM [--fuel N] [--lang comb|lambda] [--model symbolic|nat|string]"
    , "Example: llang-exe examples/monoid.llang Combined \"C.k(C.m(C.e,C.e))\""
    ]

parseSurface :: Lang -> Text -> Either Text CombTerm
parseSurface lang input =
  case lang of
    LangComb -> parseCombTerm input
    LangLambda -> do
      lam <- parseLamTerm input
      pure (toCombTerm lam)

selectModel :: ModelChoice -> Model
selectModel choice =
  case choice of
    ModelSymbolic -> symbolicModel
    ModelNat -> natModel
    ModelString -> stringMonoidModel

qualifyCombTerm :: Presentation -> Text -> CombTerm -> CombTerm
qualifyCombTerm pres ns = go
  where
    ops = sigOps (presSig pres)
    go term =
      case term of
        CVar name -> CVar name
        COp name args ->
          let name' = qualifyName name
          in COp name' (map go args)
    qualifyName name
      | T.isInfixOf "." name = name
      | M.member (OpName name) ops = name
      | otherwise =
          let qualified = ns <> "." <> name
          in if M.member (OpName qualified) ops then qualified else name
