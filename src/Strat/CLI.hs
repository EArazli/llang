{-# LANGUAGE OverloadedStrings #-}
module Strat.CLI
  ( CLIOptions(..)
  , CLIResult(..)
  , parseArgs
  , runCLI
  , runPipelineText
  , renderResult
  ) where

import Strat.Kernel.DSL.Elab (loadDoctrines)
import Strat.Kernel.DoctrineExpr (elabDocExpr)
import Strat.Kernel.RewriteSystem (RewritePolicy(..), compileRewriteSystem)
import Strat.Kernel.Rewrite (normalize)
import Strat.Kernel.Presentation (Presentation)
import Strat.Kernel.Syntax (OpName(..), Sort(..), SortName(..), Term, termSort)
import Strat.Surface
import Strat.Surface.Combinator.Parse (parseCombTerm)
import Strat.Backend (Model(..), Value(..), SortValue(..), RuntimeError(..), evalTerm)
import Strat.Backend.Concat (CatExpr(..), compileTerm)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map.Strict as M


data CLIOptions = CLIOptions
  { optFile     :: FilePath
  , optDoctrine :: Text
  , optTerm     :: Text
  , optFuel     :: Int
  , optPolicy   :: RewritePolicy
  }
  deriving (Eq, Show)

data CLIResult = CLIResult
  { crDoctrine    :: Text
  , crPresentation :: Presentation
  , crInputTerm   :: Term
  , crNormalized  :: Term
  , crCatExpr     :: CatExpr
  , crValue       :: Value
  }
  deriving (Eq, Show)

parseArgs :: [String] -> Either Text CLIOptions
parseArgs args =
  case args of
    ["--help"] -> Left usage
    ["-h"] -> Left usage
    [file, doctrine, term] ->
      Right CLIOptions
        { optFile = file
        , optDoctrine = T.pack doctrine
        , optTerm = T.pack term
        , optFuel = 5
        , optPolicy = UseOnlyComputationalLR
        }
    [file, doctrine, term, fuelStr] ->
      case reads fuelStr of
        [(fuel, "")] ->
          Right CLIOptions
            { optFile = file
            , optDoctrine = T.pack doctrine
            , optTerm = T.pack term
            , optFuel = fuel
            , optPolicy = UseOnlyComputationalLR
            }
        _ -> Left ("Invalid fuel: " <> T.pack fuelStr)
    _ -> Left usage

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
  comb <- parseCombTerm (optTerm opts)
  term <-
    case elaborate (defaultInstance pres) comb of
      Left err -> Left ("Elaboration error: " <> T.pack (show err))
      Right t -> Right t
  let norm = normalize (optFuel opts) rs term
  let cat = compileTerm norm
  val <-
    case evalTerm symbolicModel norm of
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

symbolicModel :: Model
symbolicModel =
  Model
    { interpOp = \op args ->
        if null args
          then Right (VAtom (renderOp op))
          else Right (VList (VAtom (renderOp op) : args))
    , interpSort = \s -> Right (SortValue (renderSort s))
    }

renderOp :: OpName -> Text
renderOp (OpName t) = t

renderSort :: Sort -> Text
renderSort (Sort (SortName name) _) = name

renderRuntimeError :: RuntimeError -> Text
renderRuntimeError err = T.pack (show err)

usage :: Text
usage =
  T.unlines
    [ "Usage: llang-exe FILE DOCTRINE TERM [FUEL]"
    , "Example: llang-exe examples/monoid.llang Combined \"C.k(C.m(C.e,C.e))\""
    ]
