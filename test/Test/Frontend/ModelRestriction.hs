{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.ModelRestriction
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Frontend.Run (runFile, RunResult(..))
import Strat.Backend (Value(..))
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing, removePathForcibly, getTemporaryDirectory)
import System.IO.Error (catchIOError)

tests :: TestTree
tests =
  testGroup
    "Frontend.ModelRestriction"
    [ testCase "model for super-doctrine restricts via morphism" testModelRestriction
    ]

testModelRestriction :: Assertion
testModelRestriction = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "llang-model-restrict-test"
  cleanup dir
  createDirectoryIfMissing True dir
  let file = dir </> "Main.llang"
  TIO.writeFile file $ T.unlines
    [ "doctrine Category where {"
    , "  sort Obj;"
    , "  op a : Obj;"
    , "  op f : (x:Obj) -> Obj;"
    , "}"
    , "doctrine BoolExt extends Category where {"
    , "  op g : (x:Obj) -> Obj;"
    , "  computational rB : (x:Obj) |- f(?x) -> g(?x);"
    , "}"
    , "doctrine NatExt extends Category where {"
    , "  op h : (x:Obj) -> Obj;"
    , "  computational rN : (x:Obj) |- f(?x) -> h(?x);"
    , "}"
    , "doctrine Both = pushout BoolExt.fromBase NatExt.fromBase;"
    , "syntax S where {"
    , "  allow call;"
    , "  varprefix \"?\";"
    , "}"
    , "model BothModel : Both where {"
    , "  default = symbolic;"
    , "  op Category.f(x) = x;"
    , "}"
    , "run main where {"
    , "  doctrine Category;"
    , "  syntax S;"
    , "  model BothModel;"
    , "  open Category;"
    , "  show value;"
    , "}"
    , "---"
    , "f(a)"
    ]
  result <- runFile file Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrValue out @?= VAtom "Category.a"
  cleanup dir
  where
    cleanup path = removePathForcibly path `catchIOError` \_ -> pure ()
