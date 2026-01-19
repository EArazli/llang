{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Loader
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Frontend.Run (runFile)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.FilePath ((</>))
import System.Directory (createDirectoryIfMissing, removePathForcibly, getTemporaryDirectory)
import System.IO.Error (catchIOError)


tests :: TestTree
tests =
  testGroup
    "Frontend.Loader"
    [ testCase "diamond imports" testDiamondImports
    ]


testDiamondImports :: Assertion
testDiamondImports = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "llang-loader-test"
  cleanup dir
  createDirectoryIfMissing True dir
  let aFile = dir </> "A.llang"
  let bFile = dir </> "B.llang"
  let mainFile = dir </> "Main.llang"
  TIO.writeFile aFile $ T.unlines
    [ "doctrine A where {"
    , "  sort Obj;"
    , "  op a : Obj;"
    , "}"
    ]
  TIO.writeFile bFile $ T.unlines
    [ "import \"./A.llang\";"
    , "doctrine B where {"
    , "  sort Obj;"
    , "  op b : Obj;"
    , "}"
    ]
  TIO.writeFile mainFile $ T.unlines
    [ "import \"./A.llang\";"
    , "import \"./B.llang\";"
    , "syntax S for doctrine A where {"
    , "  allow call;"
    , "  varprefix \"?\";"
    , "}"
    , "model M where {"
    , "  default = symbolic;"
    , "}"
    , "run main where {"
    , "  doctrine A;"
    , "  open A;"
    , "  syntax S;"
    , "  model M;"
    , "  show normalized;"
    , "}"
    , "---"
    , "a"
    ]
  result <- runFile mainFile Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()
  cleanup dir
  where
    cleanup path = removePathForcibly path `catchIOError` \_ -> pure ()
