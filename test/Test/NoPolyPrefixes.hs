{-# LANGUAGE OverloadedStrings #-}
module Test.NoPolyPrefixes
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Control.Monad (forM, forM_)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesDirectoryExist, getCurrentDirectory, listDirectory)
import System.FilePath ((</>), takeDirectory, takeExtension)
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "NoPolyPrefixes"
    [ testCase "examples and stdlib contain no poly* keywords" testNoPolyPrefixes
    ]


testNoPolyPrefixes :: Assertion
testNoPolyPrefixes = do
  cwd <- getCurrentDirectory
  let examplesRoot = cwd </> "examples"
  let stdlibRoot = cwd </> "stdlib"
  useLocal <- (&&) <$> doesDirectoryExist examplesRoot <*> doesDirectoryExist stdlibRoot
  (examplesDir, stdlibDir) <-
    if useLocal
      then pure (examplesRoot, stdlibRoot)
      else do
        ex <- takeDirectory <$> getDataFileName "examples/planar_monoid.run.llang"
        st <- takeDirectory <$> getDataFileName "stdlib/nat.llang"
        pure (ex, st)
  exampleFiles <- listLlangFiles examplesDir
  stdlibFiles <- listLlangFiles stdlibDir
  let banned =
        [ "polydoctrine"
        , "polymorphism"
        , "polymodel"
        , "polysurface"
        , "polyrun"
        , "polyrun_spec"
        , "polyimplements"
        ]
  forM_ (exampleFiles <> stdlibFiles) $ \path -> do
    contents <- TIO.readFile path
    forM_ banned $ \kw ->
      assertBool (path <> " contains " <> T.unpack kw) (not (kw `T.isInfixOf` contents))

listLlangFiles :: FilePath -> IO [FilePath]
listLlangFiles root = do
  entries <- listDirectory root
  paths <- forM entries $ \name -> do
    let path = root </> name
    isDir <- doesDirectoryExist path
    if isDir
      then listLlangFiles path
      else pure [path | takeExtension path == ".llang"]
  pure (concat paths)
