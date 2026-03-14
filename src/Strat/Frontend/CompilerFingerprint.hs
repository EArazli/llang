{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
module Strat.Frontend.CompilerFingerprint
  ( compilerFingerprint
  ) where

import Control.Monad (filterM, forM)
import qualified Data.ByteString as BS
import Data.List (sort)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Version (showVersion)
import Language.Haskell.TH (Loc(loc_filename), location, runIO)
import Language.Haskell.TH.Lib (stringE)
import Language.Haskell.TH.Syntax (addDependentFile)
import Strat.Util.Fingerprint (fingerprintBytes)
import System.Directory
  ( canonicalizePath
  , doesDirectoryExist
  , doesFileExist
  , listDirectory
  )
import System.FilePath ((</>), makeRelative, takeDirectory, takeExtension)
import System.Info (compilerName, compilerVersion)


compilerFingerprint :: Text
compilerFingerprint =
  T.pack
    $( do
         loc <- location
         let modulePath = loc_filename loc
         (files, hashText) <- runIO $ do
           absModulePath <- canonicalizePath modulePath
           let findProjectRoot dir = do
                 let packageYaml = dir </> "package.yaml"
                     cabalFile = dir </> "llang.cabal"
                 hasPackageYaml <- doesFileExist packageYaml
                 hasCabal <- doesFileExist cabalFile
                 if hasPackageYaml || hasCabal
                   then pure dir
                   else
                     let parent = takeDirectory dir
                      in if parent == dir then pure dir else findProjectRoot parent
               collectHaskellFiles dir = do
                 exists <- doesDirectoryExist dir
                 if not exists
                   then pure []
                   else do
                     entries <- sort <$> listDirectory dir
                     fmap concat $
                       forM entries $ \name -> do
                         let path = dir </> name
                         isDir <- doesDirectoryExist path
                         if isDir
                           then collectHaskellFiles path
                           else
                             if takeExtension path == ".hs"
                               then pure [path]
                               else pure []
               compilerStamp =
                 T.intercalate
                   ":"
                   [ "ghc"
                   , T.pack compilerName
                   , T.pack (showVersion compilerVersion)
                   ]
           projectRoot <- findProjectRoot (takeDirectory absModulePath)
           let configFiles =
                 map (projectRoot </>) ["package.yaml", "llang.cabal", "stack.yaml", "stack.yaml.lock"]
           existingConfigFiles <- filterM doesFileExist configFiles
           sourceFiles <- collectHaskellFiles (projectRoot </> "src")
           let files = sort (existingConfigFiles <> sourceFiles)
               filePayload path = do
                 bytes <- BS.readFile path
                 let relPath = makeRelative projectRoot path
                 pure (TE.encodeUtf8 (T.pack relPath) <> "\0" <> bytes <> "\0")
           payloads <- forM files filePayload
           let hashText =
                 fingerprintBytes
                   ( BS.concat
                       ( TE.encodeUtf8 compilerStamp
                           : payloads
                       )
                   )
           pure (files, hashText)
         mapM_ addDependentFile files
         stringE (T.unpack hashText)
       )
