module Titan.Std where

import qualified Data.List as List
import System.Directory (listDirectory)
import System.FilePath ((</>), takeExtension)
import Titan.Prelude
import Paths_titan (getDataDir)

stdFiles :: IO [(String, String)]
stdFiles = do
  dataDir <- getDataDir
  let stdDir = dataDir </> "std"
  stdFiles <- listDirectory stdDir
  let titanFiles = filter (\path -> takeExtension path == ".titan") stdFiles
  forM (List.sort titanFiles) $ \titanFile -> do
    contents <- readFile $ stdDir </> titanFile
    return (titanFile, contents)
