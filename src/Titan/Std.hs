module Titan.Std where

import qualified Data.List as List
import qualified Data.Text.IO
import System.Directory (listDirectory)
import System.FilePath ((</>), takeExtension)
import Titan.Prelude
import Paths_titan (getDataDir)

stdFiles :: IO [(FilePath, Text)]
stdFiles = do
  dataDir <- getDataDir
  let stdDir = dataDir </> "std"
  stdFiles <- listDirectory stdDir
  let titanFiles = filter (\path -> takeExtension path == ".titan") stdFiles
  forM (List.sort titanFiles) $ \titanFile -> do
    contents <- Data.Text.IO.readFile $ stdDir </> titanFile
    return (titanFile, contents)
