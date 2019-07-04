module Main where

import qualified Data.Text.IO
import System.Environment (getArgs)
import System.IO (stderr, hPutStrLn)
import Titan
import Titan.Prelude
import Titan.Std

main :: IO ()
main = do
  stdFiles <- stdFiles
  argFiles <- argFiles
  case foldM analyze emptyGlobal (stdFiles ++ argFiles) of
    Right g -> mapM_ (putStrLn . pprint) (dump g)
    Left e -> hPutStrLn stderr $ show e

analyze :: Global -> (FilePath, Text) -> Either Error Global
analyze global (path, code) = ti =<< ki =<< resolve =<< bind global =<< parse path code

argFiles :: IO [(FilePath, Text)]
argFiles = do
  paths <- getArgs
  forM paths $ \path -> do
    contents <- Data.Text.IO.readFile path
    return (path, contents)
