module Main where

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

analyze :: Global -> (String, String) -> Either Error Global
analyze global (path, code) = ti =<< ki =<< resolve =<< bind global =<< parse path code

argFiles :: IO [(String, String)]
argFiles = do
  paths <- getArgs
  forM paths $ \path -> do
    contents <- readFile path
    return (path, contents)
