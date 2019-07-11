module Main where

import qualified Data.Text.IO as TIO
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import System.Environment (getArgs)
import System.IO (stderr)
import qualified System.Console.Terminal.Size as Terminal
import Titan
import Titan.Prelude
import Titan.Std

main :: IO ()
main = do
  w <- Terminal.size
  let pageWidth = maybe Unbounded (\w -> AvailablePerLine (Terminal.width w) 1.0) w
  let layout = layoutSmart $ LayoutOptions pageWidth

  stdFiles <- stdFiles
  argFiles <- argFiles

  case foldM analyze emptyGlobal (stdFiles ++ argFiles) of
    Right g ->
      forM_ (dump g) $ \decl -> TIO.putStrLn $ renderStrict $ layout $ prettyBlock 0 decl
    Left e ->
      TIO.hPutStrLn stderr $ renderStrict $ layout $ pretty e

analyze :: Global -> (FilePath, Text) -> Either Error Global
analyze global (path, code) = ti =<< ki =<< resolve =<< bind global =<< parse path code

argFiles :: IO [(FilePath, Text)]
argFiles = do
  paths <- getArgs
  forM paths $ \path -> do
    contents <- TIO.readFile path
    return (path, contents)
