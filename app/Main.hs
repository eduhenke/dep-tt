module Main where

import Control.Monad.Except (runExceptT)
import Lib
import Syntax
import System.Environment
import System.IO

main :: IO ()
main = do
  [pathToFile] <- getArgs
  result <- runExceptT $ compile pathToFile
  case result of
    Left err -> putStrLn err
    Right term -> putStrLn $ "Successfully type checked!"
