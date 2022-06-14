module Main where

import Lib
import Syntax
import System.IO (putStrLn)

main :: IO ()
main = do
  let x = var "x"
      y = var "y"
      -- (x : Type) -> (y : x) -> x
      idTy = Pi Type $ bind x $ Pi (Var x) $ bind y $ Var x
  result <- typeCheck idTy
  case result of
    Left err -> print err
    Right term -> putStrLn $ "Successfully type checked! resulting term: " ++ show term
