module Main where

import Lib
import Syntax
import System.IO (putStrLn)
import Unbound.Generics.LocallyNameless (bind, makeName)

main :: IO ()
main = do
  let x = makeName "x" 0
      y = makeName "y" 0
      f = Ann (Lam $ bind x $ Lam $ bind y $ Var y) (Pi Type $ bind x $ Pi (Var x) $ bind y $ Var y)
  result <- compile f
  case result of
    Left err -> print err
    Right term -> putStrLn $ "Successfully type checked! resulting term: " ++ show term
