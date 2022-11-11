module Lib where

import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Environment
import Equality
import Parser (parseModule)
import Syntax
import System.Environment (getArgs)
import TypeCheck
import qualified Unbound.Generics.LocallyNameless as Unbound
import Data.Foldable (find)

var :: String -> TName
var = Unbound.string2Name

bind :: TName -> Term -> Unbound.Bind TName Term
bind = Unbound.bind

typeCheck :: Term -> IO (Either Err Type)
typeCheck term = runTcMonad emptyEnv $ inferType term

typeCheckModule :: Module -> IO (Either Err Module)
typeCheckModule m = runTcMonad emptyEnv $ tcModule m

compile :: String -> ExceptT String IO Module
compile fileName = do
  content <- liftIO $ readFile fileName
  liftIO $ putStrLn $ "parsing " ++ fileName ++ "..."
  parsed <- liftEither $ parseModule fileName content
  liftIO $ print parsed
  -- val <- v `exitWith` putParseError
  liftIO $ putStrLn "type checking..."
  m <- liftIO $ typeCheckModule parsed
  liftIO $ putStrLn "type checked"
  -- n <- f (var "x") $ declarations parsed 
  -- k <- whnf n
  -- liftIO $ print $ k
  liftEither m
  where
    f :: TName -> [Decl] -> Maybe Term
    f x (Def y tm : _) | x == y = Just tm
    f x (_ : decls) = f x decls
