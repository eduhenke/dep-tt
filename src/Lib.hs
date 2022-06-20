module Lib where

import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Environment
import Parser (parseModule)
import Syntax
import System.Environment (getArgs)
import TypeCheck
import qualified Unbound.Generics.LocallyNameless as Unbound

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
  liftEither m
