module Lib where

import Control.Monad.Except
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Environment
import Parser (parse)
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

compile :: String -> ExceptT String IO Term
compile fileName = do
  content <- liftIO $ readFile fileName
  liftIO $ putStrLn $ "parsing " ++ fileName ++ "..."
  parsed <- liftEither $ parse fileName content
  liftIO $ print parsed
  -- val <- v `exitWith` putParseError
  liftIO $ putStrLn "type checking..."
  ty' <- liftIO $ typeCheck parsed
  liftEither ty'
