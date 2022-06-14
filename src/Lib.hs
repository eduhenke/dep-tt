module Lib (var, bind, typeCheck) where

import Environment
import Syntax
import qualified Unbound.Generics.LocallyNameless as Unbound

var :: String -> TName
var = Unbound.string2Name

bind :: TName -> Term -> Unbound.Bind TName Term
bind = Unbound.bind

typeCheck :: Term -> IO (Either Err Type)
typeCheck term = runTcMonad emptyEnv $ inferType term
