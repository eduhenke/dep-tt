module Lib where

import Environment
import Syntax
import Unbound.Generics.LocallyNameless (bind)
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Name (makeName)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

compile :: Term -> IO (Either Err Term)
compile term = runTcMonad emptyEnv $ inferType term
