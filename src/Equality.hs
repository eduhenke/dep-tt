module Equality where

import Environment
import Syntax
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

equate :: Term -> Term -> TcMonad ()
equate _ _ = return ()

whnf :: Term -> TcMonad Term
whnf (App a b) = do
  v <- whnf a
  case v of
    -- WHNF-Lam-Beta
    (Lam bnd) -> do
      (x, a') <- unbind bnd
      whnf $ subst x (unArg b) a'
    -- WHNF-Lam-Cong
    _ -> return $ App v b
-- WHNF-Type, WHNF-Lam, WHNF-Var, WHNF-Pi
whnf tm = return tm