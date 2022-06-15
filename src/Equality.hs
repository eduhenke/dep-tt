module Equality where

import Environment
import Syntax
import Unbound.Generics.LocallyNameless

equate :: Term -> Term -> TcMonad ()
equate t1 t2 | aeq t1 t2 = return ()
equate t1 t2 = do
  nf1 <- whnf t1
  nf2 <- whnf t2
  case (nf1, nf2) of
    (Lam bnd1, Lam bnd2) -> do
      (_, t1, _, t2) <- unbind2Plus bnd1 bnd2
      equate t1 t2
    (App a1 a2, App b1 b2) -> do
      equate a1 b1
      equate (unArg a2) (unArg b2)
    (Pi ty1 bnd1, Pi ty2 bnd2) -> do
      equate ty1 ty2
      (_, t1, _, t2) <- unbind2Plus bnd1 bnd2
      equate t1 t2
    (Type, Type) -> return ()
    (Var x, Var y) | x == y -> return ()
    (_, _) -> err ["Expected", show nf2, "but found", show nf1]

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
whnf (Ann tm _) = return tm
-- WHNF-Type, WHNF-Lam, WHNF-Var, WHNF-Pi
whnf tm = return tm