module Equality where

import Control.Monad (zipWithM, zipWithM_)
import Control.Monad.Except (catchError)
import Control.Monad.Reader (MonadReader (local), ReaderT, asks, runReaderT)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace, traceShow, traceShowM)
import Environment
import Syntax
import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless (Subst (substs), unbind, unbind2)
import qualified Unbound.Generics.LocallyNameless as Unbound

equate :: Term -> Term -> TcMonad ()
-- two terms are equal, if they are alpha-equivalent
-- i.e., by just properly renaming the variables
-- they are the same term
equate t1 t2 | aeq t1 t2 = return ()
equate t1 t2 = do
  nf1 <- whnf t1
  nf2 <- whnf t2
  case (nf1, nf2) of
    (Lam bnd1, Lam bnd2) -> do
      -- get the body of each lambda
      (_, t1, _, t2) <- unbind2Plus bnd1 bnd2
      -- lambdas are equal, if their bodies are equal
      equate t1 t2
    -- application is equal when:
    -- - both functions are equal and
    -- - both args are equal
    (App f1 x1, App f2 x2) -> do
      equate f1 f2
      equate x1 x2
    (Pi ty1 bnd1, Pi ty2 bnd2) -> do
      equate ty1 ty2
      (_, t1, _, t2) <- unbind2Plus bnd1 bnd2
      equate t1 t2
    (Type, Type) -> return ()
    (Var x, Var y) | x == y -> return ()
    (TyEq a b, TyEq c d) -> do
      equate a c
      equate b d
    (Refl, Refl) -> return ()
    (Subst at1 pf1, Subst at2 pf2) -> do
      equate at1 at2
      equate pf1 pf2
    (TCon c1 ts1, TCon c2 ts2)
      | c1 == c2 ->
        zipWithM_ equateArgs [ts1] [ts2]
    (DCon d1 a1, DCon d2 a2) | d1 == d2 -> do
      equateArgs a1 a2
    (Case s1 brs1, Case s2 brs2)
      | length brs1 == length brs2 -> do
        equate s1 s2
        -- require branches to be in the same order
        -- on both expressions
        let matchBr (Match bnd1) (Match bnd2) = do
              mpb <- unbind2 bnd1 bnd2
              case mpb of
                Just (p1, a1, p2, a2) | p1 == p2 -> do
                  equate a1 a2
                _ -> err ["Cannot match branches in", show nf1, "and", show nf2]
        zipWithM_ matchBr brs1 brs2
    (_, _) -> err ["Expected", show nf1, "but found", show nf2]

equateArgs :: [Term] -> [Term] -> TcMonad ()
equateArgs (a1 : t1s) (a2 : t2s) = do
  a1 `equate` a2
  equateArgs t1s t2s
equateArgs [] [] = return ()
equateArgs a1 a2 =
  err
    [ "Expected",
      show (length a2),
      "but found",
      show (length a1)
    ]

whnf :: Term -> TcMonad Term
-- strangely WHNF-Var has a different implementation
-- than what was provided in the paper
whnf (Var x) = do
  maybeTm <- lookupDefMaybe x
  case maybeTm of
    (Just tm) -> whnf tm
    _ -> pure $ Var x
whnf (App a b) = do
  v <- whnf a
  case v of
    -- WHNF-Lam-Beta
    (Lam bnd) -> do
      (x, a') <- unbind bnd
      whnf $ subst x b a'
    -- WHNF-Lam-Cong
    _ -> return $ App v b
whnf (Ann tm _) = return tm
whnf (Subst tm pf) = do
  pf' <- whnf pf
  case pf' of
    Refl -> whnf tm
    _ -> return (Subst tm pf')
whnf (Case scrut cases) = do
  nf <- whnf scrut
  case nf of
    (DCon d args) -> f cases
      where
        f (Match bnd : cases) =
          ( do
              (pat, body) <- unbind bnd
              ss <- patternMatches nf pat
              whnf $ substs ss body
          )
            `catchError` \_ -> f cases
        f [] =
          err $
            [ "Internal error: couldn't find a matching",
              "branch for",
              show nf,
              "in"
            ]
              ++ map show cases
    _ -> return (Case nf cases)
-- WHNF-Type, WHNF-Lam, WHNF-Var, WHNF-Pi
whnf tm = return tm

-- | Determine whether the pattern matches the argument
-- If so return the appropriate substitution
-- otherwise throws an error
patternMatches :: Term -> Pattern -> TcMonad [(TName, Term)]
patternMatches t (PatVar x) = return [(x, t)]
patternMatches t pat = do
  nf <- whnf t
  case (nf, pat) of
    (DCon d [], PatCon d' pats) | d == d' -> return []
    (DCon d args, PatCon d' pats)
      | d == d' ->
        concat <$> zipWithM patternMatches args pats
    _ -> err ["arg", show nf, "doesn't match pattern", show pat]

-- | 'Unify' the two terms, producing a list of Defs
-- If there is an obvious mismatch, this function produces an error
-- If either term is "ambiguous" just fail instead.
unify :: [TName] -> Term -> Term -> TcMonad [Decl]
unify ns tx ty | traceShow ("unify", ns, tx, ty) False = undefined
unify ns tx ty = do
  txnf <- whnf tx
  tynf <- whnf ty
  if Unbound.aeq txnf tynf
    then return []
    else case (txnf, tynf) of
      (Var y, yty) | y `notElem` ns -> return [Def y yty]
      (yty, Var y) | y `notElem` ns -> return [Def y yty]
      (TyEq a1 a2, TyEq b1 b2) -> unifyArgs [a1, a2] [b1, b2]
      (TCon s1 tms1, TCon s2 tms2)
        | s1 == s2 -> unifyArgs tms1 tms2
      (DCon s1 a1s, DCon s2 a2s)
        | s1 == s2 -> unifyArgs a1s a2s
      (Lam bnd1, Lam bnd2) -> do
        (x, b1, _, b2) <- unbind2Plus bnd1 bnd2
        unify (x : ns) b1 b2
      (Pi tyA1 bnd1, Pi tyA2 bnd2) -> do
        (x, tyB1, _, tyB2) <- unbind2Plus bnd1 bnd2
        ds1 <- unify ns tyA1 tyA2
        ds2 <- unify (x : ns) tyB1 tyB2
        return (ds1 ++ ds2)
      _ ->
        if amb txnf || amb tynf
          then return []
          else err ["Cannot equate", show txnf, "and", show tynf]
  where
    unifyArgs (t1 : a1s) (t2 : a2s) = do
      ds <- unify ns t1 t2
      ds' <- unifyArgs a1s a2s
      return $ ds ++ ds'
    unifyArgs [] [] = return []
    unifyArgs _ _ = err ["internal error (unify)"]

-- | Is a term "ambiguous" when it comes to unification?
-- In general, elimination forms are ambiguous because there are multiple
-- solutions.
amb :: Term -> Bool
amb (App t1 t2) = True
amb (Case _ _) = True
amb _ = False
