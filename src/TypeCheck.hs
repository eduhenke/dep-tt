module TypeCheck where

import Control.Monad
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader (local), ReaderT, asks, runReaderT)
import Data.List
import Debug.Trace
import Environment
import Equality (equate, whnf)
import Syntax
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

inferType :: Term -> TcMonad Type
inferType t = tcTerm t Nothing

checkType :: Term -> Type -> TcMonad ()
checkType tm ty = do
  -- Whenever we call checkType we should call it with a term that has already
  -- been reduced to normal form. This will allow rule c-lam to match against
  -- a literal function type.
  nf <- whnf ty
  ty' <- tcTerm tm (Just nf)
  traceM ("Checked " ++ show tm ++ " : " ++ show ty')

-- | Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = void $ checkType tm Type

tcTerm :: Term -> Maybe Type -> TcMonad Type
tcTerm tm Nothing | trace ("Inferring " ++ show tm) False = undefined
tcTerm tm (Just ty) | trace ("Checking (" ++ show tm ++ ") = " ++ show ty) False = undefined
tcTerm (Var x) Nothing = lookupTy x
tcTerm Type Nothing = return Type
tcTerm (Ann tm ty) Nothing = do
  checkType tm ty
  return ty
tcTerm (Pi tyA bnd) Nothing = do
  (x, tyB) <- unbind bnd
  tcType tyA
  extendCtx (x, tyA) (tcType tyB)
  return Type
tcTerm (App t1 t2) Nothing = do
  ty1 <- inferType t1
  let ensurePi :: Type -> TcMonad (TName, Type, Type)
      ensurePi (Ann a _) = ensurePi a
      ensurePi (Pi tyA bnd) = do
        (x, tyB) <- unbind bnd
        return (x, tyA, tyB)
      ensurePi ty = err ["Expected a function type but found ", show ty]
  nf1 <- whnf ty1
  (x, tyA, tyB) <- ensurePi nf1
  checkType (unArg t2) tyA
  return $ subst x (unArg t2) tyB
tcTerm (Lam bnd) (Just ty@(Pi tyA bnd')) = do
  tcType tyA
  -- warning: you can't use unbind two times in a row here,
  -- because the variables in the type part and the term part won't coincide then
  (x, body, _, tyB) <- Unbound.unbind2Plus bnd bnd'
  extendCtx (x, tyA) (checkType body tyB)
  return ty
tcTerm (Lam _) (Just nf) = err ["Lambda expression should have a function type, not ", show nf]
tcTerm tm (Just ty) = do
  ty' <- inferType tm
  ty `equate` ty'
  return ty'
tcTerm tm Nothing = err ["Must have a type annotation to check ", show tm]

lookupTyMaybe :: TName -> TcMonad (Maybe Type)
lookupTyMaybe v = do
  ctx <- asks ctx
  traceShowM ctx
  return $ snd <$> find ((== v) . fst) ctx

lookupTy :: TName -> TcMonad Type
lookupTy v = do
  res <- lookupTyMaybe v
  case res of
    Just ty -> return ty
    Nothing -> err ["The variable " ++ show v ++ " was not found."]