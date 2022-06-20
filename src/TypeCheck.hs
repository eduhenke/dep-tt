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
  traceM ("Checking (" ++ show tm ++ ") : " ++ show ty)
  -- Whenever we call checkType we should call it with a term that has already
  -- been reduced to normal form. This will allow rule c-lam to match against
  -- a literal function type.
  nf <- whnf ty
  traceM ("Checking (" ++ show tm ++ ") : " ++ show ty ++ ". TyNF: " ++ show nf)
  ty' <- tcTerm tm (Just nf)
  traceM ("Checked (" ++ show tm ++ ") : " ++ show ty')

-- | Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = void $ checkType tm Type

tcTerm :: Term -> Maybe Type -> TcMonad Type
tcTerm tm Nothing | trace ("Inferring " ++ show tm) False = undefined
-- tcTerm tm (Just ty) | trace ("Checking (" ++ show tm ++ ") = " ++ show ty) False = undefined
tcTerm (Var x) Nothing = lookupTy x
tcTerm Type Nothing = return Type
tcTerm (Ann tm ty) Nothing = do
  checkType tm ty
  return ty
tcTerm (Pi tyA bnd) Nothing = do
  (x, tyB) <- unbind bnd
  tcType tyA
  extendCtx (TypeSig x tyA) (tcType tyB)
  return Type
tcTerm (App t1 t2) Nothing = do
  ty1 <- inferType t1
  let ensurePi :: Type -> TcMonad (TName, Type, Type)
      ensurePi (Ann a _) = ensurePi a
      ensurePi (Pi tyA bnd) = do
        (x, tyB) <- unbind bnd
        return (x, tyA, tyB)
      ensurePi ty = err ["Expected a function type, but found ", show ty]
  nf1 <- whnf ty1
  (x, tyA, tyB) <- ensurePi nf1
  checkType (unArg t2) tyA
  return $ subst x (unArg t2) tyB
tcTerm (TyEq a b) Nothing = do
  tyA <- inferType a
  checkType b tyA
  return Type
tcTerm (Lam bnd) (Just ty@(Pi tyA bnd')) = do
  tcType tyA
  -- warning: you can't use unbind two times in a row here,
  -- because the variables in the type part and the term part won't coincide then
  (x, body, _, tyB) <- Unbound.unbind2Plus bnd bnd'
  extendCtx (TypeSig x tyA) (checkType body tyB)
  return ty
tcTerm (Lam _) (Just nf) = err ["Lambda expression should have a function type, not ", show nf]
tcTerm Refl (Just ty@(TyEq a b)) = do
  a `equate` b
  return ty
tcTerm Refl (Just ty) = err ["Refl must be annotated with a equality type, but was annotated with: ", show ty]
tcTerm (Subst a b) (Just ty) = do
  tyProof <- inferType b
  let ensureTyEq :: Type -> TcMonad (Type, Type)
      ensureTyEq ty = do
        nf <- whnf ty
        case nf of
          TyEq m n -> return (m, n)
          _ -> err ["Expected an equality type, but found ", show ty]
  (m, n) <- ensureTyEq tyProof
  eqDecl <- def m n
  proofDecl <- def b Refl
  extendCtxs (eqDecl ++ proofDecl) $ checkType a ty
  return ty
tcTerm tm (Just ty) = do
  ty' <- inferType tm
  ty `equate` ty'
  return ty'
tcTerm tm Nothing = err ["Must have a type annotation to check ", show tm]

tcModule :: Module -> TcMonad Module
tcModule m = do
  decls <- foldr tcDecl (return []) (reverse $ declarations m)
  pure $ Module {declarations = decls}
  where
    tcDecl :: Decl -> TcMonad [Decl] -> TcMonad [Decl]
    tcDecl decl _ | trace ("tcDecl: " ++ show decl) False = undefined
    tcDecl decl@(Def name tm) mdecls = do
      decls <- mdecls
      traceM ("tcDecl: " ++ show decl ++ ", decls_ctx: " ++ show decls)
      extendCtxs decls $ do
        maybeTy <- lookupTyMaybe name
        case maybeTy of
          Nothing -> do
            ty <- inferType tm
            pure $ Def name tm : TypeSig name ty : decls
          Just ty -> do
            checkType tm ty
            pure $ Def name tm : decls
    tcDecl decl@(TypeSig name ty) mdecls = do
      decls <- mdecls
      traceM ("tcDecl: " ++ show decl ++ ", decls_ctx: " ++ show decls)
      extendCtxs decls $ tcType ty
      pure $ decl : decls

-- helpers

-- Create a Def if either side normalizes to a single variable
def :: Term -> Term -> TcMonad [Decl]
def t1 t2 = do
  nf1 <- whnf t1
  nf2 <- whnf t2
  case (nf1, nf2) of
    (Var x, _) -> return [Def x nf2]
    (_, Var x) -> return [Def x nf1]
    _ -> return []
