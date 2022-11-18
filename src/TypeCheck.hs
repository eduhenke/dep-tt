module TypeCheck where

import Control.Monad
import Control.Monad (sequence_)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader (local), ReaderT, asks, runReaderT)
import Data.List
import Debug.Trace
import Environment
import Equality (equate, unify, whnf)
import Syntax
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

inferType :: Term -> TcMonad Type
inferType t = tcTerm t Nothing

checkType :: Term -> Type -> TcMonad ()
checkType tm ty = do
  -- traceM ("Checking (" ++ show tm ++ ") : " ++ show ty)
  -- Whenever we call checkType we should call it with a term that has already
  -- been reduced to normal form. This will allow rule c-lam to match against
  -- a literal function type.
  nf <- whnf ty
  -- traceM ("Checking (" ++ show tm ++ ") : " ++ show ty ++ ". TyNF: " ++ show nf)
  ty' <- tcTerm tm (Just nf)
  pure ()

-- traceM ("Checked (" ++ show tm ++ ") : " ++ show ty')

-- Make sure that the term is a type (i.e. has type 'Type')
tcType :: Term -> TcMonad ()
tcType tm = void $ checkType tm Type

tcTerm :: Term -> Maybe Type -> TcMonad Type
-- Infer-mode
tcTerm tm Nothing | trace ("Inferring " ++ show tm) False = undefined
tcTerm tm (Just ty) | trace ("Checking (" ++ show tm ++ ") to be " ++ show ty) False = undefined
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
  checkType t2 tyA
  return $ subst x t2 tyB
tcTerm (TyEq a b) Nothing = do
  tyA <- inferType a
  checkType b tyA
  return Type
tcTerm (TCon name defs) Nothing = do
  void $ lookupDataDef name
  return Type
tcTerm (DCon dcname dcargs) Nothing = do
  (tcname, Telescope tele) <- lookupDCon dcname
  tcArgTele dcargs tele
  return $ TCon tcname []
tcTerm tm Nothing = err ["Must have a type annotation to check ", show tm]
-- Check-mode
tcTerm dc@(DCon dcname dcargs) (Just ty@(TCon tcname tcargs)) = do
  (tctele, dcs) <- lookupDataDef tcname
  (dconTcName, dctele) <- lookupDCon dcname
  if dconTcName /= tcname
    then err ["Expected data constructor", show dc, " to be of type", show ty]
    else return ()
  (Telescope dctele') <- substTele tctele tcargs dctele
  traceShowM ("tcTerm DCon, substituted dctele'", dcname, dctele', dcargs)
  tcArgTele dcargs dctele'
  return ty
tcTerm (Case scrut cases) (Just ty) = do
  traceM "inferring scrut"
  scrutTy <- inferType scrut
  traceM "inferred scrut"
  scrut' <- whnf scrut
  traceShowM (scrut, scrutTy, scrut')
  ensureTCon scrutTy

  -- checkMatch :: Match -> TcMonad ()
  let checkMatch (Match bnd) = do
        (pat, body) <- unbind bnd
        traceShowM ("checkMatch", scrut', pat, body, pat2Term pat)
        scrutDecls <- unify [] scrut' (pat2Term pat)
        traceShowM ("scrutDecls", scrutDecls)
        -- creating the new declarations coming from the pattern
        -- Suc x, will generate a new declaration x : Nat
        patDecls <- declarePat pat scrutTy
        traceShowM ("decls", scrutDecls, patDecls)
        extendCtxs (scrutDecls ++ patDecls) $ do
          checkType body ty
          return ()
        return ()
  mapM_ checkMatch cases
  return ty
  where
    ensureTCon :: Type -> TcMonad (TCName, [Term])
    ensureTCon (TCon tcname params) = return (tcname, params)
    ensureTCon scrutTy = err ["Expected case scrutinee to have type", show ty, "but found", show scrutTy]

    declarePat :: Pattern -> Type -> TcMonad [Decl]
    declarePat pat ty | trace ("declarePat: " ++ show pat ++ ", ty: " ++ show ty) False = undefined
    declarePat (PatCon dc pats) ty = do
      (tc, params) <- ensureTCon ty
      (Telescope tctele, _) <- lookupDataDef tc
      (_, Telescope dctele) <- lookupDCon dc -- here's the problem
      (Telescope tele) <- substTele (Telescope tctele) params (Telescope dctele)
      traceShowM ("declarePat", tc, dc, tele)
      declarePats dc pats tele
    declarePat (PatVar x) ty = return [TypeSig x ty]

    declarePats :: DCName -> [Pattern] -> [Decl] -> TcMonad [Decl]
    declarePats dc (pat : pats) (TypeSig x ty : tele) = do
      ds1 <- declarePat pat ty
      let tm = pat2Term pat
      ds2 <- extendCtxs ds1 $ declarePats dc pats (subst x tm tele)
      return (ds1 ++ ds2)
    declarePats dc pats (Def x ty : tele) = do
      let ds1 = [Def x ty]
      ds2 <- extendCtxs ds1 $ declarePats dc pats tele
      return (ds1 ++ ds2)
    declarePats dc [] [] = return []
    declarePats dc [] _ = err ["Not enough patterns in match for data constructor", show dc]
    declarePats dc pats [] = err ["Too many patterns in match for data constructor", show dc]
    declarePats dc _ _ = err ["Invalid telescope", show dc]

    pat2Term :: Pattern -> Term
    pat2Term (PatVar x) = Var x
    pat2Term (PatCon dc pats) = DCon dc (map pat2Term pats)
tcTerm (Lam bnd) (Just ty@(Pi tyA bnd')) = do
  tcType tyA
  -- warning: you can't use unbind two times in a row here,
  -- because the variables in the type part and the term part won't coincide then
  (x, body, _, tyB) <- Unbound.unbind2Plus bnd bnd'
  extendCtx (TypeSig x tyA) (checkType body tyB)
  return ty
tcTerm (Lam _) (Just nf) = err ["Lambda expression should have a function type, not", show nf]
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
  (lhs, rhs) <- ensureTyEq tyProof
  eqDecl <- def lhs rhs
  proofDecl <- def b Refl
  extendCtxs (eqDecl ++ proofDecl) $ checkType a ty
  return ty
tcTerm tm (Just ty) = do
  ty' <- inferType tm
  ty `equate` ty'
  return ty'

tcModule :: Module -> TcMonad Module
tcModule m = do
  decls <- foldr tcDecl (return []) (reverse $ declarations m)
  pure $ Module {declarations = decls}
  where
    tcDecl :: Decl -> TcMonad [Decl] -> TcMonad [Decl]
    tcDecl decl _ | trace ("tcDecl: " ++ show decl) False = undefined
    tcDecl decl@(Def name tm) mdecls = do
      decls <- mdecls
      -- traceM ("tcDecl: " ++ show decl ++ ", decls_ctx: " ++ show decls)
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
      -- traceM ("tcDecl: " ++ show decl ++ ", decls_ctx: " ++ show decls)
      extendCtxs decls $ tcType ty
      pure $ decl : decls
    tcDecl decl@(DataDef name tele def) mdecls = do
      decls <- mdecls
      -- traceM ("tcDecl: " ++ show decl ++ ", decls_ctx: " ++ show decls)
      -- extendCtxs decls $ tcType ty
      pure $ DataDef name tele def : decls

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

tcArgTele :: [Term] -> [Decl] -> TcMonad ()
-- tcArgTele args tele | trace ("tcArgTele: " ++ show args ++ " , " ++ show tele) False = undefined
-- Tele-Sig
tcArgTele (arg : args) (TypeSig n ty : tele) = do
  checkType arg ty
  tele' <- doSubst [(n, arg)] tele
  tcArgTele args tele'
-- Tele-Def
tcArgTele args (Def x ty : tele) = do
  tele' <- doSubst [(x, ty)] tele
  tcArgTele args tele'
tcArgTele [] [] = return ()
tcArgTele [] _ = err ["Missing arguments"]
tcArgTele _ [] = err ["Too many arguments"]
tcArgTele args tele = err ["Invalid telescope", show args, show tele]

-- Propagate the given substitution through the telescope, potentially
-- reworking the constraints
doSubst :: [(TName, Term)] -> [Decl] -> TcMonad [Decl]
-- doSubst ss tele | trace ("doSubst, ss: " ++ show ss ++ ", tele: " ++ show tele) False = undefined
doSubst ss [] = return []
doSubst ss (Def x ty : tele') = do
  let tx' = Unbound.substs ss (Var x)
  let ty' = Unbound.substs ss ty
  decls1 <- unify [] tx' ty'
  decls2 <- extendCtxs decls1 (doSubst ss tele')
  -- traceShowM ("doSubst", ss, x, tx', ty, ty', decls1, decls2)
  return $ decls1 ++ decls2
doSubst ss (TypeSig name ty : tele) = do
  tynf <- whnf (Unbound.substs ss ty)
  tele' <- doSubst ss tele
  return $ TypeSig name tynf : tele'
doSubst args tele =
  err ["Invalid telescope(doSubst)", show args, show tele]

-- given the TCon's telescope
-- a ordered list representing each argument of that telescope
-- and the DCon telescope
-- returns the substituted DCon telescope
substTele :: Telescope -> [Term] -> Telescope -> TcMonad Telescope
substTele (Telescope tctele) args (Telescope dctele) = Telescope <$> doSubst (mkSubst tctele args) dctele
  where
    mkSubst [] [] = []
    mkSubst (TypeSig x _ : tele') (tm : tms) =
      (x, tm) : mkSubst tele' tms
    mkSubst _ _ = error "Internal error: substTele given illegal arguments"

-- Given a particular type and a list of patterns, make
-- sure that the patterns cover all potential cases for that type.
-- If the list of patterns starts with a variable, then it doesn't
-- matter what the type is, the variable is exhaustive. (This code
-- does not report unreachable patterns.)
-- Otherwise, the scrutinee type must be a type constructor, so the
-- code looks up the data constructors for that type and makes sure that
-- there are patterns for each one.
exhaustivityCheck :: Term -> Type -> [Pattern] -> TcMonad ()
exhaustivityCheck scrut ty (PatVar x : _) = return ()
