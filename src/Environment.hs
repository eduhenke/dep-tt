module Environment where

import Control.Monad
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader (local), ReaderT, asks, runReaderT)
import Data.List
import Debug.Trace
import GHC.IO.Unsafe (unsafePerformIO)
import Syntax (TName, Term (..), Type, unArg)
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

type TcMonad = Unbound.FreshMT (ReaderT Env (ExceptT Err IO))

runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = do
  runExceptT $ runReaderT (Unbound.runFreshMT m) env

type Ctx = [(TName, Type)]

data Env = Env {ctx :: Ctx}

emptyEnv :: Env
emptyEnv = Env {ctx = []}

-- | Extend the context with a new binding
extendCtx :: (TName, Type) -> TcMonad a -> TcMonad a
extendCtx d = local (\m@Env {ctx = cs} -> m {ctx = d : cs})

inferType :: Term -> TcMonad Type
inferType t = tcTerm t Nothing

checkType :: Term -> Type -> TcMonad ()
checkType tm (Ann ty _) = checkType tm ty
checkType tm ty = do
  ty' <- tcTerm tm (Just ty)
  traceM ("Checked " ++ show tm ++ " : " ++ show ty')
  pure ()

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
  (x, tyA, tyB) <- ensurePi ty1
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
  if ty `Unbound.aeq` ty'
    then return ty'
    else err ["Types don't match ", show ty, " and ", show ty']
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

data Err = Err String deriving (Show, Eq)

instance Semigroup Err where
  (Err msg1) <> (Err msg2) = Err (msg1 ++ msg2)

instance Monoid Err where
  mempty = Err []
  mappend (Err msg1) (Err msg2) = Err (msg1 ++ msg2)

err :: [String] -> TcMonad b
err d = do
  throwError $ Err $ unwords d