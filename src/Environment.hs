module Environment where

import Control.Monad
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader (local), ReaderT, asks, runReaderT)
import Data.List
import Debug.Trace
import GHC.IO.Unsafe (unsafePerformIO)
import Syntax (Decl (..), TName, Term (..), Type, unArg)
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

type TcMonad = Unbound.FreshMT (ReaderT Env (ExceptT Err IO))

runTcMonad :: Env -> TcMonad a -> IO (Either Err a)
runTcMonad env m = do
  runExceptT $ runReaderT (Unbound.runFreshMT m) env

data Env = Env {ctx :: [Decl]}

emptyEnv :: Env
emptyEnv = Env {ctx = []}

-- | Extend the context with a new binding
extendCtx :: Decl -> TcMonad a -> TcMonad a
extendCtx d = local (\m@Env {ctx = cs} -> m {ctx = d : cs})

extendCtxs :: [Decl] -> TcMonad a -> TcMonad a
extendCtxs ds = local (\m@Env {ctx = cs} -> m {ctx = ds ++ cs})

type Err = String

err :: [String] -> TcMonad b
err d = do
  throwError $ unwords d

lookupTyMaybe :: TName -> TcMonad (Maybe Type)
lookupTyMaybe v = do
  ctx <- asks ctx
  traceShowM ctx
  return $ findTy ctx
  where
    findTy :: [Decl] -> Maybe Type
    findTy ((TypeSig name ty) : ds) | name == v = Just ty
    findTy (d : ds) = findTy ds
    findTy [] = Nothing

lookupTy :: TName -> TcMonad Type
lookupTy v = do
  res <- lookupTyMaybe v
  case res of
    Just ty -> return ty
    Nothing -> err ["The variable " ++ show v ++ " was not found."]

lookupDefMaybe :: TName -> TcMonad (Maybe Term)
lookupDefMaybe v = do
  ctx <- asks ctx
  traceShowM ctx
  return $ findDef ctx
  where
    findDef :: [Decl] -> Maybe Type
    findDef ((Def name tm) : ds) | name == v = Just tm
    findDef (d : ds) = findDef ds
    findDef [] = Nothing
