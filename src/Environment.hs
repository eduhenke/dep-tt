module Environment where

import Control.Monad
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader (local), ReaderT, asks, runReaderT)
import Data.List
import Debug.Trace
import GHC.IO.Unsafe (unsafePerformIO)
import Syntax
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Operations (unbind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))
import Data.Maybe (fromMaybe)
import Control.Monad (MonadPlus(mplus))

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
lookupTyMaybe v | trace ("lookupTyMaybe: " ++ show v) False = undefined
lookupTyMaybe v = do
  ctx <- asks ctx
  traceShowM ctx
  return $ findTy ctx
  where
    findTy :: [Decl] -> Maybe Type
    findTy ((TypeSig name ty) : ds) | name == v = Just ty
    -- findTy ((Data name defs) : ds) | name == v = Just $ TCon name []
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
  -- traceShowM ctx
  return $ findDef ctx
  where
    findDef :: [Decl] -> Maybe Type
    findDef ((Def name tm) : ds) | name == v = Just tm
    findDef (d : ds) = findDef ds
    findDef [] = Nothing

lookupDataDef :: TCName -> TcMonad [ConstructorDef]
lookupDataDef v = do
  ctx <- asks ctx
  -- traceShowM ctx
  case findDataDef ctx of
    Nothing -> fail "type not found"
    Just defs -> pure defs
  where
    findDataDef :: [Decl] -> Maybe [ConstructorDef]
    findDataDef ((Data name defs) : ds) | name == v = Just defs
    findDataDef (d : ds) = findDataDef ds


lookupDCon :: DCName -> TcMonad (TCName, Telescope)
lookupDCon v = do
  ctx <- asks ctx
  traceShowM ctx
  case findDataDefTele ctx of
    Nothing -> fail ("data constructor " ++ v ++ " not found")
    Just (tcname, tele) -> pure (tcname, tele)
  where
    findDataDefTele :: [Decl] -> Maybe (TCName, Telescope)
    findDataDefTele ((Data name defs) : ds) = (findDCon defs >>= (\d -> pure (name, d))) `mplus` findDataDefTele ds
    findDataDefTele (d : ds) = findDataDefTele ds
    findDataDefTele [] = Nothing

    findDCon :: [ConstructorDef] -> Maybe Telescope
    findDCon [] = Nothing
    findDCon (ConstructorDef dcName tele : defs)
      | dcName == v = Just tele
      | otherwise = findDCon defs
