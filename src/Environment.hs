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

type Err = String

err :: [String] -> TcMonad b
err d = do
  throwError $ unwords d