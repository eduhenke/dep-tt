module Syntax where

import Data.Function (on)
import GHC.Generics (Generic, from)
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Name (makeName)
import Unbound.Generics.LocallyNameless.Operations (bind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))

-- Term names for our AST
type TName = Unbound.Name Term

data Term
  = Type -- type of types
  | Var TName -- variables: x
  | Lam (Unbound.Bind TName Term) -- abstractions: λx.a
  | App Term Arg
  | Pi Type (Unbound.Bind TName Type) -- function types: (x : A) -> B
  | Ann Term Type -- "ascription" or "annotated terms": (a: A)
  | TyEq Type Type
  | Refl
  | Subst Term Term
  deriving (Show, Generic)

data Arg = Arg {unArg :: Term}
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

data Decl
  = TypeSig TName Type
  | Def TName Term
  deriving (Show)

data Module = Module
  { declarations :: [Decl]
  }
  deriving (Show)

type Type = Term

instance Unbound.Subst Term Term where
  isvar (Var x) = Just (Unbound.SubstName x)
  isvar _ = Nothing

instance Unbound.Alpha Term where
  aeq' ctx (Ann a _) b = Unbound.aeq' ctx a b
  aeq' ctx a (Ann b _) = Unbound.aeq' ctx a b
  aeq' ctx a b = (Unbound.gaeq ctx `on` from) a b