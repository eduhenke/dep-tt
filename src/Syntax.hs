module Syntax where

import Data.Function (on)
import Data.List (intercalate)
import GHC.Generics (Generic, from)
import qualified Unbound.Generics.LocallyNameless as Unbound
import Unbound.Generics.LocallyNameless.Name (makeName)
import Unbound.Generics.LocallyNameless.Operations (bind)
import Unbound.Generics.LocallyNameless.Subst (Subst (subst))
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

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
  | DCon DCName [Arg]
  | TCon TCName [Arg]
  | Case Term [Match] -- case analysis  `case a of matches`
  deriving (Generic)

instance Show Term where
  show Type = "Type"
  show (Var x) = show x
  show (Lam bnd) = let (x, a) = unsafeUnbind bnd in "(λ" ++ show x ++ ". " ++ show a ++ ")"
  show (App a b) = "(" ++ show a ++ " " ++ show b ++ ")"
  show (Pi ty bnd) = let (x, a) = unsafeUnbind bnd in "(" ++ show x ++ " : " ++ show ty ++ ") -> " ++ show a
  show (Ann tm ty) = show tm ++ " : " ++ show ty
  show (TyEq a b) = show a ++ " = " ++ show b
  show Refl = "refl"
  show (Subst a b) = "(subst " ++ show a ++ " " ++ show b ++ ")"
  show (DCon dcon args) = dcon ++ " " ++ unwords (map show args)
  show (TCon tcon args) = tcon ++ " " ++ unwords (map show args)
  show (Case tm matches) = "case " ++ show tm ++ " of {" ++ intercalate ", " (map show matches) ++ "}"

-- | Argument to a term
data Arg = Arg {unArg :: Term}
  deriving (Generic, Unbound.Alpha, Unbound.Subst Term)

instance Show Arg where
  show (Arg a) = show a

type TCName = String -- type constructor names

type DCName = String -- data constructor names

data Decl
  = TypeSig TName Type
  | Def TName Term
  | Data TCName Telescope [ConstructorDef]
  deriving (Generic, Unbound.Alpha, Unbound.Subst Term)

instance Show Decl where
  show (TypeSig x ty) = show x ++ " : " ++ show ty
  show (Def x tm) = show x ++ " := " ++ show tm
  show (Data tconname (Telescope tele) constrs) = "data " ++ tconname ++ (unwords $ map (\t -> "(" ++ show t ++ ")") tele) ++ " = " ++ show constrs

-- a data constructor has a name and a telescope of arguments
data ConstructorDef = ConstructorDef DCName Telescope
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

newtype Telescope = Telescope [Decl]
  deriving (Show, Generic, Unbound.Alpha, Unbound.Subst Term)

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

-- | A 'Match' represents a case alternative
newtype Match = Match (Unbound.Bind Pattern Term)
  deriving (Generic)
  deriving anyclass (Unbound.Alpha, Unbound.Subst Term)

instance Show Match where
  show (Match bnd) = let (pat, tm) = unsafeUnbind bnd in show pat ++ " -> " ++ show tm

-- | The patterns of case expressions bind all variables
-- in their respective branches.
data Pattern
  = PatCon DCName [Pattern]
  | PatVar TName
  deriving (Eq, Generic, Unbound.Alpha, Unbound.Subst Term)

instance Show Pattern where
  show (PatCon dcon pats) = dcon ++ " " ++ unwords (map show pats)
  show (PatVar x) = show x