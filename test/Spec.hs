import Data.Either (isRight)
import Lib
import Syntax
import Test.HUnit
import Unbound.Generics.LocallyNameless (aeq)

x = var "x"

y = var "y"

z = var "z"

b = var "b"

p = var "p"

q = var "q"

c = var "c"

-- unused
u = var "_"

assertTypeChecksTo tm expectedTy = do
  result <- typeCheck tm
  case result of
    Left err -> assertFailure $ show err
    Right ty -> assertBool "types must match" $ expectedTy `aeq` ty

assertTypeChecks tm = do
  result <- typeCheck tm
  case result of
    Left err -> assertFailure $ show err
    Right ty -> assertBool "must typecheck" True

identity =
  let idTy = Pi Type $ bind x $ Pi (Var x) $ bind y $ Var x
      idFn = Ann (Lam $ bind x $ Lam $ bind y $ Var y) idTy
   in TestCase $ assertTypeChecksTo idFn idTy

bool =
  let boolName = var "bool"
      -- bool : Type
      -- bool = (x : Type) → x → x → x
      boolTy = Ann (Pi Type $ bind x $ Pi (Var x) $ bind u $ Pi (Var x) $ bind u $ Var x) Type
      -- true : bool
      -- true = λx. λy. λz. y
      true = Ann (Lam $ bind x $ Lam $ bind y $ Lam $ bind z $ Var y) boolTy
      -- false : bool
      -- false = λx. λy. λz. z
      false = Ann (Lam $ bind x $ Lam $ bind y $ Lam $ bind z $ Var z) boolTy
      -- cond : bool → (x:Type) → x → x → x
      -- cond = λb. b
      cond =
        Ann
          (Lam $ bind b $ Var b)
          (Pi boolTy $ bind u $ Pi Type $ bind x $ Pi (Var x) $ bind u $ Pi (Var x) $ bind u $ Var x)
      -- and : Type → Type → Type
      -- and = λp. λq. (c: Type) → (p → q → c) → c
      and =
        Ann
          (Lam $ bind p $ Lam $ bind q $ Pi Type $ bind c $ Pi (Pi (Var p) $ bind u $ Pi (Var q) $ bind u $ Var c) $ bind u $ Var c)
          (Pi Type $ bind u $ Pi Type $ bind u Type)
   in TestCase $ do
        assertTypeChecks boolTy
        assertTypeChecks true
        assertTypeChecks false
        assertTypeChecks cond
        assertTypeChecks and

tests = TestList [identity, bool]

main = runTestTT tests