import Data.Either (isRight)
import Lib
import Syntax
import Test.HUnit
import Unbound.Generics.LocallyNameless (aeq)

x = var "x"

y = var "y"

z = var "z"

f = var "f"

a = var "a"

b = var "b"

p = var "p"

q = var "q"

c = var "c"

n = var "n"

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

assertTypeChecksModule mod = do
  result <- typeCheckModule mod
  case result of
    Left err -> assertFailure $ show err
    Right ty -> assertBool "must typecheck" True

identity =
  let idTy = Pi Type $ bind x $ Pi (Var x) $ bind y $ Var x
      idFn = Ann (Lam $ bind x $ Lam $ bind y $ Var y) idTy
   in TestCase $ assertTypeChecksTo idFn idTy

boolName = var "bool"

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
and' =
  Ann
    (Lam $ bind p $ Lam $ bind q $ Pi Type $ bind c $ Pi (Pi (Var p) $ bind u $ Pi (Var q) $ bind u $ Var c) $ bind u $ Var c)
    (Pi Type $ bind u $ Pi Type $ bind u Type)

bool =
  TestCase $ do
    assertTypeChecks boolTy
    assertTypeChecks true
    assertTypeChecks false
    assertTypeChecks cond
    assertTypeChecks and'

andPQ = App (App and' (Var p)) (Var q)

andQP = App (App and' (Var q)) (Var p)

-- conj : (p: Type) → (q:Type) → p → q → and p q
-- conj = λp.λq. λx.λy. λc. λf. f x y
conj =
  Ann
    (Lam $ bind p $ Lam $ bind q $ Lam $ bind x $ Lam $ bind y $ Lam $ bind c $ Lam $ bind f $ App (App (Var f) (Var x)) (Var y))
    (Pi Type $ bind p $ Pi Type $ bind q $ Pi (Var p) $ bind u $ Pi (Var q) $ bind u $ andPQ)

logicalConjunction =
  TestCase $ do
    assertTypeChecks conj

-- proj1 : (p: Type) → (q:Type) → and p q → p
-- proj1 = λp. λq. λa. a p (λx.λy.x)
proj1 =
  Ann
    (Lam $ bind p $ Lam $ bind q $ Lam $ bind a $ App (App (Var a) (Var p)) $ Lam $ bind x $ Lam $ bind y $ Var x)
    (Pi Type $ bind p $ Pi Type $ bind q $ Pi andPQ $ bind u $ Var p)

-- proj2 : (p: Type) → (q:Type) → and p q → q
-- proj2 = λp. λq. λa. a q (λx.λy.y)
proj2 =
  Ann
    (Lam $ bind p $ Lam $ bind q $ Lam $ bind a $ App (App (Var a) (Var q)) $ Lam $ bind x $ Lam $ bind y $ Var y)
    (Pi Type $ bind p $ Pi Type $ bind q $ Pi andPQ $ bind u $ Var q)

logicalProjection =
  TestCase $ do
    assertTypeChecks proj1
    assertTypeChecks proj2

-- and_commutes : (p:Type) → (q:Type) → and p q → and q p
-- and_commutes = λp. λq. λa. conj q p (proj2 p q a) (proj1 p q a)
andCommutes =
  Ann
    (Lam $ bind p $ Lam $ bind q $ Lam $ bind a proofBody)
    (Pi Type $ bind p $ Pi Type $ bind q $ Pi andPQ $ bind u andQP)
  where
    conjQP = App (App conj $ Var q) $ Var p -- conj q p
    proj2PQA = App (App (App proj2 $ Var p) $ Var q) $ Var a -- proj2 p q a
    proj1PQA = App (App (App proj1 $ Var p) $ Var q) $ Var a -- proj1 p q a
    proofBody = App (App conjQP proj2PQA) proj1PQA

andCommutesProof =
  TestCase $ do
    assertTypeChecks andCommutes

-- nat : Type
-- nat = (x : Type) -> x -> (x->x) -> x
natName = var "nat"

natTy =
  Ann
    (Pi Type $ bind x $ Pi (Var x) $ bind u $ Pi (Pi (Var x) $ bind u $ Var x) $ bind u $ Var x)
    Type

zf = var "zf"

sf = var "sf"

-- z : nat
-- z = λx. λzf. λsf. zf
natZero =
  Ann
    (Lam $ bind x $ Lam $ bind zf $ Lam $ bind sf $ Var zf)
    (Var natName)

-- s : nat -> nat
-- s = λn. λx. λzf. λsf. sf (n x zf sf)
natSuc =
  Ann
    (Lam $ bind n $ Lam $ bind x $ Lam $ bind zf $ Lam $ bind sf $ App (Var sf) $ App (App (App (Var n) $ (Var x)) $ Var zf) $ Var sf)
    (Var natName)

-- one : nat
-- one = s z

-- plus : nat -> nat -> nat
-- plus = λx. λy. x nat y s

-- one_plus_one_eq_two : ((plus one one) = (s one))
-- one_plus_one_eq_two = refl

-- -- and_commutes : (p:Type) → (q:Type) → and p q → and q p
-- -- and_commutes = λp. λq. λa. conj q p (proj2 p q a) (proj1 p q a)
-- andCommutes =
--   Ann
--     (Lam $ bind p $ Lam $ bind q $ Lam $ bind a proofBody)
--     (Pi Type $ bind p $ Pi Type $ bind q $ Pi andPQ $ bind u andQP)
--   where
--     conjQP = App (App conj $ Var q) $ Var p -- conj q p
--     proj2PQA = App (App (App proj2 $ Var p) $ Var q) $ Var a -- proj2 p q a
--     proj1PQA = App (App (App proj1 $ Var p) $ Var q) $ Var a -- proj1 p q a
--     proofBody = App (App conjQP (proj2PQA)) (proj1PQA)

-- andCommutesProof =
--   TestCase $ do
--     assertTypeChecksModule andCommutes

tests = TestList [identity, bool, logicalConjunction, logicalProjection, andCommutesProof]

main = runTestTT tests