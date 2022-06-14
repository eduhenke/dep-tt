import Lib
import Syntax
import Test.HUnit
import Unbound.Generics.LocallyNameless (aeq)

identity =
  let x = var "x"
      y = var "y"
      piTy = Pi Type $ bind x $ Pi (Var x) $ bind y $ Var x
      f = Ann (Lam $ bind x $ Lam $ bind y $ Var y) piTy
   in TestCase
        ( do
            result <- typeCheck f
            case result of
              Left err -> assertFailure $ show err
              Right ty -> assertBool "types must match" $ piTy `aeq` ty
        )

tests = TestList [identity]

main = runTestTT tests