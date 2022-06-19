module Parser where

import Control.Monad.Combinators.Expr
import Control.Monad.Identity (void)
-- import Control.Monad.Trans.Class
import Data.Char (isSpace)
import Data.String (String)
import Data.Void (Void)
import Debug.Trace (traceM, traceShowM)
import Syntax
import Text.Megaparsec
import Text.Megaparsec (MonadParsec (lookAhead, notFollowedBy), setInput)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Debug (dbg)
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Unbound.Generics.LocallyNameless as Unbound

type Parser a = ParsecT Void String (Unbound.FreshM) a

instance Unbound.Fresh (ParsecT s String Unbound.FreshM) where
  -- fresh :: Unbound.Name a -> m (Unbound.Name a)
  -- fresh = lift . Unbound.fresh
  -- fresh = lift . Unbound.fresh
  fresh x = pure x

spaceConsumer :: Parser ()
spaceConsumer =
  do
    o <- getOffset
    i <- getInput
    hasSpace <- optional spaceChar
    -- traceM $ "hasSpace: " ++ show hasSpace ++ " (" ++ show o ++ "; " ++ show i ++ ")"
    case hasSpace of
      Nothing -> return ()
      Just _ -> do
        hasIdentifier <- optional letterChar
        -- o' <- getOffset
        -- i' <- getInput
        -- traceM $ "hasIdentifier: " ++ show hasIdentifier ++ " (" ++ show o' ++ "; " ++ show i' ++ ")"
        case hasIdentifier of
          Nothing -> return ()
          Just _ -> do
            -- o' <- getOffset
            -- traceM $ "setting offset back from " ++ show o' ++ " to " ++ show o
            setOffset o
            setInput i
            -- o' <- getOffset
            -- traceM $ "set offset to: " ++ show o'
            return ()

-- space consumer
sc :: Parser ()
sc =
  L.space
    space1
    (L.skipLineComment "//")
    (L.skipBlockComment "/*" "*/")

-- consumes all available space
lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

-- consumes all available space UNTIL one letter is ahead
lexeme' :: Parser a -> Parser a
lexeme' p = p <* spaceConsumer

symbol :: String -> Parser String
symbol = L.symbol sc

symbol' :: String -> Parser String
symbol' = lexeme . string

identifier :: Parser String
identifier = some letterChar <?> "identifier"

parens :: Parser a -> Parser a
parens = between (symbol' "(") (symbol' ")")

binder :: Parser TName
binder = lexeme' $ Unbound.string2Name <$> identifier

variable :: Parser Term
variable = lexeme' (Var <$> binder <?> "variable")

lambdaSymbol = lexeme $ choice [char '\\', char 'λ']

dot = lexeme $ char '.'

arrow = choice [symbol "->", symbol "→"]

colon = lexeme $ char ':'

lam :: Parser Term
lam = label "lambda" $ do
  lambdaSymbol
  varName <- binder
  dot
  Lam . Unbound.bind varName <$> expr

type' :: Parser Term
type' = try $ Type <$ symbol "Type"

wildcardName = Unbound.string2Name "_"

piTy :: Parser Term
piTy = do
  (varName, ty) <-
    choice
      [ try $
          parens $ do
            varName <- binder
            colon
            ty <- expr
            return (varName, ty)
      ]
  arrow
  Pi ty . Unbound.bind varName <$> expr

nonApp :: Parser Term
nonApp =
  choice
    [ type',
      lam,
      piTy,
      try variable,
      parens expr
    ]

expr :: Parser Term
expr =
  makeExprParser
    nonApp
    [[InfixL app], [InfixR annotation], [InfixR wildcardPiTy]]
  where
    app = (\t1 t2 -> App t1 (Arg t2)) <$ space1
    annotation = Ann <$ colon
    wildcardPiTy =
      (\varName t1 t2 -> Pi t1 $ Unbound.bind varName t2)
        <$> (arrow *> Unbound.fresh wildcardName)

parse :: String -> String -> Either String Term
parse fileName input = case Unbound.runFreshM $ runParserT (expr <* eof) fileName input of
  Left err -> Left $ errorBundlePretty err
  Right t -> Right t