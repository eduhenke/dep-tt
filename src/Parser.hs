module Parser where

import Control.Monad.Combinators.Expr
import Control.Monad.Identity (void)
-- import Control.Monad.Trans.Class

import Control.Monad.State.Lazy (StateT (runStateT), get, modify)
import Control.Monad.Trans.State.Lazy (StateT)
import Data.Char (isSpace)
import qualified Data.Set as S
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
import Text.Megaparsec.Char (alphaNumChar)

type Parser a = ParsecT Void String (StateT ConstructorNames Unbound.FreshM) a

instance Unbound.Fresh (ParsecT s String (StateT ConstructorNames Unbound.FreshM)) where
  fresh x = pure x

data ConstructorNames = ConstructorNames
  { dconnames :: S.Set String,
    tconnames :: S.Set String
  }
  deriving (Eq)

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
        hasIdentifier <- optional $ choice [some alphaNumChar, string "("]
        -- o' <- getOffset
        -- i' <- getInput
        -- traceM $ "hasIdentifier: " ++ show hasIdentifier ++ " (" ++ show o' ++ "; " ++ show i' ++ ")"
        case hasIdentifier of
          Nothing -> return ()
          Just x -> do
            o' <- getOffset
            -- consume the space if it's a non-value reserved
            if x `elem` reservedNonVals
              then do
                -- traceM $ "setting offset back from " ++ show o' ++ " to " ++ show (o + 1)
                setOffset (o + 1)
                setInput (tail i)
                o' <- getOffset
                -- traceM $ "set offset to: " ++ show o'
                return ()
              else do
                -- traceM $ "setting offset back from " ++ show o' ++ " to " ++ show o
                setOffset o
                setInput i
                o' <- getOffset
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
symbol' = lexeme' . string

reservedNonVals = ["by", "subst", "data", "where", "of"]
reservedVals = ["refl"]
reserved = reservedVals ++ reservedNonVals

identifier :: Parser String
identifier = label "identifier" $ do
  c <- letterChar
  cs <- many $ choice [alphaNumChar, char '_', char '\'']
  let x = c : cs
  if x `elem` reserved
    then fail $ "keyword " ++ show x ++ " cannot be an identifier"
    else return x

tyIdentifier :: Parser String
tyIdentifier = label "type identifier" $ do
  c <- upperChar
  cs <- many $ choice [alphaNumChar, char '_']
  return $ c : cs

parens :: Parser a -> Parser a
parens = between (symbol' "(") (symbol' ")")

braces :: Parser a -> Parser a
braces = between (dbg "open braces" $ symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

binder :: Parser TName
binder = lexeme' $ Unbound.string2Name <$> identifier

variable :: Parser Term
variable = lexeme' (Var <$> binder <?> "variable")

lambdaSymbol = lexeme $ choice [char '\\', char 'λ']

dot = lexeme $ char '.'

arrow = choice [symbol "->", symbol "→"]

colon = lexeme $ char ':'

eqSymbol = symbol "="

lam :: Parser Term
lam = label "lambda" $ do
  lambdaSymbol
  vars <- some $ lexeme binder
  dot
  body <- expr
  return $ foldr mergeLam body vars
  where
    mergeLam :: TName -> Term -> Term
    mergeLam n tm = Lam $ Unbound.bind n tm

type' :: Parser Type
type' = try $ Type <$ symbol "Type"

wildcardName = Unbound.string2Name "_"

piTy :: Parser Type
piTy = do
  (vars, ty) <-
    try $ parens $ do
        vars <- some $ lexeme binder
        colon
        ty <- expr
        return (vars, ty)
  arrow
  let
    mergePi :: TName -> Term -> Term
    mergePi name body = Pi ty $ Unbound.bind name body
  body <- expr
  return $ foldr mergePi body vars

refl :: Parser Term
refl = Refl <$ symbol "refl"

subst :: Parser Term
subst = do
  symbol "subst"
  a <- expr
  symbol "by"
  b <- expr
  return $ Subst a b

dconname :: Parser DCName
dconname = try $ dbg "dconname" $ do
  n <- identifier
  dcnames <- get
  if not $ S.member n (dconnames dcnames)
    then fail "no data constructor with that name"
    else pure n

dcon :: Parser Term
dcon = do
  n <- dconname
  args <- try $ many $ do
    void $ dbg "dcon space" hspace1
    nonApp
  let args' = map Arg args
  pure $ DCon n args'

tconname :: Parser DCName
tconname = try $ dbg "tconname" $ do
  n <- identifier
  tcnames <- get
  if not $ S.member n (tconnames tcnames)
    then fail "no type constructor with that name"
    else pure n

tcon :: Parser Type
tcon = lexeme' $ do
  n <- tconname
  -- args <- dbg "tconargs" $ many $ try $ do
  --   void $ dbg "tcon space" hspace1
  --   nonApp
  -- let args' = map Arg args
  pure $ TCon n []

peanoNat :: Parser Term
peanoNat = lexeme' $ encode <$> dbg "decimal" L.decimal
  where
    encode :: Int -> Term
    encode 0 = DCon "Zero" []
    encode n = DCon "Succ" [Arg $ encode (n-1)]

nonApp :: Parser Term
nonApp =
  dbg "nonApp" $
    choice
      [ dbg "nat" peanoNat,
        dbg "lam" lam,
        dbg "piTy" piTy,
        dbg "case" $ try caseExpr,
        dbg "subst" $ try subst,
        dbg "type" type',
        dbg "refl" $ try refl,
        dbg "dcon" $ try dcon,
        dbg "tcon" $ try tcon,
        dbg "var" $ try variable,
        parens $ dbg "parens" expr
      ]

expr :: Parser Term
expr = dbg "expr" $
  makeExprParser
    nonApp
    [ [InfixR eqTy]
    , [InfixL app]
    , [InfixR annotation]
    , [InfixR wildcardPiTy]]
  where
    app = appFn <$ dbg "app space" (try hspace1)
    appFn :: Term -> Term -> Term
    appFn (TCon c args) t2 = TCon c $ args ++ [Arg t2]
    appFn t1 t2 = App t1 (Arg t2)
    annotation = Ann <$ colon
    wildcardPiTy =
      (\varName t1 t2 -> Pi t1 $ Unbound.bind varName t2)
        <$> (arrow *> Unbound.fresh wildcardName)
    eqTy = TyEq <$ eqSymbol

module' :: Parser Module
module' = do
  symbol "" -- consume initial space/comments
  decls <- many $ lexeme $ parseDecl
  return $ Module {declarations = decls}
  where
    typeSig = dbg "typeSig" $
      try $ do
        name <- binder
        colon
        TypeSig name <$> expr
    def = dbg "def" $
      try $ do
        name <- binder
        eqSymbol
        Def name <$> expr
    dataDef = dbg "dataDef" $
      try $ do
        dbg "data" $ symbol "data"
        name <- dbg "tyIdent" $ lexeme $ tyIdentifier
        dbg "colon" colon
        lexeme type'
        dbg "where" $ symbol "where"
        -- adding cnames before the braces so we can do recursive types
        modify (\cnames -> cnames {tconnames = S.insert name (tconnames cnames)})
        constructorDefs <- braces body
        return $ Data name constructorDefs
      where
        body = lexeme $ sepBy dataConstructor (symbol ",")
        dataConstructor = dbg "datacons" $ do
          name <- lexeme tyIdentifier
          modify (\cnames -> cnames {dconnames = S.insert name (dconnames cnames)})
          tele <- option (Telescope []) (dbg "of-rest" $ symbol "of" >> telescope)
          return $ ConstructorDef name tele
    parseDecl = choice [typeSig, def, dataDef]

telescope :: Parser Telescope
telescope = Telescope <$> many telebinding
  where
    annot = dbg "tele-annot" $ do
      (x, ty) <-
        try ((,) <$> binder <*> (colon >> expr))
          <|> ((,) <$> (Unbound.fresh wildcardName) <*> expr)
      return (TypeSig x ty)

    equal = dbg "tele-equal" $ do
      v <- binder
      eqSymbol
      Def v <$> expr

    telebinding :: Parser Decl
    telebinding =
      dbg
        "telebinding"
        ( lexeme
            ( parens annot
                <|> brackets equal
            )
            <?> "binding"
        )


caseExpr :: Parser Term
caseExpr = do
  dbg "case keyword" $ symbol "case"
  -- pos <- getPosition
  scrut <- dbg "case scrutinee" expr
  dbg "case of" $ symbol "of"
  cases <- dbg "cases" $ braces $ lexeme $ sepBy match (symbol ",")
  return $ Case scrut cases 
  where
    match :: Parser Match
    match = dbg "match" $ do
      pat <- pattern 
      dbg "match arrow" $ symbol "->"
      -- pos <- getPosition
      body <- dbg "match body" expr
      return $ Match (Unbound.bind pat body)



-- patterns are 
-- p :=  x
--       _
--       K p*
--       (p)
--       (p, p)

-- Note that 'dconstructor' and 'variable' overlaps, annoyingly.
pattern :: Parser Pattern
pattern =  dbg "pat" $ try (PatCon <$> (lexeme dconname) <*> (try $ many argPattern))
       <|> atomicPattern
  where
    argPattern, atomicPattern :: Parser Pattern
    argPattern    =  dbg "argPattern" $ pattern <|> atomicPattern
    atomicPattern = dbg "atomicPattern" $ lexeme $ 
          (PatVar <$> (symbol "_" *> Unbound.fresh wildcardName))
      <|> do
            t <- varOrCon
            case t of
              (Var x) -> return $ PatVar x
              (DCon c []) -> return $ PatCon c []
              (TCon c []) -> fail "expected a data constructor but a type constructor was found"
              _ -> error "internal error in atomicPattern"

-- variables or zero-argument constructors
varOrCon :: Parser Term
varOrCon = dbg "varOrCon" $ do
  i <- identifier
  cnames <- get
  if i `S.member` dconnames cnames
    then return (DCon i [])
    else if i `S.member` tconnames cnames
      then return (TCon i [])
      else return (Var (Unbound.string2Name i))

parseModule :: String -> String -> Either String Module
parseModule fileName input =
  let parsed = runParserT (module' <* eof) fileName input
      stated = runStateT parsed (ConstructorNames {dconnames = S.empty, tconnames = S.empty})
      (freshed, state) = Unbound.runFreshM stated
   in case freshed of
        Left err -> Left $ errorBundlePretty err
        Right t -> Right t