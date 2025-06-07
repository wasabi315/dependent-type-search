-- Adopted from elaboration-zoo

module TypeSearch.Parser
  ( parseModule,
    parseRaw,
    ParserError,
  )
where

import Control.Applicative hiding (many, some)
import Control.Monad
import Data.Char
import Data.Foldable
import Data.Text qualified as T
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L
import TypeSearch.Common
import TypeSearch.Raw

--------------------------------------------------------------------------------

type Parser = Parsec Void T.Text

type ParserError = ParseErrorBundle T.Text Void

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

withPos :: Parser Raw -> Parser Raw
withPos ptm = do
  pos <- getSourcePos
  ptm >>= \case
    t@RPos {} -> pure t
    t -> pure (RPos t pos)

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: T.Text -> Parser T.Text
symbol s = lexeme (C.string s)

char :: Char -> Parser Char
char c = lexeme (C.char c)

decimal :: Parser Int
decimal = lexeme L.decimal

parens :: Parser a -> Parser a
parens p = char '(' *> p <* char ')'

brackets :: Parser a -> Parser a
brackets p = char '[' *> p <* char ']'

pArrow :: Parser T.Text
pArrow = symbol "→" <|> symbol "->"

pProd :: Parser Char
pProd = char '*' <|> char '×'

pBind :: Parser Name
pBind = pName <|> (Name <$> symbol "_")

keyword :: T.Text -> Bool
keyword x =
  x == "module"
    || x == "where"
    || x == "import"
    || x == "let"
    || x == "λ"
    || x == "Type"
    || x == "Unit"
    || x == "tt"
    || x == "Nat"
    || x == "zero"
    || x == "suc"
    || x == "natElim"
    || x == "Eq"
    || x == "refl"
    || x == "eqElim"

pIdent :: Parser T.Text
pIdent = try do
  x <- C.letterChar
  xs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '\'' || c == '-')
  let xs' = T.cons x xs
  guard (not (keyword xs'))
  xs' <$ ws

pModuleName :: Parser ModuleName
pModuleName = ModuleName <$> pIdent

pName :: Parser Name
pName = Name <$> pIdent

pQName :: Parser QName
pQName = do
  x <- pIdent
  y <- optional (try (char '.' *> pIdent))
  pure $ case y of
    Nothing -> Unqual (Name x)
    Just z -> Qual (ModuleName x) (Name z)

pGenVar :: Parser Name
pGenVar = do
  _ <- char '$'
  v <- pIdent
  pure $ Name (T.cons '$' v)

pMeta :: Parser Name
pMeta = do
  _ <- char '?'
  v <- pIdent
  pure $ Name (T.cons '?' v)

pKeyword :: T.Text -> Parser ()
pKeyword kw = do
  _ <- C.string kw
  (takeWhileP Nothing (\c -> isAlphaNum c || c == '\'') *> empty) <|> ws

pAtom :: Parser Raw
pAtom =
  withPos
    ( (RVar <$> pQName)
        <|> (RGenVar <$> pGenVar)
        <|> (RMetaApp . Src <$> pMeta <*> option [] (brackets (pAbsPi `sepBy` char ',')))
        <|> (RType <$ pKeyword "Type")
        <|> (RUnit <$ pKeyword "Unit")
        <|> (RTT <$ pKeyword "tt")
        <|> (RNat <$ pKeyword "Nat")
        <|> (RZero <$ pKeyword "zero")
        <|> (RSuc <$ pKeyword "suc")
        <|> (RNatElim <$ pKeyword "natElim")
        <|> (REq <$ pKeyword "Eq")
        <|> (RRefl <$ pKeyword "refl")
        <|> (REqElim <$ pKeyword "eqElim")
        <|> (rnatLit <$> decimal)
    )
    <|> parens pRaw

goProj :: Raw -> Parser Raw
goProj t =
  ( char '.'
      *> ( ((char '₁' <|> char '1') *> goProj (RFst t))
             <|> ((char '₂' <|> char '2') *> goProj (RSnd t))
         )
  )
    <|> pure t

pProjExp :: Parser Raw
pProjExp = goProj =<< pAtom

pApp :: Parser Raw
pApp = do
  h <- pProjExp
  args <- many pProjExp
  pure $ foldl' RApp h args

pSigmaExp :: Parser Raw
pSigmaExp = do
  optional (try (char '(' *> pName <* char ':')) >>= \case
    Nothing -> do
      t <- pApp
      (RProd t <$> (pProd *> pSigmaExp)) <|> pure t
    Just x -> do
      a <- pRaw
      _ <- char ')'
      _ <- pProd
      b <- pSigmaExp
      pure $ RSigma x a b

pAbs :: Parser Raw
pAbs = do
  _ <- char 'λ' <|> char '\\'
  xs <- some pBind
  _ <- pArrow
  t <- pAbsPi
  pure $ foldr RAbs t xs

pPiBinder :: Parser ([Name], Raw)
pPiBinder = parens $ (,) <$> some pName <*> (char ':' *> pRaw)

pPiExp :: Parser Raw
pPiExp = do
  optional (try (some pPiBinder)) >>= \case
    Nothing -> do
      t <- pSigmaExp
      (pArrow *> (RArr t <$> pPiExp)) <|> pure t
    Just bs -> case bs of
      [([x], a)] ->
        (RPi x a <$> (pArrow *> pPiExp))
          <|> ( do
                  dom <- RSigma x a <$> (pProd *> pSigmaExp)
                  (RArr dom <$> (pArrow *> pPiExp)) <|> pure dom
              )
      dom -> do
        _ <- pArrow
        b <- pPiExp
        pure $! foldr' (\(xs, a) t -> foldr' (\x -> RPi x a) t xs) b dom

pAbsPi :: Parser Raw
pAbsPi = withPos (pAbs <|> pPiExp)

pRaw :: Parser Raw
pRaw = withPos do
  t <- pAbsPi
  (RPair t <$> (char ',' *> pRaw)) <|> pure t

pLet :: Parser Decl
pLet = do
  pos <- getSourcePos
  pKeyword "let"
  x <- pName
  _ <- char ':'
  ann <- pRaw
  _ <- char '='
  t <- pRaw
  pure $ DLet pos x ann t

pModule :: Parser Module
pModule = do
  _ <- pKeyword "module"
  m <- pModuleName
  _ <- pKeyword "where"
  imports <- many $ pKeyword "import" *> pModuleName
  decls <- many pLet
  pure $ Module m imports decls

parseModule :: FilePath -> T.Text -> Either ParserError Module
parseModule fname src = parse (ws *> pModule <* eof) fname src

parseRaw :: FilePath -> T.Text -> Either ParserError Raw
parseRaw fname src = parse (ws *> pRaw <* eof) fname src
