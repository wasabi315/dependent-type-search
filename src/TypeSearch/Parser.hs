-- Adopted from elaboration-zoo

module TypeSearch.Parser
  ( parseRaw,
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
import TypeSearch.Common hiding (QName)
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

pArrow :: Parser T.Text
pArrow = symbol "→" <|> symbol "->"

pProd :: Parser Char
pProd = char '×'

pBind :: Parser Name
pBind = pName <|> (Name <$> symbol "_")

keyword :: T.Text -> Bool
keyword x =
  x == "λ"
    || x == "U"
    || x == ":"
    || x == "->"
    || x == "→"
    || x == "×"

alternating1 :: Parser a -> Parser a -> Parser [a]
alternating1 p q = do
  let pq = (:) <$> p <*> (qp <|> pure [])
      qp = (:) <$> q <*> (pq <|> pure [])
  try pq <|> qp

pIdent :: Parser T.Text
pIdent = try do
  let pPart = do
        p <- takeWhile1P Nothing \c ->
          isPrint c && (c `notElem` (" @.(){};_" :: String))
        guard $ not (keyword p)
        pure p
      pParts = alternating1 pPart (C.string "_")
  xs <- T.concat <$> pParts
  guard $ xs /= "_"
  xs <$ ws

pName :: Parser Name
pName = Name <$> pIdent

pPQName :: Parser PQName
pPQName = do
  x <- pIdent
  y <- optional (try (char '.' *> pIdent))
  pure $ case y of
    Nothing -> Unqual $ Name x
    Just z -> Qual (ModuleName x) (Name z)

pKeyword :: T.Text -> Parser ()
pKeyword kw = do
  _ <- C.string kw
  (takeWhileP Nothing (\c -> isAlphaNum c || c == '\'') *> empty) <|> ws

pNatLit :: Parser Raw
pNatLit = do
  n <- decimal
  pure $ applyN n (RVar (Qual "Agda.Builtin.Nat" "suc") `RApp`) (RVar (Qual "Agda.Builtin.Nat" "zero"))

pAtom :: Parser Raw
pAtom =
  withPos
    ( (RVar <$> pPQName)
        <|> (RU <$ pKeyword "U")
        <|> pNatLit
    )
    <|> parens pRaw

goProj :: Raw -> Parser Raw
goProj t =
  ( char '.'
      *> ( ((char '₁' <|> char '1') *> goProj (RProj1 t))
             <|> ((char '₂' <|> char '2') *> goProj (RProj2 t))
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
      (RSigma "_" t <$> (pProd *> pSigmaExp)) <|> pure t
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
  pure $ foldr RLam t xs

pPiBinder :: Parser ([Name], Raw)
pPiBinder = parens $ (,) <$> some pName <*> (char ':' *> pRaw)

pPiExp :: Parser Raw
pPiExp = do
  optional (try (some pPiBinder)) >>= \case
    Nothing -> do
      t <- pSigmaExp
      (pArrow *> (RPi "_" t <$> pPiExp)) <|> pure t
    Just bs -> case bs of
      [([x], a)] ->
        (RPi x a <$> (pArrow *> pPiExp))
          <|> ( do
                  dom <- RSigma x a <$> (pProd *> pSigmaExp)
                  (RPi "_" dom <$> (pArrow *> pPiExp)) <|> pure dom
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

parseRaw :: FilePath -> T.Text -> Either ParserError Raw
parseRaw fname src = parse (ws *> pRaw <* eof) fname src
