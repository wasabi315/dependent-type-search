module TypeSearch.Database.Search.Parser
  ( parseQuery,
    ParserError,
  )
where

import Data.Char
import Data.Foldable
import Data.Text qualified as T
import Text.Megaparsec
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L
import TypeSearch.Core.Name hiding (QName)
import TypeSearch.Database.Search.Query
import TypeSearch.Prelude hiding (many, some)

--------------------------------------------------------------------------------

type Parser = Parsec Void T.Text

type ParserError = ParseErrorBundle T.Text Void

ws :: Parser ()
ws = L.space C.space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

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
  (x == "λ")
    || (x == "U")
    || (x == ":")
    || (x == "->")
    || (x == "→")
    || (x == "×")

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

pNatLit :: Parser Term
pNatLit = do
  n <- decimal
  pure $ applyN n (Var (Qual "Agda.Builtin.Nat" "suc") `App`) (Var (Qual "Agda.Builtin.Nat" "zero"))

pAtom :: Parser Term
pAtom =
  (Var <$> pPQName)
    <|> (U <$ pKeyword "U")
    <|> pNatLit
    <|> parens pTerm

goProj :: Term -> Parser Term
goProj t =
  ( char '.'
      *> ( ((char '₁' <|> char '1') *> goProj (Proj1 t))
             <|> ((char '₂' <|> char '2') *> goProj (Proj2 t))
         )
  )
    <|> pure t

pProjExp :: Parser Term
pProjExp = goProj =<< pAtom

pApp :: Parser Term
pApp = do
  h <- pProjExp
  args <- many pProjExp
  pure $ foldl' App h args

pSigmaExp :: Parser Term
pSigmaExp = do
  optional (try (char '(' *> pName <* char ':')) >>= \case
    Nothing -> do
      t <- pApp
      (Sigma "_" t <$> (pProd *> pSigmaExp)) <|> pure t
    Just x -> do
      a <- pTerm
      _ <- char ')'
      _ <- pProd
      b <- pSigmaExp
      pure $ Sigma x a b

pAbs :: Parser Term
pAbs = do
  _ <- char 'λ' <|> char '\\'
  xs <- some pBind
  _ <- pArrow
  t <- pAbsPi
  pure $ foldr Lam t xs

pPiBinder :: Parser ([Name], Term)
pPiBinder = parens $ (,) <$> some pName <*> (char ':' *> pTerm)

pPiExp :: Parser Term
pPiExp = do
  optional (try (some pPiBinder)) >>= \case
    Nothing -> do
      t <- pSigmaExp
      (pArrow *> (Pi "_" t <$> pPiExp)) <|> pure t
    Just bs -> case bs of
      [([x], a)] ->
        (Pi x a <$> (pArrow *> pPiExp))
          <|> ( do
                  dom <- Sigma x a <$> (pProd *> pSigmaExp)
                  (Pi "_" dom <$> (pArrow *> pPiExp)) <|> pure dom
              )
      dom -> do
        _ <- pArrow
        b <- pPiExp
        pure $! foldr' (\(xs, a) t -> foldr' (\x -> Pi x a) t xs) b dom

pAbsPi :: Parser Term
pAbsPi = pAbs <|> pPiExp

pTerm :: Parser Term
pTerm = do
  t <- pAbsPi
  (Pair t <$> (char ',' *> pTerm)) <|> pure t

parseQuery :: FilePath -> T.Text -> Either ParserError Term
parseQuery fname src = parse (ws *> pTerm <* eof) fname src
