{

{-# OPTIONS -Wno-missing-deriving-strategies #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

module TypeSearch.Lexer
  ( Parser,
    runParser,
    munchAll,
    lexer,
    Token (..),
    getCurrentPosition,
  )
where

import Codec.Binary.UTF8.String qualified as Utf8
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Text qualified as T
import Data.Word
import Error.Diagnose
import TypeSearch.Common
import TypeSearch.Error

}

$digit = [0-9]
$alpha = [a-zA-Z]
@ident = $alpha ($alpha | $digit | \- | \_ | \')*
@meta  = \? $alpha ($alpha | $digit | \- | \_ | \')*

tokens :-

<0>                $white+           ;
<0>                "--".*            ;
<0, stateComment>  "{-"              { enterComment }
<stateComment>     "-}"              { leaveComment }
<stateComment>     .                 ;
<stateComment>     \n                ;

<0>                module            { tok \_ -> TModule }
<0>                where             { tok \_ -> TWhere }
<0>                import            { tok \_ -> TImport }
<0>                let               { tok \_ -> TLet }
<0>                Σ                 { tok \_ -> TSigma }
<0>                S                 { tok \_ -> TSigma }
<0>                ".1"              { tok \_ -> TDot1 }
<0>                ".2"              { tok \_ -> TDot2 }

<0>                \(                { tok \_ -> TLParen }
<0>                \)                { tok \_ -> TRParen }
<0>                \[                { tok \_ -> TLBracket }
<0>                \]                { tok \_ -> TRBracket }
<0>                "->"              { tok \_ -> TArrow }
<0>                →                 { tok \_ -> TArrow }
<0>                \\                { tok \_ -> TLam }
<0>                λ                 { tok \_ -> TLam }
<0>                \:                { tok \_ -> TColon }
<0>                \_                { tok \_ -> TUnderscore }
<0>                \,                { tok \_ -> TComma }
<0>                \.                { tok \_ -> TDot }
<0>                \*                { tok \_ -> TAsterisk }
<0>                ×                 { tok \_ -> TAsterisk }
<0>                =                 { tok \_ -> TEq }

<0>                [$digit]+         { tok \s -> TNum (read (T.unpack s)) }
<0>                @ident            { tok \s -> TId s }
<0>                @ident \. @ident  { tok \s -> TQId (T.tail <$> T.breakOn "." s)  }
<0>                @meta             { tok \s -> TMeta s }

<0>                .                 { \inp _ -> throwError $ ParseError (currentPosition inp) [] }
<0>                \n                ;

{

data AlexInput = AlexInput
  { fileName :: !FilePath,
    currLine :: !Int,
    currCol :: !Int,
    prev :: !Char,
    bytes :: ![Word8],
    rest :: !T.Text
  }

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte input =
  case (bytes input, T.uncons (rest input)) of
    (b : bs, _) ->
      let !input' = input {bytes = bs}
       in Just (b, input')
    ([], Nothing) -> Nothing
    ([], Just (c, cs)) ->
      let b : bs = Utf8.encode [c]
          (!ln, !col) = move (currLine input, currCol input) c
          !input' = AlexInput (fileName input) ln col c bs cs
       in Just (b, input')

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar AlexInput {prev} = prev

ignorePendingBytes :: AlexInput -> AlexInput
ignorePendingBytes input = input {bytes = []}

currentPosition :: AlexInput -> Position
currentPosition AlexInput {..} =
  let p1 = (currLine, currCol)
      p2 = (currLine, currCol + 1)
   in Position p1 p2 fileName

data ParserState = ParserState
  { input :: !AlexInput,
    code :: !Int,
    commentDepth :: !Int
  }

getCurrentPosition :: Parser Position
getCurrentPosition = gets (currentPosition . input)

initState :: FilePath -> T.Text -> ParserState
initState fname inp =
  ParserState
    { input = AlexInput fname 1 1 '\n' [] inp,
      code = 0,
      commentDepth = 0
    }

type Parser = StateT ParserState (Either Error)

type Action = AlexInput -> Int -> Parser (Located Token)

runParser :: FilePath -> T.Text -> Parser a -> Either Error a
runParser fname inp p = evalStateT p (initState fname inp)

data Token
  = TId !T.Text
  | TQId (T.Text, T.Text)
  | TMeta !T.Text
  | TNum !Int
  | TModule
  | TWhere
  | TImport
  | TLet
  | TLam
  | TEq
  | TDot1
  | TDot2
  | TSigma
  | TLParen
  | TRParen
  | TLBracket
  | TRBracket
  | TArrow
  | TColon
  | TUnderscore
  | TComma
  | TDot
  | TAsterisk
  | TEOF
  deriving stock (Show)

move :: (Int, Int) -> Char -> (Int, Int)
move (ln, col) = \case
  '\n' -> (ln + 1, 1)
  _ -> (ln, col + 1)

tok :: (T.Text -> Token) -> Action
tok f inp len = do
  let !str = T.take len (rest inp)
      !beginPos = (currLine inp, currCol inp)
      !endPos = T.foldl' move beginPos str
      pos = Position beginPos endPos (fileName inp)
  pure $! f str :@ pos

enterComment :: Action
enterComment _ _ = do
  modify' \s -> s {commentDepth = commentDepth s + 1, code = stateComment}
  munch

leaveComment :: Action
leaveComment _ _ = do
  modify' \s ->
    s { commentDepth = commentDepth s - 1,
        code = if commentDepth s == 1 then 0 else stateComment
      }
  munch

munch :: Parser (Located Token)
munch = do
  (inp, sc) <- gets \s -> (input s, code s)
  case alexScan inp sc of
    AlexEOF -> do
      cd <- gets commentDepth
      pos <- gets (currentPosition . input)
      when (cd > 0) do
        throwError $ ParseError pos ["-}"]
      pure (TEOF :@ pos)
    AlexError inp' -> do
      throwError $ ParseError (currentPosition inp') []
    AlexSkip inp' _ -> do
      modify \s -> s {input = inp'}
      munch
    AlexToken inp' len act -> do
      modify \s -> s {input = inp'}
      act (ignorePendingBytes inp) len

munchAll :: Parser [Located Token]
munchAll = do
  t <- munch
  case t of
    TEOF :@ _ -> pure []
    _ -> (t :) <$> munchAll

lexer :: (Located Token -> Parser a) -> Parser a
lexer f = munch >>= f

}
