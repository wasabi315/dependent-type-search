{

{-# OPTIONS -Wno-missing-deriving-strategies #-}
{-# LANGUAGE FieldSelectors #-}
{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

module TypeSearch.Parser
  ( parseModule,
    parseRaw,
  )
where

import Control.Monad.Except
import Data.Bifunctor
import Data.Foldable
import Data.Text (Text)
import Error.Diagnose
import TypeSearch.Common
import TypeSearch.Raw
import TypeSearch.Error
import TypeSearch.Lexer

}

%name moduleParser Module
%name rawParser RawEntry
%tokentype { Located Token }

%monad { Parser } { (>>=) } { pure }
%lexer { lexer } { TEOF :@ _ }

%errorhandlertype explist
%error { (parseError . snd) }

%token

id      { (atTId -> Just $$) }
qid     { (atTQId -> Just $$) }
num     { (atTNum -> Just $$) }
meta    { (atTMeta -> Just $$) }
module  { TModule :@ _ }
where   { TWhere :@ _ }
import  { TImport :@ _ }
let     { TLet :@ _ }
sigma   { TSigma :@ _ }
".1"    { TDot1 :@ _ }
".2"    { TDot2 :@ _ }
'\\'    { TLam :@ _ }
'='     { TEq :@ _ }
'('     { TLParen :@ _ }
')'     { TRParen :@ _ }
'['     { TLBracket :@ _ }
']'     { TRBracket :@ _ }
'->'    { TArrow :@ _ }
':'     { TColon :@ _ }
'_'     { TUnderscore :@ _ }
','     { TComma :@ _ }
'.'     { TDot :@ _ }
'*'     { TAsterisk :@ _ }

%%

Module :: { Module }
Module
  : module ModuleName where Imports Decls  { Module (value $2) (reverse $4) (reverse $5) }

Imports :: { [ModuleName] }
Imports
  : {- empty -}                { [] }
  | Imports import ModuleName  { value $3 : $1 }

Decls :: { [Decl] }
Decls
  : {- empty -}  { [] }
  | Decls Decl   { $2 : $1 }

Decl :: { Decl }
Decl : let Bind ':' Raw '=' Raw  { DLoc (DLet (value $2) (RLoc $4) (RLoc $6) :@ mergePosition $1 $6) }

RawEntry :: { Raw }
RawEntry : Raw  { RLoc $1 }

Raw :: { Located Raw }
Raw : Pair  { $1 }

Pair :: { Located Raw }
Pair : Pair1 { foldl1 (flip RPair) (map RLoc $1) :@ mergePosition (last $1) (head $1) }

Pair1 :: { [Located Raw] }
Pair1
  : Component            { [$1] }
  | Pair1 ',' Component  { $3 : $1 }

Component :: { Located Raw }
Component
  : Domain '->' Pair                    { foldr (uncurry RPi . value) (RLoc $3) $1 :@ mergePosition (head $1) $3 }
  | '\\' SpaceBinds '->' Pair           { foldr (RAbs . value) (RLoc $4) $2 :@ mergePosition $1 $4 }
  | Sigma                 { $1 }

Telescope :: { [Located (Name, Raw)] }
Telescope
  : '(' SpaceNamesAbsurd ':' Pair ')'            { let { pos = mergePosition $1 $5; t = RLoc $4 }
                                                    in [ (value n, t) :@ pos | n <- $2 ]
                                                 }
  | '(' SpaceNamesAbsurd ':' Pair ')' Telescope  { let { pos = mergePosition $1 $5; t = RLoc $4 }
                                                    in [ (value n, t) :@ pos | n <- $2 ] ++ $6
                                                 }

Domain :: { [Located (Name, Raw)] }
Domain
  : Sigma      { [fmap ("_",) $1] }
  | Telescope  { $1 }

Sigma :: { Located Raw }
Sigma
  : Application                           { $1 }
  | sigma Name ':' Application '.' Sigma  { RSigma (value $2) (RLoc $4) (RLoc $6) :@ mergePosition $1 $6 }
  | Application '*' Sigma                 { RSigma "_" (RLoc $1) (RLoc $3) :@ mergePosition $1 $3 }

Application :: { Located Raw }
Application : Application1  { let f : args = reverse $1
                               in foldl' (\acc arg -> (RLoc acc `RApp` RLoc arg) :@ mergePosition acc arg) f args
                            }

Application1 :: { [Located Raw] }
Application1
  : Projection               { [$1] }
  | Application1 Projection  { $2 : $1 }

Projection :: { Located Raw }
Projection
  : Atom             { $1 }
  | Projection ".1"  { RFst (RLoc $1) :@ mergePosition $1 $2 }
  | Projection ".2"  { RSnd (RLoc $1) :@ mergePosition $1 $2 }

MetaApplication :: { Located Raw }
MetaApplication
  : Meta                        { RMetaApp (value $1) [] :@ position $1 }
  | Meta '[' MetaArguments ']'  { RMetaApp (value $1) (reverse (map RLoc $3)) :@ mergePosition $1 $4 }

MetaArguments :: { [Located Raw] }
MetaArguments
  : {- empty -}                  { [] }
  | Component                    { [$1] }
  | MetaArguments ',' Component  { $3 : $1 }

Atom :: { Located Raw }
Atom
  : '(' Pair ')'        { RLoc $2 :@ mergePosition $1 $3 }
  | Name                { case value $1 of
                            "Type" -> fmap (const RType) $1
                            "Unit" -> fmap (const RUnit) $1
                            "tt" -> fmap (const RTT) $1
                            "Nat" -> fmap (const RNat) $1
                            "zero" -> fmap (const RZero) $1
                            "suc" -> fmap (const RSuc) $1
                            "natElim" -> fmap (const RNatElim) $1
                            "Eq" -> fmap (const REq) $1
                            "refl" -> fmap (const RRefl) $1
                            "eqElim" -> fmap (const REqElim) $1
                            _ -> fmap (RVar . Unqual) $1
                        }
  | QName               { fmap RVar $1 }
  | MetaApplication     { $1 }
  | num                 { fmap rnatLit $1 }

SpaceBinds :: { [Located Name] }
SpaceBinds
  : Bind             { [$1] }
  | Bind SpaceBinds  { $1 : $2 }

-- Used in dependent function types: (x y z : A) -> B
-- This is to avoid reduce/reduce conflict in the parser
SpaceNamesAbsurd :: { [Located Name] }
SpaceNamesAbsurd
  : Application1  {% let { f (RVar (Unqual x) :@ p) = pure (x :@ p)
                         ; f (_ :@ p) = parseErrorAt [] p
                         }
                      in traverse f (reverse $1)
                  }

ModuleName :: { Located ModuleName }
ModuleName : id  { fmap ModuleName $1 }

Name :: { Located Name }
Name : id  { fmap Name $1 }

QName :: { Located QName }
QName : qid  { fmap (uncurry Qual . bimap ModuleName Name) $1 }

Meta :: { Located Meta }
Meta : meta  { fmap (Src . Name) $1 }

Bind :: { Located Name }
Bind
  : id   { fmap Name $1 }
  | '_'  { "_" :@ position $1 }

{

atTId (TId i :@ p) = Just (i :@ p)
atTId _ = Nothing

atTQId (TQId i :@ p) = Just (i :@ p)
atTQId _ = Nothing

atTMeta (TMeta i :@ p) = Just (i :@ p)
atTMeta _ = Nothing

atTNum (TNum i :@ p) = Just (i :@ p)
atTNum _ = Nothing

parseErrorAt :: [String] -> Position -> Parser a
parseErrorAt exps pos = throwError $ ParseError pos exps

parseError :: [String] -> Parser a
parseError x = getCurrentPosition >>= parseErrorAt x

parseModule :: FilePath -> Text -> Either Error Module
parseModule fname src = runParser fname src moduleParser

parseRaw :: FilePath -> Text -> Either Error Raw
parseRaw fname src = runParser fname src rawParser

}
