{
{-# OPTIONS_GHC -w #-}
{-# LANGUAGE OverloadedStrings #-}
module Logic.PDL.Parse where

import Data.String( IsString(..) )

import Logic.PDL.Token
import Logic.PDL.Lex
import Logic.PDL
import qualified Logic.BasicModal
}

%name parseK KForm
%name parsePDL PDLForm
%tokentype { Token AlexPosn }
%error { parseError }

%monad { ParseResult } { >>= } { Right }

%token
  TOP    { TokenTop    _ }
  BOT    { TokenBot    _ }
  'o'    { TokenO      _ }
  'p'    { TokenP      _ }
  'q'    { TokenQ      _ }
  'r'    { TokenR      _ }
  's'    { TokenS      _ }
  't'    { TokenT      _ }
  '('    { TokenOB     _ }
  ')'    { TokenCB     _ }
  '['    { TokenCOB    _ }
  ']'    { TokenCCB    _ }
  '<'    { TokenLA     _ }
  '>'    { TokenRA     _ }
  '&'    { TokenBinCon _ }
  '|'    { TokenBinDis _ }
  '~'    { TokenNeg    _ }
  '=>'   { TokenImpl   _ }
  '<-->' { TokenEqui   _ }
  'a'    { TokenA      _ }
  'b'    { TokenB      _ }
  'c'    { TokenC      _ }
  'd'    { TokenD      _ }
  'e'    { TokenE      _ }
  ':-'   { TokenSemicolon _ }
  '?'    { TokenTest   _ }
  'while'{ TokenWhile  _ }
  'if'   { TokenIf     _ }
  'then' { TokenThen   _ }
  'else' { TokenElse   _ }
  'u'    { TokenCup    _ }
  '*'    { TokenStar   _ }
  'n'    { TokenN      _ }
  INT    { TokenInt $$ _ }

%left '<-->'
%left '=>'
%left '|'
%left '&'
%left '[' Prog ']'
%left '<' Prog '>'
%left '~'

%left ':-' 'u'
%left '*'
%left '?'

%nonassoc 'p'
%nonassoc 'a'

%%

KForm : TOP { Logic.BasicModal.top }
     | BOT { Logic.BasicModal.Bot }
     | '(' KForm ')' { $2 }
     | '~' KForm { Logic.BasicModal.Neg $2 }
     | KForm '=>' KForm { Logic.BasicModal.imp $1 $3 }
     | KForm '&'  KForm { Logic.BasicModal.Con $1 $3 }
     | KForm '|'  KForm { Logic.BasicModal.dis $1 $3 }
     | KForm '<-->' KForm { $1 Logic.BasicModal.<--> $3 }
     | 'p' INT { Logic.BasicModal.At ('p' : show $2) }
     | 'o' { Logic.BasicModal.At ("o") }
     | 'p' { Logic.BasicModal.At ("p") }
     | 'q' { Logic.BasicModal.At ("q") }
     | 'r' { Logic.BasicModal.At ("r") }
     | 's' { Logic.BasicModal.At ("s") }
     | 't' { Logic.BasicModal.At ("t") }
     | '[' ']' KForm { Logic.BasicModal.Box $3 }
     | '<' '>' KForm { Logic.BasicModal.dia $3 }

PDLForm : TOP { top }
     | BOT { Bot }
     | '(' PDLForm ')' { $2 }
     | '~' PDLForm { Neg $2 }
     | PDLForm '=>' PDLForm { imp $1 $3 }
     | PDLForm '&'  PDLForm { Con $1 $3 }
     | PDLForm '|'  PDLForm { dis $1 $3 }
     | PDLForm '<-->' PDLForm { $1 <--> $3 }
     | 'p' INT { At ('p' : show $2) }
     | 'o' { At ("o") }
     | 'p' { At ("p") }
     | 'q' { At ("q") }
     | 'r' { At ("r") }
     | 's' { At ("s") }
     | 't' { At ("t") }
     | '[' Prog ']' PDLForm { Box $2 $4 }
     | '<' Prog '>' PDLForm { dia $2 $4 }

Prog : 'a' INT { Ap ('a' : show $2) }
     | 'a' { Ap "a" }
     | 'b' { Ap "b" }
     | 'c' { Ap "c" }
     | 'd' { Ap "d" }
     | 'e' { Ap "e" }
     | '(' Prog ')' { $2 }
     | Prog 'u' Prog { Cup $1 $3 }
     | Prog ':-' Prog { $1 :- $3 }
     | Prog '*' { Star $1 }
     | Prog 'n' { NStar $1 }
     | '?' PDLForm { Test $2 }
     | 'while' PDLForm Prog { while $2 $3 }
     | 'if' PDLForm 'then' Prog 'else' Prog { ite $2 $4 $6 }

{
type ParseResult a = Either (Int,Int) a

parseError :: [Token AlexPosn] -> ParseResult a
parseError []     = Left (1,1)
parseError (t:ts) = Left (lin,col)
  where (AlexPn _ lin col) = apn t

scanParseSafe :: _ -> String -> ParseResult a
scanParseSafe pfunc input =
  case alexScanTokensSafe input of
    Left pos        -> Left pos
    Right lexResult -> case pfunc lexResult of
      Left pos -> Left pos
      Right x  -> Right x

instance IsString Logic.BasicModal.Form where
  fromString = (\(Right f) -> f) . parseK . alexScanTokens

instance IsString Logic.PDL.Form where
  fromString = (\(Right f) -> f) . parsePDL . alexScanTokens
}
