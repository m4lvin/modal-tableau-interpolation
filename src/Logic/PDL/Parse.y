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
  'u'    { TokenCup    _ }
  '*'    { TokenStar   _ }
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
     | '?' PDLForm { Test $2 }

{
parseError :: [Token AlexPosn] -> a
parseError []     = error ("Empty parseError!")
parseError (t:ts) = error ("Parse error in line " ++ show lin ++ ", column " ++ show col ++ ": " ++ show t)
  where (AlexPn abs lin col) = apn t

instance IsString Logic.BasicModal.Form where
  fromString = parseK . alexScanTokens

instance IsString Logic.PDL.Form where
  fromString = parsePDL . alexScanTokens
}
