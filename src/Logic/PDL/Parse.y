{
{-# OPTIONS_GHC -w #-}
module Logic.PDL.Parse where
import Logic.PDL.Token
import Logic.PDL.Lex
import Logic.PDL
}

%name parse Form
%tokentype { Token AlexPosn }
%error { parseError }

%token
  TOP    { TokenTop    _ }
  BOT    { TokenBot    _ }
  'p'    { TokenP      _ }
  'q'    { TokenQ      _ }
  'r'    { TokenR      _ }
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
  'a'    { TokenA      _ }
  ':-'   { TokenSemicolon _ }
  '?'    { TokenTest   _ }
  'u'    { TokenCup    _ }
  '*'    { TokenStar   _ }
  INT    { TokenInt $$ _ }

%left '=>'
%left '|' '&'
%nonassoc '|' '&'
%left '[' Prog ']'
%left '<' Prog '>'
%left '~'

%left ':-' 'u'
%left '*'
%left '?'

%nonassoc 'p'
%nonassoc 'a'

%%

Form : TOP { Top }
     | BOT { Bot }
     | '(' Form ')' { $2 }
     | '~' Form { Neg $2 }
     | Form '=>' Form { Imp $1 $3 }
     | Form '&'  Form { Con $1 $3 }
     | Form '|'  Form { Dis $1 $3 }
     | 'p' INT { At ('p' : show $2) }
     | 'p' { At ("p") }
     | 'q' { At ("q") }
     | 'r' { At ("r") }
     | '[' Prog ']' Form { Box  $2 $4 }
     | '<' Prog '>' Form { Dia $2 $4 }

Prog : 'a' INT { Ap ('a' : show $2) }
     | '(' Prog ')' { $2 }
     | Prog 'u' Prog { Cup $1 $3 }
     | Prog ':-' Prog { $1 :- $3 }
     | Prog '*' { Star $1 }
     | '?' Form { Test $2 }

{
parseError :: [Token AlexPosn] -> a
parseError []     = error ("Empty parseError!")
parseError (t:ts) = error ("Parse error in line " ++ show lin ++ ", column " ++ show col ++ ": " ++ show t)
  where (AlexPn abs lin col) = apn t

fromString :: String -> Form
fromString = parse . alexScanTokens
}
