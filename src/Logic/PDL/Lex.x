{
{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-tabs -fno-warn-missing-signatures #-}
module Logic.PDL.Lex where
import Logic.PDL.Token
}

%wrapper "posn"

$dig = 0-9      -- digits
$alf = [a-zA-Z] -- alphabetic characters

tokens :-
  -- ignore whitespace:
  $white+           ;
  -- keywords and punctuation:
  "("               { \ p _ -> TokenOB                p }
  ")"               { \ p _ -> TokenCB                p }
  "["               { \ p _ -> TokenCOB               p }
  "]"               { \ p _ -> TokenCCB               p }
  "<"               { \ p _ -> TokenLA                p }
  ">"               { \ p _ -> TokenRA                p }
  -- Formulas:
  "Top"             { \ p _ -> TokenTop               p }
  "True"            { \ p _ -> TokenTop               p }
  "T"               { \ p _ -> TokenTop               p }
  "⊤"               { \ p _ -> TokenTop               p }
  "Bot"             { \ p _ -> TokenBot               p }
  "False"           { \ p _ -> TokenBot               p }
  "F"               { \ p _ -> TokenBot               p }
  "⊥"               { \ p _ -> TokenBot               p }
  "¬"               { \ p _ -> TokenNeg               p }
  "~"               { \ p _ -> TokenNeg               p }
  "Not"             { \ p _ -> TokenNeg               p }
  "not"             { \ p _ -> TokenNeg               p }
  "&"               { \ p _ -> TokenBinCon            p }
  "∧"               { \ p _ -> TokenBinCon            p }
  "^"               { \ p _ -> TokenBinCon            p }
  "|"               { \ p _ -> TokenBinDis            p }
  "∨"               { \ p _ -> TokenBinDis            p }
  "v"               { \ p _ -> TokenBinDis            p }
  "=>"              { \ p _ -> TokenImpl              p }
  "->"              { \ p _ -> TokenImpl              p }
  "-->"             { \ p _ -> TokenImpl              p }
  "iff"             { \ p _ -> TokenEqui              p }
  "<->"             { \ p _ -> TokenEqui              p }
  "<-->"            { \ p _ -> TokenEqui              p }
  "AND"             { \ p _ -> TokenCon               p }
  "OR"              { \ p _ -> TokenDis               p }
  "o"               { \ p _ -> TokenO                 p }
  "p"               { \ p _ -> TokenP                 p }
  "q"               { \ p _ -> TokenQ                 p }
  "r"               { \ p _ -> TokenR                 p }
  "s"               { \ p _ -> TokenS                 p }
  "t"               { \ p _ -> TokenT                 p }
  -- PDL Programs:
  "u"               { \ p _ -> TokenCup               p }
  "∪"               { \ p _ -> TokenCup               p }
  "*"               { \ p _ -> TokenStar              p }
  ";"               { \ p _ -> TokenSemicolon         p }
  "?"               { \ p _ -> TokenTest              p }
  "while"           { \ p _ -> TokenWhile             p }
  "if"              { \ p _ -> TokenIf                p }
  "then"            { \ p _ -> TokenThen              p }
  "else"            { \ p _ -> TokenElse              p }
  "a"               { \ p _ -> TokenA                 p }
  "b"               { \ p _ -> TokenB                 p }
  "c"               { \ p _ -> TokenC                 p }
  "d"               { \ p _ -> TokenD                 p }
  "e"               { \ p _ -> TokenE                 p }
  -- Ints:
  $dig+             { \ p s -> TokenInt (read s)      p }

{
type LexResult a = Either (Int,Int) a

alexScanTokensSafe :: String -> LexResult [Token AlexPosn]
alexScanTokensSafe str = go (alexStartPos,'\n',[],str) where
  go inp@(pos,_,_,str) =
    case (alexScan inp 0) of
      AlexEOF -> Right []
      AlexError ((AlexPn _ line column),_,_,_) -> Left (line,column)
      AlexSkip  inp' len     -> go inp'
      AlexToken inp' len act -> case (act pos (take len str), go inp') of
        (_, Left lc) -> Left lc
        (x, Right y) -> Right (x : y)
}
