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
  ":"               { \ p _ -> TokenColon             p }
  ","               { \ p _ -> TokenComma             p }
  "("               { \ p _ -> TokenOB                p }
  ")"               { \ p _ -> TokenCB                p }
  "["               { \ p _ -> TokenCOB               p }
  "]"               { \ p _ -> TokenCCB               p }
  "<"               { \ p _ -> TokenLA                p }
  ">"               { \ p _ -> TokenRA                p }
  -- Formulas:
  "Top"             { \ p _ -> TokenTop               p }
  "True"            { \ p _ -> TokenTop               p }
  "Bot"             { \ p _ -> TokenBot               p }
  "False"           { \ p _ -> TokenTop               p }
  "~"               { \ p _ -> TokenNeg               p }
  "Not"             { \ p _ -> TokenNeg               p }
  "not"             { \ p _ -> TokenNeg               p }
  "&"               { \ p _ -> TokenBinCon            p }
  "|"               { \ p _ -> TokenBinDis            p }
  "=>"              { \ p _ -> TokenImpl              p }
  "iff"             { \ p _ -> TokenEqui              p }
  "AND"             { \ p _ -> TokenCon               p }
  "OR"              { \ p _ -> TokenDis               p }
  "p"               { \ p _ -> TokenP                 p }
  -- PDL Programs:
  "u"               { \ p _ -> TokenCup               p }
  "*"               { \ p _ -> TokenStar              p }
  ";"               { \ p _ -> TokenSemicolon         p }
  "?"               { \ p _ -> TokenTest              p }
  "a"               { \ p _ -> TokenA                 p }
  -- Ints:
  $dig+             { \ p s -> TokenInt (read s)      p }
