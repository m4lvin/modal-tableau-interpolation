module Logic.PDL.Token where
data Token a -- == AlexPn
  = TokenColon             {apn :: a}
  | TokenComma             {apn :: a}
  | TokenInt {fooI::Int,    apn :: a}
  | TokenTop               {apn :: a}
  | TokenBot               {apn :: a}
  | TokenPrp               {apn :: a}
  | TokenP                 {apn :: a}
  | TokenQ                 {apn :: a}
  | TokenR                 {apn :: a}
  | TokenNeg               {apn :: a}
  | TokenOB                {apn :: a}
  | TokenCB                {apn :: a}
  | TokenCOB               {apn :: a}
  | TokenCCB               {apn :: a}
  | TokenLA                {apn :: a}
  | TokenRA                {apn :: a}
  | TokenBinCon            {apn :: a}
  | TokenBinDis            {apn :: a}
  | TokenCon               {apn :: a}
  | TokenDis               {apn :: a}
  | TokenImpl              {apn :: a}
  | TokenEqui              {apn :: a}
  | TokenA                 {apn :: a}
  | TokenCup               {apn :: a}
  | TokenSemicolon         {apn :: a}
  | TokenTest              {apn :: a}
  | TokenStar              {apn :: a}

  deriving (Eq,Show)
