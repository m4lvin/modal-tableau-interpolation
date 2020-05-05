module Logic.BasicModal.Examples where

import Logic.BasicModal

someValidities :: [Form]
someValidities =
  [ p --> p
  , Box (con p q) --> Box p
  , dia (con p q) --> dia p
  , con (Box (p --> q)) (dia p) --> dia q
  ]

someNonValidities :: [Form]
someNonValidities =
  [ p --> q
  , Box p --> p
  , dia (dia p) --> dia p
  , Box (dis p q) --> Box p
  ]
