module Logic.PDL.Loaded where

import Data.List

import Logic.Internal
import Logic.PDL

-- | A loaded formula is prefixed by a negation and a non-empty sequence of boxes.
-- Example: (Neg f, [a,b]) stands for ¬[a][b]f with [a][b] underlined.
type Marked f = (f, [Prog]) -- where f starts with "Neg"
-- TODO: rename to Loaded, and flip around the order?

-- A WForm is weighted (Left/Right) and may have a marking.
type WForm = (Either Form Form, [Prog])

collapse :: WForm -> Marked Form
collapse (Left f,m)  = (f,m)
collapse (Right f,m) = (f,m)

isLeft :: WForm -> Bool
isLeft (Left  _, _) = True
isLeft (Right _, _) = False

isLoadedNode :: [WForm] -> Bool
isLoadedNode = not . all (null . snd)

ppWForms :: [WForm] -> [WForm] -> String
ppWForms wfs actives = intercalate ", " (map ppFormA (filter isLeft wfs)) ++ "   |   " ++ intercalate ", " (map ppFormA (filter (not . isLeft) wfs)) where
  ppFormA wf = [ '»' |  wf `elem` actives ] ++ ppLoadForm (collapse wf) ++ [ '«' |  wf `elem` actives ]

ppLoadForm :: Marked Form -> String
ppLoadForm (x, []) = toString x
ppLoadForm (Neg f, ps) = "~__[" ++ intercalate "][" (map toString ps) ++ "]__" ++ toString f
ppLoadForm bad = error $ "bad: " ++ show bad
