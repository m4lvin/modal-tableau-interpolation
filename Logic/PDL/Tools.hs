module Logic.PDL.Tools where

-- import Logic.PDL
import Logic.PDL.Parse
import Logic.PDL.Lex
import Logic.PDL.Prove.Tree

parseNprove :: String -> Bool
parseNprove str = provable $ parse $ alexScanTokens str

parseNproveSlideshow :: String -> IO ()
parseNproveSlideshow str = proveSlideshow $ parse $ alexScanTokens str
