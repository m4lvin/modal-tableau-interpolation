module Logic.PDL.Tools where

import Data.String(fromString)

import Logic.PDL.Parse()
import Logic.PDL.Prove.Tree

parseNprove :: String -> Bool
parseNprove = provable . fromString

parseNproveSlideshow :: String -> IO ()
parseNproveSlideshow = proveSlideshow . fromString
