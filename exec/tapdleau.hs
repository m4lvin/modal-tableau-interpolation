{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module Main (main) where

import Prelude
import Control.DeepSeq (force)
import Control.Exception (evaluate, catch, SomeException)
import Data.Containers.ListUtils (nubOrd)
import Data.FileEmbed
import Data.List (intercalate, sort)
import Data.Maybe (fromMaybe, fromJust, isJust)
import Web.Scotty
import qualified Data.Text as T
import qualified Data.Text.Encoding as E
import qualified Data.Text.Lazy as TL
import qualified Language.Javascript.JQuery as JQuery
import Language.Haskell.TH.Syntax
import Network.Wai.Handler.Warp (defaultSettings, setHost, setPort)
import System.Environment (lookupEnv)
import System.IO.Unsafe
import Text.Read (readMaybe)

import qualified Logic.BasicModal as BM
import qualified Logic.BasicModal.Prove.Tree
import qualified Logic.BasicModal.Interpolation.ProofTree

import Logic.PDL
import Logic.Internal
import Logic.PDL.Parse
import Logic.PDL.Prove.Tree
import Logic.PDL.Interpolation.ProofTree

main :: IO ()
main = do
  putStrLn "taPDLeau -- https://github.com/m4lvin/modal-tableau-interpolation"
  port <- fromMaybe 3000 . (readMaybe =<<) <$> lookupEnv "PORT"
  putStrLn $ "Please open this link: http://127.0.0.1:" ++ show port ++ "/index.html"
  let mySettings = Options 1 (setHost "127.0.0.1" $ setPort port defaultSettings)
  scottyOpts mySettings $ do
    get ""  $ redirect "index.html"
    get "/" $ redirect "index.html"
    get "/index.html" . html . TL.fromStrict $ embeddedFile "index.html"
    get "/jquery.js"  . html . TL.fromStrict $ embeddedFile "jquery.js"
    post "/prove" $ do
      logic <- param "logic"
      textinput <- param "textinput"
      let parseResult = if logic == ("K" :: String)
                        then Left  (scanParseSafe parseK   textinput :: ParseResult BM.Form)
                        else Right (scanParseSafe parsePDL textinput :: ParseResult Logic.PDL.Form)
      html $ mconcat $ map TL.pack $ case parseResult of
        Left (Left (_,col)) ->
          [ "<pre>INPUT: " ++ textinput ++ "</pre>"
          , "<pre>" ++ replicate (col + length ("INPUT:" :: String)) ' ' ++ "^</pre>"
          , "<pre>Parse error in column " ++ show col ++ ".</pre>" ]
        Left (Right bmlF) ->
          let t = Logic.BasicModal.Prove.Tree.prove bmlF
              closed = Logic.BasicModal.Prove.Tree.isClosedTab t
              tWithInt = Logic.BasicModal.Interpolation.ProofTree.proveWithInt bmlF
          in
          [ "<pre>Parsed input: " ++ toString bmlF  ++ "</pre>"
          , if closed
              then "PROVED. <style type='text/css'> #output { border-color: green; } </style>\n"
              else "NOT proved. <style type='text/css'> #output { border-color: red; } </style>\n"
          , "<div align='center'>" ++ if closed then svg tWithInt else svg t ++ "</div>"
          ]
        Right (Left (_,col)) ->
          [ "<pre>INPUT: " ++ textinput ++ "</pre>"
          , "<pre>" ++ replicate (col + length ("INPUT:" :: String)) ' ' ++ "^</pre>"
          , "<pre>Parse error in column " ++ show col ++ ".</pre>" ]
        Right (Right pdlF) ->
          let t = prove pdlF
              closed = isClosedTab t
              ti = tiOf $ toEmptyTabIP t
              tWithInt = keepInterpolating ti
              interpolated = isJust (mipOf tWithInt)
              ipcheck = checkCorrectIPfor (fromJust (mipOf tWithInt)) tWithInt
              correctIP = ipcheck == (True,True,True)
              message = case (closed,interpolated,correctIP) of
                (False,_    ,_    ) -> "NOT proved. <style> #output { border-color: orange; } </style>\n"
                (True ,False,_    ) -> "PROVED, but NO interpolant. <style> #output { border-color: red; } </style>\n"
                (True ,True ,False) -> "PROVED but WRONG interpolant "++ show ipcheck ++ ". <style> #output { border-color: red; } </style>\n"
                (True ,True ,True ) -> "PROVED and CORRECT interpolant. <style> #output { border-color: green; } </style>\n"
          in
          [ "<pre>Parsed input: " ++ toString pdlF  ++ "</pre>"
          , message
          , "<div align='center'>" ++ svg t ++ "</div>"
          , if closed then interpolateInfo ti else ""
          ]

embeddedFile :: String -> T.Text
embeddedFile str = case str of
  "index.html" -> E.decodeUtf8 $(embedFile "exec/index.html")
  "jquery.js"  -> E.decodeUtf8 $(embedFile =<< runIO JQuery.file)
  _            -> error "File not found."

-- | Given the TI of a closed tableau, show TI, TJ, TK etc. to get an interpolant.
interpolateInfo :: TableauxIP -> String
interpolateInfo ti =
  unlines $ map strOrErr $
    [ "<h3>T<sup>I</sup></h3>"
    , "<p>This is T after removing all n-nodes (Def 26) and using Lemma 14 and 15 for the \"easy\" interpolants.</p>"
    , svg ti
    ]
    ++
    snd (mPlusLoop ti)
    ++
    [ "<hr /><h3>Result after we keep on interpolating</h3>"
    , svg $ keepInterpolating ti
    , case mipOf (keepInterpolating ti) of
        Nothing -> "No interpolant found."
        Just theta -> theta `isActuallyInterpolantFor` keepInterpolating ti
    ]

isActuallyInterpolantFor :: Form -> TableauxIP -> String
isActuallyInterpolantFor theta tk =
      "<p>Is " ++ toString theta ++ " actually an interpolant?</p>"
    ++
      let
        (vocCon,left,right) = checkCorrectIPfor theta tk
        lineFor str statement bit =
          "<p class='" ++ (if bit then "success" else "error") ++ "'>" ++ str ++ " (" ++ statement ++ " ): " ++ show bit ++ "</p>\n"
      in
        lineFor "Vocabulary condition" ("voc(" ++ toString theta ++ ") ⊆ voc(" ++ toStrings (leftsOf (wfsOf tk)) ++ ") ∩ voc(" ++ toStrings (rightsOf (wfsOf tk)) ++ ")") vocCon
        ++
        lineFor "Left condition" ("inconsistent: " ++ toStrings (Neg theta : map simplify (leftsOf (wfsOf tk)))) left
        ++
        lineFor "Right condition" ("inconsistent: " ++ toStrings (theta : map simplify (rightsOf (wfsOf tk)))) right


mPlusLoop :: TableauxIP -> (TableauxIP, [String])
mPlusLoop ti = case lowestMplusWithoutIP ti of
                 Nothing -> (ti, [ "<p>There are no remaining M+ nodes without interpolant.</p>" ])
                 Just _  -> let (nextTI, output) = solveLowestMplus $ fillAllIPs ti
                                (final, outputs) = mPlusLoop nextTI
                            in  (final , output ++ outputs)

solveLowestMplus :: TableauxIP -> (TableauxIP, [String])
solveLowestMplus ti =
  let
    Just mstart = lowestMplusWithoutIP ti
    tj = tjOf $ head $ childrenOf mstart
    (y1, y2) = (leftsOf $ wfsOf tj, rightsOf $ wfsOf mstart)
    rightComponents = nubOrd $ map (\pth -> rightsOf (wfsOf (tj `at` pth)) ) (allPathsIn tj)
    tk = tkOf tj
    filledTK = annotateTk tj tk
    newTI = fillLowestMplus ti
  in
    (newTI,
    [ "<hr /><h3>Lowest M+ rule without interpolant:</h3>"
    , svg mstart
    , "<h3 title='Y1 and Y2 are the left and right sets of the node obtained using M+.'>Y1 and Y2 sets</h3>"
    , "<p>Y1 = " ++ intercalate ", " (map toString y1) ++"</p>"
    , "<p>Y2 = " ++ intercalate "," (map toString y2) ++"</p>"
    , "<h3 title='TJ is a sub-tableau of TI from Y1/Y2 up to M-, free, left-empty or repeat nodes.'>T<sup>J</sup> (Def 27):</h3>"
    , svg tj
    , "<p>List of all nodes of T<sup>J</sup>:</p>"
    , "<pre>"
    , concatMap (\pth ->
                   pad 16 (show pth)
                   ++ ppWFormsTyp Nothing (wfsOf (tj `at` pth)) []
                   ++ "\n"
                ) $ allPathsIn tj
    , "</pre>"
    , "<h3>◁' relation (Def 15):</h3>"
    , "<pre>from\t\tto"
    , concatMap (\pth ->
                   pad 16 (show pth)
                   ++ show (filter (trianglePrime tj pth) (allPathsIn tj)) ++ "\n"
                ) $ allPathsIn tj
    , "</pre>"
    , "<h3 title='T(Y) are all nodes with Y as their right side.'>T(Y) sets (Defs 28 and 29):</h3>\n"
    , "<pre>"
    , "Y \t\tT(Y) \t\tT(Y)^ε \t\tT(Y)^I \t\tT(Y)^◁" ++ "\n"
    , concatMap (\y ->
            pad 16 (toStrings y)
            ++ pad 16 (show (tOf tj y))
            ++ pad 16 (show (tOfEpsilon tj y))
            ++ pad 16 (show (tOfI tj y))
            ++ show (tOfTriangle tj y) ++ "\n"
           ) rightComponents
    , "</pre>"
    , "<h3>T<sup>K</sup> with canonical programs and interpolants (Defs 30, 31, 32 and 33):</h3>"
    , svg (annotateTk tj tk)
    , "<h3>Interpolant for the root of T<sup>K</sup>:</h3>"
    , "<p>Original: " ++ toString (ipFor tj tk []) ++ "<br />"
    , "Simplified: " ++ toString (simplify $ ipFor tj tk []) ++ "</p>"
    , simplify (ipFor tj tk []) `isActuallyInterpolantFor` tk
    , "<h3>Helper functions for the proof that it is an interpolant</h3>"
    , "<p>Sets J(s) for each s in T<sup>K</sup> (Def 34):</p>"
    , "<pre>"
    , concatMap (\pth ->
                   pad 16 (show pth)
                   ++ toStrings (jSetOf tj filledTK pth)
                   ++ "\n"
                ) $ allPathsIn filledTK
    , "</pre>"
    , "<p>Sets K(s) for each s in T<sup>K</sup> (Def 34):</p>"
    , "<pre>"
    , concatMap (\pth ->
                   pad 16 (show pth)
                   ++ toStrings (kSetOf tj filledTK pth)
                   ++ "\n"
                ) $ allPathsIn filledTK
    , "</pre>"
    , "<p>Simplified K(s) for each s in T<sup>K</sup> (Def 34):</p>"
    , "<pre>"
    , concatMap (\pth ->
                   pad 16 (show pth)
                   ++ toStrings (sort $ nubOrd $ map simplify $ kSetOf tj filledTK pth)
                   ++ "\n"
                ) $ allPathsIn filledTK
    , "</pre>"
    --
    -- TODO: Lema 25: extended tableau for K(s^i)
    --
    ]
    )


strOrErr :: String -> String
strOrErr str =
  unsafePerformIO $ catch
      (evaluate (force str))
      (\e-> return $ "<pre>ERROR\n" ++ show (e :: SomeException) ++ "</pre>")
