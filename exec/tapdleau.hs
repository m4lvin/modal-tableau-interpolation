{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module Main where

import Prelude
import Control.DeepSeq (force, NFData)
import Control.Exception (evaluate, catch, SomeException)
import Control.Monad.IO.Class (liftIO)
import Data.Containers.ListUtils
import Data.FileEmbed
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Web.Scotty
import qualified Data.Text as T
import qualified Data.Text.Encoding as E
import qualified Data.Text.Lazy as TL
import Data.String(fromString)
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
import Logic.PDL.Lex
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
      extra <- param "extra"
      parseResult <- liftIO $ myCatch (if logic == ("K" :: String) then Left ( parseK (alexScanTokens textinput) :: BM.Form) else Right (fromString textinput :: Logic.PDL.Form))
      html $ mconcat $ map TL.pack $ case parseResult of
        Left err ->
          [ "<pre> INPUT: " ++ show (textinput :: String) ++ "</pre>"
          , "<pre> PARSE ERRROR: " ++ err ++ "</pre>" ]
        Right (Left bmlF) ->
          let t = Logic.BasicModal.Prove.Tree.prove bmlF
              closed = Logic.BasicModal.Prove.Tree.isClosedTab t
              tWithInt = Logic.BasicModal.Interpolation.ProofTree.proveWithInt bmlF
          in
          [ "<pre>Parsed input: " ++ toString bmlF  ++ "</pre>"
          , if closed
              then "PROVED. <style type='text/css'> #output { border-color: green; } </style>"
              else "NOT proved. <style type='text/css'> #output { border-color: red; } </style>"
          , "<div align='center'>" ++ if closed then svg tWithInt else svg t ++ "<div>"
          ]
        Right (Right pdlF) ->
          let t = prove pdlF
              closed = isClosedTab t
              tWithInt = fillAllIPs $ toEmptyTabIP t
          in
          [ "<pre>Parsed input: " ++ toString pdlF  ++ "</pre>"
          , if closed
              then "PROVED. <style type='text/css'> #output { border-color: green; } </style>"
              else "NOT proved. <style type='text/css'> #output { border-color: red; } </style>"
          , "<div align='center'>" ++ if closed then svg tWithInt else svg t ++ "<div>"
          , if closed && extra == (1 :: Int) then "<div align=left>" ++ extraInfo tWithInt ++ "</div>" else ""
          ]

myCatch :: NFData a => a -> IO (Either String a)
myCatch x = catch (evaluate (force (Right x))) (\e-> return $ Left (show (e :: SomeException)))

embeddedFile :: String -> T.Text
embeddedFile str = case str of
  "index.html" -> E.decodeUtf8 $(embedFile "exec/index.html")
  "jquery.js"  -> E.decodeUtf8 $(embedFile =<< runIO JQuery.file)
  _            -> error "File not found."

-- | Given a closed tableau, show TI, TJ, TK etc. to get an interpolant.
extraInfo :: TableauxIP -> String
extraInfo tWithInt =
  let
    ti = tiOf tWithInt
    Just mstart = lowestMplusWithoutIP ti
    tj = tjOf $ head $ childrenOf mstart
    (y1, y2) = (leftsOf $ wfsOf tj, rightsOf $ wfsOf mstart)
    rightComponents = nubOrd $ map (\pth -> rightsOf (wfsOf (tj `at` pth)) ) (allPathsIn tj)
    tk = tkOf tj
  in
    unlines $ map strOrErr $
    [ "<h3>T<sup>I</sup>, after removing all n-nodes (Def 26):</h3>"
    , svg ti
    , "<h3>Lowest M+ rule without interpolant:</h3>"
    , svg mstart
    , "<h3>Y1 and Y2 sets</h3>"
    , "<p>Y1 = " ++ intercalate ", " (map toString y1) ++"</p>"
    , "<p>Y2 = " ++ intercalate "," (map toString y2) ++"</p>"
    , "<h3>T<sup>J</sup> (Def 27):</h3>"
    , svg tj
    , "<p>List of all nodes of T<sup>J</sup>:</p>"
    , "<pre>"
    , concatMap (\pth ->
                   show pth ++ "\t\t"
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
    , "<h3>T(Y) sets (Def 29):</h3>\n"
    , "<pre>"
    , "Y \t\tT(Y) \t\tT(Y)^ε \t\tT(Y)^I \t\tT(Y)^◁" ++ "\n"
    ,concatMap (\y ->
            pad 16 (toStrings y)
            ++ pad 16 (show (tOf tj y))
            ++ pad 16 (show (tOfEpsilon tj y))
            ++ pad 16 (show (tOfI tj y))
            ++ show (tOfTriangle tj y) ++ "\n"
           ) rightComponents
    , "</pre>"
    , "<h3>T<sup>K</sup> (Def 31):</h3>"
    , svg tk
    ]
    -- ++
    -- [ "<h3>Canonical programs (single steps in T<sup>K</sup> (Def 32):</h3>"
    -- , "<pre>"
    -- ]
    -- ++
    -- [ pad 42 (show (init pth) ++ " to " ++ show pth ++ ": ") ++ toString (canonProg tj tk (tk `at` init pth) [last pth]) | pth <- filter (not . null) (allPathsIn tk) ]
    -- ++
    -- ++ "</pre>"
    ++
    [ "<h3>T<sup>K</sup> with canonical programs and interpolants (Def 32 and 33):</h3>"
    , svg (annotateTk tj tk)
    , "<h3>Interpolant for the root of T<sup>K</sup>:</h3>"
    , "<p>"
    , toString $ ipFor tj tk []
    , "</p>"
    , "<p>Simplified: "
    , toString $ simplify $ ipFor tj tk []
    , "</p>"
    , "<p>Is it actually an interpolant for the root of T<sup>K</sup>?</h3>"
    , show $ isCorrectIPfor (ipFor tj tk []) tk
    , "<h3>Result after we keep on interpolating</h3>"
    , svg $ keepInterpolating tWithInt
    ]

strOrErr :: String -> String
strOrErr str =
  unsafePerformIO $ catch
      (evaluate (force str))
      (\e-> return $ "<pre>ERROR\n" ++ show (e :: SomeException) ++ "</pre>")
