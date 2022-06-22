{-# LANGUAGE OverloadedStrings, TemplateHaskell #-}

module Main where

import Prelude
import Control.DeepSeq (force, NFData)
import Control.Exception (evaluate, catch, SomeException)
import Control.Monad.IO.Class (liftIO)

import Data.FileEmbed
import Data.Maybe (fromMaybe)
import Web.Scotty
import qualified Data.Text as T
import qualified Data.Text.Encoding as E
import qualified Data.Text.Lazy as TL
import qualified Language.Javascript.JQuery as JQuery
import Language.Haskell.TH.Syntax
import Network.Wai.Handler.Warp (defaultSettings, setHost, setPort)
import System.Environment (lookupEnv)
import Text.Read (readMaybe)

import qualified Logic.BasicModal as BM
import qualified Logic.BasicModal.Prove.Tree
import qualified Logic.BasicModal.Interpolation.ProofTree
import Logic.BasicModal.Interpolation.ProofTree (forgetIPs)

import Logic.PDL
import Logic.Internal
import Logic.PDL.Lex
import Logic.PDL.Parse
import Logic.PDL.Prove.Tree

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
          in
          [ "<pre>Parsed input: " ++ toString pdlF  ++ "</pre>"
          , if isClosedTab t
              then "PROVED. <style type='text/css'> #output { border-color: green; } </style>"
              else "NOT proved. <style type='text/css'> #output { border-color: red; } </style>"
          , "<div align='center'>" ++ svg t ++ "<div>"
          ]

myCatch :: NFData a => a -> IO (Either String a)
myCatch x = catch (evaluate (force (Right x))) (\e-> return $ Left (show (e :: SomeException)))

embeddedFile :: String -> T.Text
embeddedFile str = case str of
  "index.html" -> E.decodeUtf8 $(embedFile "exec/index.html")
  "jquery.js"  -> E.decodeUtf8 $(embedFile =<< runIO JQuery.file)
  _            -> error "File not found."
