{-# LANGUAGE FlexibleInstances, BangPatterns #-}

module Logic.PDL.TeX where

import Control.Monad hiding (ap)
import Control.Concurrent (threadDelay)
import System.IO (hGetContents)
import System.IO.Temp
import System.IO.Unsafe (unsafePerformIO)
import System.Process
-- import Data.GraphViz hiding (Star)
-- import Data.GraphViz.Types.Generalised
-- import Data.GraphViz.Types.Monadic
import Data.Time.Clock.POSIX

import Logic.PDL hiding (a,b,c,p,q,r)
-- import Logic.PDL.Prove.Tree
-- import Logic.PDL.Interpolation.ProofTree

-- * TexAble for Formulas and Programs

instance TexAble Form where
  tex Bot = " \\bot "
  tex (At x) = show x
  tex (Neg Bot)  = " \\top "
  tex (Neg (Con (Neg f) (Neg g)))  = "(" ++ tex f ++ " \\lor " ++ tex g ++ ")"
  tex (Neg f) = " \\lnot " ++ tex f
  tex (Con f g) = tex f ++ " \\land " ++ tex g
  tex (Box a f) = " [ " ++ tex a ++ " ] " ++ tex f

instance TexAble Prog where
  tex (Ap x) = show x
  tex (Cup p1 p2) = "(" ++ tex p1 ++ " \\cup " ++ tex p2 ++ " ) "
  tex (p1 :- p2) = tex p1 ++ " ; " ++ tex p2
  tex (Star (Ap ap)) = "{" ++ show ap ++ "}^\\ast "
  tex (Star p) = "{( " ++ tex p ++ ")}^\\ast "
  tex (Test tf) = "? " ++ tex tf

-- * Tools copied from SMCDEL

class TexAble a where
  tex :: a -> String
  texTo :: a -> String -> IO ()
  texTo !x filename = writeFile (filename++".tex") (tex x)
  texDocumentTo :: a -> String -> IO ()
  texDocumentTo !x filename =
    writeFile (filename++".tex") (pre ++ tex x ++ post) where
      pre = concat [ "\\documentclass{standalone}"
                   , "\\usepackage[utf8]{inputenc}"
                   , "\\usepackage{tikz,fontenc,graphicx}"
                   , "\\usepackage[pdftex]{hyperref}"
                   , "\\hypersetup{pdfborder={0 0 0},breaklinks=true}"
                   , "\\begin{document}"
                   ]
      post= "\\end{document}"
  pdfTo :: a -> String -> IO ()
  pdfTo !x filename = do
    texDocumentTo x filename
    runAndWait $ "cd " ++ filename ++ "/../; /usr/bin/pdflatex -interaction=nonstopmode "++filename++".tex"
  disp :: a -> IO ()
  disp !x = withSystemTempDirectory "tapdleau" $ \tmpdir -> do
    ts <- round <$> getPOSIXTime
    let filename = tmpdir ++ "/disp-" ++ show (ts :: Int)
    pdfTo x filename
    runIgnoreAndWait $ "open " ++ filename ++ ".pdf"
    threadDelay 5000000 -- give viewer five seconds before deleting tmpdir
  svgViaTex :: a -> String
  svgViaTex !x = unsafePerformIO $ withSystemTempDirectory "tapdleau" $ \tmpdir -> do
    ts <- round <$> getPOSIXTime
    let filename = tmpdir ++ "/svgViaTex-" ++ show (ts :: Int)
    pdfTo x filename
    runAndWait $ "pdftocairo -nocrop -svg "++filename++".pdf "++filename++".svg"
    readFile (filename ++ ".svg")

instance TexAble String where
  tex i = " \\text{" ++ i ++ "} "

instance TexAble Int where
  tex = show

runAndWait :: String -> IO ()
runAndWait command = do
  (_inp,_out,err,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  hGetContents err >>= (\x -> unless (null x) (putStrLn x))
  return ()

runIgnoreAndWait :: String -> IO ()
runIgnoreAndWait command = do
  (_inp,_out,_err,pid) <- runInteractiveCommand command
  _ <- waitForProcess pid
  return ()
