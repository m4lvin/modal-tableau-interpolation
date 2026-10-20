module Main where

import Data.String( IsString(..) )
import Data.Maybe(fromJust)
import Logic.PDL
import Logic.Internal
import Logic.PDL.Parse ()
import Logic.PDL.Prove.Tree
import Logic.PDL.Interpolation.ProofTree

main :: IO ()
main = do
  let
    pdlF = fromString "(s ∧ [a*]((p ∧ s) → (⟨a⟩⊤ ∧ [a]s))) → ¬([a*](q → p) ∧ [a*](⟨a⟩q → q) ∧⟨a*⟩(q ∧ [a]⊥))" :: Logic.PDL.Form
    t = prove pdlF
    closed = isClosedTab t
    tWithInt = keepInterpolating $ fillAllIPs $ toEmptyTabIP t
    ip = (fromJust (mipOf tWithInt))
    ipSimp = simplify ip
    ipSimpCheck = checkCorrectIPfor ipSimp tWithInt

  putStrLn $ "Formula: " ++ toString pdlF
  putStrLn $ if closed then "PROVED." else "NOT proved."

  -- putStrLn "\nTableau with interpolants:"
  -- ppTab tWithInt

  putStrLn $ "Interpolant: " ++ toString ip

  putStrLn $ "Simplified: " ++ toString ipSimp
  putStrLn $ "Check: " ++ show ipSimpCheck
