module Main where

open import Data.Nat
open import Game
open import Search
open GameImplementation

open import Data.String

postulate
  Int : Set

{-# BUILTIN INTEGER Int    #-}

primitive
  primNatToInteger    : ℕ -> Int
  primShowInteger     : Int -> String

showResult : Result → String
showResult (Win X) = "Won X"
showResult (Win O) = "Won O"
showResult Draw    = "Draw"


data Unit : Set where
  unit : Unit

{-# COMPILED_DATA Unit () () #-}

postulate 
  IO : Set -> Set

{-# COMPILED_TYPE IO IO #-}

postulate 
  putStrLn : String -> IO Unit

{-# COMPILED putStrLn putStrLn #-}

postulate
  getLine : IO String

{-# COMPILED getLine getLine #-}

postulate 
  return : {A : Set} → A → IO A
  _>>=_ : {A B : Set} → IO A → (A → IO B) → IO B

{-# COMPILED return (\ _ -> return) #-}
{-# COMPILED _>>=_ (\ _ _ -> (>>=)) #-}


main : IO Unit
main = putStrLn (showResult (bestResult empty)) >>= (λ x → putStrLn (primShowInteger (primNatToInteger (leaves (generateTree empty)))))
