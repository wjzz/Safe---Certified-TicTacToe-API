{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Strategy where

-- computational parts

open import Data.Fin       using    (Fin; zero; suc)
open import Data.List      hiding   (partition)
open import Data.Nat       renaming ( _≟_ to _≟ℕ_
                                    ; _⊔_ to max
                                    )
open import Data.Product
open import Data.Sum
open import Data.Vec       renaming ( map to vmap)
open import Data.Vec.Utils renaming ( map-in to vmap-in 
                                    ; delete to vdelete
                                    ; _⊂_ to _⊂-v_
                                    )

-- propositional parts

open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import Game

open GameImplementation

-------------------------
--  The strategy type  --
-------------------------

-- A strategy for a given player c is a function from the current
-- position into the chosen move, provided that c is the the current player.

-- Each (b : Board n) has n possible moves, so we can just return the index
-- of the move.
-- Alternatively we could return something from the set Σ[ m ∶ Move ] (m ∈ B.valid b)

Strategy : Color → Set
Strategy c = {n : ℕ} → (b : Board n) → B.currentPlayer b ≡ c → Fin n

----------------------------------------------------
--  Strategies for X and O packed in a function   --
----------------------------------------------------

GamePlan : Set
GamePlan = (c : Color) → Strategy c

--------------------------------------------------------------
--  Utilizing the strategies to calculate the final result  --
--------------------------------------------------------------

simulateGame : {n : ℕ} → GamePlan → Board n → Result
simulateGame {zero}  gamePlan b = ⊥-elim (absurdBoard b)
simulateGame {suc n} gamePlan b with inspect (B.currentPlayer b)
simulateGame {suc n} gamePlan b | c with-≡ eq with B.possibleMoves b ! (gamePlan c) b eq
simulateGame {suc n} gamePlan b | c with-≡ eq | m , m∈possible with addMove b m m∈possible
... | inj₁ nextBoard = simulateGame gamePlan nextBoard
... | inj₂ finished  = getResult finished

