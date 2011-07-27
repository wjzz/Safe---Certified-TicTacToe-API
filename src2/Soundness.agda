{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Soundness where

-- computational parts

open import Data.Bool
open import Data.List      hiding (partition)
open import Data.Maybe
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
open import Data.Nat.Theorems
open import Data.List.Theorems renaming ( _∈_ to _∈-list_
                                        ; _∉_ to _∉-list_
                                        )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

{- BASE IMPORT Data.Nat.Theorems  -}

open import Game
open import Search
open import Strategy

open GameImplementation

------------------------------------------------------------
--  Equivalence of two ways to calculate the best result  --
------------------------------------------------------------

equivalence-iter : ∀ {n : ℕ} (b : Board n) → bestTree (B.currentPlayer b) (generateTree b) ≡ bestResultVec b
equivalence-iter {zero}  b = ⊥-elim (absurdBoard b)
equivalence-iter {suc n} (c-board currentPlayer noPlayed playedMoves (x ∷ xs) y) with checkGameStatus playedMoves x (proj₁ (I.noWin y) , proj₂ (I.noWin y)) (I.k<9 y)
equivalence-iter {suc currentPlayer} (c-board noPlayed playedMoves _ (x ∷ xs) y) | stWon y' y0 = {!!}
equivalence-iter {suc currentPlayer} (c-board noPlayed playedMoves _ (x ∷ xs) y) | stDraw y' y0 = {!!}
equivalence-iter {suc currentPlayer} (c-board noPlayed playedMoves _ (x ∷ xs) y) | stInProgress y' y0 = {!!}

{-
 (vmap-in (B.possibleMoves b) (GT.f n b) : Vec Tree (suc n)

Goal: bestTree (B.currentPlayer b)
      (node b (vmap-in (B.possibleMoves b) (GT.f n b)))
      ≡
      BRV.maximum n b (B.currentPlayer b)
      (vmap-in (B.possibleMoves b) (BRV.f n b))
-}


equivalence : ∀ {n : ℕ} (b : Board n) → bestResultTree b ≡ bestResultVec b
equivalence = equivalence-iter