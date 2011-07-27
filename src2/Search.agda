{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Search where

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
open import ResultOrdering

open GameImplementation

---------------------
--  The game tree  --
---------------------

data Tree : Set where
  leaf : (fin : FinishedBoard) → Tree
  node : {n : ℕ} → (b : Board (suc n)) → Vec Tree (suc n) → Tree

-------------------------------------------------------------
--  Tree traversal example: counting the number of leaves  --
-------------------------------------------------------------

leaves : Tree → ℕ
leaves (leaf fin) = 1
leaves (node b y) = sumVec y where
  sumVec : {n : ℕ} → Vec Tree n → ℕ
  sumVec []       = 0
  sumVec (x ∷ xs) = leaves x + sumVec xs

------------------------------------
--  Building the whole game tree  --
------------------------------------

generateTree : {n : ℕ} → Board n → Tree
generateTree {0}     b = ⊥-elim (absurdBoard b)
generateTree {suc n} b = node b (vmap-in (B.possibleMoves b) f) 
  module GT where
    f : (a : Move) → a ∈ B.possibleMoves b → Tree
    f m m∈possible with addMove b m m∈possible
    f m m∈possible | inj₁ brd = generateTree brd
    f m m∈possible | inj₂ fin = leaf fin

----------------------------------
--  Finding the optimal result  --
----------------------------------

mutual
  bestTree : Color → Tree → Result
  bestTree c (leaf fin)        = getResult fin
  bestTree c (node b (x ∷ xs)) = bestNode c (bestTree (otherColor c) x) xs

  bestNode : {n : ℕ} → Color → Result → Vec Tree n → Result
  bestNode c r []       = r
  bestNode c r (x ∷ xs) = bestNode c (maxByColor c r (bestTree (otherColor c) x)) xs

bestResultTree : {n : ℕ} → Board n → Result
bestResultTree b = bestTree (B.currentPlayer b) (generateTree b)

-------------------------------------------------------
--  Searching without creating an explicit GameTree  --
-------------------------------------------------------

bestResultVec : {n : ℕ} → Board n → Result
bestResultVec {0}     b = ⊥-elim (absurdBoard b)
bestResultVec {suc n} b = maximum (B.currentPlayer b) (vmap-in (B.possibleMoves b) f) 
  module BRV where
    maximum : {n : ℕ} → Color → Vec Result (suc n) → Result
    maximum c (x ∷ [])      = x
    maximum c (x ∷ x' ∷ xs) = maximum c ((maxByColor c x x') ∷ xs)
  
    f : (a : Move) → a ∈ B.possibleMoves b → Result
    f a a∈possible with addMove b a a∈possible
    f a a∈possible | inj₁ brd = bestResultVec brd
    f a a∈possible | inj₂ fin = getResult fin
