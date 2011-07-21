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

------------------------------------
--  Building the whole game tree  --
------------------------------------

generateTree : {n : ℕ} → Board n → Tree
generateTree {0}     b = ⊥-elim (absurdBoard b)
generateTree {suc n} b = node b (vmap-in (B.valid b) f) module genTree where
  f : (a : Move) → a ∈ B.valid b → Tree
  f m m∈valid with addMove b m m∈valid
  f m m∈valid | inj₁ brd = generateTree brd
  f m m∈valid | inj₂ fin = leaf fin

----------------------------------
--  Finding the optimal result  --
----------------------------------

mutual
  bestResultByColor : Color → Tree → Result
  bestResultByColor c (leaf fin)        = getResult fin
  bestResultByColor c (node b (x ∷ xs)) = bestResultByColorIter c (bestResultByColor (otherColor c) x) xs

  bestResultByColorIter : {n : ℕ} → Color → Result → Vec Tree n → Result
  bestResultByColorIter c r []       = r
  bestResultByColorIter c r (x ∷ xs) = bestResultByColorIter c (maxByColor c r (bestResultByColor (otherColor c) x)) xs

bestResult : {n : ℕ} → Board n → Result
bestResult b = bestResultByColor (B.c b) (generateTree b)

-------------------------------------
--  Counting the number of leaves  --
-------------------------------------

leaves : Tree → ℕ
leaves (leaf fin) = 1
leaves (node b y) = sumVec y where
  sumVec : {n : ℕ} → Vec Tree n → ℕ
  sumVec []       = 0
  sumVec (x ∷ xs) = leaves x + sumVec xs

