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

equivalence : ∀ {n : ℕ} (b : Board n) → bestResult b ≡ bestResultVec b
equivalence = {!!}