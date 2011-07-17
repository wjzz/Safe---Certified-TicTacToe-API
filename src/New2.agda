{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module New2 where

open import Function

open import Data.Bool
open import Data.Maybe

open import Data.List hiding (_++_)
open import Data.List.Theorems hiding (_∈_)

open import Data.Nat
open import Data.Nat.Theorems

{- BASE IMPORT Data.Nat.Theorems -}

open import Data.Sum
open import Data.Product

open import Data.Empty
open import Data.Unit using (⊤)

open import Data.Vec renaming (map to vmap; concat to vconcat)
--open import Data.Vec.Theorems
--open import Data.Fin

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open ≡-Reasoning

data Color : Set where
  X O : Color

otherColor : Color → Color
otherColor X = O
otherColor O = X


data Move : Set where
  P1 P2 P3 : Move


infixr 5 _∷_

data Moves : Color → ℕ → Set where
  []  : Moves X 0
  _∷_ : {c : Color}{n : ℕ} → Move → Moves c n → Moves (otherColor c) (suc n)


data Board : ℕ → Set where
  board : {n : ℕ}
        → {k : ℕ}
        → {c : Color}
        → (n≤3 : n ≤ 3)
--        → (k≤3 : k ≤ 3)
        → (n+k : n + k ≡ 3)  -- do we need the previous two fact? they can be derived from this one
        → (moves      : Moves c k)
        → (validMoves : Vec Move n)
        → Board n

validMoves : {n : ℕ} → Board n → Vec Move n
validMoves (board n≤3 n+k moves validMoves) = validMoves


emptyBoard : Board 3
emptyBoard = board (s≤s (s≤s (s≤s z≤n))) refl [] (P1 ∷ P2 ∷ P3 ∷ [])


vdelete : {A : Set} {n : ℕ} → (a : A) → (v : Vec A (suc n)) → a ∈ v → Vec A n
vdelete a (.a ∷ xs)    here         = xs
vdelete a (y ∷ [])     (there x∈xs) = []
vdelete a (y ∷ x ∷ xs) (there x∈xs) = y ∷ vdelete a (x ∷ xs) x∈xs

addMove : {n : ℕ} → (b : Board (suc n)) → (m : Move) → m ∈ validMoves b → Board n
addMove {n} (board {k = k} n≤3 n+k moves validMoves) m m∈valid rewrite lem-plus-s n k
  = board (lem-≤-trans (lem-≤-suc n) n≤3) n+k 
          (m ∷ moves) (vdelete m validMoves m∈valid)


vmap-in : {A B : Set}{n : ℕ} → (v : Vec A n) → (f : (a : A) → (a ∈ v) → B) → Vec B n
vmap-in []       f = []
vmap-in (x ∷ xs) f = f x here ∷ vmap-in xs (λ a a∈xs → f a (there a∈xs))

allOutcomes : {n : ℕ} → Board n → List (Board 0)
allOutcomes {zero}  b = b ∷ []
allOutcomes {suc n} b = foldr₁ (Data.List._++_) 
                               (vmap-in (validMoves b) (λ a a∈v → allOutcomes (addMove b a a∈v)))


factorial : ℕ → ℕ
factorial zero    = 1
factorial (suc n) = suc n * factorial n

vAllOutcomes : {n : ℕ} → Board n → Vec (Board 0) (factorial n)
vAllOutcomes {zero}  b = b ∷ []
vAllOutcomes {suc n} b = vconcat 
                           (vmap-in (validMoves b) 
                                    (λ a a∈v → vAllOutcomes (addMove b a a∈v)))


-- this combinator was meant to simplify the equation above,
-- but type(a∈v) is dependent on type(a) so it won't work
-- I think I saw this combinator in Smullyan's book somewhere

comb : {A B C D : Set} → (A → B → C) → (C → D) → (A → B → D)
comb f g = (_∘_ g) ∘ f -- LOL! haskell: (g .) . f or  flip (.) (.) (.) ;d;d;d


-- Q: what if we have to concatenate vectors of vectors of different lenghts? 
-- A: we hide the lengths! (under an existential quantifier)

record Vrec (A : Set) : Set where
  field
    n : ℕ
    v : Vec A n

concatVrec : {A : Set} {n : ℕ} → Vec (Vrec A) (suc n) → Vrec A
concatVrec (x ∷ []) = x
concatVrec (x ∷ x' ∷ xs) with concatVrec (x' ∷ xs)
...                      | rec = record { n = Vrec.n x +  Vrec.n rec
                                        ; v = Vrec.v x ++ Vrec.v rec 
                                        }

econcat : {A : Set} {n : ℕ} → Vec (∃ (Vec A)) (suc n) → ∃ (Vec A)
econcat (x ∷ []) = x
econcat ((n , v) ∷ x' ∷ xs) with econcat (x' ∷ xs)
... | (n' , vs) = (n + n') , (v ++ vs)

-- if we want to expose the Board to the use, we hide the details:

module Implementation where
  abstract
    UBoard : Set
    UBoard = ∃ Board     -- BEATIFUL!

open Implementation
