>{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module New where

open import Data.Bool
open import Data.Maybe

open import Data.List
open import Data.List.Theorems

open import Data.Nat renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Theorems

open import Data.Sum
open import Data.Product

open import Data.Empty
open import Data.Unit

open import Data.Fin
--open import Data.Vec.Theorems

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

{- BASE IMPORT Data.Nat.Theorems -}

{-
  an experimental implementation
-}

data Move : Set where
  P1 P2 : Move

_==_ : (m1 m2 : Move) → Dec (m1 ≡ m2)
P1 == P1 = yes refl
P1 == P2 = no (λ ())
P2 == P1 = no (λ ())
P2 == P2 = yes refl


data Board : Set where
  board : (k : ℕ) →
          k ≤ℕ 2 →
          (validMoves : List Move) →
          (conts : ((m : Move) → m ∈ validMoves → Maybe Board)) →
          Board
  
-- ok, Board is not empty
lastBoard : Board
lastBoard = board 0 z≤n [] (λ m ())
{-
succesors : (b : Board) → List (Maybe Board)
succesors (board l n y validMoves conts) = map-in validMoves conts

addMove : Board → Move → Maybe Board
addMove (board k n y validMoves conts) m with member m validMoves _==_
addMove (board k n y validMoves conts) m | yes p = conts m p
addMove (board k n y validMoves conts) m | no ¬p = nothing
-}

buildBoard : (k : ℕ) → (p : k ≤ℕ 2) → (validMoves : List Move) → Maybe Board
buildBoard zero    p validMoves = nothing
buildBoard (suc k) p validMoves = just (board (suc k) p validMoves aux) 
 module Local where
  aux : (m : Move) → m ∈ validMoves → Maybe Board
  aux m m-val = buildBoard k (lem-≤-trans (lem-≤-suc k) p) validMoves

emptyBoard : Maybe Board
emptyBoard = buildBoard 2 (s≤s (s≤s z≤n)) (P1 ∷ P2 ∷ [])

lemma : emptyBoard ≢ nothing
lemma ()

empty : Board
empty with inspect emptyBoard
empty | just x  with-≡ eq = x
empty | nothing with-≡ eq = ⊥-elim (lemma eq)

moves : Board → List Move
moves (board k y validMoves conts) = validMoves

func : (b : Board) → (m : Move) → m ∈ moves b → Maybe Board
func (board k y validMoves conts) = conts

{-
emptyBoard : Board
emptyBoard = board 0 z≤n (P1 ∷ P2 ∷ []) aux where
  aux : (m : Move) → m ∈ P1 ∷ P2 ∷ [] → Board
  aux .P1 ∈-take = board 1 (s≤s z≤n) [ P2 ] {!!}
  aux .P2 (∈-drop ∈-take) = {!!}
  aux m (∈-drop (∈-drop ()))
-}

{-
mutual
  allTheWay : (b : Board) → List Board
  allTheWay (board k zero    y validMoves conts) = []
  allTheWay (board k (suc n) y [] conts) = []
  allTheWay (board k (suc n) y (x ∷ xs) conts) = allTheWay (conts x ∈-take)

  iter : List Board → List Board → List Board
  iter acc [] = acc
  iter acc (x ∷ xs) = iter (allTheWay x ++ acc) xs

-}