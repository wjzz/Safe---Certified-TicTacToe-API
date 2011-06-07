module StrongSpec where

open import Data.Bool
open import Data.List
--open import Data.List.Theorems
open import Data.Nat
open import Data.Nat.Theorems
open import Data.Product
open import Data.Sum

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

--------------------
-- the color type
--------------------

data Color : Set where
  X O : Color


otherColor : Color → Color
otherColor X = O
otherColor O = X

otherColorValid : ∀ (c : Color) → otherColor c ≢ c
otherColorValid X ()
otherColorValid O ()

------------------------------------------------------------
-- list membership, a version with implicit args
-- (this makes proof much shorter)
--
-- adapted from Data.List.Theorems
-----------------------------------------------------------

infix 4 _∈_

data _∈_ {A : Set} : (a : A) → (xs : List A) → Set where
  ∈-take : {a : A}   → {xs : List A} → a ∈ a ∷ xs
  ∈-drop : {a x : A} → {xs : List A} → a ∈ xs → a ∈ x ∷ xs

-- if equality is decidable for A then list membership is decidable

member : {A : Set} → (a : A) → (l : List A) → Decidable {A = A} (_≡_) → Dec(a ∈ l)
member a [] eq = no (λ ())
member a (x ∷ xs) eq with inspect (eq a x)
member a (x ∷ xs) eq | yes p with-≡ eq' rewrite p = yes ∈-take
member a (x ∷ xs) eq | no ¬p with-≡ eq' with member a xs eq
member a (x ∷ xs) eq | no ¬p with-≡ eq' | yes p = yes (∈-drop p)
member a (x ∷ xs) eq | no ¬p' with-≡ eq' | no ¬p = no (imp a x xs ¬p ¬p') where
  imp : {A : Set}(a x : A)(xs : List A) → (¬ a ∈ xs) → (¬ a ≡ x) → ¬ a ∈ x ∷ xs
  imp .x' x' xs' ¬axs ¬ax (∈-take {.x'} {.xs'}) = ¬ax refl
  imp a' x' xs' ¬axs ¬ax (∈-drop {.a'} {.x'} {.xs'} y) = ¬axs y

-------------------
-- the move type
-------------------

data Move : Set where
  P11 P12 P13 : Move
  P21 P22 P23 : Move
  P31 P32 P33 : Move


-- a list of all possible moves

allMoves : List Move
allMoves = P11 ∷ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ []

allMovesValid : ∀ (m : Move) → m ∈ allMoves
allMovesValid P11 = ∈-take
allMovesValid P12 = ∈-drop ∈-take
allMovesValid P13 = ∈-drop (∈-drop ∈-take)
allMovesValid P21 = ∈-drop (∈-drop (∈-drop ∈-take))
allMovesValid P22 = ∈-drop (∈-drop (∈-drop (∈-drop ∈-take)))
allMovesValid P23 = ∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ∈-take))))
allMovesValid P31 = ∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ∈-take)))))
allMovesValid P32 = ∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ∈-take))))))
allMovesValid P33 = ∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ∈-take)))))))

-- decidable equality

_==_ : (m1 m2 : Move) → Dec (m1 ≡ m2)
P11 == P11 = yes refl
P11 == P12 = no (λ ())
P11 == P13 = no (λ ())
P11 == P21 = no (λ ())
P11 == P22 = no (λ ())
P11 == P23 = no (λ ())
P11 == P31 = no (λ ())
P11 == P32 = no (λ ())
P11 == P33 = no (λ ())
P12 == P11 = no (λ ())
P12 == P12 = yes refl
P12 == P13 = no (λ ())
P12 == P21 = no (λ ())
P12 == P22 = no (λ ())
P12 == P23 = no (λ ())
P12 == P31 = no (λ ())
P12 == P32 = no (λ ())
P12 == P33 = no (λ ())
P13 == P11 = no (λ ())
P13 == P12 = no (λ ())
P13 == P13 = yes refl
P13 == P21 = no (λ ())
P13 == P22 = no (λ ())
P13 == P23 = no (λ ())
P13 == P31 = no (λ ())
P13 == P32 = no (λ ())
P13 == P33 = no (λ ())
P21 == P11 = no (λ ())
P21 == P12 = no (λ ())
P21 == P13 = no (λ ())
P21 == P21 = yes refl
P21 == P22 = no (λ ())
P21 == P23 = no (λ ())
P21 == P31 = no (λ ())
P21 == P32 = no (λ ())
P21 == P33 = no (λ ())
P22 == P11 = no (λ ())
P22 == P12 = no (λ ())
P22 == P13 = no (λ ())
P22 == P21 = no (λ ())
P22 == P22 = yes refl
P22 == P23 = no (λ ())
P22 == P31 = no (λ ())
P22 == P32 = no (λ ())
P22 == P33 = no (λ ())
P23 == P11 = no (λ ())
P23 == P12 = no (λ ())
P23 == P13 = no (λ ())
P23 == P21 = no (λ ())
P23 == P22 = no (λ ())
P23 == P23 = yes refl
P23 == P31 = no (λ ())
P23 == P32 = no (λ ())
P23 == P33 = no (λ ())
P31 == P11 = no (λ ())
P31 == P12 = no (λ ())
P31 == P13 = no (λ ())
P31 == P21 = no (λ ())
P31 == P22 = no (λ ())
P31 == P23 = no (λ ())
P31 == P31 = yes refl
P31 == P32 = no (λ ())
P31 == P33 = no (λ ())
P32 == P11 = no (λ ())
P32 == P12 = no (λ ())
P32 == P13 = no (λ ())
P32 == P21 = no (λ ())
P32 == P22 = no (λ ())
P32 == P23 = no (λ ())
P32 == P31 = no (λ ())
P32 == P32 = yes refl
P32 == P33 = no (λ ())
P33 == P11 = no (λ ())
P33 == P12 = no (λ ())
P33 == P13 = no (λ ())
P33 == P21 = no (λ ())
P33 == P22 = no (λ ())
P33 == P23 = no (λ ())
P33 == P31 = no (λ ())
P33 == P32 = no (λ ())
P33 == P33 = yes refl


--------------------------------------------------------------
-- the moves type
--
-- A list of moves augmented with the color of player to move 
-- and the number of moves already played
--------------------------------------------------------------

data Moves : (currPlayer : Color) → (n : ℕ) → Set where
  []  : Moves X 0
  _▸_ : {c : Color} {n : ℕ} → Moves c n → Move → Moves (otherColor c) (suc n)


-- the relations between the parity of indexes and the current color

mutual
  lem-moves-even-parity-color : ∀ (c : Color) (n : ℕ) → (m : Moves c n) → Even n → c ≡ X
  lem-moves-even-parity-color .X .0 [] ev-0 = refl
  lem-moves-even-parity-color .(otherColor c) .(suc (suc n)) (_▸_ {c} y y') (ev-s {n} y0) with lem-moves-odd-parity-color c n y (odd y0)
  ... | rec rewrite rec = refl

  lem-moves-odd-parity-color : ∀ (c : Color) (n : ℕ) → (m : Moves c (suc n)) → Odd (suc n) → c ≡ O
  lem-moves-odd-parity-color .(otherColor c) n (_▸_ {c} y y') (odd y0) with lem-moves-even-parity-color c n y y0
  ... | rec rewrite rec = refl


-- a convertion to a list type, so we can hide the Moves type from the user

movesToList : {currPlayer : Color}{n : ℕ} → Moves currPlayer n → List Move
movesToList []          = []
movesToList (ms ▸ move) = move ∷ movesToList ms


xMoves : {c : Color}{n : ℕ} → Moves c n → List Move
xMoves [] = []
xMoves (_▸_ {X} ms m) = xMoves ms
xMoves (_▸_ {O} ms m) = m ∷ xMoves ms

oMoves : {c : Color}{n : ℕ} → Moves c n → List Move
oMoves [] = []
oMoves (_▸_ {X} ms m) = m ∷ oMoves ms
oMoves (_▸_ {O} ms m) = oMoves ms


--------------------------------------
-- the board and finished game types
--------------------------------------

data Result : Set where
  Win :   (c : Color) → Result
  Draw       : Result

module Game where
  private
    Board : Set
    Board = ∃₂ Moves
    
    FinishedGame : Set
    FinishedGame = Result × Board

  emptyBoard : Board
  emptyBoard = X , zero , []

  currentPlayer : Board → Color
  currentPlayer (currentColor , _ ) = currentColor

  moveList : Board → List Move
  moveList (_ , _ , ms) = movesToList ms  

  validMoves : Board → List Move
  validMoves b = []  

  isEmpty : Board → Bool
  isEmpty (.X , .0 , [])                                  = true
  isEmpty (.(otherColor c) , .(suc n) , _▸_ {c} {n} y y') = false  

  makeMove' : (b : Board) → {- valid b → -} Board ⊎ FinishedGame
  makeMove' = {!!}

  makeMove : (m : Move) → (b : Board) → (m ∈ validMoves b) → Board ⊎ FinishedGame
  makeMove move (c , n , ms) valid = makeMove' (otherColor c , suc n , ms ▸ move)


open Game

