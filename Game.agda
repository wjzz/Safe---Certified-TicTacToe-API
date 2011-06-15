{- This file defines and implements a safe and certified TicTacToe API.
  For some theorems about the properties of TicTacToe see the Theory.agda file.
  
  All contents of the GameImplementation module (exluding the game record) should be private,
  but that prevents us from proving theories about it in other modules should they need to 
  expose the implementation details. For a version with the private section see the 
  StrongSpec.agda file.
-}

module Game where

open import Data.Maybe
open import Data.Bool
open import Data.List
open import Data.List.Theorems
open import Data.Nat renaming (_≟_ to _≟ℕ_; _⊔_ to max)
open import Data.Nat.Theorems
open import Data.Product
open import Data.Sum

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

{- BASE IMPORT Data.Nat.Theorems  -}
{- BASE IMPORT Data.List.Theorems -}

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

-- decidable equality on moves

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

------------------------
--  The result type   --
------------------------

data Result : Set where
  Win  : (c : Color) → Result
  Draw : Result

-------------------------------------------------------------------------
--  The public API that will guarantee the properties we want to have  --
-------------------------------------------------------------------------

record GameInterface : Set₁ where
  field 

  -- abstract types

    Board         : Set
    FinishedBoard  : Set

  -- operations

    emptyBoard      : Board
    isEmpty         : Board → Bool
    currentPlayer   : Board → Color

    getResult       : FinishedBoard → Result

    undo            : Board         → Maybe Board
    undoFin         : FinishedBoard → Board

    validMoves      : Board → List Move
    isMovePossible? : Board → Move → Bool
    makeMove        : (b : Board) → (m : Move) → m ∈ validMoves b → Board ⊎ FinishedBoard
  
  -- properties

    empty-is-empty   : isEmpty emptyBoard       ≡ true
    starting-player  : currentPlayer emptyBoard ≡ X
    no-undo-empty    : undo     emptyBoard      ≡ nothing

    valid-possible-l : ∀ (b : Board) (m : Move) → isMovePossible? b m ≡ true → m ∈ validMoves b
    valid-possible-r : ∀ (b : Board) (m : Move) → m ∈ validMoves b → isMovePossible? b m ≡ true

    undo-make-move   : ∀ (b b' : Board) (m : Move) (vld : m ∈ validMoves b) →
                                 makeMove b m vld ≡ inj₁ b' → undo b' ≡ just b

  -- additional properties
    all-possible     : validMoves emptyBoard ≡ allMoves

    undo-make-move2  : ∀ (b : Board) (f : FinishedBoard) (m : Move) (vld : m ∈ validMoves b) →
                                 makeMove b m vld ≡ inj₂ f → undoFin f ≡ b


-----------------------------------------------------------------------------------------------------------------
--  An implementation of the TicTacToe game system that will reify the API and provide many static guarantees  --
-----------------------------------------------------------------------------------------------------------------

module GameImplementation where
  --private

  -----------------------------------------------------------------
  -- the moves type
  --
  -- A list of moves augmented with the color of the player to move 
  -- and the number of moves already played
  -----------------------------------------------------------------

  data Moves : (currPlayer : Color) → (n : ℕ) → Set where
    []  : Moves X 0
    _▸_ : {c : Color} {n : ℕ} → (ms : Moves c n) → (m : Move) → Moves (otherColor c) (suc n)
  

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

  movesToList-length : ∀ {currPlayer : Color}{n : ℕ} (m : Moves currPlayer n) → length (movesToList m) ≡ n
  movesToList-length [] = refl
  movesToList-length (ms ▸ m) = cong suc (movesToList-length ms)

  -- moves membership relation

  infix 4 _∈′_

  data _∈′_ : {c : Color}{n : ℕ} → Move → Moves c n → Set where
    ∈-take : {c : Color}{n : ℕ} {m : Move} {ms : Moves c n} → m ∈′ ms ▸ m
    ∈-drop : {c : Color}{n : ℕ} {m m0 : Move} {ms : Moves c n} → m ∈′ ms → m ∈′ ms ▸ m0
  
  infix 4 _∉′_

  _∉′_ : {c : Color}{n : ℕ} → Move → Moves c n → Set
  _∉′_ m ms = ¬ (m ∈′ ms)

  lem-∈′-neq : ∀ {c : Color}{n : ℕ} → (m1 m2 : Move) → (ms : Moves c n) → m1 ≢ m2 → ¬ (m1 ∈′ ms) → ¬ (m1 ∈′ ms ▸ m2)
  lem-∈′-neq .m2 m2 ms neq nin ∈-take = neq refl
  lem-∈′-neq m1 m2 ms neq nin (∈-drop y) = nin y

  member′ : {c : Color}{n : ℕ} → (m : Move) → (ms : Moves c n) → Dec (m ∈′ ms)
  member′ m [] = no (λ ())
  member′ m (ms ▸ m0) with m == m0
  ... | yes p rewrite p = yes ∈-take
  ... | no ¬p with member′ m ms
  ... | yes p' = yes (∈-drop p')
  ... | no ¬p' = no (lem-∈′-neq m m0 ms ¬p ¬p')
    
  -- the relation with the list ∈

  movesToList-in : ∀ {currPlayer : Color}{n : ℕ} (ms : Moves currPlayer n) (m : Move) → m ∈′ ms → m ∈ movesToList ms
  movesToList-in .(ms ▸ m) m (∈-take {c} {n} {.m} {ms}) = ∈-take
  movesToList-in .(ms ▸ m0) m (∈-drop {c} {n} {.m} {m0} {ms} y) = ∈-drop (movesToList-in ms m y)

  -- selectors by color

  xMoves : {c : Color}{n : ℕ} → Moves c n → List Move
  xMoves [] = []
  xMoves (_▸_ {X} ms m) = m ∷ xMoves ms
  xMoves (_▸_ {O} ms m) = xMoves ms
  
  oMoves : {c : Color}{n : ℕ} → Moves c n → List Move
  oMoves [] = []
  oMoves (_▸_ {X} ms m) = oMoves ms
  oMoves (_▸_ {O} ms m) = m ∷ oMoves ms

  winningPositions : List (List Move)
  winningPositions = (P11 ∷ P12 ∷ P13 ∷ []) ∷                        -- horizontal
                     (P21 ∷ P22 ∷ P23 ∷ []) ∷ 
                     (P31 ∷ P32 ∷ P33 ∷ []) ∷ 
                   
                     (P11 ∷ P21 ∷ P31 ∷ []) ∷                        -- vertical
                     (P12 ∷ P22 ∷ P32 ∷ []) ∷ 
                     (P13 ∷ P23 ∷ P33 ∷ []) ∷ 

                     (P11 ∷ P22 ∷ P33 ∷ []) ∷                        -- diagonal
                     (P13 ∷ P22 ∷ P31 ∷ []) ∷ 
                     []

  movesByColor : forall {c0 n} → (c : Color) → (m : Moves c0 n) → List Move
  movesByColor X m = xMoves m
  movesByColor O m = oMoves m

  lem-same-color : ∀ {n} (cand : Color) → (m : Move) (ms : Moves (otherColor cand) n) → movesByColor cand ms ≡ movesByColor cand (ms ▸ m)
  lem-same-color X m ms = refl
  lem-same-color O m ms = refl

  lem-other-color : ∀ {n} (cand : Color) → (m : Move) (ms : Moves cand n) → m ∷ movesByColor cand ms ≡ movesByColor cand (ms ▸ m)
  lem-other-color X m ms = refl
  lem-other-color O m ms = refl

  lem-movesByColor-ext : ∀ {c n} (cand : Color) → (m : Move) (ms : Moves c n) → movesByColor cand ms ⊂ movesByColor cand (ms ▸ m)
  lem-movesByColor-ext {X} X m ms = lem-⊂-ext m (xMoves ms) (xMoves ms) (⊂-refl (xMoves ms))
  lem-movesByColor-ext {O} X m ms = ⊂-refl (xMoves ms)
  lem-movesByColor-ext {X} O m ms = ⊂-refl (oMoves ms)
  lem-movesByColor-ext {O} O m ms = lem-⊂-ext m (oMoves ms) (oMoves ms) (⊂-refl (oMoves ms))

  {- BASE subset lem-movesByColor-ext -}

  -------------------------
  --  winning positions  --
  -------------------------

  data WonC : forall {c n} → (winner : Color) (ms : Moves c n) → Set where
    wonC : ∀ {c n winner} → (m : Moves c n) → (winning : List Move) →
             winning ∈ winningPositions → 
             winning ⊂ movesByColor winner m →
             WonC winner m              
  
  noWinner : forall {c n} → Moves c n → Set
  noWinner b = (¬ WonC X b) × (¬ WonC O b)
                                        
  lem-won-empty : ∀ (c : Color) → ¬ WonC c []
  lem-won-empty c (wonC .[] .[] (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ())))))))) nil)
  lem-won-empty X (wonC .[] .(m ∷ ms) y (cons {m} {ms} y' ()))
  lem-won-empty O (wonC .[] .(m ∷ ms) y (cons {m} {ms} y' ()))

  lem-win-extend : ∀ {c n} → (winner : Color)(ms : Moves c n) → (m : Move) → WonC winner ms → WonC winner (ms ▸ m)
  lem-win-extend winner ms m (wonC .ms winning winningPosition winnning∈movesByClr) 
    = wonC (ms ▸ m) winning winningPosition (⊂-trans winning (movesByColor winner ms)
         (movesByColor winner (ms ▸ m)) winnning∈movesByClr (lem-movesByColor-ext winner m ms))

  lem-nowin-prev : ∀ {c n} → (winner : Color)(ms : Moves c n) → (m : Move) → ¬ WonC winner (ms ▸ m) → ¬ WonC winner ms
  lem-nowin-prev winner ms m x x' = x (lem-win-extend winner ms m x')
    
  {- BASE won lem-won-empty lem-nowin-prev lem-win-extend -}


  P : forall {c n} → Color → Moves c n → List Move → Set
  P cand ms winConfig = winConfig ⊂ movesByColor cand ms

  decP : forall {c n} → (cand : Color) → (ms : Moves c n) → (x : List Move) → Dec (x ⊂ movesByColor cand ms)
  decP cand ms l = subsetDec l (movesByColor cand ms) _==_

  wonDec : forall {c n} → (cand : Color) → (ms : Moves c n) → Dec (WonC cand ms)
  wonDec cand ms with any-dec (P cand ms) winningPositions (decP cand ms)
  wonDec cand ms | yes p with lem-any-exists (P cand ms) winningPositions p
  ... | winningPosition , inWinning , movesSubset = yes (wonC ms winningPosition inWinning movesSubset)
  wonDec cand ms | no ¬p with lem-none-exists (P cand ms) winningPositions ¬p
  ... | noWinningPosition = no lem where
    lem : (x : WonC cand ms) → ⊥
    lem (wonC .ms winning y y') = noWinningPosition (winning , y , y')

  --------------------------------
  --    Every move is unique    --
  --------------------------------

  -- a list is distinct iff all moves are unique

  data distinctm : {c : Color}{n : ℕ} → Moves c n → Set where
    dist-nil  : distinctm []
    dist-cons : {c : Color}{n : ℕ} → {m : Move}{ms : Moves c n} → (v : distinctm ms) → 
                            m ∉′ ms → distinctm (ms ▸ m)

  ----------------------------
  --  the WorkerBoard type  --
  ----------------------------

  -- this is the most general board type

  data WorkerBoard : Set where
    worker : {c : Color}{n : ℕ} → (n<9  : n < 9)                 -- at most all fields filled
                                → (ms   : Moves c n)             -- list of moves
                                → (dist : distinctm ms)           -- previous moves distinct
                                → (noWin : noWinner ms)          -- the games had no winner before m
                                → (m    : Move)                  -- the last move
                                → (v-m  : m ∉′ ms)               -- m is valid
                                → WorkerBoard
  
  -- basic queries
  wMovesNo : WorkerBoard → ℕ
  wMovesNo (worker {c} {n} n≤9 ms dist noWin m v-m) = suc n
    
  noWinnerW : WorkerBoard → Set
  noWinnerW (worker n<9 ms dist noWin m v-m) = noWinner (ms ▸ m)

  wonW : Color → WorkerBoard → Set
  wonW c (worker n<9 ms dist noWin m v-m) = WonC c (ms ▸ m)

  ----------------------
  --  the Board type  --
  ----------------------

  -- this type can be only constructed for situations
  -- where the game is still in progress
  
  data Board : Set where
    goodBoard : {c : Color}{n : ℕ} → (n<9   : n < 9)                 -- draw impossible
                                   → (ms    : Moves c n  )           -- moves so far
                                   → (dist  : distinctm ms)           -- everything ok so far
                                   → (noWin : noWinner ms)           -- no winner yet
                                   → Board

  -- most basic queries

  emptyBoard : Board
  emptyBoard = goodBoard (s≤s z≤n) [] dist-nil (lem-won-empty X , lem-won-empty O)

  isEmpty : Board → Bool
  isEmpty (goodBoard _ [] _ _)      = true
  isEmpty (goodBoard _ (_ ▸ _) _ _) = false

  movesNo : Board → ℕ
  movesNo (goodBoard {c} {n} _ _ _ _) = n

  currentPlayer : Board → Color
  currentPlayer (goodBoard {c} {n} y ms y' _) = c

  ----------------------------------------
  --  valid moves and their properties  --
  ----------------------------------------

  validMoves : Board → List Move
  validMoves (goodBoard n<9 ms dist noWin) = removeDec allMoves (λ move → member′ move ms)

  validMoves-distinct : ∀ {c n} → (m : Move) (ms : Moves c n) (n<9 : n < 9) (dist : distinctm ms) (noWin : noWinner ms)
                          → m ∈ validMoves (goodBoard {c} {n} n<9 ms dist noWin) → m ∉′ ms
  validMoves-distinct {c} {n} m ms n<9 dist noWin m∈valid m∈ms with removeDec-valid-rev allMoves (λ move → member′ move ms) m m∈valid
  validMoves-distinct m ms n<9 dist noWin m∈valid m∈ms | _ , ¬Pa  = ¬Pa m∈ms

  validMoves-distinct-rev : ∀ {c n m ms n<9 dist noWin} → m ∉′ ms → m ∈ validMoves (goodBoard {c} {n} n<9 ms dist noWin) 
  validMoves-distinct-rev {c} {n} {m} {ms} m∉ms = removeDec-valid allMoves (λ move → member′ move ms) m m∉ms (allMovesValid m)

  isMovePossible? : Board → Move → Bool
  isMovePossible? b m with member m (validMoves b) _==_
  isMovePossible? b m | yes p = true
  isMovePossible? b m | no ¬p = false

  -- relative validness of two ways to generate valid moves

  valid-possible-l : ∀ (b : Board) → (m : Move) → isMovePossible? b m ≡ true → m ∈ validMoves b
  valid-possible-l b m x with member m (validMoves b) _==_
  valid-possible-l b m x | yes p = p
  valid-possible-l b m () | no ¬p

  valid-possible-r : ∀ (b : Board) → (m : Move) → m ∈ validMoves b → isMovePossible? b m ≡ true
  valid-possible-r b m x with member m (validMoves b) _==_
  valid-possible-r b m x | yes p = refl
  valid-possible-r b m x | no ¬p = ⊥-elim (¬p x)

  ------------------------------
  --  The FinishedBoard type  --
  ------------------------------
    
  data FinishedBoard : Set where
    draw : (w : WorkerBoard) → noWinnerW w → wMovesNo w ≡ 9 → FinishedBoard
    win  : (c : Color) (w : WorkerBoard) → wonW c w → FinishedBoard

  getResult : FinishedBoard → Result
  getResult (draw _ _ _)  = Draw
  getResult (win c _ _)   = Win c    

  -- adding a given move

  addMove : (b : Board) → (m : Move) → (p : m ∈ validMoves b) → WorkerBoard
  addMove (goodBoard {c} {n} n<9 ms dist noWin) m p = worker n<9 ms dist noWin m (validMoves-distinct m ms n<9 dist noWin p)

  makeMoveWorker : WorkerBoard → Board ⊎ FinishedBoard
  makeMoveWorker (worker n<9 ms dist noWin m v-m) with wonDec X (ms ▸ m)
  makeMoveWorker (worker n<9 ms dist noWin m v-m) | yes xWin = inj₂ (win X (worker n<9 ms dist noWin m v-m) xWin)
  makeMoveWorker (worker n<9 ms dist noWin m v-m) | no ¬xWin with wonDec O (ms ▸ m)
  makeMoveWorker (worker n<9 ms dist noWin m v-m) | no ¬xWin | yes oWin = inj₂ (win O (worker n<9 ms dist noWin m v-m) oWin)
  makeMoveWorker (worker {c} {n} n<9 ms dist noWin m v-m) | no ¬xWin | no ¬oWin with suc n ≟ℕ 9
  makeMoveWorker (worker n<9 ms dist noWin m v-m) | no ¬xWin | no ¬oWin | yes d = inj₂ (draw (worker n<9 ms dist noWin m v-m) (¬xWin , ¬oWin) d)
  makeMoveWorker (worker {c} {n} n<9 ms dist noWin m v-m) | no ¬xWin | no ¬oWin | no ¬d 
    = inj₁ (goodBoard (lem-≤-cases-ext (suc n) 9 n<9 ¬d) (ms ▸ m) (dist-cons dist v-m) (¬xWin , ¬oWin))

  makeMove : (b : Board) → (m : Move) → m ∈ validMoves b → Board ⊎ FinishedBoard
  makeMove b m m∈valid = makeMoveWorker (addMove b m m∈valid)

  --------------------------------------
  --  Operations concerned with undo  --
  --------------------------------------
  
  undo : (b : Board) → Maybe Board
  undo (goodBoard n<9 [] dist noWin) = nothing
  undo (goodBoard n<9 (_▸_ {c} {n} ms m) (dist-cons v y) (noWinX , noWinO)) = just (goodBoard (lem-≤-trans (s≤s (lem-≤-suc n)) n<9) ms v 
       ((lem-nowin-prev X ms m noWinX) , lem-nowin-prev O ms m noWinO))

  undoFin : (fin : FinishedBoard) → Board
  undoFin (draw (worker n<9 ms dist noWin m v-m) y y') = goodBoard n<9 ms dist noWin
  undoFin (win c (worker n<9 ms dist noWin m v-m) y)   = goodBoard n<9 ms dist noWin
 
  -- I think I can't prove this irrevelence lemma, so I took it as an axiom
  postulate
    lem-noWin-irrelv : ∀ {c n} → (cand : Color) (m : Move) → (ms : Moves c n) 
                       → (f1 : ¬ WonC cand ms) → (f2 : ¬ WonC cand ms) → f1 ≡ f2


  undo-make-move : (b b' : Board) (m : Move) (vld : m ∈ validMoves b) →
                   makeMove b m vld ≡ inj₁ b' → undo b' ≡ just b
  undo-make-move (goodBoard n<9 ms dist noWin) b' m vld x with wonDec X (ms ▸ m)
  undo-make-move (goodBoard n<9 ms dist noWin) b' m vld () | yes p
  undo-make-move (goodBoard n<9 ms dist noWin) b' m vld x | no ¬p with wonDec O (ms ▸ m)
  undo-make-move (goodBoard n<9 ms dist noWin) b' m vld () | no ¬p | yes p
  undo-make-move (goodBoard {c} {n} n<9 ms dist noWin) b' m vld x | no ¬p' | no ¬p with suc n ≟ℕ 9
  undo-make-move (goodBoard n<9 ms dist noWin) b' m vld () | no ¬p' | no ¬p | yes p
  undo-make-move (goodBoard {c} {n} n<9 ms dist noWin) b' m vld x | no ¬p0 | no ¬p' | no ¬p with lem-≤-cases-ext (suc n) 9 n<9 ¬p
  undo-make-move (goodBoard n<9 ms dist (noWinX , noWinO)) 
                 .(goodBoard lem (ms ▸ m) (dist-cons dist (validMoves-distinct m ms n<9 dist (noWinX , noWinO) vld)) (¬p0 , ¬p')) 
                 m vld refl | no ¬p0 | no ¬p' | no ¬p | lem 
             = cong₂ (λ l1 l2 → just (goodBoard l1 ms dist l2)) lem-≤-irrelv 
               (cong₂ _,_ (lem-noWin-irrelv X m ms (λ x' → ¬p0 (lem-win-extend X ms m x')) noWinX) 
                          (lem-noWin-irrelv O m ms (λ x' → ¬p' (lem-win-extend O ms m x')) noWinO))


  undo-make-move2 : ∀ (b : Board) (f : FinishedBoard) (m : Move) (vld : m ∈ validMoves b) →
                           makeMove b m vld ≡ inj₂ f → undoFin f ≡ b
  undo-make-move2 (goodBoard n<9 ms dist noWin) f m vld x with wonDec X (ms ▸ m)
  undo-make-move2 (goodBoard n<9 ms dist noWin) .(win X (worker n<9 ms dist noWin m (validMoves-distinct m ms n<9 dist noWin vld)) p) 
                                                  m vld refl | yes p = refl
  undo-make-move2 (goodBoard n<9 ms dist noWin) f m vld x | no ¬p with wonDec O (ms ▸ m)
  undo-make-move2 (goodBoard n<9 ms dist noWin) .(win O (worker n<9 ms dist noWin m (validMoves-distinct m ms n<9 dist noWin vld)) p) 
                                                m vld refl | no ¬p | yes p = refl
  undo-make-move2 (goodBoard {c} {n} n<9 ms dist noWin) f m vld x | no ¬p' | no ¬p with suc n ≟ℕ 9
  undo-make-move2 (goodBoard n<9 ms dist noWin) .(draw (worker n<9 ms dist noWin m (validMoves-distinct m ms n<9 dist noWin vld)) (¬p' , ¬p) p) 
                                                m vld refl | no ¬p' | no ¬p | yes p = refl
  undo-make-move2 (goodBoard n<9 ms dist noWin) f m vld () | no ¬p0 | no ¬p' | no ¬p


  game : GameInterface
  game = record {
           Board            = Board;
           FinishedBoard    = FinishedBoard;
           emptyBoard       = emptyBoard;
           isEmpty          = isEmpty;
           currentPlayer    = currentPlayer;
           getResult        = getResult;
           undoFin          = undoFin;
           undo             = undo;
           validMoves       = validMoves;
           isMovePossible?  = isMovePossible?;
           makeMove         = makeMove;
           empty-is-empty   = refl;
           starting-player  = refl;
           no-undo-empty    = refl;
           all-possible     = refl;
           valid-possible-l = valid-possible-l;
           valid-possible-r = valid-possible-r;
           undo-make-move   = undo-make-move;
           undo-make-move2  = undo-make-move2
         }


-- make all fields visible
open GameInterface (GameImplementation.game)

brd : Board
brd = emptyBoard

empt : Bool
empt = isEmpty emptyBoard

{-
t : Maybe Result
t = GameImplementation.bestResultColor 9 X (inj₁ emptyBoard)

t2 : Maybe Result
t2 = GameImplementation.bestResultColor 5 X (inj₁ emptyBoard)

{-
this type checks after around 30 minutes

lemma : t2 ≡ just (Win 
lemma = refl

-}

b : Board ⊎ FinishedBoard 
b = GameImplementation.tryMoves (inj₁ emptyBoard) (P11 {- ∷ P12 ∷ P13 ∷ P21  ∷ P22 ∷ P23 ∷ P31 -} ∷ [])

b2 : Bool
b2 with b
... | inj₁ _ = true
... | inj₂ _ = false

leaves : ℕ
leaves = GameImplementation.leavesNo --(GameImplementation.generateTree (inj₁ emptyBoard)) -- 
         (GameImplementation.generateTree b)
-}
{-
r : Result
r = GameImplementation.bestResultOpt (inj₁ emptyBoard) -- (GameImplementation.tryMoves (inj₁ emptyBoard) (P11 ∷ []))
-}
--n : Maybe ℕ
--n = GameImplementation.depthM (GameImplementation.generateTree b)