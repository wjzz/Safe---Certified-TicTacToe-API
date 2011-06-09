module StrongSpec where

open import Data.Maybe
open import Data.Bool
open import Data.List
open import Data.List.Theorems
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Nat.Theorems
open import Data.Product
open import Data.Sum

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

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


-----------------------------------------------------------------------------------------------------------------
--  An implementation of the TicTacToe game system that will reify the API and provide many static guarantees  --
-----------------------------------------------------------------------------------------------------------------

module GameImplementation where
  private

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

    data distinct : {c : Color}{n : ℕ} → Moves c n → Set where
      dist-nil  : distinct []
      dist-cons : {c : Color}{n : ℕ} → {m : Move}{ms : Moves c n} → (v : distinct ms) → 
                            m ∉′ ms → distinct (ms ▸ m)

    ----------------------------
    --  the WorkerBoard type  --
    ----------------------------

    -- this is the most general board type

    data WorkerBoard : Set where
      worker : {c : Color}{n : ℕ} → (n≤9  : n ≤ 9)                 -- at most all fields filled
                                  → (ms   : Moves c n)             -- list of moves
                                  → (dist : distinct ms)           -- all moves distinct
                                  → WorkerBoard
  
    -- basic queries

    wMoves : WorkerBoard → ∃₂ Moves
    wMoves (worker {c} {n} n≤9 ms dist) = c , n , ms

    wMovesNo : WorkerBoard → ℕ
    wMovesNo (worker {c} {n} n≤9 ms dist) = n

    wIsEmpty : WorkerBoard → Bool
    wIsEmpty (worker n≤9 [] dist)       = true
    wIsEmpty (worker n≤9 (ms ▸ m) dist) = false

    noWinnerW : WorkerBoard → Set
    noWinnerW (worker n≤9 ms dist) = noWinner ms

    wonW : Color → WorkerBoard → Set
    wonW c (worker n≤9 ms dist) = WonC c ms

    ----------------------
    --  the Board type  --
    ----------------------

    -- this type can be only constructed for situations
    -- where the game is still in progress
  
    data Board : Set where
      goodBoard : {c : Color}{n : ℕ} → (n<9   : n < 9)                 -- draw impossible
                                     → (ms    : Moves c n  )           -- moves so far
                                     → (dist  : distinct ms)           -- everything ok so far
                                     → (noWin : noWinner ms)           -- no winner yet
                                     → Board

    -- most basic queries

    moves : Board → ∃₂ Moves
    moves (goodBoard {c} {n} n<9 ms dist noWin) = c , n , ms

    emptyBoard : Board
    emptyBoard = goodBoard (s≤s z≤n) [] dist-nil (lem-won-empty X , lem-won-empty O)

    isEmpty : Board → Bool
    isEmpty (goodBoard _ [] _ _)      = true
    isEmpty (goodBoard _ (_ ▸ _) _ _) = false

    movesNo : Board → ℕ
    movesNo (goodBoard {c} {n} y ms y' _) = n

    currentPlayer : Board → Color
    currentPlayer (goodBoard {c} {n} y ms y' _) = c

    noWinnerB : Board → Set
    noWinnerB (goodBoard n<9 ms dist noWin) = noWinner ms

    wonB : Color → Board → Set
    wonB c (goodBoard n<9 ms dist noWin) = WonC c ms

    -- conversion to worker

    toWorker : Board → WorkerBoard
    toWorker (goodBoard {c} {n} n<9 ms dist noWin) = worker (lem-≤-trans (lem-≤-suc n) n<9) ms dist

    toWorker-valid : ∀ (b : Board) → movesNo b ≡ wMovesNo (toWorker b)
    toWorker-valid (goodBoard n<9 ms dist noWin) = refl

    ----------------------------------------
    --  valid moves and their properties  --
    ----------------------------------------

    validMoves : Board → List Move
    validMoves (goodBoard n<9 ms dist noWin) = removeDec allMoves (λ move → member′ move ms)

    validMoves-distinct : ∀ {c n m ms n<9 dist noWin} → m ∈ validMoves (goodBoard {c} {n} n<9 ms dist noWin) → m ∉′ ms
    validMoves-distinct {c} {n} {m} {ms} m∈valid m∈ms with removeDec-valid-rev allMoves (λ move → member′ move ms) m m∈valid
    validMoves-distinct m∈valid m∈ms | _ , ¬Pa  = ¬Pa m∈ms

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
    addMove (goodBoard {c} {n} n<9 ms dist noWin) m p = worker n<9 (ms ▸ m) (dist-cons dist 
          (validMoves-distinct {c} {n} {m} {ms} {n<9} {dist} {noWin} p))    

    makeMoveWorker : WorkerBoard → Board ⊎ FinishedBoard
    makeMoveWorker (worker n≤9 ms dist) with wonDec X ms
    makeMoveWorker (worker n≤9 ms dist) | yes xWin = inj₂ (win X (worker n≤9 ms dist) xWin)
    makeMoveWorker (worker n≤9 ms dist) | no ¬xWin with wonDec O ms
    makeMoveWorker (worker n≤9 ms dist) | no ¬xWin | yes yWin = inj₂ (win O (worker n≤9 ms dist) yWin)
    makeMoveWorker (worker {c} {n} n≤9 ms dist) | no ¬xWin | no ¬yWin with n ≟ℕ 9
    makeMoveWorker (worker {c} {n} n≤9 ms dist) | no ¬xWin | no ¬yWin | yes d = inj₂ (draw (worker n≤9 ms dist) (¬xWin , ¬yWin) d)
    makeMoveWorker (worker {c} {n} n≤9 ms dist) | no ¬xWin | no ¬yWin | no ¬d = inj₁ (goodBoard (lem-≤-cases-ext n 9 n≤9 ¬d) ms dist (¬xWin , ¬yWin))

    makeMove : (b : Board) → (m : Move) → m ∈ validMoves b → Board ⊎ FinishedBoard
    makeMove b m m∈valid = makeMoveWorker (addMove b m m∈valid)

    --------------------------------------
    --  Operations concerned with undo  --
    --------------------------------------
  
    undo : (b : Board) → Maybe Board
    undo (goodBoard n<9 [] dist noWin) = nothing
    undo (goodBoard n<9 (ms ▸ m) (dist-cons v y) (noWinX , noWinO)) = just (goodBoard (lem-<-trans lem-≤-refl n<9) ms v 
         ((λ x → noWinX (lem-win-extend X ms m x)) , (λ x → noWinO (lem-win-extend O ms m x))))

    lem-non-zero-means-not-empty : ∀ {b : WorkerBoard} → 0 < wMovesNo b → wIsEmpty b ≡ false
    lem-non-zero-means-not-empty {worker {c} {zero} n≤9 ms dist} ()
    lem-non-zero-means-not-empty {worker {.(otherColor c)} {suc .n} n≤9 (_▸_ {c} {n} ms m) dist} (s≤s m≤n) = refl

    -- lemma: if won then wasn't empty
    undoFin : (fin : FinishedBoard) → Board
    undoFin (draw (worker n≤9 [] dist) (noWinX , noWinO) ())
    undoFin (draw (worker n≤9 (_▸_ {c} {n} ms m) (dist-cons v y)) (noWinX , noWinO) n≡9) = goodBoard n≤9 ms v 
          ((λ x → noWinX (lem-win-extend X ms m x)) , (λ x → noWinO (lem-win-extend O ms m x)))
    undoFin (win c (worker n≤9 [] dist) y) = ⊥-elim (lem-won-empty c y)
    undoFin (win winner (worker n≤9 (_▸_ {c} {n} ms m) (dist-cons v y)) y') = {!!}
    -- here we need to have a proof that ms had no winner
    -- we can either embed the proof somewhere, or try to prove that
    -- the construction so far guarantees that property
 
    undo-make-move : (b b' : Board) (m : Move) (vld : m ∈ validMoves b) →
                     makeMove b m vld ≡ inj₁ b' → undo b' ≡ just b
    undo-make-move b b' m vld x = {!!}




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
           valid-possible-l = valid-possible-l;
           valid-possible-r = valid-possible-r;
           undo-make-move   = undo-make-move 
         }

module Test where
  open GameInterface (GameImplementation.game) public

open Test

brd : Board
brd = emptyBoard

empt : Bool
empt = isEmpty emptyBoard

