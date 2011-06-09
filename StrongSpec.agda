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

{- BASE IMPORT Data.Nat.Theorems -}

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
    UndoableBoard : Set

  -- operations

    emptyBoard      : Board
    isEmpty         : Board → Bool
    currentPlayer   : Board → Color

    getResult       : FinishedBoard → Result

    canUndo?        : Board         → Maybe UndoableBoard
    undoFin         : FinishedBoard  → UndoableBoard
    undo            : UndoableBoard → Board

    validMoves      : Board → List Move
    isMovePossible? : Board → Move → Bool
    makeMove        : (b : Board) → (m : Move) → m ∈ validMoves b → Board ⊎ FinishedBoard
  
  -- properties

    empty-is-empty   : isEmpty emptyBoard       ≡ true
    starting-player  : currentPlayer emptyBoard ≡ X
    no-undo-empty    : canUndo? emptyBoard      ≡ nothing

    valid-possible-l : ∀ {b m} → isMovePossible? b m ≡ true → m ∈ validMoves b
    valid-possible-r : ∀ {b m} → m ∈ validMoves b           → isMovePossible? b m ≡ true

    undo-make-move   : ∀ {b b' m} → (vld : m ∈ validMoves b) → makeMove b m vld ≡ inj₁ b' 
                                  → ∃ (λ undoableBoard → (canUndo? b' ≡ just undoableBoard) × (undo undoableBoard ≡ b))

  -- Agda's way to simulate
  -- Haskell's type classes

  data Undoable : Set where
    B : Undoable
    F : Undoable

  interp : Undoable → Set
  interp B = Board
  interp F = FinishedBoard

  undo? : {t : Undoable} → interp t → Maybe UndoableBoard
  undo? {B} = canUndo?
  undo? {F} = λ f → just (undoFin f)

------------------------------------------------------------------------------------------------------------------
--  An implementation of the TicTacToe game system that will reify the API and provide many static guarantress  --
------------------------------------------------------------------------------------------------------------------

module GameImplementation where
  private

    --------------------------------------------------------------
    -- the moves type
    --
    -- A list of moves augmented with the color of player to move 
    -- and the number of moves already played
    --------------------------------------------------------------

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
    xMoves (_▸_ {X} ms m) = xMoves ms
    xMoves (_▸_ {O} ms m) = m ∷ xMoves ms
  
    oMoves : {c : Color}{n : ℕ} → Moves c n → List Move
    oMoves [] = []
    oMoves (_▸_ {X} ms m) = m ∷ oMoves ms
    oMoves (_▸_ {O} ms m) = oMoves ms

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

    -- winning positions

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

    {- BASE won lem-won-empty -}

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
  
    wMovesNo : WorkerBoard → ℕ
    wMovesNo (worker {c} {n} n≤9 ms dist) = n

    wIsEmpty : WorkerBoard → Bool
    wIsEmpty (worker n≤9 [] dist)       = true
    wIsEmpty (worker n≤9 (ms ▸ m) dist) = false

    ----------------------
    --  the Board type  --
    ----------------------

    -- this type can be only constructed for situations
    -- where the game is still in progress
  
    data Board : Set where
      goodBoard : {c : Color}{n : ℕ} → (n<9  : n < 9)                  -- draw impossible
                                     → (ms   : Moves c n  )            -- moves so far
                                     → (dist : distinct ms)            -- everything ok so far
                                     → (noWin : noWinner ms)           -- no winner yet
                                     → Board

    -- most basic queries

    emptyBoard : Board
    emptyBoard = goodBoard (s≤s z≤n) [] dist-nil (lem-won-empty X , lem-won-empty O)

    isEmpty : Board → Bool
    isEmpty (goodBoard _ [] _ _)      = true
    isEmpty (goodBoard _ (_ ▸ _) _ _) = false

    movesNo : Board → ℕ
    movesNo (goodBoard {c} {n} y ms y' _) = n

    currentPlayer : Board → Color
    currentPlayer (goodBoard {c} {n} y ms y' _) = c

    -- conversion to worker

    toWorker : Board → WorkerBoard
    toWorker (goodBoard {c} {n} n<9 ms dist noWin) = worker (lem-≤-trans (lem-≤-suc n) n<9) ms dist

    toWorker-valid : ∀ (b : Board) → movesNo b ≡ wMovesNo (toWorker b)
    toWorker-valid (goodBoard n<9 ms dist noWin) = refl

    -- checking if there is a winner

    wonByColor : Color → Board → Bool
    wonByColor c (goodBoard n<9 ms dist noWin) with wonDec c ms
    ... | yes p = true
    ... | no ¬p = false

    data Won : (c : Color) (b : Board) → Set where
      won : {c : Color} {b : Board} → wonByColor c b ≡ true → Won c b

    data FinishedBoard : Set where
      draw : (b : Board)             → movesNo b ≡ 9 → FinishedBoard
      win  : (c : Color) (b : Board) → Won c b       → FinishedBoard

    getResult : FinishedBoard → Result
    getResult (draw b y)  = Draw
    getResult (win c b y) = Win c

    validMoves : Board → List Move
    validMoves b = [] -- TO FIX!!

    -- the code below is totally wrong, we need to add the move m before any other matching!!!
    -- TO FIX!!
    makeMove : (b : Board) → (m : Move) → m ∈ validMoves b → Board ⊎ FinishedBoard
    makeMove b m valid with inspect (wonByColor X b)
    makeMove b m valid | true with-≡ eq = inj₂ (win X b (won eq))
    makeMove b m valid | false with-≡ eq with inspect (wonByColor O b)
    makeMove b m valid | false with-≡ eq | true with-≡ eq' = inj₂ (win O b (won eq'))
    makeMove b m valid | false with-≡ eq | false with-≡ eq' with movesNo b ≟ℕ 9
    makeMove b m valid | false with-≡ eq | false with-≡ eq' | yes p = inj₂ (draw {!!} p)
    makeMove b m valid | false with-≡ eq | false with-≡ eq' | no ¬p = {!!}

    ------------------------------
    --  the UndoableBoard type  --
    ------------------------------

    data UndoableBoard : Set where
      undoable : Σ[ b ∶ WorkerBoard ] (wIsEmpty b ≡ false) → UndoableBoard

    canUndo? : (b : Board) → Maybe UndoableBoard
    canUndo? (goodBoard n<9 [] dist noWin)       = nothing
    canUndo? (goodBoard n<9 (ms ▸ m) dist noWin) = just (undoable (toWorker (goodBoard n<9 (ms ▸ m) dist noWin) , refl))


    lem-non-zero-means-not-empty : ∀ (b : WorkerBoard) → 0 < wMovesNo b → wIsEmpty b ≡ false
    lem-non-zero-means-not-empty (worker {c} {zero} n≤9 ms dist) ()
    lem-non-zero-means-not-empty (worker {.(otherColor c)} {suc .n} n≤9 (_▸_ {c} {n} ms m) dist) (s≤s m≤n) = refl

    undoFin : (fin : FinishedBoard) → UndoableBoard
    undoFin (draw b y) rewrite toWorker-valid b = undoable (toWorker b , lem-non-zero-means-not-empty (toWorker b) 
                                                  (subst (λ x → 1 ≤ x) (sym y) (s≤s z≤n)))
    undoFin (win c b y) = undoable (toWorker b , {!!})


    undo : (ub : UndoableBoard) → Board
    undo (undoable (worker n≤9 [] dist , ()))
    undo (undoable (worker n≤9 (ms ▸ m) (dist-cons v y) , nonEmpt)) = goodBoard n≤9 ms v {!!}

    undo-valid : ∀ (w : WorkerBoard) → (nonEmpt : wIsEmpty w ≡ false) → 
                       suc (movesNo (undo (undoable (w , nonEmpt)))) ≡ wMovesNo w
    undo-valid (worker n≤9 [] dist) ()
    undo-valid (worker n≤9 (ms ▸ m) (dist-cons v y)) nonEmpt = refl



  game : GameInterface
  game = record {
           Board            = Board;
           FinishedBoard    = FinishedBoard;
           UndoableBoard    = UndoableBoard;
           emptyBoard       = emptyBoard;
           isEmpty          = isEmpty;
           currentPlayer    = currentPlayer;
           getResult        = getResult;
           canUndo?         = canUndo?;
           undoFin          = undoFin;
           undo             = undo;
           validMoves       = validMoves;
           isMovePossible?  = {!!};
           makeMove         = makeMove;
           empty-is-empty   = refl;
           starting-player  = refl;
           no-undo-empty    = {!!};
           valid-possible-l = {!!};
           valid-possible-r = {!!};
           undo-make-move   = {!!} 
         }

module Test where
  open GameInterface (GameImplementation.game) public

open Test

brd : Board
brd = emptyBoard

empt : Bool
empt = isEmpty emptyBoard

