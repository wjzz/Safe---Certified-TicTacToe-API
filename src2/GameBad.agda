{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module GameBad where

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

allMoves : Vec Move 9
allMoves = P11 ∷ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ []

allMovesValid : ∀ (m : Move) → m ∈ allMoves
allMovesValid P11 = here
allMovesValid P12 = there here
allMovesValid P13 = there (there here)
allMovesValid P21 = there (there (there here))
allMovesValid P22 = there (there (there (there here)))
allMovesValid P23 = there (there (there (there (there here))))
allMovesValid P31 = there (there (there (there (there (there here)))))
allMovesValid P32 = there (there (there (there (there (there (there here))))))
allMovesValid P33 = there (there (there (there (there (there (there (there here)))))))

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

  infixr 5 _∷_

  data Moves : (currPlayer : Color) → (n : ℕ) → Set where
    []  : Moves X 0
    _∷_ : {c : Color} {n : ℕ} → (m : Move) → (ms : Moves c n) → Moves (otherColor c) (suc n)
  

  -- moves membership relation

  infix 4 _∈'_

  data _∈'_ : {c : Color} {n : ℕ} → Move → Moves c n → Set where
    here    : {c : Color} {n : ℕ} {m    : Move} {ms : Moves c n} → m ∈' m ∷ ms
    there   : {c : Color} {n : ℕ} {m m' : Move} {ms : Moves c n} → m ∈' ms → m ∈' m' ∷ ms
  
  infix 4 _∉'_

  _∉'_ : {c : Color} {n : ℕ} → Move → Moves c n → Set
  _∉'_ m ms = ¬ (m ∈' ms)


  -- move membership is decidable

  lem-∈'-neq : ∀ {c : Color}{n : ℕ} → (m1 m2 : Move) → (ms : Moves c n) → m1 ≢ m2 → ¬ (m1 ∈' ms) → ¬ (m1 ∈' m2 ∷ ms)
  lem-∈'-neq .m2 m2 ms neq nin here = neq refl
  lem-∈'-neq m1 m2 ms neq nin (there y) = nin y

  member′ : {c : Color}{n : ℕ} → (m : Move) → (ms : Moves c n) → Dec (m ∈' ms)
  member′ m [] = no (λ ())
  member′ m (m' ∷ ms) with m == m'
  ... | yes p rewrite p = yes here
  ... | no ¬p with member′ m ms
  ... | yes p' = yes (there p')
  ... | no ¬p' = no (lem-∈'-neq m m' ms ¬p ¬p')


  -- selectors by color
  -- TODO: should we change the result type to Vec Move (something-related-to n/2)?

  xMoves : {c : Color} {n : ℕ} → Moves c n → List Move
  xMoves []             = []
  xMoves (_∷_ {X} m ms) = m ∷ xMoves ms
  xMoves (_∷_ {O} m ms) = xMoves ms
  
  oMoves : {c : Color} {n : ℕ} → Moves c n → List Move
  oMoves []             = []
  oMoves (_∷_ {X} m ms) = oMoves ms
  oMoves (_∷_ {O} m ms) = m ∷ oMoves ms
  
  -- we can write a version with a more precise type, but unfortunately
  -- the definitions become more complicated 
  -- (however, this way we don't need to write any proofs! 
  --   [because the structure is exactly the same ;-) ])

  colorwiseHalf : (c : Color) → (n : ℕ) → ℕ
  colorwiseHalf c zero          = 0
  colorwiseHalf X (suc zero)    = 1
  colorwiseHalf O (suc zero)    = 0
  colorwiseHalf c (suc (suc n)) = 1 + colorwiseHalf c n

  xMovesVec : {c : Color} {n : ℕ} → Moves c n → Vec Move (colorwiseHalf X n)
  xMovesVec []                         = []
  xMovesVec (m ∷ [])                   = m ∷ []
  xMovesVec {.O} (m ∷ (_∷_ {O} m' ms)) = m  ∷ xMovesVec ms
  xMovesVec {.X} (m ∷ (_∷_ {X} m' ms)) = m' ∷ xMovesVec ms

  oMovesVec : {c : Color} {n : ℕ} → Moves c n → Vec Move (colorwiseHalf O n)
  oMovesVec []                         = []
  oMovesVec (m ∷ [])                   = []
  oMovesVec {.O} (m ∷ (_∷_ {O} m' ms)) = m' ∷ oMovesVec ms
  oMovesVec {.X} (m ∷ (_∷_ {X} m' ms)) = m  ∷ oMovesVec ms

  movesByColor : forall {c0 n} → (c : Color) → (m : Moves c0 n) → List Move
  movesByColor X m = xMoves m
  movesByColor O m = oMoves m

  movesByColorVec : forall {c0 n} → (c : Color) → (m : Moves c0 n) → Vec Move (colorwiseHalf c n)
  movesByColorVec X m = xMovesVec m
  movesByColorVec O m = oMovesVec m

  lem-same-color : ∀ {n} (cand : Color) → (m : Move) (ms : Moves (otherColor cand) n) → movesByColor cand ms ≡ movesByColor cand (m ∷ ms)
  lem-same-color X m ms = refl
  lem-same-color O m ms = refl

  lem-other-color : ∀ {n} (cand : Color) → (m : Move) (ms : Moves cand n) → m ∷ movesByColor cand ms ≡ movesByColor cand (m ∷ ms)
  lem-other-color X m ms = refl
  lem-other-color O m ms = refl

  lem-movesByColor-ext : ∀ {c n} (cand : Color) → (m : Move) (ms : Moves c n) → movesByColor cand ms ⊂ movesByColor cand (m ∷ ms)
  lem-movesByColor-ext {X} X m ms = lem-⊂-ext m (xMoves ms) (xMoves ms) (⊂-refl (xMoves ms))
  lem-movesByColor-ext {O} X m ms = ⊂-refl (xMoves ms)
  lem-movesByColor-ext {X} O m ms = ⊂-refl (oMoves ms)
  lem-movesByColor-ext {O} O m ms = lem-⊂-ext m (oMoves ms) (oMoves ms) (⊂-refl (oMoves ms))

  -------------------------
  --  winning positions  --
  -------------------------

  -- winning configurations

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


  winningPositionsVec : Vec (Vec Move 3) _        -- using underscores can help if we change that one day
  winningPositionsVec = (P11 ∷ P12 ∷ P13 ∷ []) ∷                        -- horizontal 
                        (P21 ∷ P22 ∷ P23 ∷ []) ∷ 
                        (P31 ∷ P32 ∷ P33 ∷ []) ∷ 
                   
                        (P11 ∷ P21 ∷ P31 ∷ []) ∷                        -- vertical
                        (P12 ∷ P22 ∷ P32 ∷ []) ∷ 
                        (P13 ∷ P23 ∷ P33 ∷ []) ∷ 

                        (P11 ∷ P22 ∷ P33 ∷ []) ∷                        -- diagonal
                        (P13 ∷ P22 ∷ P31 ∷ []) ∷ 
                        []

  -- the won relation for the Moves type

  data WonC : forall {c n} → (winner : Color) (ms : Moves c n) → Set where
    wonC : ∀ {c n winner} → (m : Moves c n) → (winning : List Move) →
             winning ∈-list winningPositions → 
             winning ⊂ movesByColor winner m →
             WonC winner m              
  
  noWinner : forall {c n} → Moves c n → Set
  noWinner b = (¬ WonC X b) × (¬ WonC O b)

  -- basic properties 
                                        
  lem-won-empty : ∀ (c : Color) → ¬ WonC c []
  lem-won-empty c (wonC .[] .[] (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ())))))))) nil)
  lem-won-empty X (wonC .[] .(m ∷ ms) y (cons {m} {ms} y' ()))
  lem-won-empty O (wonC .[] .(m ∷ ms) y (cons {m} {ms} y' ()))

  lem-win-extend : ∀ {c n} → (winner : Color) (ms : Moves c n) → (m : Move) → WonC winner ms → WonC winner (m ∷ ms)
  lem-win-extend winner ms m (wonC .ms winning winningPosition winnning∈movesByClr) 
    = wonC (m ∷ ms) winning winningPosition (⊂-trans winnning∈movesByClr (lem-movesByColor-ext winner m ms))

  lem-nowin-prev : ∀ {c n} → (winner : Color)(ms : Moves c n) → (m : Move) → ¬ WonC winner (m ∷ ms) → ¬ WonC winner ms
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

  ------------------------------------------------------
  --  A relation that forces every move to be unique  --
  ------------------------------------------------------

  -- a moves list is distinct iff all moves are unique

  data distinct-m : {c : Color} {n : ℕ} → Moves c n → Set where
    dist-nil  : distinct-m []
    dist-cons : {c : Color} {n : ℕ} → {m : Move} {ms : Moves c n} → 
                (v-ms : distinct-m ms) → (m∉ms : m ∉' ms) → distinct-m (m ∷ ms)

  ---------------------------------------------------------------------------------
  --  A relation that states that {made}moves and valid{Moves} form a partition  --
  ---------------------------------------------------------------------------------

  data partition : {n k : ℕ} {c : Color} → Moves c k → Vec Move n → Set where
    part : {n k : ℕ} {c : Color} 
         → {moves   : Moves c k}
         → {valid   : Vec Move n}
         → (all     : ∀ (m : Move) → m ∈' moves ⊎ m ∈ valid)
         → (m-not-v : ∀ (m : Move) → m ∈' moves → m ∉  valid)
         → (v-not-m : ∀ (m : Move) → m ∈  valid → m ∉' moves)
         → partition moves valid

  -- lemmas

{- given
v-not-m : (m0 : Move) → m0 ∈ valid → m0 ∈' m ∷ ms → ⊥
m-not-v : (m0 : Move) → m0 ∈' m ∷ ms → m0 ∈ valid → ⊥
all     : (m0 : Move) → m0 ∈' m ∷ ms ⊎ m0 ∈ valid
m∉ms    : m ∈' ms → ⊥
v-ms    : distinct-m ms
v-dist  : distinct-v valid

we need to prove

p1 : (m' : Move) → m' ∈' ms ⊎ m' ∈ m ∷ valid
p2 : (m' : Move) → m' ∈' ms → m' ∈ m ∷ valid → ⊥
p3 : (m' : Move) → m' ∈ m ∷ valid → m' ∈' ms → ⊥

-}

  ---------------------------------
  --  Board types - WorkerBoard  --
  ---------------------------------


  data WorkerBoard : {-ℕ → -}Set where
    worker : {n : ℕ}                                               -- number of possible moves
           → {c : Color}                                           -- color of pl. to move
           → {k : ℕ}                                               -- number of made moves

           → (k<9 : k < 9)
           → (n+k : n + k ≡ 9)                                     -- reified invariant

           → (moves : Moves c k)                                   -- moves made so far
           → (valid : Vec Move n)                                  -- list of possible moves
           → (m     : Move)                                        -- the last move

           → (m-new  : m ∉' moves)
           → (m-dist : distinct-m (m ∷ moves))
           → (v-dist : distinct-v valid)
           → (part   : partition moves valid)
           → (noWin  : noWinner moves)

           → WorkerBoard --(pred n)                                   -- we index by the amount of valid moves

  -- Commentary:
  -- The WorkerBoard represents a game that might have been concluded **just now**.

  -- Q: Why do we store the last move independently of moves (and valid)?
  -- A: This makes the task of implementing the undo operation trivial - all pieces are assembled.

  -- TODO: add m ∈ valid
  --       state that valid and moves form a partition of the Move type

  noWinnerW : {-{n : ℕ} → -} WorkerBoard → Set
  noWinnerW (worker k<9 n+k moves valid m m-new m-dist v-dist partit noWin) = noWinner (m ∷ moves)

  wonW : {-{n : ℕ} → -} Color → WorkerBoard → Set
  wonW c (worker k<9 n+k moves valid m m-new m-dist v-dist partit noWin) = WonC c (m ∷ moves)

  wMovesNo : WorkerBoard → ℕ
  wMovesNo (worker {k = k} k<9 n+k moves valid m m-new m-dist v-dist partit noWin) = suc k

  -- no of valid moves BEFORE the last one

  wValidNo : WorkerBoard → ℕ
  wValidNo (worker {n = n} {c} {k} k<9 n+k moves valid m m-new m-dist v-dist partit noWin) = n


  ---------------------------
  --  Board types - Board  --
  ---------------------------

  data Board : ℕ → Set where
    board  : {n : ℕ}                                               -- number of possible moves
           → {c : Color}                                           -- color of pl. to move
           → {k : ℕ}                                               -- number of made moves

           → (k<9 : k < 9)
           → (n+k : n + k ≡ 9)                                     -- reified invariant

           → (moves : Moves c k)                                   -- moves made so far
           → (valid : Vec Move n)                                  -- list of possible moves

           → (m-dist : distinct-m moves)
           → (v-dist : distinct-v valid)
           → (part   : partition moves valid)
           → (noWin  : noWinner moves)

           → Board n                                               -- we index by the amount of valid moves
  

  -----------------------------------
  --  Board types - FinishedBoard  --
  -----------------------------------

  data FinishedBoard : Set where
    draw : (wb : WorkerBoard) → wMovesNo wb ≡ 9 → noWinnerW wb → FinishedBoard
    win  : (wb : WorkerBoard) → (c : Color) → wonW c wb → FinishedBoard

  -----------------------
  --  Undo operations  --
  -----------------------

  undoWorker : (wb : WorkerBoard) → Board (wValidNo wb)
  undoWorker (worker k<9 n+k moves valid m m-new (dist-cons v m∉ms) v-dist partit noWin) 
    = board k<9 n+k moves valid v v-dist partit noWin

  undoFin : FinishedBoard → ∃ Board
  undoFin (draw wb _ _) = _ , undoWorker wb
  undoFin (win  wb _ _) = _ , undoWorker wb


  undo : {n : ℕ} → Board n → Board (suc n)
  undo (board k<9 n+k [] valid m-dist v-dist partit noWin) = {!!} -- IMPOSSIBLE; ABSURD CASE
  undo (board {n = n} {k = suc k} k<9 n+k (m ∷ ms) valid 
       (dist-cons v-ms m∉ms) v-dist (part all m-not-v v-not-m) noWin) rewrite sym (lem-plus-s n k)
   = board (lem-<-trans lem-≤-refl k<9) n+k ms (m ∷ valid) v-ms 
            (dist-cons v-dist (λ x → v-not-m m x here))
            (part p1 p2 p3)
            ((λ x → proj₁ noWin (lem-win-extend X ms m x)) , 
             (λ x → proj₂ noWin (lem-win-extend O ms m x))) where

              -- TODO: these will need to be extracted as lemmas

              p1 : (m' : Move) → m' ∈' ms ⊎ m' ∈ m ∷ valid
              p1 m' = {!!}

              p2 : (m' : Move) → m' ∈' ms → m' ∈ m ∷ valid → ⊥
              p2 m' m'∈ms = {!!}

              p3 : (m' : Move) → m' ∈ m ∷ valid → m' ∈' ms → ⊥
              p3 m' m'∈mv m'∈ms = {!!}

-- TODOs

-- we use a lot of datatypes with exactly one field and lots (10+) of constructor arguments -
-- this makes out patterns very long, often unnecessarily. Should we switch to records?
-- Hey! can records be indexed?

-- Should we index FinishedBoard and WorkerBoard in the same way as we index the Board type?