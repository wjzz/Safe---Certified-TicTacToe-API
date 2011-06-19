module GameImplementation where
  -----------------------------------------------------------------
  -- the moves type
  --
  -- A list of moves augmented with the color of the player to move 
  -- and the number of moves already played
  -----------------------------------------------------------------

  data Moves : (currPlayer : Color) → (n : ℕ) → Set where
    []  : Moves X 0
    _▸_ : {c : Color} {n : ℕ} → (ms : Moves c n) → (m : Move) → Moves (otherColor c) (suc n)
  

  -- moves membership relation

  infix 4 _∈′_

  data _∈′_ : {c : Color}{n : ℕ} → Move → Moves c n → Set where
  
  infix 4 _∉′_

  _∉′_ : {c : Color}{n : ℕ} → Move → Moves c n → Set
  _∉′_ m ms = ¬ (m ∈′ ms)

  member′ : {c : Color}{n : ℕ} → (m : Move) → (ms : Moves c n) → Dec (m ∈′ ms)

  movesToList-in : ∀ {currPlayer : Color}{n : ℕ} (ms : Moves currPlayer n) (m : Move) → m ∈′ ms → m ∈ movesToList ms

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

  lem-win-extend : ∀ {c n} → (winner : Color)(ms : Moves c n) → (m : Move) → WonC winner ms → WonC winner (ms ▸ m)

  lem-nowin-prev : ∀ {c n} → (winner : Color)(ms : Moves c n) → (m : Move) → ¬ WonC winner (ms ▸ m) → ¬ WonC winner ms
    
  wonDec : forall {c n} → (cand : Color) → (ms : Moves c n) → Dec (WonC cand ms)

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

  ----------------------------------------
  --  valid moves and their properties  --
  ----------------------------------------

  validMoves : Board → List Move
  validMoves (goodBoard n<9 ms dist noWin) = removeDec allMoves (λ move → member′ move ms)

  isMovePossible? : Board → Move → Bool

  -- relative validness of two ways to generate valid moves

  valid-possible-l : ∀ (b : Board) → (m : Move) → isMovePossible? b m ≡ true → m ∈ validMoves b
  valid-possible-r : ∀ (b : Board) → (m : Move) → m ∈ validMoves b → isMovePossible? b m ≡ true

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

  undo-make-move2 : ∀ (b : Board) (f : FinishedBoard) (m : Move) (vld : m ∈ validMoves b) →
                           makeMove b m vld ≡ inj₂ f → undoFin f ≡ b


