data Color : Set where
  X O : Color

otherColor : Color → Color

data Move : Set where
  P11 P12 P13 : Move
  P21 P22 P23 : Move
  P31 P32 P33 : Move

-- a list of all possible moves

allMoves : List Move
allMoves = P11 ∷ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ []

allMovesValid : ∀ (m : Move) → m ∈ allMoves

_==_ : (m1 m2 : Move) → Dec (m1 ≡ m2)

data Result : Set where
  Win  : (c : Color) → Result
  Draw : Result

-------------------------------------------------------------------------
--  The public API that will guarantee the properties we want to have  --
-------------------------------------------------------------------------

record GameInterface : Set₁ where
  field 

  -- abstract types

    Board          : Set
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

