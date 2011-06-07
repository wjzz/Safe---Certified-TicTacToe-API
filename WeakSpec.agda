{- This module implements a TicTacToe game engine. -}

module WeakSpec where

open import Data.Bool
open import Data.List
open import Data.List.Theorems
open import Data.Maybe
open import Data.Nat renaming (_≟_ to  _ℕ≟_)

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

-- types

data Color : Set where
  X O : Color

data Move : Set where
  P11 P12 P13 : Move
  P21 P22 P23 : Move
  P31 P32 P33 : Move

allMoves : List Move
allMoves = P11 ∷ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ []


-- a result view

data Result : Set where
  Win :   (c : Color) → Result
  Draw       : Result
  InProgress : Result


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


module Game where
  private

    record Board : Set where
      field
        currPlayer : Color                                             -- color of the player to move
        xs         : List Move                                         -- moves by X player
        os         : List Move                                         -- moves by O player

  private
    otherColor : (c : Color) → Color
    otherColor X = O
    otherColor O = X

    decToBool : {P : Set} → Dec P → Bool
    decToBool (yes p) = true
    decToBool (no ¬p) = false

    moveListMember : (m : Move) → (l : List Move) → Bool
    moveListMember m l = decToBool (member m l _==_)

    selectMoves : Color → Board → List Move
    selectMoves X b = Board.xs b
    selectMoves O b = Board.os b

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

    isWinByColor : Color → Board → Bool
    isWinByColor c b = any (λ winPos → all (λ move → moveListMember move winPos)
                                           (selectMoves c b)) 
                           winningPositions  

    isDraw : (b : Board) → Bool
    isDraw b with length (Board.xs b) + length (Board.os b) ℕ≟ 9
    ... | yes p = true
    ... | no ¬p = false

  -- public definitions

  emptyBoard : Board
  emptyBoard = record { currPlayer = X
                      ; xs         = []
                      ; os         = []
                      }


  makeMove : (b : Board) → (m : Move) → Board
  makeMove b m with Board.currPlayer b
  ...          | X = record { currPlayer = otherColor (Board.currPlayer b) 
                            ; xs         = m ∷ Board.xs b 
                            ; os         = Board.os b 
                            }
  ...          | O = record { currPlayer = otherColor (Board.currPlayer b) 
                            ; xs         = Board.xs b 
                            ; os         = m ∷ Board.os b 
                            }

  validMoves : (b : Board) → List Move
  validMoves b = filter (λ move → not (moveListMember move 
                                                      (selectMoves (Board.currPlayer b) b))) 
                        allMoves  

  
  getResult : (b : Board) → Result
  getResult b with isDraw b
  ... | true = Draw
  ... | false with isWinByColor X b
  ... | true = Win X
  ... | false with isWinByColor O b
  ... | true = Win O
  ... | false = InProgress

open Game

ms : List Move
ms = validMoves (makeMove (makeMove emptyBoard P12) P11)
