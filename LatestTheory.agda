{-

-}
module LatestTheory where

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

--open import Level
--open import Induction
--open import Induction.Nat
open import Induction.WellFounded

open ≡-Reasoning

open import Game
open import ResultOrdering
open import Theory

open GameImplementation
open GameTheory

module LatestGameTheory where

  --------------------------------
  --  Properties of bestResult  --
  --------------------------------


  mutual
    resultNodeDefault : ∀ (c : Color)(r : Result)(l : List GameTree) → r ⊑ resultNode c r l [ c ]
    resultNodeDefault c r [] = ⊑-refl {c} {r}
    resultNodeDefault c r (x ∷ xs) = {!!} -- ⊑-trans c r {!!} {!!} {!!} {!!}


    resultNodeValid : ∀ (c : Color)(r : Result)(l : List GameTree)(t : GameTree)(t∈l : t ∈ l) 
     → resultColor (otherColor c) t ⊑ resultNode c r l [ c ]
    resultNodeValid c r [] t ()
    resultNodeValid c r (x ∷ xs) .x ∈-take = {!!}
    resultNodeValid c r (x ∷ xs) t (∈-drop y) = resultNodeValid c (maxByColor c r (resultColor (otherColor c) x)) xs t y

  bestResultValid : ∀ (b : Board) (m : Move) (p : m ∈ validMoves b) → bestResult (makeMove b m p) ⊑ bestResult (inj₁ b) [ currentPlayer b ]
  bestResultValid b m p = {!!}

  
  ----------------------------------------
  --  Soundness of the implementations  --
  ----------------------------------------
{-
  BestResultMoveList : ∀ (b : Board)(r : Result) → BestResult b r → ∃₂ (λ (l : List Move)(fin : FinishedBoard) → 
     distinct l × l ⊂ validMoves b × tryMoves (inj₁ b) l ≡ inj₂ fin × getResult fin ≡ r)
  BestResultMoveList b r best-r = {!!}


  uniquenessOfBestResult' : ∀ (b : Board) (r1 r2 : Result) → BestResult b r1 → BestResult b r2 → 
       r1 ⊑ r2 [ currentPlayer b ]   ×   r2 ⊑ r1 [ currentPlayer b ]
  uniquenessOfBestResult' b r1 r2 best1 best2 with BestResultMoveList b r1 best1 | BestResultMoveList b r2 best2
  uniquenessOfBestResult' b r1 r2 (best .b .r1 y) (best .b .r2 y') | l1 , fin1 , dist1 , l1-val , try1 , res1 | l2 , fin2 , dist2 , l2-val , try2 , res2 
      with y' l1 fin1 dist1 l1-val try1 | y l2 fin2 dist2 l2-val try2
  uniquenessOfBestResult' b r1 r2 (best .b .r1 y) (best .b .r2 y') | l1 , fin1 , dist1 , l1-val , try1 , res1 | l2 , fin2 , dist2 , l2-val , try2 , res2 
      | p1 | p2 rewrite res1 | res2 = p1 , p2

  uniquenessOfBestResult : ∀ (b : Board) (r1 r2 : Result) → BestResult b r1 → BestResult b r2 → r1 ≡ r2
  uniquenessOfBestResult b r1 r2 best1 best2 = ⊑-antisym {currentPlayer b} {r1} {r2} (proj₁ (uniquenessOfBestResult' b r1 r2 best1 best2))
                                                                                     (proj₂ (uniquenessOfBestResult' b r1 r2 best1 best2))
 
  inj2-inv : ∀ {f f' : FinishedBoard} → _≡_ {A = Board ⊎ FinishedBoard} (inj₂ f) (inj₂ f') → f ≡ f'
  inj2-inv refl = refl

  bestResultSound : ∀ (b : Board)(l : List Move)(fin : FinishedBoard) → distinct l → l ⊂ validMoves b 
    → tryMoves (inj₁ b) l ≡ inj₂ fin → getResult fin ⊑ bestResult (inj₁ b) [ currentPlayer b ]
  bestResultSound b [] fin dist l-val ()
  bestResultSound b (m ∷ ms) fin (dist-cons dist y) (cons y' m∈val) try rewrite lem-member-refl-valid b m m∈val with inspect (makeMove b m m∈val)
  ... | inj₂ f  with-≡ eq rewrite eq | sym (inj2-inv try) = {!!}
  ... | inj₁ b' with-≡ eq = {!!}



  soundResult : ∀ (b : Board) → BestResult b (bestResult (inj₁ b))
  soundResult b = best b (bestResult (inj₁ b)) (bestResultSound b)
  -}