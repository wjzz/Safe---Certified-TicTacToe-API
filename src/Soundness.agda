module Soundness where

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

open import Game
open import ResultOrdering
open import WellFounded
open import Search

{- BASE IMPORT Game -}
{- BASE IMPORT ResultOrdering -}

open GameImplementation
--open GameTheory

----------------------------------
--  Properties of generateTree  --
----------------------------------

-- to prove this theorems we will need to use the wf-induction and generalize to generateTreeIter

postulate
  generateTreeList : ∀ (b : Board) (l : List GameTree) (val-l : length l ≡ length (validMoves b)) 
    → generateTree (inj₁ b) ≡ node b l val-l → (m : Move) → (p : m ∈ validMoves b) → generateTree (makeMove b m p) ∈ l

--  generateTreeBoard : ∀ (b : Board) → ∃₂ (λ (l : List GameTree) (val-l : length l ≡ length (validMoves b)) 
--                                         → generateTree (inj₁ b) ≡ node b l val-l)
  
--  generateTreeLeaf : ∀ (f : FinishedBoard) → generateTree (inj₂ f) ≡ leaf f

  generateTreeLastNode : ∀ (b : Board) (m : Move) (p : m ∈ validMoves b) (fin : FinishedBoard) →
    makeMove b m p ≡ inj₂ fin → ∃ (λ len → generateTree (inj₁ b) ≡ node b (leaf fin ∷ []) len)

--generateTreeIter : (x : Board ⊎ FinishedBoard)(rec : (x0 : Board ⊎ FinishedBoard) → (x1 : x0 ≪ x) → GameTree) → GameTree

generateTreeLeaf : ∀ (f : FinishedBoard) → generateTree (inj₂ f) ≡ leaf f
generateTreeLeaf f = refl

generateTreeBoard : ∀ (b : Board) → ∃₂ (λ (l : List GameTree) (val-l : length l ≡ length (validMoves b)) 
                                         → generateTree (inj₁ b) ≡ node b l val-l)
generateTreeBoard b = {!bf-recursor!}

{-
(P' : Board ⊎ FinishedBoard → Set) →
((x : Board ⊎ FinishedBoard) →
 ((y : Board ⊎ FinishedBoard) →
  suc (measure y) ≤′ measure x → P' y) →
 P' x) →
(x : Board ⊎ FinishedBoard) → P' x
-}

{-

-----------------------------------------------------------
--  Formalization on the notion of best possible result  --
-----------------------------------------------------------
  
data BestResult : Board → Result → Set where
  best : (b : Board) (result : Result) →               -- Permutation l (validMoves b) ?
    (∀ (l : List Move)(fin : FinishedBoard) → 
       distinct l → l ⊂ validMoves b → (tryMoves (inj₁ b) l ≡ inj₂ fin) → getResult fin ⊑ result [ currentPlayer b ]) 
    → BestResult b result

--------------------------------
--  Properties of bestResult  --
--------------------------------

resultNodeInv : ∀ (c : Color) (r result : Result) (l : List GameTree) → resultNode c r l ≡ result 
  → result ≡ r ⊎ ∃ (λ (t : GameTree) → t ∈ l × result ≡ resultColor (otherColor c) t)
resultNodeInv c r result []       resNode = inj₁ (sym resNode)
resultNodeInv c r result (x ∷ xs) resNode with resultNodeInv c ((maxByColor c r (resultColor (otherColor c) x))) result xs resNode
resultNodeInv c r result (x ∷ xs) resNode | inj₁ x' with maxByColor-inv c r (resultColor (otherColor c) x)
resultNodeInv c r result (x ∷ xs) resNode | inj₁ x0 | inj₁ x' rewrite x'     = inj₁ x0
resultNodeInv c r result (x ∷ xs) resNode | inj₁ x' | inj₂ y  rewrite sym x' = inj₂ (x , ∈-take , y)
resultNodeInv c r result (x ∷ xs) resNode | inj₂ (t , t∈xs , res)            = inj₂ (t , ∈-drop t∈xs , res)


resultNodeDefault : ∀ (c : Color)(r : Result)(l : List GameTree) → r ⊑ resultNode c r l [ c ]
resultNodeDefault c r []       = ⊑-refl
resultNodeDefault c r (x ∷ xs) = ⊑-trans ⊑-max-l (resultNodeDefault c (maxByColor c r (resultColor (otherColor c) x)) xs) 


resultNodeValid : ∀ (c : Color) (r : Result) (l : List GameTree) (t : GameTree) (t∈l : t ∈ l) 
                                  → resultColor (otherColor c) t ⊑ resultNode c r l [ c ]
resultNodeValid c r [] t ()
resultNodeValid c r (x ∷ xs) .x ∈-take    = ⊑-trans ⊑-max-r (resultNodeDefault c (maxByColor c r (resultColor (otherColor c) x)) xs)
resultNodeValid c r (x ∷ xs) t (∈-drop y) = resultNodeValid c (maxByColor c r (resultColor (otherColor c) x)) xs t y

bestResultValid : ∀ (b : Board) (m : Move) (p : m ∈ validMoves b) → bestResult (makeMove b m p) ⊑ bestResult (inj₁ b) [ currentPlayer b ]
bestResultValid b m p with inspect (makeMove b m p)
bestResultValid b m p | inj₁ b' with-≡ eq with generateTreeBoard b
bestResultValid b m p | inj₁ b' with-≡ eq | []     , len-l , genTree = ABSURD-CASE b len-l
bestResultValid b m p | inj₁ b' with-≡ eq | x ∷ xs , len-l , genTree with generateTreeList b (x ∷ xs) len-l genTree m p
bestResultValid b m p | inj₁ b' with-≡ eq | .(generateTree (makeMove b m p)) ∷ xs , len-l , genTree | ∈-take 
  rewrite eq | genTree | currPlayerMakeMove b b' m p eq 
  = resultNodeDefault (currentPlayer b) (resultColor (otherColor (currentPlayer b)) (generateTree (inj₁ b'))) xs 
bestResultValid b m p | inj₁ b' with-≡ eq | x ∷ xs , len-l , genTree | ∈-drop y rewrite eq | genTree | currPlayerMakeMove b b' m p eq 
  = resultNodeValid (currentPlayer b) (resultColor (otherColor (currentPlayer b)) x) xs (generateTree (inj₁ b')) y
bestResultValid b m p | inj₂ f  with-≡ eq with generateTreeLastNode b m p f eq
bestResultValid b m p | inj₂ f  with-≡ eq | len-val , genTree rewrite eq | genTree | generateTreeLeaf f = ⊑-refl

----------------------------------------
--  Soundness of the implementations  --
----------------------------------------
  
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
uniquenessOfBestResult b r1 r2 best1 best2 = uncurry′ ⊑-antisym (uniquenessOfBestResult' b r1 r2 best1 best2)


inj2-inv : ∀ {f f' : FinishedBoard} → _≡_ {A = Board ⊎ FinishedBoard} (inj₂ f) (inj₂ f') → f ≡ f'
inj2-inv refl = refl
                
postulate
  makeMoveLemma : ∀ (b b' : Board)(m : Move)(ms : List Move)(p : m ∈ validMoves b) → makeMove b m p ≡ inj₁ b' → m ∉ ms → 
    ms ⊂ validMoves b → ms ⊂ validMoves b'

-- → bestResult (makeMove b m p) ⊑ bestResult (inj₁ b) [ currentPlayer b ]
bestResultSound : ∀ (b : Board)(l : List Move)(fin : FinishedBoard) → distinct l → l ⊂ validMoves b → tryMoves (inj₁ b) l ≡ inj₂ fin
                                              → getResult fin ⊑ bestResult (inj₁ b) [ currentPlayer b ]
bestResultSound b [] fin dist l-val ()
bestResultSound b (m ∷ ms) fin (dist-cons dist y) (cons y' m∈val) try with inspect (makeMove b m m∈val) | bestResultValid b m m∈val 
... | inj₂ f  with-≡ eq | bestResult rewrite lem-member-refl-valid b m m∈val | eq | sym (inj2-inv try) | generateTreeLeaf f = bestResult
... | inj₁ b' with-≡ eq | bestResult rewrite lem-member-refl-valid b m m∈val | eq with bestResultSound b' ms fin dist (makeMoveLemma b b' m ms m∈val eq y y') try
... | rec = {!⊑-trans rec bestResult!}
                          
                          
soundResult : ∀ (b : Board) → BestResult b (bestResult (inj₁ b))
soundResult b = best b (bestResult (inj₁ b)) (bestResultSound b)

-}
