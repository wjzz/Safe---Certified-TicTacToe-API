{-# OPTIONS --universe-polymorphism #-}

{- This file presents many theorems about the properties of both the implementation
  from the Game.agda file and of the TicTacToe game itself.

  For instance, we define (in three ways) a function that determines the result of the
  game given perfect play by both players. It took around 70 minutes to run the bestResult
  function on (inj₁ emptyBoard) and 45 minutes to call leaves on the same board, so be careful :)
  [ the results were Draw and 255168, resp.]
-}

module Search where

open import Data.Maybe
open import Data.Bool
open import Data.List
open import Data.List.Theorems
open import Data.Nat renaming (_≟_ to _≟ℕ_; _⊔_ to max)
open import Data.Nat.Theorems
open import Data.Product
open import Data.Sum

--open import Data.Vec hiding (_∈_)

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import Game
open import ResultOrdering
open import WellFounded

{- BASE IMPORT Game -}
{- BASE IMPORT ResultOrdering -}

open GameImplementation
--open GameInterface (GameImplementation.game)
                     
                                 
----------------------------------------
--  Further properties about the api  --
----------------------------------------
  
distinctAll : distinct allMoves
distinctAll = dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons (dist-cons dist-nil (λ ()))
  lem1) lem2) lem3) lem4) lem5) lem6) lem7) lem8 where
        lem1 : (x : P32 ∈ P33 ∷ []) → ⊥
        lem1 (∈-drop ())
                     
        lem2 : P31 ∈ P32 ∷ P33 ∷ [] → ⊥
        lem2 (∈-drop (∈-drop ()))
                             
        lem3 : P23 ∈ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem3 (∈-drop (∈-drop (∈-drop ())))
                                     
        lem4 : P22 ∈ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem4 (∈-drop (∈-drop (∈-drop (∈-drop ()))))
                                             
        lem5 : P21 ∈ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem5 (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ())))))
                                                     
        lem6 : P13 ∈ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem6 (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ()))))))
                                                             
        lem7 : P12 ∈ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem7 (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ())))))))
                                                                     
        lem8 : P11 ∈ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] → ⊥
        lem8 (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop (∈-drop ()))))))))
                                                                             
                                                                             
noStuckBoard : (b : Board) → ∃ (λ (m : Move) → m ∈ validMoves b)
noStuckBoard b with member P11 (validMoves b) _==_
... | yes p = P11 , p
noStuckBoard b | no ¬p with member P12 (validMoves b) _==_
... | yes p = P12 , p
noStuckBoard b | no ¬p' | no ¬p with member P13 (validMoves b) _==_
... | yes p = P13 , p
noStuckBoard b | no ¬p0 | no ¬p' | no ¬p with member P21 (validMoves b) _==_
... | yes p = P21 , p
noStuckBoard b | no ¬p1 | no ¬p0 | no ¬p' | no ¬p with member P22 (validMoves b) _==_
... | yes p = P22 , p
noStuckBoard b | no ¬p2 | no ¬p1 | no ¬p0 | no ¬p' | no ¬p with member P23 (validMoves b) _==_
... | yes p = P23 , p
noStuckBoard b | no ¬p3 | no ¬p2 | no ¬p1 | no ¬p0 | no ¬p' | no ¬p with member P31 (validMoves b) _==_
... | yes p = P31 , p
noStuckBoard b | no ¬p4 | no ¬p3 | no ¬p2 | no ¬p1 | no ¬p0 | no ¬p' | no ¬p with member P32 (validMoves b) _==_
... | yes p = P32 , p
noStuckBoard b | no ¬p5 | no ¬p4 | no ¬p3 | no ¬p2 | no ¬p1 | no ¬p0 | no ¬p' | no ¬p with member P33 (validMoves b) _==_
... | yes p = P33 , p
noStuckBoard (goodBoard {c} {n} n<9 ms dist noWin) | no ¬p6 | no ¬p5 | no ¬p4 | no ¬p3 | no ¬p2 | no ¬p1 | no ¬p0 | no ¬p' | no ¬p 
  = ⊥-elim (lem-both-≤-<-impossible final-lem n<9) where
  helper : (m : Move) → m ∉ validMoves (goodBoard n<9 ms dist noWin) → m ∈′ ms
  helper m ¬p = removeDec-valid2 allMoves _==_ ((λ move → member′ move ms)) m (allMovesValid m) ¬p
                                                                                                
  allMovesInMs' : ∀ (m : Move) → m ∈′ ms
  allMovesInMs' P11 = helper P11 ¬p6
  allMovesInMs' P12 = helper P12 ¬p5
  allMovesInMs' P13 = helper P13 ¬p4
  allMovesInMs' P21 = helper P21 ¬p3
  allMovesInMs' P22 = helper P22 ¬p2
  allMovesInMs' P23 = helper P23 ¬p1
  allMovesInMs' P31 = helper P31 ¬p0
  allMovesInMs' P32 = helper P32 ¬p'
  allMovesInMs' P33 = helper P33 ¬p
                                 
  allMovesInMs : ∀ (m : Move) → m ∈ movesToList ms
  allMovesInMs m = movesToList-in ms m (allMovesInMs' m)
                                                      
  len : length (movesToList ms) ≡ n
  len = movesToList-length ms
                           
  sub : P11 ∷ P12 ∷ P13 ∷ P21 ∷ P22 ∷ P23 ∷ P31 ∷ P32 ∷ P33 ∷ [] ⊂ movesToList ms
  sub = cons (cons (cons (cons (cons (cons (cons (cons (cons nil (allMovesInMs P33))(allMovesInMs P32))(allMovesInMs P31))
        (allMovesInMs P23))(allMovesInMs P22))(allMovesInMs P21))(allMovesInMs P13))(allMovesInMs P12)) (allMovesInMs P11)
                                                                                                                      
  lem : length allMoves ≤ length (movesToList ms)
  lem = lem-subset-length allMoves (movesToList ms) _==_ distinctAll sub
                                                                     
  final-lem : 9 ≤ n
  final-lem = subst (λ m → 9 ≤ m) len lem

ABSURD-CASE : ∀ {w} {Whatever : Set w} (b : Board) → (0 ≡ length (validMoves b)) → Whatever
ABSURD-CASE b y with noStuckBoard b
... | move , p = ⊥-elim (lem-∈-len-nonzero p y)

{- BASE global ABSURD-CASE -}
                                      
postulate
  lem-filterDec-add : ∀ {c n} (ms : Moves c n) (m : Move) →  {- distinctm ms → -}
    length (filterDec allMoves (λ move → member′ move (ms ▸ m))) ≡ suc (length (filterDec allMoves (λ move → member′ move ms)))
  --lem-filterDec-add [] m = {!!}
  --lem-filterDec-add (ms ▸ m) m' = {!!}
                                    
lem-filterDec-moves : ∀ {c n} (ms : Moves c n) → length (filterDec allMoves (λ move → member′ move ms)) ≡ length (movesToList ms)
lem-filterDec-moves [] = refl
lem-filterDec-moves (ms ▸ m) rewrite lem-filterDec-add ms m | lem-filterDec-moves ms = refl
                                                                                       
validMovesLength : ∀ (b : Board) → length (validMoves b) ≡ 9 ∸ movesNo b
validMovesLength (goodBoard {c} {n} n<9 ms dist noWin) with lem where
  lem : movesNo (goodBoard {c} {n} n<9 ms dist noWin) ≡ length (filterDec allMoves (λ move → member′ move ms))
  lem = sym (trans (lem-filterDec-moves ms) (movesToList-length ms))
validMovesLength (goodBoard n<9 ms dist noWin) | cond = trans (removeDec-length allMoves ((λ move → member′ move ms))) 
                                                        (sym (cong (_∸_ 9) cond))
                                                                           

-- TODO
-- the pattern in the next three proof needs to be abstracted away to a seperate lemma

currPlayerMakeMove : ∀ (b b' : Board)(m : Move) → (p : m ∈ validMoves b) → makeMove b m p ≡ inj₁ b' → currentPlayer b' ≡ otherColor (currentPlayer b)
currPlayerMakeMove (goodBoard {c} {n} n<9 ms dist noWin) b' m p b'-makeMove-b with wonDec X (ms ▸ m)
currPlayerMakeMove (goodBoard n<9 ms dist noWin) b' m p' () | yes p
currPlayerMakeMove (goodBoard n<9 ms dist noWin) b' m p b'-makeMove-b | no ¬p with wonDec O (ms ▸ m)
currPlayerMakeMove (goodBoard n<9 ms dist noWin) b' m p' () | no ¬p | yes p
currPlayerMakeMove (goodBoard {c} {n} n<9 ms dist noWin) b' m p b'-makeMove-b | no ¬p' | no ¬p with suc n ≟ℕ 9
currPlayerMakeMove (goodBoard n<9 ms dist noWin) b' m p' () | no ¬p' | no ¬p | yes p
currPlayerMakeMove (goodBoard {c} {n} n<9 ms dist noWin) b' m p b'-makeMove-b | no ¬p0 | no ¬p' | no ¬p with lem-≤-cases-ext (suc n) 9 n<9 ¬p
currPlayerMakeMove (goodBoard n<9 ms dist noWin) .(goodBoard (s≤s m≤n) (ms ▸ m) 
  (dist-cons dist (validMoves-distinct m ms n<9 dist noWin p)) (¬p0 , ¬p')) m p refl | no ¬p0 | no ¬p' | no ¬p | s≤s m≤n = refl

                                                                           
movesNoMakeMove : ∀ (b b' : Board)(m : Move) → (p : m ∈ validMoves b) → makeMove b m p ≡ inj₁ b' → suc (movesNo b) ≡ movesNo b'
movesNoMakeMove (goodBoard {c} {n} n<9 ms dist noWin) b' m p b'-makeMove-b with wonDec X (ms ▸ m)
movesNoMakeMove (goodBoard n<9 ms dist noWin) b' m p' () | yes p
movesNoMakeMove (goodBoard n<9 ms dist noWin) b' m p b'-makeMove-b | no ¬p with wonDec O (ms ▸ m)
movesNoMakeMove (goodBoard n<9 ms dist noWin) b' m p' () | no ¬p | yes p
movesNoMakeMove (goodBoard {c} {n} n<9 ms dist noWin) b' m p b'-makeMove-b | no ¬p' | no ¬p with suc n ≟ℕ 9
movesNoMakeMove (goodBoard n<9 ms dist noWin) b' m p' () | no ¬p' | no ¬p | yes p
movesNoMakeMove (goodBoard {c} {n} n<9 ms dist noWin) b' m p b'-makeMove-b | no ¬p0 | no ¬p' | no ¬p with lem-≤-cases-ext (suc n) 9 n<9 ¬p
movesNoMakeMove (goodBoard n<9 ms dist noWin) .(goodBoard (s≤s m≤n) (ms ▸ m) 
  (dist-cons dist (validMoves-distinct m ms n<9 dist noWin p)) (¬p0 , ¬p')) m p refl | no ¬p0 | no ¬p' | no ¬p | s≤s m≤n = refl
                                                                                                                           

validMovesSubset : ∀ (b b' : Board)(m : Move) → (p : m ∈ validMoves b) → makeMove b m p ≡ inj₁ b' → validMoves b' ⊂ validMoves b
validMovesSubset (goodBoard n<9 ms dist noWin) b' m p make with wonDec X (ms ▸ m)
validMovesSubset (goodBoard n<9 ms dist noWin) b' m p () | yes p'
validMovesSubset (goodBoard n<9 ms dist noWin) b' m p make | no ¬p with wonDec O (ms ▸ m)
validMovesSubset (goodBoard n<9 ms dist noWin) b' m p ()| no ¬p | yes p'
validMovesSubset (goodBoard {c} {n} n<9 ms dist noWin) b' m p make | no ¬p | no ¬p' with suc n ≟ℕ 9
validMovesSubset (goodBoard {c} {n} n<9 ms dist noWin) b' m p () | no ¬p | no ¬p' | yes p'
validMovesSubset (goodBoard {c} {n} n<9 ms dist noWin) b' m p make | no ¬p0 | no ¬p' | no ¬p with lem-≤-cases-ext (suc n) 9 n<9 ¬p
validMovesSubset (goodBoard n<9 ms dist noWin) .(goodBoard (s≤s m≤n) (ms ▸ m) 
  (dist-cons dist (validMoves-distinct m ms n<9 dist noWin p)) (¬p0 , ¬p')) m p refl | no ¬p0 | no ¬p' | no ¬p | s≤s m≤n 
    = removeDec-pred-subset allMoves (λ move → member′ move (ms ▸ m)) (λ move → member′ move ms) (λ a → ∈-drop) 

-- lemma: it's not possible to find a board and a move after which Won X and Won O are true
                                                                                       
onlyOneWinner : ∀ {c n} (ms : Moves c n) (m : Move) → noWinner ms → WonC X (ms ▸ m) → WonC O (ms ▸ m) → ⊥
onlyOneWinner {X} ms m (noWinX , noWinO) wonX (wonC .(ms ▸ m) winning y' y0) = noWinO (wonC ms winning y' y0)
onlyOneWinner {O} ms m (noWinX , noWinO) (wonC .(ms ▸ m) winning y' y0) wonO = noWinX (wonC ms winning y' y0)
                                                                                                          
                                                                                                          
------------------------
--  A testing helper  --
------------------------
  
tryMoves : Board ⊎ FinishedBoard → List Move → Board ⊎ FinishedBoard
tryMoves (inj₂ f) l  = inj₂ f
tryMoves (inj₁ b) [] = inj₁ b
tryMoves (inj₁ b) (m ∷ ms) with member m (validMoves b) _==_
...                        | no ¬p = inj₁ b
...                        | yes p = tryMoves (makeMove b m p) ms
                                                               
                                                               
-- moving from start

-- this seems to be provable most easily by generalizing 9
-- to measureB b and proceeding by well-founded recursion
                                                
{-
tryMovesEmptyBoard : ∀ (l : List Move) → distinct l → length l ≡ 9 → 
  ∃ (λ (fin : FinishedBoard) → tryMoves (inj₁ emptyBoard) l ≡ inj₂ fin)
tryMovesEmptyBoard l dist len = {!!}
-}
  
lem-valid-moves-distinct : ∀ (b : Board) → distinct (validMoves b)
lem-valid-moves-distinct (goodBoard n<9 ms dist noWin) = removeDec-distinct allMoves (λ move → member′ move ms) distinctAll
                                                                                                                
-- this proof pattern of matching against WonDec X, WonDec O and ≟ℕ is very repeatetive
-- can this be abstracted somehow?
                          
addedMoveNoLongerValid : ∀ (b b' : Board)(m : Move) → (p : m ∈ validMoves b) → (makeMove b m p ≡ inj₁ b') →
  m ∉ validMoves b'
addedMoveNoLongerValid (goodBoard n<9 ms dist noWin) b' m p make with wonDec X (ms ▸ m)
addedMoveNoLongerValid (goodBoard n<9 ms dist noWin) b' m p' () | yes p
addedMoveNoLongerValid (goodBoard n<9 ms dist noWin) b' m p make | no ¬p with wonDec O (ms ▸ m)
addedMoveNoLongerValid (goodBoard n<9 ms dist noWin) b' m p' () | no ¬p | yes p
addedMoveNoLongerValid (goodBoard {c} {n} n<9 ms dist noWin) b' m p make | no ¬p' | no ¬p with suc n ≟ℕ 9
addedMoveNoLongerValid (goodBoard n<9 ms dist noWin) b' m p' () | no ¬p' | no ¬p | yes p
addedMoveNoLongerValid (goodBoard {c} {n} n<9 ms dist noWin) b' m p make | no ¬p0 | no ¬p' | no ¬p with lem-≤-cases-ext (suc n) 9 n<9 ¬p
addedMoveNoLongerValid (goodBoard n<9 ms dist noWin) .(goodBoard lem (ms ▸ m) 
  (dist-cons dist (validMoves-distinct m ms n<9 dist noWin p)) (¬p0 , ¬p')) m p refl | no ¬p0 | no ¬p' | no ¬p | lem 
    = removeDec-valid2-rev allMoves (λ move → member′ move (ms ▸ m)) m (allMovesValid m) ∈-take
                                                                                         
                                                                                         
lem-member-refl-valid : ∀ (b : Board) (m : Move) → (p : m ∈ validMoves b) → member m (validMoves b) _==_ ≡ yes p
lem-member-refl-valid b m m∈v with member m (validMoves b) _==_
lem-member-refl-valid b m m∈v | yes p = cong yes (lem-∈-irrelv (lem-valid-moves-distinct b) p m∈v)
lem-member-refl-valid b m m∈v | no ¬p = ⊥-elim (¬p m∈v)
                                                   
allGamesTerminateIter : ∀ (b : Board) → ((y : Board) → y ≺ b → ∃₂ (λ (l : List Move) (fin : FinishedBoard) → distinct l ×
  l ⊂ validMoves y × tryMoves (inj₁ y) l ≡ inj₂ fin)) → 
      ∃₂ (λ (l : List Move) (fin : FinishedBoard) → distinct l × l ⊂ validMoves b × tryMoves (inj₁ b) l ≡ inj₂ fin)
allGamesTerminateIter b rec with noStuckBoard b
allGamesTerminateIter b rec | move , move-valid with inspect (makeMove b move move-valid) | lem-member-refl-valid b move move-valid
allGamesTerminateIter b rec | move , move-valid | inj₂ fin with-≡ eq | p  = 
  move ∷ [] , fin , (dist-cons dist-nil (λ ())) , ((cons nil move-valid) , lem) where
    lem : tryMoves (inj₁ b) (move ∷ []) ≡ inj₂ fin
    lem rewrite p | eq = refl
allGamesTerminateIter b rec | move , move-valid | inj₁ b' with-≡ eq | p  with rec b' (lem-measure-board b b' move move-valid eq)
allGamesTerminateIter b rec | move , move-valid | inj₁ b' with-≡ eq | p | l , fin , dist , l⊂valid , tryMvs
  = move ∷ l , fin , (dist-cons dist lem) , (cons (⊂-trans l⊂valid (validMovesSubset b b' move move-valid eq)) move-valid) , lem2 where
    lem : move ∉ l
    lem move∈l = addedMoveNoLongerValid b b' move move-valid eq (lem-subset-alt move l (validMoves b') l⊂valid move∈l)
                                                                                                               
    lem2 : tryMoves (inj₁ b) (move ∷ l) ≡ inj₂ fin
    lem2 rewrite p | eq = tryMvs
                          
allGamesTerminate : ∀ (b : Board) → 
  ∃₂ (λ (l : List Move) (fin : FinishedBoard) → distinct l × l ⊂ validMoves b × tryMoves (inj₁ b) l ≡ inj₂ fin)
allGamesTerminate b = b-recursor (λ x → ∃₂ (λ (l : List Move) (fin : FinishedBoard) 
                                 → distinct l × l ⊂ validMoves x × tryMoves (inj₁ x) l ≡ inj₂ fin))
                                 allGamesTerminateIter b

                                                       
                   
---------------------------------------------------------------------------------------------------
--  Functions that analyze all possible outcomes and return the optimal result for both players  --
---------------------------------------------------------------------------------------------------
  
{-
bestResultColor' : ℕ → Color → Board ⊎ FinishedBoard → Maybe Result
bestResultColor' zero c b = nothing
bestResultColor' (suc n) c (inj₂ fin) = just (getResult fin)
bestResultColor' (suc n) c (inj₁ brd) with inspect (validMoves brd)
bestResultColor' (suc n) c (inj₁ brd) | [] with-≡ eq with noStuckBoard brd
bestResultColor' (suc n) c (inj₁ brd) | [] with-≡ eq | move , p rewrite eq = ⊥-elim (lem-∉-empty move p)
bestResultColor' (suc n) c (inj₁ brd) | (x ∷ xs) with-≡ eq = {!!}
-}
  
maximumByColor : Color → Maybe Result → List (Maybe Result) -> Maybe Result
maximumByColor c r [] = r
maximumByColor c r (just x ∷ xs) with maximumByColor c r xs
maximumByColor c r (just x' ∷ xs) | just x = just (maxByColor c x' x)
maximumByColor c r (just x ∷ xs)  | nothing = just x
maximumByColor c r (nothing ∷ xs) = maximumByColor c r xs   

bestResultColor : ℕ → Color → Board ⊎ FinishedBoard → Maybe Result
bestResultColor 0 c b = nothing
bestResultColor (suc n) c (inj₂ fin) = just (getResult fin)
bestResultColor (suc n) c (inj₁ brd) with inspect (validMoves brd)
bestResultColor (suc n) c (inj₁ brd) | [] with-≡ eq = nothing
bestResultColor (suc n) c (inj₁ brd) | (x ∷ xs) with-≡ eq = maximumByColor c r l where
  r : Maybe Result
  r = bestResultColor n (otherColor c) (makeMove brd x (subst (λ p → x ∈ p) (sym eq) ∈-take))
                                                                                     
  lem : ∀ {A : Set} → (l1 l2 : List A) → (a : A) → (a ∈ l1) → l1 ≡ l2 → a ∈ l2
  lem .l2 l2 a x' refl = x'   
                         
  l : List (Maybe Result)
  l = map-in xs (λ m inn → bestResultColor n (otherColor c) (makeMove brd m (lem ((x ∷ xs)) ((validMoves brd)) m (∈-drop inn) (sym eq))))
  
-------------------------------------------------------------------
--  Positions  reachable from a given board in exactly one move  --
-------------------------------------------------------------------

boardSuccessors : (b : Board) → List (Board ⊎ FinishedBoard)
boardSuccessors b = map-in (validMoves b) (λ m m∈valid → makeMove b m m∈valid)
                                                                      
lem-map-empty : {A B : Set}{a : B}{l : List A}{f : (a : A) → (a ∈ l) → B} → (l ≡ []) → a ∈ map-in l f → a ∈ []
lem-map-empty refl a∈map = a∈map
                           
lem-successors-ex : (b : Board) (b' : Board ⊎ FinishedBoard) → b' ∈ boardSuccessors b → 
  ∃₂ (λ (m : Move) (p : m ∈ validMoves b) → b' ≡ makeMove b m p)
lem-successors-ex b b' b'∈map = lem-map-in-inv (validMoves b) (λ m m∈valid → makeMove b m m∈valid) b'∈map
                                                                                                   
lem-successors-in : (b : Board) (b' : Board ⊎ FinishedBoard) → b' ∈ boardSuccessors b → b' ≪ (inj₁ b)
lem-successors-in b b' b'∈suc with lem-successors-ex b b' b'∈suc
lem-successors-in b b' b'∈suc | m , p1 , eq rewrite eq = lem-measure' b m p1
                                                                          
----------------------------------------------------------------
--  An explicit game-tree of all possible game continuations  --
----------------------------------------------------------------
  
data GameTree : Set where
  leaf : FinishedBoard → GameTree
  node : (b : Board) → (l : List GameTree) → (length l ≡ length (validMoves b)) → GameTree
                                                                                  
generateTreeIter : (x : Board ⊎ FinishedBoard)(rec : (x0 : Board ⊎ FinishedBoard) → (x1 : x0 ≪ x) → GameTree) → GameTree
generateTreeIter (inj₂ fin) rec = leaf fin
generateTreeIter (inj₁ b)   rec = node b (map-in (boardSuccessors b)(λ a val → rec a (lem-successors-in b a val))) 
  (trans (lem-length-map-in (boardSuccessors b) ((λ a val → rec a (lem-successors-in b a val)))) 
         (lem-length-map-in (validMoves b) (makeMove b)))
        
--abstract                                             
generateTree : Board ⊎ FinishedBoard → GameTree
generateTree = bf-recursor (λ x → GameTree) generateTreeIter
                                            
---------------------------------------
--  All possible games of TicTacToe  --
---------------------------------------
  
-- the leaves represent all possible final positions in the game of TicTacToe
-- according to the Haskell & SML implementation (and also Wikipedia)
-- there should be 255168 leaves!
                          
allGames : GameTree
allGames = generateTree (inj₁ emptyBoard)
                              
---------------------------------------
--  Inductive functions on GameTree  --
---------------------------------------
  
mutual 
  depth : GameTree → ℕ
  depth (leaf y) = 0
  depth (node b (x ∷ xs) y) = depthNode (depth x) xs
  depth (node b [] y) = ABSURD-CASE b y
                                                                                            
  depthNode : ℕ → List GameTree → ℕ
  depthNode d []       = 1 + d
  depthNode d (x ∷ xs) = depthNode (max d (depth x)) xs

mutual
  leavesNo : GameTree → ℕ
  leavesNo (leaf f) = 1
  leavesNo (node b xs y) = leavesNoNode 0 xs
                                          
  leavesNoNode : ℕ → List GameTree → ℕ
  leavesNoNode n [] = n
  leavesNoNode n (x ∷ xs) = leavesNoNode (n + leavesNo x) xs
                                                          
--------------------------------------------
--  Solving TicTacToe using the GameTree  --
--------------------------------------------
  
getColor : Board ⊎ FinishedBoard → Color
getColor (inj₁ b) = currentPlayer b
getColor (inj₂ f) = X --doesn't matter
                                
mutual
  resultColor : Color → GameTree → Result
  resultColor c (leaf fin) = getResult fin
  resultColor c (node b (x ∷ xs) y) = resultNode c (resultColor (otherColor c) x) xs

  -- impossible case
  resultColor c (node b [] y) = ABSURD-CASE b y
  
  resultNode : Color → Result → List GameTree → Result
  resultNode c r []       = r
  resultNode c r (x ∷ xs) = resultNode c (maxByColor c r (resultColor (otherColor c) x)) xs
                                                                                         
bestResult : Board ⊎ FinishedBoard → Result
bestResult b = resultColor (getColor b) (generateTree b)
                                                      
-- a simple buf useful property
                       
resultNodeWin : ∀ (c : Color)(xs : List GameTree) → resultNode c (Win c) xs ≡ Win c
resultNodeWin c []       = refl
resultNodeWin X (x ∷ xs) = resultNodeWin X xs
resultNodeWin O (x ∷ xs) = resultNodeWin O xs
                                           
---------------------------------------------------
--  (not-so) Optimized searching (with pruning)  --
---------------------------------------------------
  
mutual
  resultColor2 : Color → GameTree → Result
  resultColor2 c (leaf fin) = getResult fin
  resultColor2 c (node b (x ∷ xs) y) = resultNode2 c (resultColor2 (otherColor c) x) xs

  -- impossible case
  resultColor2 c (node b [] y) = ABSURD-CASE b y
  
  resultNode2 : Color → Result → List GameTree → Result
  resultNode2 X (Win X) xs = Win X
  resultNode2 O (Win O) xs = Win O
  resultNode2 c r []       = r
  resultNode2 c r (x ∷ xs) = resultNode2 c (maxByColor c r (resultColor2 (otherColor c) x)) xs
                                                                                            
bestResult2 : Board ⊎ FinishedBoard → Result
bestResult2 b = resultColor2 (getColor b) (generateTree b)
                                                        
-------------------------------------------------------------------
--  Another version of searching (more lazy, not tail-recursive) --
-------------------------------------------------------------------
  
mutual
  resultColor3 : Color → GameTree → Result
  resultColor3 c (leaf fin)          = getResult fin
  resultColor3 c (node b (x ∷ xs) y) = resultNode3 c (resultColor3 (otherColor c) x) xs

  -- impossible case
  resultColor3 c (node b [] y) = ABSURD-CASE b y
  
  resultNode3 : Color → Result → List GameTree → Result
  resultNode3 c r []       = r
  resultNode3 c r (x ∷ xs) = maxByColor c r (resultNode3 c (resultColor3 (otherColor c) x) xs)
                           -- resultNode3 c (maxByColor c r (resultColor3 (otherColor c) x)) xs
                           -- we only change from tail recursive to non-tail recursive
                                                                             
bestResult3 : Board ⊎ FinishedBoard → Result
bestResult3 b = resultColor3 (getColor b) (generateTree b)
                                                        
resultNode3-step : ∀ {c : Color} (r r' : Result) (xs : List GameTree) → resultNode3 c (maxByColor c r r') xs ≡ maxByColor c r (resultNode3 c r' xs)
resultNode3-step r r' [] = refl
resultNode3-step {c} r r' (x ∷ xs) = maxByColorAssoc c r r' (resultNode3 c (resultColor3 (otherColor c) x) xs)
                                                                                                           
-------------------------------------------------------------------
--  Relationships between various ways to analyze the Game Tree  --
-------------------------------------------------------------------
  
----------------------------------
--  bestResult and bestResult2  --
----------------------------------
  
mutual
  resultColorEquiv : ∀ (c : Color) (t : GameTree) → resultColor c t ≡ resultColor2 c t
  resultColorEquiv c (leaf y) = refl
  resultColorEquiv c (node b [] y) = ABSURD-CASE b y
  
  resultColorEquiv c (node b (x ∷ xs) y) rewrite resultColorEquiv (otherColor c) x 
    = resultNodeEquiv c (resultColor2 (otherColor c) x) xs
                                                        
  resultNodeEquiv : ∀ (c : Color) (r : Result) (l : List GameTree) → resultNode c r l ≡ resultNode2 c r l
  resultNodeEquiv X (Win X) xs = resultNodeWin X xs
  resultNodeEquiv O (Win O) xs = resultNodeWin O xs
  resultNodeEquiv O (Win X) [] = refl
  resultNodeEquiv X (Win O) [] = refl
  resultNodeEquiv X Draw    [] = refl
  resultNodeEquiv O Draw    [] = refl
                                 
  resultNodeEquiv O (Win X) (x ∷ xs) rewrite resultColorEquiv X x = resultNodeEquiv O (resultColor2 X x) xs
  resultNodeEquiv X (Win O) (x ∷ xs) rewrite resultColorEquiv O x = resultNodeEquiv X (resultColor2 O x) xs 
  resultNodeEquiv X Draw    (x ∷ xs) rewrite resultColorEquiv O x = resultNodeEquiv X (maxByColor X Draw (resultColor2 O x)) xs
  resultNodeEquiv O Draw    (x ∷ xs) rewrite resultColorEquiv X x = resultNodeEquiv O (maxByColor O Draw (resultColor2 X x)) xs
                                                                                                                             
-- main result
        
bestResultEquiv : ∀ (bf : Board ⊎ FinishedBoard) → bestResult bf ≡ bestResult2 bf
bestResultEquiv bf = resultColorEquiv (getColor bf) (generateTree bf)
                                                                  
                                                                  
-----------------------------------------
--  bestResult and bestResult3 equiv.  --
-----------------------------------------
  
mutual
  resultColorEquiv3 : ∀ (c : Color) (t : GameTree) → resultColor c t ≡ resultColor3 c t
  resultColorEquiv3 c (leaf y) = refl
  resultColorEquiv3 c (node b [] y) = ABSURD-CASE b y
  
  resultColorEquiv3 c (node b (x ∷ xs) y) rewrite resultColorEquiv3 (otherColor c) x 
    = resultNodeEquiv3 c (resultColor3 (otherColor c) x) xs
                                                         
  resultNodeEquiv3 : ∀ (c : Color) (r : Result) (l : List GameTree) → resultNode c r l ≡ resultNode3 c r l
  resultNodeEquiv3 c r [] = refl
  resultNodeEquiv3 c r (x ∷ xs) rewrite sym (resultColorEquiv3 (otherColor c) x) | resultNodeEquiv3 c (maxByColor c r (resultColor (otherColor c) x)) xs 
    = resultNode3-step r (resultColor (otherColor c) x) xs

-- main result

bestResultEquiv3 : ∀ (bf : Board ⊎ FinishedBoard) → bestResult bf ≡ bestResult3 bf
bestResultEquiv3 bf = resultColorEquiv3 (getColor bf) (generateTree bf)

---------------------------------
--  Example queries and calls  --
---------------------------------

--open GameInterface (GameImplementation.game)

empt : Bool
empt = isEmpty emptyBoard

-- 65 minutes to evaluate

r : Result
r = bestResult3 (inj₁ emptyBoard) 



{-
-- (GameTheory.tryMoves (inj₁ emptyBoard) (P11 ∷ P12 ∷ []))

t : Maybe Result
t = GameImplementation.bestResultColor 9 X (inj₁ emptyBoard)

b : Board ⊎ FinishedBoard 
b = GameImplementation.tryMoves (inj₁ emptyBoard) (P11 {- ∷ P12 ∷ P13 ∷ P21  ∷ P22 ∷ P23 ∷ P31 -} ∷ [])

leaves : ℕ
leaves = GameImplementation.leavesNo --(GameImplementation.generateTree (inj₁ emptyBoard)) -- 
         (GameImplementation.generateTree b)

n : Maybe ℕ
n = GameImplementation.depthM (GameImplementation.generateTree b)
-}
