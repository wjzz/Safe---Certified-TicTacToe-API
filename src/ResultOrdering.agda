module ResultOrdering where

open import Data.Product
open import Data.Sum

open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

open import Game

------------------------------------------------------
--  Induction rules to make automation work better  --
------------------------------------------------------
  
color-ind : {t : Color → Set} → t X → t O → (∀ (c : Color) → t c)
color-ind tX tO X = tX
color-ind tX tO O = tO
                    
result-ind : {t : Result → Set} → t (Win X) → t Draw → t (Win O) → (∀ (r : Result) → t r)
result-ind tWX tD tWO (Win X) = tWX
result-ind tWX tD tWO (Win O) = tWO
result-ind tWX tD tWO Draw    = tD
                                
                                
--------------------------------------------------------------------------------------------------
--  Functions for comparing results from a given player's perspective and picking the best one  --
--------------------------------------------------------------------------------------------------
  
maxByColor : Color → Result → Result → Result
maxByColor X (Win X) r2 = Win X
maxByColor X (Win O) r2 = r2
maxByColor X Draw (Win X) = Win X
maxByColor X Draw (Win O) = Draw
maxByColor X Draw Draw = Draw
maxByColor O (Win O) r2 = Win O
maxByColor O (Win X) r2 = r2
maxByColor O Draw (Win O) = Win O
maxByColor O Draw (Win X) = Draw
maxByColor O Draw Draw = Draw
                         
maxByColorAssoc : ∀ (c : Color) (r1 r2 r3 : Result) → maxByColor c (maxByColor c r1 r2) r3 ≡ maxByColor c r1 (maxByColor c r2 r3)
maxByColorAssoc = color-ind (result-ind (result-ind (result-ind refl refl refl)(result-ind refl refl refl)(result-ind refl refl refl))
                                        (result-ind (result-ind refl refl refl)(result-ind refl refl refl)(result-ind refl refl refl))
                                        (result-ind (result-ind refl refl refl)(result-ind refl refl refl)(result-ind refl refl refl)))
                            (result-ind (result-ind (result-ind refl refl refl)(result-ind refl refl refl)(result-ind refl refl refl))
                                        (result-ind (result-ind refl refl refl)(result-ind refl refl refl)(result-ind refl refl refl))
                                        (result-ind (result-ind refl refl refl)(result-ind refl refl refl)(result-ind refl refl refl)))

{- BASE result maxByColorAssoc -} 
                                                                                                                                {-
maxByColorAssoc X (Win X) r2 r3 = refl
maxByColorAssoc X Draw (Win X) r3 = refl
maxByColorAssoc X Draw (Win O) r3 = refl
maxByColorAssoc X Draw Draw (Win X) = refl
maxByColorAssoc X Draw Draw (Win O) = refl
maxByColorAssoc X Draw Draw Draw = refl
maxByColorAssoc X (Win O) r2 r3 = refl
maxByColorAssoc O (Win O) r2 r3 = refl
maxByColorAssoc O Draw (Win O) r3 = refl
maxByColorAssoc O Draw (Win X) r3 = refl
maxByColorAssoc O Draw Draw (Win O) = refl
maxByColorAssoc O Draw Draw (Win X) = refl
maxByColorAssoc O Draw Draw Draw = refl
maxByColorAssoc O (Win X) r2 r3 = refl
                                  -}
maxByColor-refl : ∀ (c : Color) (r : Result) → maxByColor c r r ≡ r
maxByColor-refl = color-ind (result-ind refl refl refl) 
                            (result-ind refl refl refl)

{- BASE result maxByColor-refl -} 

                                                  {-
maxByColor-refl X (Win X) = refl
maxByColor-refl X (Win O) = refl
maxByColor-refl X Draw    = refl
maxByColor-refl O (Win X) = refl
maxByColor-refl O (Win O) = refl
maxByColor-refl O Draw    = refl
                            -}
                              
maxByColor-antisym : ∀ (c : Color) (r1 r2 : Result) → maxByColor c r1 r2 ≡ r2 → maxByColor c r2 r1 ≡ r1 → r1 ≡ r2
maxByColor-antisym X (Win X) r2 r12 r21 = r12
maxByColor-antisym X (Win O) (Win X) r12 r21 = sym r21
maxByColor-antisym X (Win O) (Win O) r12 r21 = refl
maxByColor-antisym X (Win O) Draw r12 r21 = sym r21
maxByColor-antisym X Draw (Win X) r12 r21 = sym r21
maxByColor-antisym X Draw (Win O) r12 r21 = r12
maxByColor-antisym X Draw Draw r12 r21 = refl
maxByColor-antisym O (Win O) r2 r12 r21 = r12
maxByColor-antisym O (Win X) (Win O) r12 r21 = sym r21
maxByColor-antisym O (Win X) (Win X) r12 r21 = refl
maxByColor-antisym O (Win X) Draw r12 r21 = sym r21
maxByColor-antisym O Draw (Win O) r12 r21 = sym r21
maxByColor-antisym O Draw (Win X) r12 r21 = r12
maxByColor-antisym O Draw Draw r12 r21 = refl
                                         
maxByColor-trans : ∀ (c : Color) (r1 r2 r3 : Result) → maxByColor c r1 r2 ≡ r2 → maxByColor c r2 r3 ≡ r3 → maxByColor c r1 r3 ≡ r3
maxByColor-trans X (Win X) (Win X) r3 r122 r233 = r233
maxByColor-trans X (Win X) (Win O) r3 () r233
maxByColor-trans X (Win X) Draw r3 () r233
maxByColor-trans X (Win O) r2 r3 r122 r233 = refl
maxByColor-trans X Draw r2 (Win X) r122 r233 = refl
maxByColor-trans X Draw (Win X) (Win O) r122 ()
maxByColor-trans X Draw (Win O) (Win O) () r233
maxByColor-trans X Draw Draw (Win O) r122 ()
maxByColor-trans X Draw r2 Draw r122 r233 = refl
maxByColor-trans O (Win O) (Win O) r3 r122 r233 = r233
maxByColor-trans O (Win O) (Win X) r3 () r233
maxByColor-trans O (Win O) Draw r3 () r233
maxByColor-trans O (Win X) r2 r3 r122 r233 = refl
maxByColor-trans O Draw r2 (Win O) r122 r233 = refl
maxByColor-trans O Draw (Win O) (Win X) r122 ()
maxByColor-trans O Draw (Win X) (Win X) () r233
maxByColor-trans O Draw Draw (Win X) r122 ()
maxByColor-trans O Draw r2 Draw r122 r233 = refl

{- BASE result maxByColor-antisym maxByColor-trans -} 
                           
maxByColor-inv : ∀ (c : Color)(r1 r2 : Result) → maxByColor c r1 r2 ≡ r1 ⊎ maxByColor c r1 r2 ≡ r2                 
maxByColor-inv = color-ind (result-ind (result-ind (inj₁ refl) (inj₁ refl) (inj₁ refl)) 
                           (result-ind (inj₂ refl) (inj₁ refl) (inj₁ refl)) (result-ind (inj₂ refl) (inj₂ refl) (inj₁ refl)))
                           (result-ind (result-ind (inj₁ refl) (inj₂ refl) (inj₂ refl)) (result-ind (inj₁ refl) (inj₁ refl) (inj₂ refl)) 
                           (result-ind (inj₁ refl) (inj₁ refl) (inj₁ refl)))

maxByColor-comm : ∀ (c : Color)(r1 r2 : Result) → maxByColor c r1 r2 ≡ maxByColor c r2 r1
maxByColor-comm = color-ind (result-ind (result-ind refl refl refl) (result-ind refl refl refl) (result-ind refl refl refl))
                            (result-ind (result-ind refl refl refl) (result-ind refl refl refl) (result-ind refl refl refl))

{- BASE result maxByColor-comm -}

--------------------------
--  A poset on results  --
-------------------------

data _⊑_[_] : Result → Result → Color → Set where
  mbc : {c : Color}{r1 r2 : Result} → maxByColor c r1 r2 ≡ r2 → r1 ⊑ r2 [ c ]
  
{-
_⊑_[_] : Result → Result → Color → Set
r1 ⊑ r2 [ c ] = maxByColor c r1 r2 ≡ r2
-}

⊑-refl : ∀ {c : Color} {r : Result} → r ⊑ r [ c ]
⊑-refl {c} {r} = mbc (maxByColor-refl c r)
                                   
⊑-antisym : ∀ {c : Color} {r1 r2 : Result} → r1 ⊑ r2 [ c ] → r2 ⊑ r1 [ c ] → r1 ≡ r2
⊑-antisym {c} {r1} {r2} (mbc p1) (mbc p2) = maxByColor-antisym c r1 r2 p1 p2
                                                  
⊑-trans : ∀ {c : Color} {r1 r2 r3 : Result} → r1 ⊑ r2 [ c ] → r2 ⊑ r3 [ c ] → r1 ⊑ r3 [ c ]
⊑-trans {c} {r1} {r2} {r3} (mbc p1) (mbc p2) = mbc (maxByColor-trans c r1 r2 r3 p1 p2)
                                                      
⊑-max-l : ∀ {c : Color} {r1 r2 : Result} → r1 ⊑ (maxByColor c r1 r2) [ c ]
⊑-max-l {c} {r1} {r2} = mbc lem where
  lem : maxByColor c r1 (maxByColor c r1 r2) ≡ maxByColor c r1 r2
  lem rewrite sym (maxByColorAssoc c r1 r1 r2) | maxByColor-refl c r1 = refl

⊑-max-r : ∀ {c : Color} {r1 r2 : Result} → r2 ⊑ (maxByColor c r1 r2) [ c ]
⊑-max-r {c} {r1} {r2} rewrite maxByColor-comm c r1 r2 = ⊑-max-l {c} {r2} {r1}
                                                                                              
{- BASE result ⊑-refl ⊑-antisym ⊑-trans ⊑-max-l ⊑-max-r -}
