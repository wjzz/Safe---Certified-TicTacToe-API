{-
  @author: Wojciech Jedynak (wjedynak@gmail.com)
-}
module Test where

open import Data.Vec hiding (sum; tail; head)
open import Data.Bool
open import Data.Nat

-- normal recursion schema

sum : {n : ℕ} → Vec ℕ n → ℕ
sum []       = 0
sum (x ∷ xs) = x + sum xs

-- the same, but contrived

head : {n : ℕ} → Vec ℕ (suc n) → ℕ
head (x ∷ xs) = x

tail : {n : ℕ} → Vec ℕ (suc n) → Vec ℕ n
tail (x ∷ xs) = xs

csum : {n : ℕ} → Vec ℕ n → ℕ
csum {zero}  v = 0
csum {suc n} v = head v + csum (tail v)

-- this is structurally recursive, because the last eq is 
-- sum {suc n} v = head v + csum {n} (tail v)
-- so n plays the role of the principal argument

-- a simple test

tsum : {n : ℕ} → Vec ℕ n → ℕ
tsum {0}        []             = 0
tsum {.(1 + n)} (_∷_ {n} x xs) = x + tsum {n} xs

