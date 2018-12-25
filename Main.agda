module Main where

open import Data.Nat using (ℕ)
open import PRF
open import Examples

plus : ℕ → ℕ → ℕ
plus m n = ⟦ add ⟧ ((nil , n) , m)
