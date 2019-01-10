module Examples where

open import PRF
open import Data.Fin  using (Fin; zero; suc)
open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (+-*-suc; +-comm; *-comm)
open import Data.Bool using (Bool; true; false; _∧_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

𝟎 : Fin 1
𝟎 = zero

𝟏 : Fin 3
𝟏 = suc zero

add : PRF 2
add = rec (proj 𝟎) (comp suc (nil , proj 𝟏))

add-correct : ∀ m n → m + n ≡ ⟦ add ⟧ ((nil , n) , m)
add-correct zero    n = refl
add-correct (suc m) n = cong suc (add-correct m n)

mult : PRF 2
mult = rec (comp zero nil) (comp add (nil , proj (suc zero) , proj (suc (suc zero))))

mult-correct : ∀ m n → m * n ≡ ⟦ mult ⟧ ((nil , n) , m)
mult-correct zero    n = refl
mult-correct (suc m) n rewrite add-correct n (m * n) | mult-correct m n = refl

exp : PRF 2
exp = rec (comp suc (nil , comp zero nil)) (comp mult (nil , proj (suc zero) , proj (suc (suc zero))))

exp-correct : ∀ m n → n ^ m ≡ ⟦ exp ⟧ ((nil , n) , m)
exp-correct zero    n = refl
exp-correct (suc m) n rewrite mult-correct n (n ^ m) | exp-correct m n = refl

ite : PRF 3
ite = rec (proj zero) (proj (suc (suc zero)))

conj : PRF 2
conj = rec (comp zero nil) (proj (suc (suc zero)))

to-bool : ℕ → Bool
to-bool zero    = false
to-bool (suc n) = true

conj-correct : ∀ m n → to-bool (⟦ conj ⟧ ((nil , m) , n)) ≡ (to-bool m) ∧ (to-bool n)
conj-correct zero zero = refl
conj-correct (suc m) zero = refl
conj-correct zero (suc n) = refl
conj-correct (suc m) (suc n) = refl

L2Q4-1 : ⟦ comp zero nil ⟧ ((nil , 5) , 7) ≡ 0
L2Q4-1 = refl

L2Q4-2 : ⟦ comp suc (nil , proj zero) ⟧ (nil , 5 , 7) ≡ 8
L2Q4-2 = refl

L2Q4-3 : ⟦ rec zero (proj (suc zero)) ⟧ (nil , 2) ≡ 0
L2Q4-3 = refl
