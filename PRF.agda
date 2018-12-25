module PRF where

open import Relation.Binary.PropositionalEquality using (refl; _≡_; sym)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Nat            using (ℕ; zero; suc; _+_)
open import Data.Fin            using (Fin; zero; suc)

natrec : ∀ {A : Set} → A → (ℕ → A → A) → ℕ → A
natrec z s zero     = z
natrec z s (suc n)  = s n (natrec z s n)

data Vec (A : Set) : ℕ → Set where
  nil : Vec A 0
  _,_ : ∀ {n} → Vec A n → A → Vec A (suc n)

data PRF : ℕ → Set where
  zero : PRF 0
  suc  : PRF 1
  proj : ∀ {n} → Fin n → PRF n
  comp : ∀ {m n} → PRF m → Vec (PRF n) m → PRF n
  rec  : ∀ {n} → PRF n → PRF (suc (suc n)) → PRF (suc n)

index : ∀ {A n} → Vec A n → Fin n → A
index nil ()
index (_  , x) zero    = x
index (xs , _) (suc n) = index xs n

mutual
  ⟦_⟧ : ∀ {n} → PRF n → Vec ℕ n → ℕ
  ⟦ zero       ⟧ nil        = 0
  ⟦ suc        ⟧ (nil , n)  = 1 + n
  ⟦ proj i     ⟧ ρ          = index ρ i
  ⟦ comp f gs  ⟧ ρ          = ⟦ f ⟧ (⟦ gs ⟧⋆ ρ)
  ⟦ rec f g    ⟧ (ρ , n)    = natrec (⟦ f ⟧ ρ) (λ n r → ⟦ g ⟧ ((ρ , r) , n)) n

  ⟦_⟧⋆ : ∀ {m n} → Vec (PRF m) n → Vec ℕ m → Vec ℕ n
  ⟦ nil     ⟧⋆ ρ = nil
  ⟦ fs , f  ⟧⋆ ρ = ⟦ fs ⟧⋆ ρ , ⟦ f ⟧ ρ
