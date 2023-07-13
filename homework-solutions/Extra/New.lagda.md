{-# OPTIONS --safe #-}
```
module homework-solutions.Extra.New where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Pointed
open import Cubical.Structures.Pointed

private
    variable
        ℓ ℓ' : Level

data S¹ : Type where
    base : S¹
    loop : base ≡ base

-- TypeWithALoop : ∀ {ℓ} → Type (ℓ-suc ℓ)
-- TypeWithALoop {ℓ} = Σ[ X ∈ Type ℓ ] (S¹ → X)

TypeWithALoop : ∀ {ℓ} → Type ℓ → Type (ℓ-suc ℓ)
TypeWithALoop {ℓ} = λ X → Σ[ x ∈ Type ℓ ] (S¹ → x)

-- taffy : ∀ {ℓ} (n : ℕ) → (X : Type ℓ) → (x : X) → TypeWithStr ℓ TypeWithALoop'
-- taffy {ℓ} n X x = X , (X , λ s → x)

taffy : (ℓ : Level) → Type (ℓ-suc ℓ)
taffy ℓ = TypeWithStr ℓ TypeWithALoop

taffyPt : ∀ {ℓ} (A : taffy ℓ) → TypeWithALoop (typ A)
taffyPt = str

TypeWithALoop' : ∀ {ℓ} → (n : ℕ) → (X : Type ℓ) → Type (ℓ-suc ℓ)
TypeWithALoop' {ℓ} n X = {!  !}
```  