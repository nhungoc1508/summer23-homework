module homework-solutions.Extra.NewNew where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Empty as ⊥

open import Cubical.Algebra.Group
open import Cubical.HITs.Bouquet
open import Cubical.HITs.S1

open import Cubical.Data.Fin
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots; predℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.FinData.Base using(predFin)
open import Cubical.Data.Sigma

open import Cubical.Foundations.SIP
open import Cubical.Structures.Pointed
open import Cubical.HITs.S1.Base

open import Cubical.HITs.S1
open import Cubical.HITs.Bouquet

open import Cubical.Structures.Macro
open import Cubical.Structures.Auto

module _ {ℓ} (n : ℕ) where

  taffyDesc : Desc ℓ ℓ ℓ
  taffyDesc = autoDesc (λ (X : Type ℓ) → (S¹ → X) × (Fin n → (S¹ → X)))

  open Macro ℓ taffyDesc public renaming
    ( structure to TaffyStructure
    ; equiv to TaffyEquivStr
    ; univalent to TaffyUnivalentStr
    )

circleHelper : (k : ℕ) →  (n : ℕ) → (k < n) →  S¹ → Bouquet (Fin n)
circleHelper k n _ base = base
circleHelper k zero _ s = base
circleHelper zero (suc n) _ (loop i) = loop (zero , suc-≤-suc zero-≤) i
circleHelper (suc k) (suc n) p (loop i) = ( (λ j → circleHelper k (suc n) (suc-< p) (loop j)) ∙ loop (suc k , p )) i

circToBouq : (n : ℕ) → S¹ → Bouquet (Fin n)
circToBouq zero s = base
circToBouq (suc n) s = circleHelper n (suc n) ≤-refl s

BouquetInstance : ∀ n → TaffyStructure n (Bouquet (Fin n))
BouquetInstance n = circToBouq n , λ x y → circToBouq n y

h' : (n : ℕ) → ((c₁ , c₂) : TaffyStructure n (Bouquet (Fin n))) 
   → {! !} → Type
h' n (c₁ , c₂) = {! BouquetInstance n .fst !}

tmp = {! BouquetInstance zero  !}

h : (n : ℕ) → (f g : S¹ → Bouquet (Fin n))
  → (f ≡ g)
  → (S¹ → Bouquet (Fin n))
h n f g p base = f base
h n f g p (loop i) = hcomp (λ { j (i = i0) → (sym p) j base 
                              ; j (i = i1) → (sym p) j base }) 
                           (g (loop i))
∂ : I → I
∂ i = i ∨ ~ i

lemmaFaces : (n : ℕ) → (f g : S¹ → Bouquet (Fin n)) 
           → (p : f ≡ g) → (i : I) → (j : I) → I
           → Partial (∂ i ∨ ∂ j) (Bouquet (Fin n))
lemmaFaces n f g p i j k (i = i0) = sym p k (loop j)
lemmaFaces n f g p i j k (i = i1) = hfill (λ { k (j = i0) → sym p k base 
                                             ; k (j = i1) → sym p k base }) 
                                          (inS (g (loop j))) k
lemmaFaces n f g p i j k (j = i0) = sym p k base
lemmaFaces n f g p i j k (j = i1) = sym p k base

lemma : (n : ℕ) → (f g : S¹ → Bouquet (Fin n)) 
      → (p : f ≡ g) → (f ≡ h n f g p)
lemma n f g p i base = h n f g p base
lemma n f g p i (loop j) = hcomp (lemmaFaces n f g p i j) (g (loop j)) 