{-# OPTIONS --safe #-}
```
module homework-solutions.Extra.HW where

open import Cubical.Foundations.Prelude

private
    variable
        ℓ : Level

-- * Define the circle
data S¹ : Type where
    base : S¹
    loop : base ≡ base

TypeWithALoop : ∀ {ℓ} →  Type (ℓ-suc ℓ)
TypeWithALoop {ℓ} = Σ[ X ∈ Type ℓ ] (S¹ → X) 

-- Paths (X , c) ≡ (X , c) in TypeWithALoop are
-- f : X ≃ X  so that f(c) = β ∙ c ∙ β⁻¹

betterloop : {X : Type ℓ} (f g : S¹ → X) 
             → (f ≡ g) 
             → (S¹ → X)
betterloop f g p base = f base
betterloop f g p (loop i) = hcomp (λ { j (i = i0) → (sym p) j base 
                                     ; j (i = i1) → (sym p) j base }) 
                            (g (loop i))

∂ : I → I
∂ i = i ∨ ~ i

betterloopSides : {X : Type ℓ} (f g : S¹ → X) → (p : f ≡ g) 
                  → (i j : I) → Partial (∂ i) X
betterloopSides f g p i j (i = i0) = sym p j base
betterloopSides f g p i j (i = i1) = sym p j base

lemmaFaces : {X : Type ℓ} (f g : S¹ → X) → (p : f ≡ g) 
             → (i : I) → (j : I) → I → Partial (∂ i ∨ ∂ j) X
lemmaFaces f g p i j k (i = i0) = sym p k (loop j)
lemmaFaces f g p i j k (i = i1) = hfill (betterloopSides f g p j) (inS (g (loop j))) k
lemmaFaces f g p i j k (j = i0) = sym p k base
lemmaFaces f g p i j k (j = i1) = sym p k base

lemma : {X : Type ℓ} (f g : S¹ → X) 
        → (p : f ≡ g)
        → (f ≡ betterloop f g p)
lemma f g p i base = betterloop f g p base
lemma f g p i (loop j) = hcomp (lemmaFaces f g p i j) (g (loop j))
```    