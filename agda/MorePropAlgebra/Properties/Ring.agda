{-# OPTIONS --cubical --no-import-sorts  #-}

-- open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)

open import Cubical.Structures.Ring

module MorePropAlgebra.Properties.Ring {ℓ} (R : Ring {ℓ}) where

open Ring R
open Cubical.Structures.Ring.Theory R

-- NOTE: a few facts about rings that might be collected from elsewhere
a+b-b≡a : ∀ a b → a ≡ (a + b) - b
a+b-b≡a a b = let P = sym (fst (+-inv b))
                  Q = sym (fst (+-identity a))
                  R = transport (λ i → a ≡ a + P i) Q
                  S = transport (λ i → a ≡ (+-assoc a b (- b)) i ) R
              in S

-- NOTE: this is called `simplL` and `simplL` in `Cubical.Structures.Group.Properties.GroupLemmas`
+-preserves-≡ : ∀{a b} → ∀ c → a ≡ b → a + c ≡ b + c
+-preserves-≡ c a≡b i = a≡b i + c

+-preserves-≡-l : ∀{a b} → ∀ c → a ≡ b → c + a ≡ c + b
+-preserves-≡-l c a≡b i = c + a≡b i

a+b≡0→a≡-b : ∀{a b} → a + b ≡ 0r → a ≡ - b
a+b≡0→a≡-b {a} {b} a+b≡0 = transport
  (λ i →
    let RHS = snd (+-identity (- b))
        LHS₁ : a + (b + - b) ≡ a + 0r
        LHS₁ = +-preserves-≡-l a (fst (+-inv b))
        LHS₂ : (a + b) - b ≡ a
        LHS₂ = transport (λ j →  (+-assoc a b (- b)) j ≡ fst (+-identity a) j) LHS₁
        in  LHS₂ i ≡ RHS i
  ) (+-preserves-≡ (- b) a+b≡0)

-- NOTE: there is already
-- -commutesWithRight-· : (x y : R) →  x · (- y) ≡ - (x · y)

a·-b≡-a·b : ∀ a b → a · (- b) ≡ - (a · b)
a·-b≡-a·b a b =
  let P : a · 0r ≡ 0r
      P = 0-rightNullifies a
      Q : a · (- b + b) ≡ 0r
      Q = transport (λ i →  a · snd (+-inv b) (~ i) ≡ 0r) P
      R : a · (- b) + a · b ≡ 0r
      R = transport (λ i → ·-rdist-+ a (- b) b i ≡ 0r) Q
  in a+b≡0→a≡-b R

a·b-a·c≡a·[b-c] : ∀ a b c → a · b - (a · c) ≡ a · (b - c)
a·b-a·c≡a·[b-c] a b c =
  let P : a · b + a · (- c) ≡ a · (b + - c)
      P = sym (·-rdist-+ a b (- c))
      Q : a · b - a · c ≡ a · (b + - c)
      Q = transport (λ i →  a · b + a·-b≡-a·b a c i ≡ a · (b + - c) ) P
  in  Q
