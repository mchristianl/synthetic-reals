{-# OPTIONS --cubical --no-import-sorts #-}

module NumberSecondAttempt where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)

open import NumberPostulates
open import NumberStructures ℝℓ ℝℓ'
open import NumberBundles    ℝℓ ℝℓ'
open import NumberInclusions ℝℓ ℝℓ'

module _ where
  open ROrderedField ℝOF
  data Number : Type (ℓ-max ℝℓ ℝℓ') where
    ℕ[_]   : (x : ℝCarrier) → Σ[ z ∈ ℕCarrier ] ℕ↪ℝ z ≡ x → Number
    ℤ[_]   : (x : ℝCarrier) → Σ[ z ∈ ℤCarrier ] ℤ↪ℝ z ≡ x → Number
    ℚ[_]   : (x : ℝCarrier) → Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x → Number
    ℝ[_]   : (x : ℝCarrier) → Unit → Number
    ℚ₀⁺[_] : (x : ℝCarrier) → (0f ≤ x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x) → Number
    ℚ⁺[_]  : (x : ℝCarrier) → (0f < x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x) → Number
    ℝ₀⁺[_] : (x : ℝCarrier) → 0f ≤ x → Number
    ℝ⁺[_]  : (x : ℝCarrier) → 0f < x → Number

  num : Number → ℝCarrier
  num (ℕ[   x ] _) = x
  num (ℤ[   x ] _) = x
  num (ℚ[   x ] _) = x
  num (ℝ[   x ] _) = x
  num (ℚ₀⁺[ x ] _) = x
  num (ℚ⁺[  x ] _) = x
  num (ℝ₀⁺[ x ] _) = x
  num (ℝ⁺[  x ] _) = x

  data NumberType : Type where
    Tℕ   : NumberType
    Tℤ   : NumberType
    Tℚ   : NumberType
    Tℝ   : NumberType
    Tℚ₀⁺ : NumberType
    Tℚ⁺  : NumberType
    Tℝ₀⁺ : NumberType
    Tℝ⁺  : NumberType

  totype : NumberType → Type (ℓ-max ℝℓ ℝℓ')
  totype Tℕ   = (x : ℝCarrier) → Lift {ℝℓ} {ℓ-max ℝℓ ℝℓ'} (Σ[ z ∈ ℕCarrier ] ℕ↪ℝ z ≡ x)
  totype Tℤ   = (x : ℝCarrier) → Lift {ℝℓ} {ℓ-max ℝℓ ℝℓ'} (Σ[ z ∈ ℤCarrier ] ℤ↪ℝ z ≡ x)
  totype Tℚ   = (x : ℝCarrier) → Lift {ℝℓ} {ℓ-max ℝℓ ℝℓ'} (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x)
  totype Tℝ   = (x : ℝCarrier) → Lift {ℓ-zero} {ℓ-max ℝℓ ℝℓ'} (Unit)
  totype Tℚ₀⁺ = (x : ℝCarrier) → (0f ≤ x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x)
  totype Tℚ⁺  = (x : ℝCarrier) → (0f < x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x)
  totype Tℝ₀⁺ = (x : ℝCarrier) → 0f ≤ x
  totype Tℝ⁺  = (x : ℝCarrier) → 0f < x
  
  +-table : NumberType → NumberType → NumberType
  +-table x y = y

module GenericOperations where
  module ℕ' = ROrderedCommSemiring ℕOCSR
  module ℝ' = ROrderedField ℝOF
  module ℚ' = ROrderedField ℚOF

  module _ where
    open ℝ'
    postulate
      lemma1 : ∀ x y → 0f < x → 0f < y → 0f < (x + y)
      lemma2 : ∀ x y → 0f ≤ x → 0f ≤ y → 0f ≤ (x + y)

  _+_ : Number → Number → Number
  -- IsROrderedCommSemiringInclusion.preserves-+ ℕ↪ℝinc
  ℕ[ x ] (x₁ , p₁)        + ℕ[ y ] (y₁ , q₁)        =  ℕ[ x ℝ'.+ y ]
    (x₁ ℕ'.+ y₁ , transport (λ i → ℕ↪ℝ (x₁ ℕ'.+ y₁) ≡ (p₁ i ℝ'.+ q₁ i)) (IsROrderedCommSemiringInclusion.preserves-+ ℕ↪ℝinc x₁ y₁) )
  ℚ⁺[ x ] (p₂ , x₁ , p₁) + ℚ⁺[ y ] (q₂ , y₁ , q₁) = ℚ⁺[ x ℝ'.+ y ]
    (lemma1 x y p₂ q₂ , (x₁ ℚ'.+ y₁ , transport (λ i → ℚ↪ℝ (x₁ ℚ'.+ y₁) ≡ (p₁ i ℝ'.+ q₁ i)) (IsROrderedFieldInclusion.preserves-+ ℚ↪ℝinc x₁ y₁)))
  ℚ₀⁺[ x ] (p₂ , x₁ , p₁) + ℚ₀⁺[ y ] (q₂ , y₁ , q₁) = ℚ₀⁺[ x ℝ'.+ y ]
    (lemma2 x y p₂ q₂ , (x₁ ℚ'.+ y₁ , transport (λ i → ℚ↪ℝ (x₁ ℚ'.+ y₁) ≡ (p₁ i ℝ'.+ q₁ i)) (IsROrderedFieldInclusion.preserves-+ ℚ↪ℝinc x₁ y₁)))
  -- TODO: more cases
  -- default case
  x + y = ℝ[ num x ℝ'.+ num y ] tt

  instance
    0<ℚ⁺ : ∀{x p} → ℝ'.0f ℝ'.< num (ℚ⁺[ x ] p)
    0<ℚ⁺ {x} {0<x , p} = 0<x

