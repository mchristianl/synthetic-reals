{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module NumberPostulates where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Data.Maybe.Base

postulate
  ℝℓ ℝℓ' : Level

open import NumberStructures ℝℓ ℝℓ'
open import NumberBundles    ℝℓ ℝℓ'
open import NumberInclusions ℝℓ ℝℓ'

postulate
  ℕOCSR : ROrderedCommSemiring {ℝℓ} {ℝℓ'}
  ℤOCR  : ROrderedCommRing     {ℝℓ} {ℝℓ'}
  ℚOF   : ROrderedField        {ℝℓ} {ℝℓ'}
  ℝOF   : ROrderedField        {ℝℓ} {ℝℓ'}
  ℂF    : RField               {ℝℓ} {ℝℓ'}

-- NOTE: these should correspond with the "real" ℕ, ℤ, ℚ and ℝ
ℕCarrier = ROrderedCommSemiring.Carrier ℕOCSR
ℤCarrier = ROrderedCommRing.Carrier ℤOCR
ℚCarrier = ROrderedField.Carrier ℚOF
ℝCarrier = ROrderedField.Carrier ℝOF
ℂCarrier = RField.Carrier ℂF

postulate
  ℕ↪ℤ    : ℕCarrier → ℤCarrier
  ℕ↪ℤinc : IsROrderedCommSemiringInclusion ℕOCSR (record { ROrderedCommRing ℤOCR }) ℕ↪ℤ

  ℕ↪ℚ    : ℕCarrier → ℚCarrier
  ℕ↪ℚinc : IsROrderedCommSemiringInclusion ℕOCSR (record { ROrderedField ℚOF }) ℕ↪ℚ

  ℕ↪ℂ    : ℕCarrier → ℂCarrier
  -- ℕ↪ℂinc : IsRFieldInclusion (record { ROrderedCommSemiring ℕOCSR } ) (record { RField ℂF }) ℕ↪ℂ

  ℕ↪ℝ    : ℕCarrier → ℝCarrier
  ℕ↪ℝinc : IsROrderedCommSemiringInclusion ℕOCSR (record { ROrderedField ℝOF }) ℕ↪ℝ

  ℤ↪ℚ    : ℤCarrier → ℚCarrier
  ℤ↪ℚinc : IsROrderedCommRingInclusion ℤOCR (record { ROrderedField ℚOF }) ℤ↪ℚ

  ℤ↪ℝ    : ℤCarrier → ℝCarrier
  ℤ↪ℝinc : IsROrderedCommRingInclusion ℤOCR (record { ROrderedField ℝOF }) ℤ↪ℝ

  ℤ↪ℂ    : ℤCarrier → ℂCarrier
  -- ℤ↪ℂinc : IsRCommRingInclusion ℤOCR (record { RField ℂF }) ℤ↪ℂ

  ℚ↪ℝ    : ℚCarrier → ℝCarrier
  ℚ↪ℝinc : IsROrderedFieldInclusion ℚOF (record { ROrderedField ℝOF }) ℚ↪ℝ

  ℚ↪ℂ    : ℚCarrier → ℂCarrier
  ℚ↪ℂinc : IsRFieldInclusion (record { ROrderedField ℚOF }) (record { RField ℂF }) ℚ↪ℂ

  ℝ↪ℂ    : ℝCarrier → ℂCarrier
  ℝ↪ℂinc : IsRFieldInclusion (record { ROrderedField ℝOF }) (record { RField ℂF }) ℝ↪ℂ
