{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module Number.Postulates where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
-- open import Cubical.Data.Nat using (zero; suc) renaming (ℕ to Nat; _+_ to _+ₙ_)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

-- open import Cubical.Data.Unit.Base -- Unit
-- open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
-- open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
-- open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- open import Cubical.Data.Maybe.Base
open import Cubical.Relation.Binary.Base -- Rel
open import Function.Base using (_∋_)

ℕℓ  = ℓ-zero
ℕℓ' = ℓ-zero

postulate  
  ℤℓ ℤℓ' : Level
  ℚℓ ℚℓ' : Level
  ℝℓ ℝℓ' : Level
  ℂℓ ℂℓ' : Level

open import Number.Structures
open import Number.Bundles   
open import Number.Inclusions

import MoreAlgebra

module ℕ* where
  import Cubical.Data.Nat as Nat
  import Cubical.Data.Nat.Order as Order

  module Postulates where
    postulate
      min max : Nat.ℕ → Nat.ℕ → Nat.ℕ
      isROrderedCommSemiring : IsROrderedCommSemiring
        (Order._<_)
        (Order._≤_)
        ((MoreAlgebra.Definitions._#'_ {_<_ = Order._<_}))
        (min)
        (max)
        (Nat.zero)
        (1)
        (Nat._+_)
        (Nat._*_)

  module Bundle = ROrderedCommSemiring {ℕℓ} {ℕℓ'}
  Bundle = ROrderedCommSemiring {ℕℓ} {ℕℓ'}
  
  ℕ = Nat.ℕ
  Carrier = ℕ

  bundle : Bundle
  bundle = (record
    { Carrier = ℕ -- Lift {ℓ-zero} {ℝℓ} Nat.ℕ
    ; _<_ = Order._<_
    ; _≤_ = Order._≤_
    ; _#_ = (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
    ; min = Postulates.min
    ; max = Postulates.max
    ; 0f  = Nat.zero
    ; 1f  = (Nat.suc Nat.zero)
    ; _+_ = Nat._+_
    ; _·_ = Nat._*_
    ; isROrderedCommSemiring = Postulates.isROrderedCommSemiring
    })

  _<_ = Bundle._<_ bundle
  _≤_ = Bundle._≤_ bundle
  _#_ = Bundle._#_ bundle
  min = Bundle.min bundle
  max = Bundle.max bundle
  0f  = Bundle.0f  bundle
  1f  = Bundle.1f  bundle
  _+_ = Bundle._+_ bundle
  _·_ = Bundle._·_ bundle
  isROrderedCommSemiring = Bundle.isROrderedCommSemiring bundle

  open IsROrderedCommSemiring isROrderedCommSemiring public
  open import Agda.Builtin.Nat using () renaming (Nat to ℕ₀) public -- this makes ℕ₀ prettier in goals

module ℕ  = ℕ* hiding (ℕ; ℕ₀)
module ℕⁿ = ℕ*
    renaming
    ( Carrier to Carrierⁿ
    ; _<_ to _<ⁿ_
    ; _≤_ to _≤ⁿ_
    ; _#_ to _#ⁿ_
    ; min to minⁿ
    ; max to maxⁿ
    ; 0f  to 0ⁿ 
    ; 1f  to 1ⁿ 
    ; _+_ to _+ⁿ_
    ; _·_ to _·ⁿ_
    ; isROrderedCommSemiring to isROrderedCommSemiringⁿ
    )

module ℤ* where
  module Bundle = ROrderedCommRing {ℤℓ} {ℤℓ'}
  postulate
    bundle : ROrderedCommRing {ℤℓ} {ℤℓ'}

  open Bundle bundle public
  ℤ = Carrier

module ℤ  = ℤ* hiding (ℤ)
module ℤᶻ = ℤ
    renaming
    ( Carrier to Carrierᶻ
    ; _<_ to _<ᶻ_
    ; _≤_ to _≤ᶻ_
    ; _#_ to _#ᶻ_
    ; min to minᶻ
    ; max to maxᶻ
    ; 0f  to 0ᶻ
    ; 1f  to 1ᶻ
    ; _+_ to _+ᶻ_
    ; _·_ to _·ᶻ_
    ; -_  to -ᶻ_ 
    ; isROrderedCommRing to isROrderedCommRingᶻ
    )

module ℚ* where
  module Bundle = ROrderedField {ℚℓ} {ℚℓ'}
  postulate
    bundle : ROrderedField {ℚℓ} {ℚℓ'}

  open Bundle bundle public
  ℚ = Carrier

module ℚ  = ℚ* hiding (ℚ)
module ℚᶠ = ℚ*
  renaming
  ( Carrier to Carrierᶠ
  ; _<_ to _<ᶠ_
  ; _≤_ to _≤ᶠ_
  ; _#_ to _#ᶠ_
  ; min to minᶠ
  ; max to maxᶠ
  ; 0f  to 0ᶠ
  ; 1f  to 1ᶠ
  ; _+_ to _+ᶠ_
  ; _·_ to _·ᶠ_
  ; -_  to -ᶠ_ 
  ; _⁻¹ to _⁻¹ᶠ
  ; isROrderedField to isROrderedFieldᶠ
  )

module ℝ* where
  module Bundle = ROrderedField {ℝℓ} {ℝℓ'}
  postulate
    bundle : ROrderedField {ℝℓ} {ℝℓ'}

  open Bundle bundle public
  ℝ = Carrier

module ℝ  = ℝ* hiding (ℝ)
module ℝʳ = ℝ*
    renaming
    ( Carrier to Carrierʳ
    ; _<_ to _<ʳ_
    ; _≤_ to _≤ʳ_
    ; _#_ to _#ʳ_
    ; min to minʳ
    ; max to maxʳ
    ; 0f  to 0ʳ
    ; 1f  to 1ʳ
    ; _+_ to _+ʳ_
    ; _·_ to _·ʳ_
    ; -_  to -ʳ_ 
    ; _⁻¹ to _⁻¹ʳ
    ; isROrderedField to isROrderedFieldʳ
    )

module ℂ* where
  module Bundle = RField {ℂℓ} {ℂℓ'}
  postulate
    bundle : RField {ℂℓ} {ℂℓ'}

  open Bundle bundle public
  ℂ = Carrier

module ℂ  = ℂ* hiding (ℂ)
module ℂᶜ = ℂ
    renaming
    ( Carrier to Carrierᶜ
    ; _#_ to _#ᶜ_
    ; 0f  to 0ᶜ
    ; 1f  to 1ᶜ
    ; _+_ to _+ᶜ_
    ; _·_ to _·ᶜ_
    ; -_  to -ᶜ_
    ; _⁻¹ to _⁻¹ᶜ
    ; isRField to isRFieldᶜ
    )

module _ where
  open ℕ* using (ℕ)
  open ℤ* using (ℤ)
  open ℚ* using (ℚ)
  open ℝ* using (ℝ)
  open ℂ* using (ℂ)
  postulate
    ℕ↪ℤ : ℕ → ℤ
    ℕ↪ℚ : ℕ → ℚ
    ℕ↪ℂ : ℕ → ℂ
    ℕ↪ℝ : ℕ → ℝ
    ℤ↪ℚ : ℤ → ℚ
    ℤ↪ℝ : ℤ → ℝ
    ℤ↪ℂ : ℤ → ℂ
    ℚ↪ℝ : ℚ → ℝ
    ℚ↪ℂ : ℚ → ℂ
    ℝ↪ℂ : ℝ → ℂ

    ℕ↪ℤinc : IsROrderedCommSemiringInclusion ℕ.bundle                       (record { ℤ.Bundle ℤ.bundle }) ℕ↪ℤ
    ℕ↪ℚinc : IsROrderedCommSemiringInclusion ℕ.bundle                       (record { ℚ.Bundle ℚ.bundle }) ℕ↪ℚ
    ℕ↪ℂinc : Isℕ↪ℂ                           ℕ.bundle                       ℂ.bundle                       ℕ↪ℂ
    ℕ↪ℝinc : IsROrderedCommSemiringInclusion ℕ.bundle                       (record { ℝ.Bundle ℝ.bundle }) ℕ↪ℝ
    ℤ↪ℚinc : IsROrderedCommRingInclusion     ℤ.bundle                       (record { ℚ.Bundle ℚ.bundle }) ℤ↪ℚ
    ℤ↪ℝinc : IsROrderedCommRingInclusion     ℤ.bundle                       (record { ℝ.Bundle ℝ.bundle }) ℤ↪ℝ
    ℤ↪ℂinc : Isℤ↪ℂ                           ℤ.bundle                       ℂ.bundle                       ℤ↪ℂ
    ℚ↪ℝinc : IsROrderedFieldInclusion        ℚ.bundle                       (record { ℝ.Bundle ℝ.bundle }) ℚ↪ℝ
    ℚ↪ℂinc : IsRFieldInclusion               (record { ℚ.Bundle ℚ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℚ↪ℂ
    ℝ↪ℂinc : IsRFieldInclusion               (record { ℝ.Bundle ℝ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℝ↪ℂ
