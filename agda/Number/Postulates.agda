{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module Number.Postulates where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
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
import Number.Inclusions

import MoreAlgebra

module ℕ* where
  import Cubical.Data.Nat as Nat
  import Cubical.Data.Nat.Order as Order

  open import Agda.Builtin.Nat using () renaming (Nat to ℕ) public

  module Postulates where
    postulate
      min max : ℕ → ℕ → ℕ
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

  Carrier = ℕ

  bundle : Bundle
  bundle = (record
    { Carrier = ℕ
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

module ℕ  = ℕ* hiding (ℕ)
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
  module Postulates where
    postulate
      ℤ           : Type ℤℓ
      _<_ _≤_ _#_ : Rel ℤ ℤ ℤℓ'
      min max     : ℤ → ℤ → ℤ
      0f 1f       : ℤ
      _+_ _·_     : ℤ → ℤ → ℤ
      -_          : ℤ → ℤ
      isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_
      
  module Bundle = ROrderedCommRing {ℤℓ} {ℤℓ'}
  Bundle = ROrderedCommRing {ℤℓ} {ℤℓ'}
  
  open Postulates public
  
  Carrier = ℤ

  bundle : Bundle
  bundle = (record
    { Carrier = ℤ
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; -_  = -_
    ; isROrderedCommRing = isROrderedCommRing
    })
  
  open IsROrderedCommRing isROrderedCommRing public

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
  module Postulates where
    postulate
      ℚ           : Type ℚℓ
      _<_ _≤_ _#_ : Rel ℚ ℚ ℚℓ'
      min max     : ℚ → ℚ → ℚ
      0f 1f       : ℚ
      _+_ _·_     : ℚ → ℚ → ℚ
      -_          : ℚ → ℚ
      _⁻¹         : (x : ℚ) → {{ x # 0f }} → ℚ
      isROrderedField : IsROrderedField _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ _⁻¹

  module Bundle = ROrderedField {ℚℓ} {ℚℓ'}
  Bundle = ROrderedField {ℚℓ} {ℚℓ'}
  
  open Postulates public
  
  Carrier = ℚ

  bundle : Bundle
  bundle = (record
    { Carrier = ℚ
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; -_  = -_
    ; _⁻¹ = _⁻¹
    ; isROrderedField = isROrderedField
    })

  open IsROrderedField isROrderedField public

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
  module Postulates where
    postulate
      ℝ           : Type ℝℓ
      _<_ _≤_ _#_ : Rel ℝ ℝ ℝℓ'
      min max     : ℝ → ℝ → ℝ
      0f 1f       : ℝ
      _+_ _·_     : ℝ → ℝ → ℝ
      -_          : ℝ → ℝ
      _⁻¹         : (x : ℝ) → {{ x # 0f }} → ℝ
      isROrderedField : IsROrderedField _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ _⁻¹

  module Bundle = ROrderedField {ℝℓ} {ℝℓ'}
  Bundle = ROrderedField {ℝℓ} {ℝℓ'}
  
  open Postulates public
  
  Carrier = ℝ

  bundle : Bundle
  bundle = (record
    { Carrier = ℝ
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; -_  = -_
    ; _⁻¹ = _⁻¹
    ; isROrderedField = isROrderedField
    })

  open IsROrderedField isROrderedField public

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
  module Postulates where
    postulate
      ℂ           : Type ℂℓ
      _#_         : Rel ℂ ℂ ℂℓ'
      0f 1f       : ℂ
      _+_ _·_     : ℂ → ℂ → ℂ
      -_          : ℂ → ℂ
      _⁻¹         : (x : ℂ) → {{ x # 0f }} → ℂ
      isRField : IsRField _#_ 0f 1f _+_ _·_ -_ _⁻¹

  module Bundle = RField {ℂℓ} {ℂℓ'}
  Bundle = RField {ℂℓ} {ℂℓ'}

  open Postulates public

  Carrier = ℂ

  bundle : Bundle
  bundle = (record
    { Carrier  = ℂ
    ; _#_      = _#_
    ; 0f       = 0f
    ; 1f       = 1f
    ; _+_      = _+_
    ; _·_      = _·_
    ; -_       = -_
    ; _⁻¹      = _⁻¹
    ; isRField = isRField
    })

  open IsRField isRField public

module ℂ  = ℂ* hiding (ℂ)
module ℂᶜ = ℂ*
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

Isℕ↪ℤ = Number.Inclusions.IsROrderedCommSemiringInclusion
Isℕ↪ℚ = Number.Inclusions.IsROrderedCommSemiringInclusion
Isℕ↪ℂ = Number.Inclusions.Isℕ↪ℂ
Isℕ↪ℝ = Number.Inclusions.IsROrderedCommSemiringInclusion
Isℤ↪ℚ = Number.Inclusions.IsROrderedCommRingInclusion
Isℤ↪ℝ = Number.Inclusions.IsROrderedCommRingInclusion
Isℤ↪ℂ = Number.Inclusions.Isℤ↪ℂ
Isℚ↪ℝ = Number.Inclusions.IsROrderedFieldInclusion
Isℚ↪ℂ = Number.Inclusions.IsRFieldInclusion
Isℝ↪ℂ = Number.Inclusions.IsRFieldInclusion

module Isℕ↪ℤ = Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℕ↪ℚ = Number.Inclusions.IsROrderedCommSemiringInclusion
--module Isℕ↪ℂ = Number.Inclusions.Isℕ↪ℂ
module Isℕ↪ℝ = Number.Inclusions.IsROrderedCommSemiringInclusion
module Isℤ↪ℚ = Number.Inclusions.IsROrderedCommRingInclusion
module Isℤ↪ℝ = Number.Inclusions.IsROrderedCommRingInclusion
--module Isℤ↪ℂ = Number.Inclusions.Isℤ↪ℂ
module Isℚ↪ℝ = Number.Inclusions.IsROrderedFieldInclusion
module Isℚ↪ℂ = Number.Inclusions.IsRFieldInclusion
module Isℝ↪ℂ = Number.Inclusions.IsRFieldInclusion

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

    ℕ↪ℤinc : Isℕ↪ℤ (record {ℕ*}) (record {ℤ*}) ℕ↪ℤ
    ℕ↪ℚinc : Isℕ↪ℚ (record {ℕ*}) (record {ℚ*}) ℕ↪ℚ
    ℕ↪ℂinc : Isℕ↪ℂ (record {ℕ*}) (record {ℂ*}) ℕ↪ℂ
    ℕ↪ℝinc : Isℕ↪ℝ (record {ℕ*}) (record {ℝ*}) ℕ↪ℝ
    ℤ↪ℚinc : Isℤ↪ℚ (record {ℤ*}) (record {ℚ*}) ℤ↪ℚ
    ℤ↪ℝinc : Isℤ↪ℝ (record {ℤ*}) (record {ℝ*}) ℤ↪ℝ
    ℤ↪ℂinc : Isℤ↪ℂ (record {ℤ*}) (record {ℂ*}) ℤ↪ℂ
    ℚ↪ℝinc : Isℚ↪ℝ (record {ℚ*}) (record {ℝ*}) ℚ↪ℝ
    ℚ↪ℂinc : Isℚ↪ℂ (record {ℚ*}) (record {ℂ*}) ℚ↪ℂ
    ℝ↪ℂinc : Isℝ↪ℂ (record {ℝ*}) (record {ℂ*}) ℝ↪ℂ

    {-
    ℕ↪ℤinc : Isℕ↪ℤ                    ℕ.bundle    (record { ℤ.Bundle ℤ.bundle }) ℕ↪ℤ
    ℕ↪ℚinc : Isℕ↪ℚ                    ℕ.bundle    (record { ℚ.Bundle ℚ.bundle }) ℕ↪ℚ
    ℕ↪ℂinc : Isℕ↪ℂ                    ℕ.bundle                       ℂ.bundle    ℕ↪ℂ
    ℕ↪ℝinc : Isℕ↪ℝ                    ℕ.bundle    (record { ℝ.Bundle ℝ.bundle }) ℕ↪ℝ
    ℤ↪ℚinc : Isℤ↪ℚ                    ℤ.bundle    (record { ℚ.Bundle ℚ.bundle }) ℤ↪ℚ
    ℤ↪ℝinc : Isℤ↪ℝ                    ℤ.bundle    (record { ℝ.Bundle ℝ.bundle }) ℤ↪ℝ
    ℤ↪ℂinc : Isℤ↪ℂ                    ℤ.bundle                       ℂ.bundle    ℤ↪ℂ
    ℚ↪ℝinc : Isℚ↪ℝ                    ℚ.bundle    (record { ℝ.Bundle ℝ.bundle }) ℚ↪ℝ
    ℚ↪ℂinc : Isℚ↪ℂ (record { ℚ.Bundle ℚ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℚ↪ℂ
    ℝ↪ℂinc : Isℝ↪ℂ (record { ℝ.Bundle ℝ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℝ↪ℂ
    -}
