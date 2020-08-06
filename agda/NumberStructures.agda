{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module NumberStructures (ℝℓ ℝℓ' : Level) where

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

-- ℚ ℝ ℂ
record IsRField {F : Type ℓ} (_#_ : Rel F F ℓ') (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ x # 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ x y → x + y ≡ y + x
    distrib : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
    -- TODO: properties

-- Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
record IsRLattice {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) : Type (ℓ-max ℓ ℓ') where
  -- TODO: properties

-- ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
-- ring without additive inverse
record IsROrderedCommSemiring {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRLattice : IsRLattice _<_ _≤_ _#_ min max
    -- TODO: properties
  open IsRLattice isRLattice public

-- ℤ ℚ ℝ
record IsROrderedCommRing {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
    -- TODO: properties
  open IsROrderedCommSemiring isROrderedCommSemiring public

-- ℚ ℝ
record IsROrderedField {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ x # 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_
    isRField           : IsRField _#_ 0f 1f _+_ _·_ -_ _⁻¹
  open IsROrderedCommRing isROrderedCommRing public
  open IsRField isRField public

-- ℚ₀⁺ ℝ₀⁺
record IsROrderedSemifield {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (_⁻¹ : (x : F) → {{ x < 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
    -- TODO: properties
    #0-implies-0< : ∀ x → 0f # x → 0f < x
    positivity : ∀ x → 0f ≤ x
  open IsROrderedCommSemiring isROrderedCommSemiring public

-- ℚ⁺ ℝ⁺
record IsROrderedSemifieldWithoutZero {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (_⁻¹ : (x : F) → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRLattice : IsRLattice _<_ _≤_ _#_ min max
    -- isGroup : IsGroup 1f _·_ _⁻¹
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ x y → x + y ≡ y + x
    distrib : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
    -- TODO: properties
  open IsRLattice isRLattice public

