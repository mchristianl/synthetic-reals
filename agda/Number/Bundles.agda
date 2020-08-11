{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module Number.Bundles where

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

open import Number.Structures

-- Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
record RLattice : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor rlattice
  field
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    isRLattice  : IsRLattice _<_ _≤_ _#_ min max

  infixl 4 _<_
  infixl 4 _≤_
  infixl 4 _#_

-- ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
-- ring without additive inverse
record ROrderedCommSemiring : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- _-_         : (x y : Carrier) → (y ≤ x) → Carrier -- is that a good idea?
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
  open IsROrderedCommSemiring isROrderedCommSemiring public


-- ℤ ℚ ℝ
record ROrderedCommRing : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- ROrderedCommRing
    -_          : Carrier → Carrier
    isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_
  open IsROrderedCommRing isROrderedCommRing public

-- ℚ ℝ
record ROrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- ROrderedCommRing
    -_          : Carrier → Carrier
    -- ROrderedField
    _⁻¹         : (x : Carrier) → {{ x # 0f }} → Carrier
    isROrderedField : IsROrderedField _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_ _⁻¹
  open IsROrderedField isROrderedField public

-- ℚ₀⁺ ℝ₀⁺
record ROrderedSemifield : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- ROrderedSemifield
    _-_         : (x y : Carrier) → (y ≤ x) → Carrier -- is that a good idea?
    _⁻¹         : (x : Carrier) → {{ 0f < x }} → Carrier

-- ℚ⁺ ℝ⁺
record ROrderedSemifieldWithoutZero : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    -- RLattice
    Carrier     : Type ℓ
    _<_ _≤_ _#_ : Rel Carrier Carrier ℓ'
    min max     : Carrier → Carrier → Carrier
    -- ROrderedSemifieldWithoutZero
    1f          : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    _-_         : (x y : Carrier) → (y < x) → Carrier -- is that a good idea?
    _⁻¹         : Carrier → Carrier

-- ℚ ℝ ℂ
record RField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier     : Type ℓ
    _#_ : Rel Carrier Carrier ℓ'
    -- RCommSemiring
    0f 1f       : Carrier
    _+_ _·_     : Carrier → Carrier → Carrier
    -- RCommRing
    -_          : Carrier → Carrier
    -- RField
    _⁻¹         : (x : Carrier) → {{ x # 0f }} → Carrier
    isRField : IsRField _#_ 0f 1f _+_ _·_ -_ _⁻¹

