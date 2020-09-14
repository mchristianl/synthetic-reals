{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Structures2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic

open import Utils
open import MoreLogic.Definitions
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions
open import MorePropAlgebra.Consequences
open import MorePropAlgebra.Structures


{-
| name | struct              | apart | abs | order | cauchy | sqrt₀⁺  | exp | final name                                                             |
|------|---------------------|-------|-----|-------|--------|---------|-----|------------------------------------------------------------------------|
| ℕ    | CommSemiring        |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedCommSemiring                                            |
| ℤ    | CommRing            |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedCommRing                                                |
| ℚ    | Field               |  (✓)  | (✓) | lin.  |        | (on x²) | (✓) | LinearlyOrderedField                                                   |
| ℝ    | Field               |  (✓)  | (✓) | part. |   ✓    |    ✓    | (✓) | CompletePartiallyOrderedFieldWithSqrt                                  |
| ℂ    | euclidean 2-Product |  (✓)  | (✓) |       |  (✓)   |         |  ?  | EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt             |
| R    | Ring                |   ✓   |  ✓  |       |        |         |  ?  | ApartnessRingWithAbsIntoCompletePartiallyOrderedFieldWithSqrt          |
| G    | Group               |   ✓   |  ✓  |       |        |         |  ?  | ApartnessGroupWithAbsIntoCompletePartiallyOrderedFieldWithSqrt         |
| K    | Field               |   ✓   |  ✓  |       |   ✓    |         |  ?  | CompleteApartnessFieldWithAbsIntoCompletePartiallyOrderedFieldWithSqrt |

-- NOTE: what about conjugation `conj`?
-}

-- we usually mean "CommRing" when writing just "Ring" ⇒ TODO: rename this where applicable

-- IsLinearlyOrderedCommSemiring
--   isSet
--   IsCommSemiring 0f 1f _+_ _·_
--   IsStrictLinearOrder _<_
--     ⇒ IsApartnessRel _#_
--     ⇒ IsLinearOrder _≤_
--   IsLattice _≤_ min max
--   +-<-ext       : ∀ w x y z → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
--   ·-preserves-< : ∀ x y z   → [ 0f < z ] → [ x < y ] → [ (x · z) < (y · z) ]

-- IsLinearlyOrderedCommRing
--   isSet
--   IsCommRing 0f 1f _+_ _·_ -_
--   IsStrictLinearOrder _<_
--     ⇒ IsApartnessRel _#_
--     ⇒ IsLinearOrder _≤_
--   IsLattice _≤_ min max
--   +-<-ext       : ∀ w x y z → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
--   ·-preserves-< : ∀ x y z   → [ 0f < z ] → [ x < y ] → [ (x · z) < (y · z) ]

-- IsLinearlyOrderedField
--   isSet
--   IsCommRing 0f 1f _+_ _·_ -_
--   IsStrictLinearOrder _<_
--     ⇒ IsApartnessRel _#_
--     ⇒ IsLinearOrder _≤_
--   IsLattice _≤_ min max
--   ·-inv''       : ∀ x       → [ (∃[ y ] [ is-set ] x · y ≡ˢ 1f) ⇔ x # 0f ]
--   +-<-ext       : ∀ w x y z → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
--   ·-preserves-< : ∀ x y z   → [ 0f < z ] → [ x < y ] → [ (x · z) < (y · z) ]

record IsLinearlyOrderedField {ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor islinearlyorderedfield
  field
    is-PartiallyOrderedField : [ isPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max ]

  open IsPartiallyOrderedField is-PartiallyOrderedField public

record IsCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ'} {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) (sqrt : (x : F) → {{ ! [ ¬(x < 0f) ] }} → F) : Type (ℓ-max ℓ ℓ') where
  constructor ispartiallyorderedfield
  field
    -- 1. 2. 3. 4. 5. 6. (†) and (∗)
    is-PartiallyOrderedField : [ isPartiallyOrderedField 0f 1f _+_ _·_ -_ _<_ min max ]
