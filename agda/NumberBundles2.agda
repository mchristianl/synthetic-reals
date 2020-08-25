{-# OPTIONS --cubical --no-import-sorts #-}

module NumberBundles2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Structures.Ring
open import Cubical.Structures.Group
open import Cubical.Structures.AbGroup


{-
| name | struct              | apart | abs | order | cauchy | sqrt₀⁺  | exp | final name                                                 |
|------|---------------------|-------|-----|-------|--------|---------|-----|------------------------------------------------------------|
| ℕ    | Semiring            |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedSemiring                                    |
| ℤ    | Ring                |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedRing                                        |
| ℚ    | Field               |  (✓)  | (✓) | lin.  |        | (on x²) | (✓) | LinearlyOrderedField                                       |
| ℝ    | Field               |  (✓)  | (✓) | part. |   ✓    |    ✓    | (✓) | CompletePartiallyOrderedFieldWithSqrt                      |
| ℂ    | euclidean 2-Product |  (✓)  | (✓) |       |  (✓)   |         |  ?  | EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt |
| R    | Ring                |   ✓   |  ✓  |       |        |         |  ?  | ApartnessRingWithAbs                                       |
| G    | Group               |   ✓   |  ✓  |       |        |         |  ?  | ApartnessGroupWithAbs                                      |
| K    | Field               |   ✓   |  ✓  |       |   ✓    |         |  ?  | CompleteApartnessFieldWithAbs                              |
-}

record CompleteApartnessFieldWithAbs {ℓ : Level} : Type (ℓ-suc ℓ) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier

  -- TODO: complete this
