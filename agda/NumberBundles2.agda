{-# OPTIONS --cubical --no-import-sorts #-}

module NumberBundles2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic
open import Cubical.Structures.Ring
open import Cubical.Structures.Group
open import Cubical.Structures.AbGroup

open import Cubical.HITs.PropositionalTruncation --.Properties

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

hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
hPropRel A B ℓ' = A → B → hProp ℓ'

record CompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _<_     : hPropRel Carrier Carrier ℓ'
    isset   : isSet Carrier

  _≤_ : hPropRel Carrier Carrier ℓ'
  x ≤ y = ¬(y < x)

module _
  { ℓ  ℓ' : Level} {F : Type ℓ }
  (isset  : isSet F) (0f : F) (_+_  _·_  : F → F → F) (_#_  : hPropRel F F  ℓ')
  {Rℓ Rℓ' : Level} {R : Type Rℓ} (abs : F → R)
  (issetᴿ : isSet R) (0ᴿ : R) (_+ᴿ_ _·ᴿ_ : R → R → R) (_≤ᴿ_ : hPropRel R R Rℓ')
  where

  -- NOTE: do we need to use `Cubical.HITs.PropositionalTruncation.MagicTrick` here?
  --         "any truncated element (of a homogeneous type) can be recovered by agda's normalizer!"
  --       we also do have in `Cubical.HITs.PropositionalTruncation.Properties` an "Eliminator for propositional truncation"
  --       and we have
  --         propTruncIdempotent : isProp A → ∥ A ∥ ≡ A
  --         ∥ A ∥ₚ = ∥ A ∥ , propTruncIsProp
  --       No! we can make use of isSet to eliminate _≡ₚ_

  record IsAbs : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max Rℓ Rℓ'))) where
    constructor isabs
    field
      0≤abs           : ∀ x   → [            0ᴿ ≤ᴿ (abs x)          ]
      abs-preserves-0 : ∀ x   → [      x ≡ₚ 0f  ⇒ abs x ≡ₚ 0ᴿ       ] -- TODO: remove `_≡ₚ_` with `isSet`
      abs-reflects-0  : ∀ x   → [  abs x ≡ₚ 0ᴿ  ⇒     x ≡ₚ 0f       ] -- TODO: remove `_≡ₚ_` with `isSet`
      abs-preserves-· : ∀ x y →   (abs (x · y)) ≡  (abs x ·ᴿ abs y)
      triangle-ineq   : ∀ x y → [  abs (x + y)  ≤ᴿ (abs x +ᴿ abs y) ]

    -- abs-preserves-·' : F → F → hProp {!   !}
    -- abs-preserves-·' =  λ x y → let z = {! abs-preserves-· x y  !}
    --                             in  {! transport (propTruncIdempotent (isProp[] ((abs (x · y)) ≡ₚ (abs x ·ᴿ abs y))))   !}

  isAbsᵖ : hProp (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max Rℓ Rℓ')))
  isAbsᵖ = IsAbs , φ-prop where
    φ-prop : isProp IsAbs
    φ-prop (isabs 0≤abs₀ abs-preserves-0₀ abs-reflects-0₀ abs-preserves-·₀ triangle-ineq₀)
           (isabs 0≤abs₁ abs-preserves-0₁ abs-reflects-0₁ abs-preserves-·₁ triangle-ineq₁) =
      λ i → isabs (isPropΠ  (λ x   → isProp[] (           0ᴿ ≤ᴿ (abs x)         )) 0≤abs₀ 0≤abs₁ i)
                  (isPropΠ  (λ x   → isProp[] (     x ≡ₚ 0f  ⇒ abs x ≡ₚ 0ᴿ      )) abs-preserves-0₀ abs-preserves-0₁ i)
                  (isPropΠ  (λ x   → isProp[] ( abs x ≡ₚ 0ᴿ  ⇒     x ≡ₚ 0f      )) abs-reflects-0₀  abs-reflects-0₁  i)
                  --(isPropΠ2 (λ x y → isProp[] ((abs (x · y)) ≡ₚ (abs x ·ᴿ abs y))) abs-preserves-·₀ abs-preserves-·₁ i)
                  (λ(x y : F) → issetᴿ (abs (x · y)) (abs x ·ᴿ abs y) (abs-preserves-·₀ x y) (abs-preserves-·₁ x y) i)
                  (isPropΠ2 (λ x y → isProp[] ( abs (x + y)  ≤ᴿ (abs x +ᴿ abs y))) triangle-ineq₀   triangle-ineq₁   i)

-----------8<--------------------------------------------8<------------------------------------------8<------------------

postulate
  ℝℓ ℝℓ' : Level
  ℝM : CompletePartiallyOrderedFieldWithSqrt {ℝℓ} {ℝℓ'}
module ℝ = CompletePartiallyOrderedFieldWithSqrt ℝM
open ℝ using () renaming (Carrier to ℝ; isset to issetʳ; _≤_ to _≤ʳ_; 0f to 0ʳ; _+_ to _+ʳ_; _·_ to _·ʳ_)

record CompleteApartnessFieldWithAbs {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _#_     : hPropRel Carrier Carrier ℓ'
    abs     : Carrier → ℝ
    isset   : isSet Carrier
    isAbs   : [ isAbsᵖ isset 0f _+_ _·_ _#_ abs issetʳ 0ʳ _+ʳ_ _·ʳ_ _≤ʳ_ ]

  -- TODO: complete this
