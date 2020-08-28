{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Bundles2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
-- open import Cubical.Foundations.Logic
-- open import Cubical.Structures.Ring
-- open import Cubical.Structures.Group
-- open import Cubical.Structures.AbGroup

open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (_∋_)

open import Cubical.HITs.PropositionalTruncation --.Properties


import MoreLogic
open MoreLogic.Definitions
open MoreLogic.Properties
import MorePropAlgebra
open MorePropAlgebra.Definitions
open MorePropAlgebra.Consequences
open import Number.Structures2



{-
| name | struct              | apart | abs | order | cauchy | sqrt₀⁺  | exp | final name                                                             |
|------|---------------------|-------|-----|-------|--------|---------|-----|------------------------------------------------------------------------|
| ℕ    | Semiring            |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedSemiring                                                |
| ℤ    | Ring                |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedRing                                                    |
| ℚ    | Field               |  (✓)  | (✓) | lin.  |        | (on x²) | (✓) | LinearlyOrderedField                                                   |
| ℝ    | Field               |  (✓)  | (✓) | part. |   ✓    |    ✓    | (✓) | CompletePartiallyOrderedFieldWithSqrt                                  |
| ℂ    | euclidean 2-Product |  (✓)  | (✓) |       |  (✓)   |         |  ?  | EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt             |
| R    | Ring                |   ✓   |  ✓  |       |        |         |  ?  | ApartnessRingWithAbsIntoCompletePartiallyOrderedFieldWithSqrt          |
| G    | Group               |   ✓   |  ✓  |       |        |         |  ?  | ApartnessGroupWithAbsIntoCompletePartiallyOrderedFieldWithSqrt         |
| K    | Field               |   ✓   |  ✓  |       |   ✓    |         |  ?  | CompleteApartnessFieldWithAbsIntoCompletePartiallyOrderedFieldWithSqrt |
-}

-- NOTE: this smells like "CPO" https://en.wikipedia.org/wiki/Complete_partial_order
record CompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _<_     : hPropRel Carrier Carrier ℓ'
    <-irrefl : [ isIrreflᵖ _<_ ]
    <-trans  : [ isTransᵖ _<_ ]
    isset   : isSet Carrier

  _≤_ : hPropRel Carrier Carrier ℓ'
  x ≤ y = ¬ᵖ(y < x)

  _≤ⁱ_ : hPropRel Carrier Carrier ℓ'
  -- x ≤ᵢ y = ({{p : [ y < x ]}} → ⊥⊥) , λ f g → instanceFunExt {A = [ y < x ]} {B = λ q i → ⊥⊥} {f = f} {g = g} λ {{r}} → ⊥-elim {A = λ _ → f ≡ g} f
  -- x ≤ᵢ y = ({{p : [ y < x ]}} → ⊥⊥) , λ f g → instanceFunExt (λ {{_}} → ⊥-elim {A = λ _ → f ≡ g} f)
  x ≤ⁱ y = ¬ⁱ(y < x)

  -- isPropΠ λ _ → ⊥.isProp⊥

  ≤-≡-≤ⁱ : ∀ x y → x ≤ y ≡ x ≤ⁱ y
  ≤-≡-≤ⁱ x y = ¬-≡-¬ⁱ (y < x)
    -- ⇒∶ (λ f {{p}} → f   p  )
    -- ⇐∶ (λ f   p   → f {{p}})

  ≤ⁱ-inst : ∀{x y} → [ x ≤ y ] → [ x ≤ⁱ y ]
  ≤ⁱ-inst x≤y = pathTo⇒ (≤-≡-≤ⁱ _ _) x≤y

  field
    -- NOTE: `[ 0f ≤ x ]` normalizes to `fst (x < 0f) → ⊥⊥` and therefore it takes an explicit argument `fst (x < 0f)`
    --       when making this an instance argument, agda complains
    --         Instance arguments with explicit arguments are never considered by instance search
    -- we circumvent this by introducing `_≤ⁱ_`
    sqrt₀⁺ : (x : Carrier) → {{ [ 0f ≤ⁱ x ] }} → Carrier

  sqrt-test : (x y : Carrier) → [ 0f ≤ x ] → [ 0f ≤ y ] → Carrier
  sqrt-test x y 0≤x 0≤y = let instance itx = ≤ⁱ-inst 0≤x
                              instance ity = ≤ⁱ-inst 0≤y
                          in {! sqrt₀⁺ x  !}

  <-asym : [ isAsymᵖ _<_ ]
  <-asym = irrefl+trans→asym _<_ <-irrefl <-trans

  _#_ : hPropRel Carrier Carrier ℓ'
  x # y = ([ x < y ] ⊎ [ y < x ]) , isProp-P⊎Q (x < y) (y < x) (inl (<-asym x y))

  field
    _⁻¹ : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier

-----------8<--------------------------------------------8<------------------------------------------8<------------------

{- currently, we have that IsAbs works on "rigs" (rings where `-_` is not necessary)
   but in our applications, we do want to take the square root immediately on modules
   therefore, `abs` is defined here as always mapping into `CompletePartiallyOrderedFieldWithSqrt` although more general `abs`es would be possible
-}

module _ -- mathematical structures with `abs` into the real numbers
  {ℝℓ ℝℓ' : Level}
  (ℝbundle : CompletePartiallyOrderedFieldWithSqrt {ℝℓ} {ℝℓ'})
  where
  module ℝ = CompletePartiallyOrderedFieldWithSqrt ℝbundle
  open ℝ using () renaming (Carrier to ℝ; isset to issetʳ; _≤_ to _≤ʳ_; 0f to 0ʳ; _+_ to _+ʳ_; _·_ to _·ʳ_)

  -- this makes the complex numbers ℂ
  module EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt where
    Carrier : Type ℝℓ
    Carrier = ℝ × ℝ

    re im : Carrier → ℝ
    re = fst
    im = snd


  -- this makes the `R` in `RModule`
  record ApartnessRingWithAbsIntoCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
    field
      Carrier : Type ℓ
      0f      : Carrier
      1f      : Carrier
      _+_     : Carrier → Carrier → Carrier
      _·_     : Carrier → Carrier → Carrier
      -_      : Carrier → Carrier
      _#_     : hPropRel Carrier Carrier ℓ'
      abs     : Carrier → ℝ

  -- this makes the `G` in `GModule`
  record ApartnessGroupWithAbsIntoCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
    field
      Carrier : Type ℓ
      1f      : Carrier
      _·_     : Carrier → Carrier → Carrier
      _⁻¹     : Carrier → Carrier
      _#_     : hPropRel Carrier Carrier ℓ'
      abs     : Carrier → ℝ

  -- this makes the `K` in `KModule`
  record CompleteApartnessFieldWithAbsIntoCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
    field
      Carrier : Type ℓ
      0f      : Carrier
      1f      : Carrier
      _+_     : Carrier → Carrier → Carrier
      _·_     : Carrier → Carrier → Carrier
      -_      : Carrier → Carrier
      _#_     : hPropRel Carrier Carrier ℓ'
      _⁻¹     : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier
      abs     : Carrier → ℝ
      isset   : isSet Carrier
      isAbs   : [ isAbsᵖ isset 0f _+_ _·_ _#_ abs issetʳ 0ʳ _+ʳ_ _·ʳ_ _≤ʳ_ ]

    -- TODO: complete this
