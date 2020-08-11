{-# OPTIONS --cubical --no-import-sorts #-}

module NumberFirstAttempt where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Binary.Base -- Rel
open import Cubical.Data.Unit.Base -- Unit

record PoorField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier : Type ℓ
    -- comm ring
    0f   : Carrier
    1f   : Carrier
    _+_  : Carrier → Carrier → Carrier
    _·_  : Carrier → Carrier → Carrier
    -_   : Carrier → Carrier
    -- lattice
    _<_  : Rel Carrier Carrier ℓ' -- stronger than _#_ and _≤_
    min  : Carrier → Carrier → Carrier
    max  : Carrier → Carrier → Carrier
    -- other
    _#_  : Rel Carrier Carrier ℓ'
    _≤_  : Rel Carrier Carrier ℓ'
    ∣_∣ᶠ' : Carrier → Σ[ x ∈ Carrier ] 0f ≤ x -- absolute value NOTE: better have `0 ≤ x` as a separate property
    _⁻¹ᶠ : (x : Carrier) → {{x # 0f}} → Carrier
    conj : Carrier → Carrier -- complex conjugation (only for ℂ; this is the identity function on ℝ)
    -- sqrt⁺ -- positive sqrt
    --       -- need that on ℝ₀⁺ to define a norm from an inner product
    --       -- on ℝ₀⁺ we have `∀ x → sqrt (x · x) ≡ x`
    -- NOTE: squares are nonnegative in an ordered field

  ∣_∣ᶠ : Carrier → Carrier -- NOTE: well, this should be "into" ℝ₀⁺
  ∣ x ∣ᶠ = fst (∣ x ∣ᶠ')

  _-_ : Carrier → Carrier → Carrier
  x - y = x + (- y)

  infix  9 _⁻¹ᶠ
  infix  8 -_
  infixl 7 _·_
  infixl 6 _+_
  infixl 6 _-_
  infixl 4 _#_
  infixl 4 _<_
  infixl 4 _≤_

record IsℝField (PF : PoorField {ℓ} {ℓ'}) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  open PoorField PF

record Isℝ₀⁺Field (PF : PoorField {ℓ} {ℓ'}) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  open PoorField PF
  field
    isℝField : IsℝField PF
    isNonnegative : ∀ x → 0f ≤ x
  open IsℝField isℝField public

record Isℝ⁺Field (PF : PoorField {ℓ} {ℓ'}) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  open PoorField PF
  field
    isℝField : IsℝField PF
    -- NOTE: 0f is not an element of ℝ⁺, so we do not have a neutral element for addition
    --       so the following holds in a different way
    -- isPositive : ∀ x → 0f < x
  open IsℝField isℝField public

record Is𝕂Field (PF : PoorField {ℓ} {ℓ'}) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  open PoorField PF

record ℝField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    poorField : PoorField {ℓ} {ℓ'}
    isℝField : IsℝField poorField
  open PoorField poorField public
  open IsℝField isℝField public

record ℝ₀⁺Field : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    poorField : PoorField {ℓ} {ℓ'}
    isℝ₀⁺Field : Isℝ₀⁺Field poorField
  open PoorField poorField public
  open Isℝ₀⁺Field isℝ₀⁺Field public

record ℝ⁺Field : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    poorField : PoorField {ℓ} {ℓ'}
    isℝ⁺Field : Isℝ⁺Field poorField
  open PoorField poorField public
  open Isℝ⁺Field isℝ⁺Field public

record 𝕂Field : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    poorField : PoorField {ℓ} {ℓ'}
    is𝕂Field : Is𝕂Field poorField
  open PoorField poorField public
  open Is𝕂Field is𝕂Field public

postulate
  ℝℓ ℝℓ' : Level
  ℝF    : ℝField   {ℝℓ} {ℝℓ'} -- reals
  ℝ⁺F   : ℝ⁺Field  {ℝℓ} {ℝℓ'} -- positive reals without 0
  ℝ₀⁺F  : ℝ₀⁺Field {ℝℓ} {ℝℓ'} -- positive reals with 0

open ℝField ℝF using () renaming
  ( Carrier to ℝ
  )


record PoorSubField-ℝ (φ : ℝ → Type ℓ) : Type (ℓ-max ℝℓ ℓ) where
  -- module R = ℝField ℝF
  open ℝField ℝF
  field
    ι : Σ ℝ φ
    
  _<⁺_ : Σ ℝ φ → Σ ℝ φ → Type ℝℓ'
  _<⁺_ (x , xp) (y , yp) = x < y

module Test where
  module R =  ℝField ℝF
  φᵢ = λ(x : ℝ) → Unit

  -- the following "absorbs" different `Σ ℝ φ` ℝ-numbers and falls back to the "raw" operation from ℝ
  _+_ : {φ₁ φ₂ : ℝ → Type ℓ'} → Σ ℝ φ₁ → Σ ℝ φ₂ → Σ ℝ φᵢ
  _+_ (x , _) (y , _) = x R.+ y , tt

  -- we might add an enumeration for different φs and pattern-match on those
  data ℝ-props (x : ℝ) : Type ℝℓ where
    φ-id : Unit → ℝ-props x
    -- more ...

  -- this works for subsets of ℝ but not for inter-sort-mixing (e.g. ℕ + ℝ) .. which we do want to coerce explicitly?
  -- we could start with a number, e.g. z₀ ∈ ℕ
  -- then include it into ℝ and have a Σ ℝ φ-from-nat
  -- we could track the from-nat'ness and back-coerce this number when needed (as long as from-nat is preserved)

  {-
  data ℝ-sub (x : ℝ) : Type ℝℓ where
    φ-from-ℝ   : Unit -- default "fallback" case
    φ-from-ℕ   : Σ[ z ∈ ℕ ] ℕ↪ℝ z ≡ x -- with this we can use the `reflects`-properties of `ℕ↪ℝ` to get corresponding properties on ℕ
    φ-from-ℤ   : Σ[ z ∈ ℤ ] ℤ↪ℝ z ≡ x
    φ-from-ℚ   : Σ[ z ∈ ℚ ] ℚ↪ℝ z ≡ x
    φ-from-ℝ₀⁺ :  0f ≤ x
                ¬( x < 0f)
    φ-from-ℝ⁺  :  0f < x
    -- ... more

  -- first projection
  num : ∀{x} → ℝ-sub x → ℝ
  num p = ... cases

  -- target type "table"
  +-Coerce : (x y : ℝ-sub) → Type ℝℓ
  +-Coerce x y = ... cases

  -- implementation
  _+_ : (x y : ℝ-sub) → +-Coerce x y
  x + y = ... cases
  -}

record IsPoorFieldInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : PoorField {ℓ} {ℓₚ}) (G : PoorField {ℓ'} {ℓₚ'})
  (f : (PoorField.Carrier F) → (PoorField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = PoorField F
    module G = PoorField G
  field
    -- injectivity? might follow from preserves-#?
    reflects-≡    : ∀ x y → f x   ≡ f y →   x ≡     y
    -- lattice
    preserves-<   : ∀ x y →   x F.<   y → f x G.< f y
    preserves-≤   : ∀ x y →   x F.≤   y → f x G.≤ f y
    preserves-#   : ∀ x y →   x F.#   y → f x G.# f y
    reflects-<    : ∀ x y → f x G.< f y →   x F.<   y
    reflects-≤    : ∀ x y → f x G.≤ f y →   x F.≤   y
    reflects-#    : ∀ x y → f x G.# f y →   x F.#   y
    preserves-min : ∀ x y → f (F.min x y) ≡ G.min (f x) (f y)
    preserves-max : ∀ x y → f (F.max x y) ≡ G.max (f x) (f y)
    preserves-0   :         f  F.0f       ≡ G.0f
    -- Fin 1 does not preserve 
    preserves-1   :         f  F.1f       ≡ G.1f
    -- Fin k might not preserve
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
    -- ℕ might not preserve
    preserves-    : ∀ x   → f (  F.- x)   ≡     G.- (f x)
    -- ℤ does not preserve
    -- preserves-⁻¹' : ∀ x → (p : x F.# F.0f) → f (F._⁻¹ᶠ x {{p}}) ≡ G._⁻¹ᶠ (f x) {{ transport (λ i → f x G.# preserves-0 i) (preserves-# x F.0f p) }}
    -- NOTE: we better let the "user" decide how the proof of `f x # 0` is obtained
    preserves-⁻¹  : ∀ x → (p : x F.# F.0f) → (q : f x G.# G.0f) → f (F._⁻¹ᶠ x {{p}}) ≡ G._⁻¹ᶠ (f x) {{q}}

record PoorFieldInclusion {ℓ ℓ' ℓₚ ℓₚ'} (F : PoorField {ℓ} {ℓₚ}) (G : PoorField {ℓ'} {ℓₚ'}) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ')) where
  constructor poorfieldmor
  module F = PoorField F
  module G = PoorField G
  field
    fun : F.Carrier → G.Carrier
    isPoorFieldInclusion : IsPoorFieldInclusion F G fun
  open IsPoorFieldInclusion isPoorFieldInclusion public

