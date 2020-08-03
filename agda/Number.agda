{-# OPTIONS --cubical --no-import-sorts #-}

module Number where


open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel
open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
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
    ∣_∣ᶠ' : Carrier → Σ[ x ∈ Carrier ] 0f ≤ x -- absolute value
    _⁻¹ᶠ : (x : Carrier) → {{x # 0f}} → Carrier
    conj : Carrier → Carrier -- complex conjugation (only for ℂ; this is the identity function on ℝ)
    -- sqrt -- need that on ℝ₀⁺ to define a norm from an inner product
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

{-

coercion should preserve
- identity: a ≡ b ⇔ coerce a ≡ coerce b
- _#_, _<_ and _≤_
- min max and basically all other "operations"

so it is a Field-morphism
..unless we are making use of ℂ which does not have the lattice properties
so, when we have a function like the inner product ⟨_,_⟩ : V → V → ℂ
which has the property that ⟨ x , x ⟩ ∈ ℝ, how do we formalize that?
well, we have for `z = ⟨ x , x ⟩` that `z ≡ conj z` and therefore `imag z ≡ 0`
so we might add `real` and `imag` to our ℂ and allow a coercion only when `imag z ≡ 0`

generally we do not have back-inclusion
the chain goes like ℕ ↪ ℤ ↪ ℚ ↪ ℝ ↪ ℂ

ℕ, ℤ, ℚ and ℝ share _+_, _·_, the lattice-like parts _<_, _≤_, _#_, min, max and also abs

.....| ℕ ℤ ℚ ℝ ℂ | ℝ₀⁺ ℝ⁺ Finₖ
-----|-----------|-------------
_+_  | ✓ ✓ ✓ ✓ ✓ | ✓   ✓   p
_-_  | p ✓ ✓ ✓ ✓ | p   p   p
_·_  | ✓ ✓ ✓ ✓ ✓ | ✓   ✓   p
_⁻¹  | ✗ ✗ * * * | *   ✓   ✗
_<_  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
_≤_  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
_#_  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
min  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
max  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
-----|-----------|-------------
abs  | • ✓ ✓ ✓ ✓ | •   •   •
sqrt | p p p * * | ✓   ✓   p
conj | • • • • ✓ | •   •   •

• = trivial
✓ = total
* = almost completely / special
p = partial
✗ = not available

we might exclude ℂ from this coercion system, because they are too different since they are not an ordered field
  but we might have a separate just-field-coercion system that allows for 𝕂

the "usual" number domains are
  ℝ
  ℝ₀⁺ -- nonnegative
  ℝ⁺  -- nonnegative, nonzero
  ℚ
  ℚ₀⁺ -- nonnegative
  ℚ⁺  -- nonnegative, nonzero
  ℕ
  ℕ⁺  -- nonzero
  ℤ
  ℤ₀⁺ -- nonnegative
  ℤ⁺  -- nonnegative, nonzero
  ℂ
  ℂ⁺  -- nonzero
  𝕂  -- ℂ or ℝ
  𝕂⁺ -- nonzero

how to set up these injections?
  https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses
    A function f with a left inverse is necessarily injective.
    In classical mathematics, every injective function f with a nonempty domain necessarily has a left inverse;
      however, this may fail in constructive mathematics.
    For instance, a left inverse of the inclusion {0,1} → R of the two-element set in the reals violates indecomposability
      by giving a retraction of the real line to the set {0,1}.
  https://en.wikipedia.org/wiki/Indecomposability

-}

{-

partial morphisms
e.g. for `x > 0` as a prerequisite for an inclusion to ℝ⁺
  (φ ↪ ℝ) ≅ ℝ⁺
  Σ ℝ φ ≅ ℝ⁺
-}

record IsPoorFieldMor
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : PoorField {ℓ} {ℓₚ}) (G : PoorField {ℓ'} {ℓₚ'})
  (f : (PoorField.Carrier F) → (PoorField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  module F = PoorField F
  module G = PoorField G
  field
    preserves-<   : ∀ x y   → x F.< y       → f x G.< f y
    preserves-≤   : ∀ x y   → x F.≤ y       → f x G.≤ f y
    preserves-#   : ∀ x y   → x F.# y       → f x G.# f y
    preserves-min : ∀ x y z → F.min x y ≡ z → G.min (f x) (f y) ≡ f z
    preserves-max : ∀ x y z → F.max x y ≡ z → G.max (f x) (f y) ≡ f z
    -- uniqueness ? .. might follow from preserves-#
    reflects-≡   : ∀ x y   → f x ≡ f y               → x ≡ y
    reflects-<   : ∀ x y   → f x G.< f y             → x F.< y
    reflects-≤   : ∀ x y   → f x G.≤ f y             → x F.≤ y
    reflects-#   : ∀ x y   → f x G.# f y             → x F.# y
    reflects-min : ∀ x y z → G.min (f x) (f y) ≡ f z → F.min x y ≡ z
    reflects-max : ∀ x y z → G.max (f x) (f y) ≡ f z → F.max x y ≡ z
    -- and ring homomorphism properties
    --     preserves-+
    --     preserves-
    --     preserves-·
    --     preserves-⁻¹ if applicable

record PoorFieldMor {ℓ ℓ' ℓₚ ℓₚ'} (F : PoorField {ℓ} {ℓₚ}) (G : PoorField {ℓ'} {ℓₚ'}) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ')) where
  constructor poorfieldmor
  module F = PoorField F
  module G = PoorField G
  field
    fun : F.Carrier → G.Carrier
    isPoorFieldMor : IsPoorFieldMor F G fun

record Coercion' (Y : Type ℓ') (P : Y → Type ℓ'') {X : Type ℓ} (x : X) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
    coerce' : Σ Y P

instance
  coerce-id' : {X : Type ℓ} {x : X} → Coercion' X (λ _ → Unit) {X = X} x
  coerce-id' {x = x} = record { coerce' = x , tt }

coerce : {X : Type ℓ} {Y : Type ℓ'} → (x : X) → {{c : Coercion' Y {!!} x}}  → Y
coerce = {!!}

{-

now the issue is, that while we can define operations that work on a general Number type with hidden instance arguments
  the output of such an operation still needs to be of "some" type
we cannot output the resulting number and an instance with its properties,
  at least not in a way where the instance is immediately taken up for instance serach
  e.g. in equational reasoning with _≡⟨_⟩ which is a single term and cannot introduce additional instances mid-term
therefore these operations output

-}
