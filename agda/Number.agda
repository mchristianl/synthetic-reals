{-# OPTIONS --cubical --no-import-sorts #-}

module Number where


open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

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

-- open import Bundles

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
0ᶠ   | ✓ ✓ ✓ ✓ ✓ | ✓   ✗   ✓
1ᶠ   | ✓ ✓ ✓ ✓ ✓ | ✓   ✓   *
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

what about congruence classes (ℤ mod M)?

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

Maybe we add a "new" Σ type with an implicit instance argument
  a function might suffice

we need the differing properties
but it is also somehow the definition of ℝ⁺
so can we "just" replace the carrier of ℝ⁺ to `Σ ℝ φ` ?
  or we define a subspace with an explicit inclusion anihilating these things
if we want to add 0ᶠ from ℝ to some x from ℝ⁺ (which does not contain 0ᶠ) then we might not want to have explicit inclusions
  (x , 0 < x)
-}

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

{-

there is from `Relation.Binary.Core`

  _Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
  f Preserves P ⟶ Q = P =[ f ]⇒ Q

which is a synonym for _=[_]⇒_

  _=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
  P =[ f ]⇒ Q = P ⇒ (Q on f)

with `⇒`

  P ⇒ Q = ∀ {x y} → P x y → Q x y

and `_on_` from `Function.Base`

  _on_ : (B → B → C) → (A → B) → (A → A → C)
  _*_ on f = λ x y → f x * f y

-}

-- "preserve" and "reflect"
--   e.g. from http://www.mat.uc.pt/~mmc/courses/CategoryTheory.pdf
--     A functor `F : A → B` preserves property (P) of  morphisms  (of  objects) if `F f` has that property whenever `f` has it
--     [ P f ⇒ P (F f) ]
--     A functor `F : A → C` reflects one property if `f` fulfils that property whenever `F f` does
--     [ P (F f) ⇒ P f ]

_Preserves_⟶_ : ∀{Aℓ Bℓ ℓ ℓ'} {A : Type Aℓ} {B : Type Bℓ} → (A → B) → Rel A A ℓ → Rel B B ℓ' → Set _
f Preserves P ⟶ Q = ∀{x y} → P x y → Q (f x) (f y)

_Reflects_⟶_ : ∀{Aℓ Bℓ ℓ ℓ'} {A : Type Aℓ} {B : Type Bℓ} → (A → B) → Rel A A ℓ → Rel B B ℓ' → Set _
f Reflects P ⟶ Q = ∀{x y} → Q (f x) (f y) → P x y

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

-- Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
record IsRLattice {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) : Type (ℓ-max ℓ ℓ') where
  -- TODO: properties

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

record IsRLatticeInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : RLattice {ℓ} {ℓₚ}) (G : RLattice {ℓ'} {ℓₚ'})
  (f : (RLattice.Carrier F) → (RLattice.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = RLattice F
    module G = RLattice G
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

-- ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
-- ring without additive inverse
record IsROrderedCommSemiring {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRLattice : IsRLattice _<_ _≤_ _#_ min max
    -- TODO: properties
  open IsRLattice isRLattice public

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

record IsROrderedCommSemiringInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : ROrderedCommSemiring {ℓ} {ℓₚ}) (G : ROrderedCommSemiring {ℓ'} {ℓₚ'})
  (f : (ROrderedCommSemiring.Carrier F) → (ROrderedCommSemiring.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = ROrderedCommSemiring F
    module G = ROrderedCommSemiring G
  field
    isRLatticeInclusion : IsRLatticeInclusion (record {F}) (record {G}) f
    preserves-0   :         f  F.0f       ≡ G.0f
    preserves-1   :         f  F.1f       ≡ G.1f
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
  open IsRLatticeInclusion isRLatticeInclusion public

-- ℤ ℚ ℝ
record IsROrderedCommRing {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
    -- TODO: properties
  open IsROrderedCommSemiring isROrderedCommSemiring public

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

record IsROrderedCommRingInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : ROrderedCommRing {ℓ} {ℓₚ}) (G : ROrderedCommRing {ℓ'} {ℓₚ'})
  (f : (ROrderedCommRing.Carrier F) → (ROrderedCommRing.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = ROrderedCommRing F
    module G = ROrderedCommRing G
  field
    isROrderedCommSemiringInclusion : IsROrderedCommSemiringInclusion (record {F}) (record {G}) f
    preserves-    : ∀ x   → f (  F.- x)   ≡     G.- (f x)
  open IsROrderedCommSemiringInclusion isROrderedCommSemiringInclusion public

-- ℚ ℝ
record IsROrderedField {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ x # 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommRing : IsROrderedCommRing _<_ _≤_ _#_ min max 0f 1f _+_ _·_ -_
  open IsROrderedCommRing isROrderedCommRing public

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

record IsROrderedFieldInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : ROrderedField {ℓ} {ℓₚ}) (G : ROrderedField {ℓ'} {ℓₚ'})
  (f : (ROrderedField.Carrier F) → (ROrderedField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = ROrderedField F
    module G = ROrderedField G
  field
    isROrderedCommRingInclusion : IsROrderedCommRingInclusion (record {F}) (record {G}) f
    preserves-⁻¹  : ∀ x → (p : x F.# F.0f) → (q : f x G.# G.0f) → f (F._⁻¹ x {{p}}) ≡ G._⁻¹ (f x) {{q}}
  open IsROrderedCommRingInclusion isROrderedCommRingInclusion public

-- ℚ₀⁺ ℝ₀⁺
record IsROrderedSemifield {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (_⁻¹ : (x : F) → {{ x < 0f }} → F) : Type (ℓ-max ℓ ℓ') where
  field
    isROrderedCommSemiring : IsROrderedCommSemiring _<_ _≤_ _#_ min max 0f 1f _+_ _·_
    -- TODO: properties
    #0-implies-0< : ∀ x → 0f # x → 0f < x
    positivity : ∀ x → 0f ≤ x
  open IsROrderedCommSemiring isROrderedCommSemiring public

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
record IsROrderedSemifieldWithoutZero {F : Type ℓ} (_<_ _≤_ _#_ : Rel F F ℓ') (min max : F → F → F) (0f 1f : F) (_+_ _·_ : F → F → F) (_⁻¹ : (x : F) → F) : Type (ℓ-max ℓ ℓ') where
  field
    isRLattice : IsRLattice _<_ _≤_ _#_ min max
    -- isGroup : IsGroup 1f _·_ _⁻¹
    +-assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
    +-comm  : ∀ x y → x + y ≡ y + x
    distrib : ∀ x y z → (x + y) · z ≡ (x · z) + (y · z)
    -- TODO: properties
  open IsRLattice isRLattice public

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

record IsRFieldInclusion
  {ℓ ℓ' ℓₚ ℓₚ'}
  (F : RField {ℓ} {ℓₚ}) (G : RField {ℓ'} {ℓₚ'})
  (f : (RField.Carrier F) → (RField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  private
    module F = RField F
    module G = RField G
  field
    -- CommSemiringInclusion
    preserves-0   :         f  F.0f       ≡ G.0f
    preserves-1   :         f  F.1f       ≡ G.1f
    preserves-+   : ∀ x y → f (x F.+ y)   ≡ f x G.+  f y
    preserves-·   : ∀ x y → f (x F.· y)   ≡ f x G.·  f y
    -- other
    reflects-≡    : ∀ x y → f x   ≡ f y →   x ≡     y
    preserves-#   : ∀ x y →   x F.#   y → f x G.# f y
    reflects-#    : ∀ x y → f x G.# f y →   x F.#   y
    -- TODO: properties


-- TODO: put these into a Postulates.agda module

postulate
  ℕOCSR : ROrderedCommSemiring {ℝℓ} {ℝℓ'}
  ℤOCR  : ROrderedCommRing     {ℝℓ} {ℝℓ'}
  ℚOF   : ROrderedField        {ℝℓ} {ℝℓ'}
  ℝOF   : ROrderedField        {ℝℓ} {ℝℓ'}
  ℂF    : RField               {ℝℓ} {ℝℓ'}

-- NOTE: these should correspond with the "real" ℕ, ℤ, ℚ and ℝ
ℕCarrier = ROrderedCommSemiring.Carrier ℕOCSR
ℤCarrier = ROrderedCommRing.Carrier ℤOCR
ℚCarrier = ROrderedField.Carrier ℚOF
ℝCarrier = ROrderedField.Carrier ℝOF
ℂCarrier = RField.Carrier ℂF

postulate
  ℕ↪ℤ    : ℕCarrier → ℤCarrier
  ℕ↪ℤinc : IsROrderedCommSemiringInclusion ℕOCSR (record { ROrderedCommRing ℤOCR }) ℕ↪ℤ

  ℕ↪ℚ    : ℕCarrier → ℚCarrier
  ℕ↪ℚinc : IsROrderedCommSemiringInclusion ℕOCSR (record { ROrderedField ℚOF }) ℕ↪ℚ

  ℕ↪ℂ    : ℕCarrier → ℂCarrier
  ℕ↪ℂinc : IsRFieldInclusion (record { ROrderedCommSemiring ℕOCSR } ) (record { RField ℂF }) ℕ↪ℂ

  ℕ↪ℝ    : ℕCarrier → ℝCarrier
  ℕ↪ℝinc : IsROrderedCommSemiringInclusion ℕOCSR (record { ROrderedField ℝOF }) ℕ↪ℝ

  ℤ↪ℚ    : ℤCarrier → ℚCarrier
  ℤ↪ℚinc : IsROrderedCommRingInclusion ℤOCR (record { ROrderedField ℚOF }) ℤ↪ℚ

  ℤ↪ℝ    : ℤCarrier → ℝCarrier
  ℤ↪ℝinc : IsROrderedCommRingInclusion ℤOCR (record { ROrderedField ℝOF }) ℤ↪ℝ

  ℤ↪ℂ    : ℤCarrier → ℂCarrier
  -- ℤ↪ℂinc : IsRCommRingInclusion ℤOCR (record { RField ℂF }) ℤ↪ℂ

  ℚ↪ℝ    : ℚCarrier → ℝCarrier
  ℚ↪ℝinc : IsROrderedFieldInclusion ℚOF (record { ROrderedField ℝOF }) ℚ↪ℝ

  ℚ↪ℂ    : ℚCarrier → ℂCarrier
  ℚ↪ℂinc : IsRFieldInclusion (record { ROrderedField ℚOF }) (record { RField ℂF }) ℚ↪ℂ

  ℝ↪ℂ    : ℝCarrier → ℂCarrier
  ℝ↪ℂinc : IsRFieldInclusion (record { ROrderedField ℝOF }) (record { RField ℂF }) ℝ↪ℂ


ℝ↪ℝ : ℝCarrier → ℝCarrier
ℝ↪ℝ x = x

ℝ↪ℝinc : IsROrderedFieldInclusion ℝOF ℝOF ℝ↪ℝ
ℝ↪ℝinc = {!!}

  {-
  More generally, it seems that we are tracking properties such as
    isNat isInt isRat isReal isNonnegative isNonzero
  attached to the corresponding numbers 
  An inclusion into ℝ might not be necessary
  we could do this with a small domain specific language / small coercion grammar
  -}

module Numbers where
  open import Cubical.Data.Fin.Base
  -- import Cubical.Data.Fin.Properties
  open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
  open import Cubical.Data.Nat.Properties using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)
  open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_; _≟_ to _≟ₙ_)
  -- open import Data.Nat.Base using (ℕ; z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ₙ_; _<_ to _<ₙ_; _+_ to _+ₙ_)
  open import Agda.Builtin.Bool renaming (true to TT; false to FF)
  open import Function.Base using (it; _$_) -- instance search
  import Cubical.Data.Fin.Properties
  open import Data.Nat.Properties using (+-mono-<)

  minₙ : ℕ → ℕ → ℕ
  minₙ a b with a ≟ₙ b
  ... | lt a<b = a 
  ... | eq a≡b = a 
  ... | gt b<a = b 

  maxₙ : ℕ → ℕ → ℕ
  maxₙ a b with a ≟ₙ b
  ... | lt a<b = b
  ... | eq a≡b = a
  ... | gt b<a = a

  private
    instance
      z≤n' : ∀ {n}                 → zero  ≤ₙ n
      z≤n' {n} = z≤n
      s≤s' : ∀ {m n} {{m≤n : m ≤ₙ n}} → suc m ≤ₙ suc n
      s≤s' {m} {n} {{m≤n}} = s≤s m≤n

  ¬1<0 : ¬(1 <ₙ 0)
  ¬1<0 (k , p) = snotz (sym (+-suc k 1) ∙ p) 
  --¬1<0 = λ ()

  suc-preserves-<ₙ : ∀{x y} → x <ₙ y → suc x <ₙ suc y
  suc-preserves-<ₙ {x} {y} p = s≤s p
  suc-reflects-<ₙ : ∀{x y} → suc x <ₙ suc y → x <ₙ y
  suc-reflects-<ₙ {x} {y} (k , p) = k , (injSuc (sym (+-suc k (suc x)) ∙ p))
  -- suc-reflects-<ₙ {x} {y} (s≤s p) = p

  ¬[k+x<k] : ∀ k x → ¬(k +ₙ x <ₙ k)
  ¬[k+x<k] k x (z , p) = snotz $ sym $ inj-m+ {k} {0} (+-zero k ∙ sym p ∙ +-suc z (k +ₙ x) ∙ (λ i → suc (+-comm z (k +ₙ x) i)) ∙ (λ i → suc (+-assoc k x z (~ i))) ∙ sym (+-suc k (x +ₙ z)))
  
  -- ¬[k+x<k] (zero ) (zero )   = λ ()
  -- ¬[k+x<k] (suc k) (zero ) p = ¬[k+x<k] _ _ (suc-reflects-<ₙ p)
  -- ¬[k+x<k] (zero ) (suc x)   = λ ()
  -- ¬[k+x<k] (suc k) (suc x) p = ¬[k+x<k] _ _ (suc-reflects-<ₙ p)

  data NumberLevel : Type where
    isNat     : NumberLevel
    isInt     : NumberLevel
    isRat     : NumberLevel
    isReal    : NumberLevel
    isComplex : NumberLevel  

  -- NumberLevelEnumeration
  NLE' : NumberLevel → ℕ
  NLE' isNat     = 0
  NLE' isInt     = 1
  NLE' isRat     = 2
  NLE' isReal    = 3
  NLE' isComplex = 4

  NLE⁻¹' : ℕ → NumberLevel
  NLE⁻¹' 0 = isNat
  NLE⁻¹' 1 = isInt
  NLE⁻¹' 2 = isRat
  NLE⁻¹' 3 = isReal
  NLE⁻¹' 4 = isComplex
  NLE⁻¹' x = isComplex
  -- NLE⁻¹' (suc⁵ fst₁) = isComplex

  NLE : NumberLevel → Fin 5
  NLE isNat     = 0 , it
  NLE isInt     = 1 , it
  NLE isRat     = 2 , it
  NLE isReal    = 3 , it
  NLE isComplex = 4 , it

  _^ᶠ_ : ∀{A : Type ℓ} → (A → A) → ℕ → A → A
  _^ᶠ_ f zero x = x
  _^ᶠ_ f (suc zero) x = (f x) 
  _^ᶠ_ f (suc n) x = (f ^ᶠ n) (f x)

  pattern suc⁵ x = suc (suc (suc (suc (suc x))))

  NLE⁻¹ : Fin 5 → NumberLevel
  NLE⁻¹ (0 , p) = isNat
  NLE⁻¹ (1 , p) = isInt
  NLE⁻¹ (2 , p) = isRat
  NLE⁻¹ (3 , p) = isReal
  NLE⁻¹ (4 , p) = isComplex
  NLE⁻¹ (suc⁵ fst₁ , p) = ⊥-elim {A =  λ _ → NumberLevel} $ ¬[k+x<k] 5 fst₁ p

  NLE-id¹ : ∀ x → fst (NLE (NLE⁻¹ x)) ≡ fst x
  NLE-id¹ (0 , p) = refl
  NLE-id¹ (1 , p) = refl
  NLE-id¹ (2 , p) = refl
  NLE-id¹ (3 , p) = refl
  NLE-id¹ (4 , p) = refl
  NLE-id¹ (suc⁵ fst₁ , p) = ⊥-elim {A =  λ _ → fst (NLE (NLE⁻¹ (suc⁵ fst₁ , p))) ≡ suc⁵ fst₁} $ ¬[k+x<k] 5 fst₁ p

  NLE-id² : ∀ x → NLE⁻¹ (NLE x) ≡ x
  NLE-id² isNat     = refl 
  NLE-id² isInt     = refl
  NLE-id² isRat     = refl
  NLE-id² isReal    = refl
  NLE-id² isComplex = refl

  _≤ₙₗ_ : NumberLevel → NumberLevel → Type
  a ≤ₙₗ b = fst (NLE a) ≤ₙ fst (NLE b)

  _≤ₙₗ'_ : NumberLevel → NumberLevel → Type
  a ≤ₙₗ' b = (NLE' a) ≤ₙ (NLE' b)

  minₙₗ' : NumberLevel → NumberLevel → NumberLevel
  minₙₗ' a b = NLE⁻¹' (minₙ (NLE' a) (NLE' b))

  maxₙₗ' : NumberLevel → NumberLevel → NumberLevel
  maxₙₗ' a b = NLE⁻¹' (maxₙ (NLE' a) (NLE' b))

  data PositivityLevel : Type where
    anyPositivity : PositivityLevel
    isNonzero     : PositivityLevel
    isNonnegative : PositivityLevel
    isPositive    : PositivityLevel
    isNegative    : PositivityLevel
    isNonpositive : PositivityLevel

  private
    pattern ⁇x⁇ = anyPositivity
    pattern x#0 = isNonzero
    pattern 0≤x = isNonnegative
    pattern 0<x = isPositive
    pattern x<0 = isNegative
    pattern x≤0 = isNonpositive

  record NumberProp : Type where
    constructor _,,_
    field
      level     : NumberLevel
      positivity : PositivityLevel

  -- splitting this into a separate function to be able to make use of NumberLevel without inspecting PositivitLevel

  -- NumberLevel interpretation
  Il : NumberLevel → Type ℝℓ
  Il isNat     = ℕCarrier
  Il isInt     = ℤCarrier
  Il isRat     = ℚCarrier
  Il isReal    = ℝCarrier
  Il isComplex = ℂCarrier

  -- PositivityLevel interpretation
  Ip : (nl : NumberLevel) → PositivityLevel → (x : Il nl) → Type ℝℓ'
  Ip isNat     ⁇x⁇ x =                                        Lift Unit
  Ip isNat     x#0 x = let open ROrderedCommSemiring ℕOCSR in ( x # 0f)
  Ip isNat     0≤x x = let open ROrderedCommSemiring ℕOCSR in (0f ≤  x)
  Ip isNat     0<x x = let open ROrderedCommSemiring ℕOCSR in (0f <  x)
  Ip isNat     x≤0 x = let open ROrderedCommSemiring ℕOCSR in ( x ≤ 0f)
  Ip isNat     x<0 x =                                        Lift ⊥
  Ip isInt     ⁇x⁇ x =                                        Lift Unit
  Ip isInt     x#0 x = let open ROrderedCommRing     ℤOCR  in ( x # 0f)
  Ip isInt     0≤x x = let open ROrderedCommRing     ℤOCR  in (0f ≤  x)
  Ip isInt     0<x x = let open ROrderedCommRing     ℤOCR  in (0f <  x)
  Ip isInt     x≤0 x = let open ROrderedCommRing     ℤOCR  in ( x ≤ 0f)
  Ip isInt     x<0 x = let open ROrderedCommRing     ℤOCR  in ( x < 0f)
  Ip isRat     ⁇x⁇ x =                                        Lift Unit        
  Ip isRat     x#0 x = let open ROrderedField        ℚOF   in ( x # 0f)
  Ip isRat     0≤x x = let open ROrderedField        ℚOF   in (0f ≤  x)
  Ip isRat     0<x x = let open ROrderedField        ℚOF   in (0f <  x)
  Ip isRat     x≤0 x = let open ROrderedField        ℚOF   in ( x ≤ 0f)
  Ip isRat     x<0 x = let open ROrderedField        ℚOF   in ( x < 0f)
  Ip isReal    ⁇x⁇ x =                                        Lift Unit 
  Ip isReal    x#0 x = let open ROrderedField        ℝOF   in ( x # 0f)
  Ip isReal    0≤x x = let open ROrderedField        ℝOF   in (0f ≤  x)
  Ip isReal    0<x x = let open ROrderedField        ℝOF   in (0f <  x)
  Ip isReal    x≤0 x = let open ROrderedField        ℝOF   in ( x ≤ 0f)
  Ip isReal    x<0 x = let open ROrderedField        ℝOF   in ( x < 0f)
  Ip isComplex ⁇x⁇ x =                                        Lift Unit 
  Ip isComplex x#0 x = let open RField               ℂF    in ( x # 0f)
  Ip isComplex 0≤x x =                                        Lift ⊥
  Ip isComplex 0<x x =                                        Lift ⊥
  Ip isComplex x≤0 x =                                        Lift ⊥
  Ip isComplex x<0 x =                                        Lift ⊥

  -- NumberProp interpretation
  In : NumberProp → Type (ℓ-max ℝℓ ℝℓ')
  In (level ,, positivity) = Σ (Il level) (Ip level positivity)

  -- common level
  Cl : (a : NumberLevel) → (b : NumberLevel) → NumberLevel -- Σ[ c ∈ NumberLevel ] a ≤ₙₗ c × b ≤ₙₗ c
  Cl a b = maxₙₗ' a b
  -- Cl _         isComplex = isComplex
  -- Cl isComplex _         = isComplex
  -- Cl _         isReal    = isReal
  -- Cl isReal    _         = isReal
  -- Cl _         isRat     = isRat
  -- Cl isRat     _         = isRat
  -- Cl _         isInt     = isInt
  -- Cl isInt     _         = isInt
  -- Cl isNat     isNat     = isNat

  private
    pattern X   = anyPositivity
    pattern X⁺⁻ = isNonzero
    pattern X₀⁺ = isNonnegative
    pattern X⁺  = isPositive
    pattern X⁻  = isNegative
    pattern X₀⁻ = isNonpositive

  -- workflow:
  -- 1. split on the both positivities at once
  -- 2. add a general clause on top
  -- 3. check file
  -- 4. remove all unreachable clauses and goto 2.
  -- feel free to remove too many clauses and let agda display the missing ones
  +-Positivity : PositivityLevel → PositivityLevel → PositivityLevel
  +-Positivity _   X   = X  
  +-Positivity X   _   = X  
  +-Positivity _   X⁺⁻ = X  
  +-Positivity X⁺⁻ _   = X
  -- clauses with same sign
  +-Positivity X₀⁺ X₀⁺ = X₀⁺ 
  +-Positivity X₀⁻ X₀⁻ = X₀⁻ 
  +-Positivity X₀⁺ X⁺  = X⁺  
  +-Positivity X⁺  X₀⁺ = X⁺  
  +-Positivity X⁺  X⁺  = X⁺  
  +-Positivity X₀⁻ X⁻  = X⁻ 
  +-Positivity X⁻  X⁻  = X⁻
  +-Positivity X⁻  X₀⁻ = X⁻
  -- remaining clauses with alternating sign
  +-Positivity X₀⁻ X₀⁺ = X  
  +-Positivity X₀⁺ X₀⁻ = X  
  +-Positivity X⁻  X₀⁺ = X  
  +-Positivity X₀⁺ X⁻  = X  
  +-Positivity X⁻  X⁺  = X  
  +-Positivity X⁺  X⁻  = X  
  +-Positivity X₀⁻ X⁺  = X  
  +-Positivity X⁺  X₀⁻ = X  

  ·-Positivity : PositivityLevel → PositivityLevel → PositivityLevel
  ·-Positivity _   X   = X  
  ·-Positivity X   _   = X  
  ·-Positivity X₀⁺ X⁺⁻ = X  
  ·-Positivity X⁺⁻ X₀⁺ = X
  ·-Positivity X₀⁻ X⁺⁻ = X 
  ·-Positivity X⁺⁻ X₀⁻ = X
  -- multiplying nonzero numbers gives a nonzero number
  ·-Positivity X⁺⁻ X⁺⁻ = X⁺⁻ 
  ·-Positivity X⁺  X⁺⁻ = X⁺⁻ 
  ·-Positivity X⁺⁻ X⁺  = X⁺⁻
  ·-Positivity X⁻  X⁺⁻ = X⁺⁻
  ·-Positivity X⁺⁻ X⁻  = X⁺⁻
  -- multiplying positive numbers gives a positive number
  ·-Positivity X₀⁺ X₀⁺ = X₀⁺ 
  ·-Positivity X₀⁺ X⁺  = X₀⁺ 
  ·-Positivity X⁺  X₀⁺ = X₀⁺ 
  ·-Positivity X⁺  X⁺  = X⁺
  -- multiplying negative numbers gives a negative number
  ·-Positivity X₀⁻ X⁻  = X₀⁺
  ·-Positivity X⁻  X₀⁻ = X₀⁺
  ·-Positivity X₀⁻ X₀⁻ = X₀⁺  
  ·-Positivity X⁻  X⁻  = X⁺ 
  -- multiplying a positive and a negative number gives a negative number
  ·-Positivity X⁻  X₀⁺ = X₀⁻
  ·-Positivity X₀⁺ X⁻  = X₀⁻
  ·-Positivity X₀⁻ X⁺  = X₀⁻
  ·-Positivity X⁺  X₀⁻ = X₀⁻
  ·-Positivity X₀⁻ X₀⁺ = X₀⁻
  ·-Positivity X₀⁺ X₀⁻ = X₀⁻
  ·-Positivity X⁻  X⁺  = X⁻ 
  ·-Positivity X⁺  X⁻  = X⁻

  -- NOTE: well, for 15 allowed coercions, we might just enumerate them
  --   unfortunately with overlapping patterns a style as in `Cl` is not possible
  --   we need to explicitly write out all the 5×5 combinations
  --   or, we implement a min operator which might work even with overlapping patterns

  k+x+sy≢x : ∀ k x y → ¬(k +ₙ (x +ₙ suc y) ≡ x)
  k+x+sy≢x k x y p = snotz $ sym (+-suc k y) ∙ inj-m+ {x} (+-assoc x k (suc y) ∙ (λ i → (+-comm x k) i +ₙ (suc y)) ∙ sym (+-assoc k x (suc y)) ∙ p ∙ sym (+-zero x))

  data Number (p : NumberProp) : Type (ℓ-max ℝℓ ℝℓ') where
    number : In p → Number p

  num : ∀{(l ,, p) : NumberProp} → Number (l ,, p) → Il l
  num (number p) = fst p
  -- num {isNat     ,, p} (number (x , q)) = x
  -- num {isInt     ,, p} (number (x , q)) = x
  -- num {isRat     ,, p} (number (x , q)) = x
  -- num {isReal    ,, p} (number (x , q)) = x
  -- num {isComplex ,, p} (number (x , q)) = x

  -- this narrows the to-be-preserved properties down to the properties that are available
  -- it only affects ℂ where we do not have < and ≤
  availablePositivity : NumberLevel → PositivityLevel → PositivityLevel
  availablePositivity isNat      p  =  p
  availablePositivity isInt      p  =  p
  availablePositivity isRat      p  =  p
  availablePositivity isReal     p  =  p
  availablePositivity isComplex ⁇x⁇ = ⁇x⁇
  availablePositivity isComplex x#0 = x#0
  availablePositivity isComplex 0≤x = ⁇x⁇
  availablePositivity isComplex 0<x = x#0
  availablePositivity isComplex x<0 = x#0
  availablePositivity isComplex x≤0 = ⁇x⁇

  -- TODO: name this "inject" instead of "coerce"
  -- TODO: make the module ℤ and the Carrier ℤ.ℤ
  -- TODO: for a binary relation `a # b` it would be nice to have a way to compose ≡-pathes to the left and the right
  --       similar to how ∙ can be used for pathes
  --       this reasoning might extend to transitive relations
  --       `cong₂ _#_ refl x` and `cong₂ _#_ x refl` to this (together with `transport`)
  -- NOTE: maybe ℕ↪ℤ should be a postfix operation

  module _ where
    module ℕ' = ROrderedCommSemiring ℕOCSR
    module ℤ' = ROrderedCommRing     ℤOCR
    module ℚ' = ROrderedField        ℚOF
    module ℝ' = ROrderedField        ℝOF
    module ℂ' = RField               ℂF

    -- coerce-OCSR : ∀{l p} {ll : NumberLevel} {𝕏OCSR 𝕐OCSR : ROrderedCommSemiring {ℝℓ} {ℝℓ'}}
    --             → (x : Number (l ,, p))
    --             → {f : Il l → Il ll}
    --             → IsROrderedCommSemiringInclusion 𝕏OCSR 𝕐OCSR f
    --             → Ip ll p (f (num x))
    -- coerce-OCSR {l} {ll} {p} {𝕏OCSR} {𝕐OCSR} {f} (number (x , q)) = ?
    
    module _ where
      open ℤ'
      open IsROrderedCommSemiringInclusion ℕ↪ℤinc
      private f = ℕ↪ℤ
      coerce-ℕ↪ℤ : ∀{p} → (x : Number (isNat ,, p)) → Ip isInt p (ℕ↪ℤ (num x))
      coerce-ℕ↪ℤ {⁇x⁇} (number (x , q)) = lift tt
      coerce-ℕ↪ℤ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
      coerce-ℕ↪ℤ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
      coerce-ℕ↪ℤ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
      coerce-ℕ↪ℤ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

    module _ where
      open ℚ'
      open IsROrderedCommSemiringInclusion ℕ↪ℚinc
      private f = ℕ↪ℚ
      coerce-ℕ↪ℚ : ∀{p} → (x : Number (isNat ,, p)) → Ip isRat p (ℕ↪ℚ (num x))
      coerce-ℕ↪ℚ {⁇x⁇} (number (x , q)) = lift tt
      coerce-ℕ↪ℚ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
      coerce-ℕ↪ℚ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q) 
      coerce-ℕ↪ℚ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) 
      coerce-ℕ↪ℚ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

    module _ where
      open ℝ'
      open IsROrderedCommSemiringInclusion ℕ↪ℝinc
      private f = ℕ↪ℝ
      coerce-ℕ↪ℝ : ∀{p} → (x : Number (isNat ,, p)) → Ip isReal p (ℕ↪ℝ (num x))
      coerce-ℕ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
      coerce-ℕ↪ℝ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
      coerce-ℕ↪ℝ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
      coerce-ℕ↪ℝ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
      coerce-ℕ↪ℝ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

    module _ where
      open ℂ'
      -- open IsRFieldInclusion ℕ↪ℝinc
      private f = ℕ↪ℂ
      coerce-ℕ↪ℂ : ∀{p} → (x : Number (isNat ,, p)) → Ip isComplex (availablePositivity isComplex p) (ℕ↪ℂ (num x))
      coerce-ℕ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
      coerce-ℕ↪ℂ {x#0} (number (x , q)) = {!transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)!}
      coerce-ℕ↪ℂ {0≤x} (number (x , q)) = lift tt
      coerce-ℕ↪ℂ {0<x} (number (x , q)) = {!!}
      coerce-ℕ↪ℂ {x≤0} (number (x , q)) = lift tt

    coerce-ℤ↪ℚ : ∀{p} → (x : Number (isInt ,, p)) → Ip isRat p (ℤ↪ℚ (num x))
    coerce-ℤ↪ℚ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℤ↪ℚ {x#0} (number (x , q)) = {!!}
    coerce-ℤ↪ℚ {0≤x} (number (x , q)) = {!!}
    coerce-ℤ↪ℚ {0<x} (number (x , q)) = {!!}
    coerce-ℤ↪ℚ {x<0} (number (x , q)) = {!!}
    coerce-ℤ↪ℚ {x≤0} (number (x , q)) = {!!}

    coerce-ℤ↪ℝ : ∀{p} → (x : Number (isInt ,, p)) → Ip isReal p (ℤ↪ℝ (num x))
    coerce-ℤ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℤ↪ℝ {x#0} (number (x , q)) = {!!}
    coerce-ℤ↪ℝ {0≤x} (number (x , q)) = {!!}
    coerce-ℤ↪ℝ {0<x} (number (x , q)) = {!!}
    coerce-ℤ↪ℝ {x<0} (number (x , q)) = {!!}
    coerce-ℤ↪ℝ {x≤0} (number (x , q)) = {!!}

    coerce-ℤ↪ℂ : ∀{p} → (x : Number (isInt ,, p)) → Ip isComplex p (ℤ↪ℂ (num x))
    coerce-ℤ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℤ↪ℂ {x#0} (number (x , q)) = {!!}
    coerce-ℤ↪ℂ {0≤x} (number (x , q)) = {!!}
    coerce-ℤ↪ℂ {0<x} (number (x , q)) = {!!}
    coerce-ℤ↪ℂ {x<0} (number (x , q)) = {!!}
    coerce-ℤ↪ℂ {x≤0} (number (x , q)) = {!!}

    coerce-ℚ↪ℝ : ∀{p} → (x : Number (isRat ,, p)) → Ip isReal p (ℚ↪ℝ (num x))
    coerce-ℚ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℚ↪ℝ {x#0} (number (x , q)) = {!!}
    coerce-ℚ↪ℝ {0≤x} (number (x , q)) = {!!}
    coerce-ℚ↪ℝ {0<x} (number (x , q)) = {!!}
    coerce-ℚ↪ℝ {x<0} (number (x , q)) = {!!}
    coerce-ℚ↪ℝ {x≤0} (number (x , q)) = {!!}

    coerce-ℚ↪ℂ : ∀{p} → (x : Number (isRat ,, p)) → Ip isComplex p (ℚ↪ℂ (num x))
    coerce-ℚ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℚ↪ℂ {x#0} (number (x , q)) = {!!}
    coerce-ℚ↪ℂ {0≤x} (number (x , q)) = {!!}
    coerce-ℚ↪ℂ {0<x} (number (x , q)) = {!!}
    coerce-ℚ↪ℂ {x<0} (number (x , q)) = {!!}
    coerce-ℚ↪ℂ {x≤0} (number (x , q)) = {!!}

    coerce-ℝ↪ℂ : ∀{p} → (x : Number (isReal ,, p)) → Ip isComplex p (ℝ↪ℂ (num x))
    coerce-ℝ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℝ↪ℂ {x#0} (number (x , q)) = {!!}
    coerce-ℝ↪ℂ {0≤x} (number (x , q)) = {!!}
    coerce-ℝ↪ℂ {0<x} (number (x , q)) = {!!}
    coerce-ℝ↪ℂ {x<0} (number (x , q)) = {!!}
    coerce-ℝ↪ℂ {x≤0} (number (x , q)) = {!!}

  coerce : (from : NumberLevel)
         → (to   : NumberLevel)
         → from ≤ₙₗ' to
         → ∀{p}
         → Number (from ,, availablePositivity from p)
         → Number (to   ,, availablePositivity to   p)
  coerce isNat     isNat     q {p} x = x 
  coerce isNat     isInt     q {p} x = number (ℕ↪ℤ (num x) , coerce-ℕ↪ℤ x)
  coerce isNat     isRat     q {p} x = {! ℕ↪ℚ !}
  coerce isNat     isReal    q {p} x = {! ℕ↪ℝ !}
  coerce isNat     isComplex q {p} x = {! ℕ↪ℂ !}
  coerce isInt     isInt     q {p} x = x 
  coerce isInt     isRat     q {p} x = {! ℤ↪ℚ !}
  coerce isInt     isReal    q {p} x = {! ℤ↪ℝ !}
  coerce isInt     isComplex q {p} x = {! ℤ↪ℂ !}
  coerce isRat     isRat     q {p} x = x 
  coerce isRat     isReal    q {p} x = {! ℚ↪ℝ !}
  coerce isRat     isComplex q {p} x = {! ℚ↪ℂ !}
  coerce isReal    isReal    q {p} x = x 
  coerce isReal    isComplex q {p} x = {! ℝ↪ℂ !}
  coerce isComplex isComplex q {p} x = x 
  --coerce x         y         = nothing
  coerce isInt     isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isRat     isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)  
  coerce isRat     isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isReal    isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isReal    isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isReal    isRat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isComplex isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isComplex isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isComplex isRat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  ,, p)} (k+x+sy≢x _ _ _ q)
  coerce isComplex isReal (k , q) {p} x = ⊥-elim {A = λ _ → Number (isReal ,, p)} (k+x+sy≢x _ _ _ q)

  +-Types : NumberProp → NumberProp → NumberProp
  +-Types (level₀ ,, pos₀) (level₁ ,, pos₁) = (Cl level₀ level₁) ,, +-Positivity pos₀ pos₁

  ·-Types : NumberProp → NumberProp → NumberProp
  ·-Types (level₀ ,, pos₀) (level₁ ,, pos₁) =  (Cl level₀ level₁) ,, ·-Positivity pos₀ pos₁

  ⁻¹-Levels : (a : NumberLevel) → Σ[ b ∈ NumberLevel ] a ≤ₙₗ b
  ⁻¹-Levels isNat     = isRat     , it
  ⁻¹-Levels isInt     = isRat     , it
  ⁻¹-Levels isRat     = isRat     , it
  ⁻¹-Levels isReal    = isReal    , it
  ⁻¹-Levels isComplex = isComplex , it

  ⁻¹-Levels' : (a : NumberLevel) → NumberLevel
  ⁻¹-Levels' x = maxₙₗ' x isRat
  
  ⁻¹-Types : NumberProp → Maybe NumberProp
  ⁻¹-Types (level ,, X  ) = nothing
  ⁻¹-Types (level ,, X₀⁺) = nothing
  ⁻¹-Types (level ,, X₀⁻) = nothing
  ⁻¹-Types (level ,, p  ) = just (fst (⁻¹-Levels level) ,, p)
  
  -Levels : NumberLevel → NumberLevel
  -Levels x = minₙₗ' x isInt
  -- -Levels isNat = isInt
  -- -Levels x     = x

  -Types : NumberProp → NumberProp
  -Types (level ,, X  ) = -Levels level ,, X
  -Types (level ,, X⁺⁻) = -Levels level ,, X⁺⁻
  -Types (level ,, X₀⁺) = -Levels level ,, X₀⁻
  -Types (level ,, X⁺ ) = -Levels level ,, X⁻
  -Types (level ,, X⁻ ) = -Levels level ,, X⁺
  -Types (level ,, X₀⁻) = -Levels level ,, X₀⁺


  -- coerce : (level-from level-to : NumberLevel) → level-to ≤ₙₗ level-from → Il level-from → Il level-to
  -- coerce level-from level-to x = {!!}
  
  --coerce : ∀{p} → (level-from level-to : NumberLevel) → level-from ≤ₙₗ' level-to → Number (level-from ,, p) → Number (level-to ,, p)
  --coerce {p} level-from level-to l<l (number (x , q)) = {!!}

  _+'_ : ∀{l p q} → Number (l ,, p) → Number (l ,, q) → Number (l ,, +-Positivity p q)
  _+'_ a b = {!!}

  _+_ : ∀{p q} → Number p → Number q → Number (+-Types p q)
  _+_ {xlevel ,, xpos} {ylevel ,, ypos} (number (x , xp)) (number (y , yp)) = number ({!!} , {!!})


module _ where
  open ROrderedField ℝOF
  data Number : Type (ℓ-max ℝℓ ℝℓ') where
    ℕ[_]   : (x : ℝCarrier) → Σ[ z ∈ ℕCarrier ] ℕ↪ℝ z ≡ x → Number
    ℤ[_]   : (x : ℝCarrier) → Σ[ z ∈ ℤCarrier ] ℤ↪ℝ z ≡ x → Number
    ℚ[_]   : (x : ℝCarrier) → Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x → Number
    ℝ[_]   : (x : ℝCarrier) → Unit → Number
    ℚ₀⁺[_] : (x : ℝCarrier) → (0f ≤ x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x) → Number
    ℚ⁺[_]  : (x : ℝCarrier) → (0f < x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x) → Number
    ℝ₀⁺[_] : (x : ℝCarrier) → 0f ≤ x → Number
    ℝ⁺[_]  : (x : ℝCarrier) → 0f < x → Number

  num : Number → ℝCarrier
  num (ℕ[   x ] _) = x
  num (ℤ[   x ] _) = x
  num (ℚ[   x ] _) = x
  num (ℝ[   x ] _) = x
  num (ℚ₀⁺[ x ] _) = x
  num (ℚ⁺[  x ] _) = x
  num (ℝ₀⁺[ x ] _) = x
  num (ℝ⁺[  x ] _) = x

  data NumberType : Type where
    Tℕ   : NumberType
    Tℤ   : NumberType
    Tℚ   : NumberType
    Tℝ   : NumberType
    Tℚ₀⁺ : NumberType
    Tℚ⁺  : NumberType
    Tℝ₀⁺ : NumberType
    Tℝ⁺  : NumberType

  totype : NumberType → Type (ℓ-max ℝℓ ℝℓ')
  totype Tℕ   = (x : ℝCarrier) → Lift {ℝℓ} {ℓ-max ℝℓ ℝℓ'} (Σ[ z ∈ ℕCarrier ] ℕ↪ℝ z ≡ x)
  totype Tℤ   = (x : ℝCarrier) → Lift {ℝℓ} {ℓ-max ℝℓ ℝℓ'} (Σ[ z ∈ ℤCarrier ] ℤ↪ℝ z ≡ x)
  totype Tℚ   = (x : ℝCarrier) → Lift {ℝℓ} {ℓ-max ℝℓ ℝℓ'} (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x)
  totype Tℝ   = (x : ℝCarrier) → Lift {ℓ-zero} {ℓ-max ℝℓ ℝℓ'} (Unit)
  totype Tℚ₀⁺ = (x : ℝCarrier) → (0f ≤ x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x)
  totype Tℚ⁺  = (x : ℝCarrier) → (0f < x) × (Σ[ z ∈ ℚCarrier ] ℚ↪ℝ z ≡ x)
  totype Tℝ₀⁺ = (x : ℝCarrier) → 0f ≤ x
  totype Tℝ⁺  = (x : ℝCarrier) → 0f < x
  
  +-table : NumberType → NumberType → NumberType
  +-table x y = y


module GenericOperations where
  module ℕ' = ROrderedCommSemiring ℕOCSR
  module ℝ' = ROrderedField ℝOF
  module ℚ' = ROrderedField ℚOF

  module _ where
    open ℝ'
    postulate
      lemma1 : ∀ x y → 0f < x → 0f < y → 0f < (x + y)
      lemma2 : ∀ x y → 0f ≤ x → 0f ≤ y → 0f ≤ (x + y)

  _+_ : Number → Number → Number
  -- IsROrderedCommSemiringInclusion.preserves-+ ℕ↪ℝinc
  ℕ[ x ] (x₁ , p₁)        + ℕ[ y ] (y₁ , q₁)        =  ℕ[ x ℝ'.+ y ]
    (x₁ ℕ'.+ y₁ , transport (λ i → ℕ↪ℝ (x₁ ℕ'.+ y₁) ≡ (p₁ i ℝ'.+ q₁ i)) (IsROrderedCommSemiringInclusion.preserves-+ ℕ↪ℝinc x₁ y₁) )
  ℚ⁺[ x ] (p₂ , x₁ , p₁) + ℚ⁺[ y ] (q₂ , y₁ , q₁) = ℚ⁺[ x ℝ'.+ y ]
    (lemma1 x y p₂ q₂ , (x₁ ℚ'.+ y₁ , transport (λ i → ℚ↪ℝ (x₁ ℚ'.+ y₁) ≡ (p₁ i ℝ'.+ q₁ i)) (IsROrderedFieldInclusion.preserves-+ ℚ↪ℝinc x₁ y₁)))
  ℚ₀⁺[ x ] (p₂ , x₁ , p₁) + ℚ₀⁺[ y ] (q₂ , y₁ , q₁) = ℚ₀⁺[ x ℝ'.+ y ]
    (lemma2 x y p₂ q₂ , (x₁ ℚ'.+ y₁ , transport (λ i → ℚ↪ℝ (x₁ ℚ'.+ y₁) ≡ (p₁ i ℝ'.+ q₁ i)) (IsROrderedFieldInclusion.preserves-+ ℚ↪ℝinc x₁ y₁)))
  -- TODO: more cases
  -- default case
  x + y = ℝ[ num x ℝ'.+ num y ] tt

  instance
    0<ℚ⁺ : ∀{x p} → ℝ'.0f ℝ'.< num (ℚ⁺[ x ] p)
    0<ℚ⁺ {x} {0<x , p} = 0<x

{-

Frobenius theorem:
  The only finite-dimensional associative division algebras over the reals are
  - the reals themselves,
  - the complex numbers,
  - and the quaternions. 

"Nonzero ring" means "not the trivial ring, the ring with one element".

we have different "levels"

Lattice
  Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
OrderedCommSemiring (ring without additive inverse)
  ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺
OrderedCommRing
  ℤ ℚ ℝ
OrderedField (ring with multiplicative inverse for nonzero elements)
  ℚ ℝ

but we also have
OrderedSemifield (no additive inverse, but multiplicative inverse for nonzero elements)
  ℚ₀⁺ ℝ₀⁺
OrderedSemifieldWithoutZero (no additive inverse, no 0, all multiplicative inverses)
  ℚ⁺ ℝ⁺

for all x from a subspace of ℝ, it's "defining property" is that
  Σ[ z ∈ 𝕏 ] 𝕏↪ℝ z ≡ x
when we have a subspace like 𝕏₀⁺ then additionally we get
  0f ≤ x
and for 𝕏⁺ we get
  0f < x

for all these "levels" we have incusions 𝕏↪ℝ into ℝ
  an included element "carries" the missing properties
  

-}

record PoorFieldInclusion {ℓ ℓ' ℓₚ ℓₚ'} (F : PoorField {ℓ} {ℓₚ}) (G : PoorField {ℓ'} {ℓₚ'}) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ')) where
  constructor poorfieldmor
  module F = PoorField F
  module G = PoorField G
  field
    fun : F.Carrier → G.Carrier
    isPoorFieldInclusion : IsPoorFieldInclusion F G fun
  open IsPoorFieldInclusion isPoorFieldInclusion public

record Coercion' (Y : Type ℓ') (P : Y → Type ℓ'') {X : Type ℓ} (x : X) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
    coerce' : Σ Y P

instance
  coerce-id' : {X : Type ℓ} {x : X} → Coercion' X (λ _ → Unit) {X = X} x
  coerce-id' {x = x} = record { coerce' = x , tt }

coerce : {X : Type ℓ} {Y : Type ℓ'} → (x : X) → {{c : Coercion' Y (λ _ → Y) x}}  → Y
coerce = λ x ⦃ c ⦄ → fst (Coercion'.coerce' c)

{-

now the issue is, that while we can define operations that work on a general Number type with hidden instance arguments
  the output of such an operation still needs to be of "some" type
we cannot output the resulting number and an instance with its properties,
  at least not in a way where the instance is immediately taken up for instance serach
  e.g. in equational reasoning with _≡⟨_⟩ which is a single term and cannot introduce additional instances mid-term
therefore these operations output

-}

{-

reals in Coq
  https://arxiv.org/abs/0809.1644
  Kaliszyk, O'Connor 2009 - Computing with Classical Real Numbers
  Finally, the CReals structure is defined on top of the COrderedField structure. The full list of structures is given below.
    CSetoid    - constructive setoid
    CSemiGroup - semi group
    CMonoid    - monoid
    CGroup     - group
    CAbGroup   - Abelian group
    CRing      - ring
    CField     - field
    COrdField  - ordered field
    CReals     - real number structure

https://perso.crans.org/cohen/CoqWS2018.pdf
  Cohen 2018 - Classical analysis with Coq
  .. has an overview of current implementations in different proof assistants

-}
