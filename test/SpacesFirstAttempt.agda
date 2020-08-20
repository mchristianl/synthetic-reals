{-# OPTIONS --cubical --no-import-sorts #-}

module SpacesFirstAttempt where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel
open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)

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

-- different "variants" of reals
--   this might be a "basis" for an instance-based, typeclass-like coercion "mechanism" between different "numbers"
--
-- NOTE: the intuition with "variants" might align with "subset" where different properties are available
--       from a "subset" in this manner, we want that it is "easy" to
--       - make use of properties from the "full" set
--         - this might be realized with an abuse of Agda's record-update syntax
--         - the "core" of such a mechanism is to have a proper naming-scheme (because record-update basically just matches names)
--       - "spontaneously enrich" some current context with a subset proof
--         and then make use of the subset lemmas on elements of the "whole" set

{- IDEA: for the organization of these definitions

we might have some "ur"-reals
  these are "the" "numbers"
or even better: just "ur-numbers" to support functions from 𝕂 into ℝ₀⁺
being part of some concrete number type is attached via a hidden instance-proof property
  this should be similar to a typeclass mechanism in Coq or Isabelle/HOL
  TODO: maybe, when re-reading their papers, it becomes apparent that this is how it's done in Hölzl 2013 and the Coq-Port of their work
    because I remember them writing something like "this work makes heavy use of typeclasses"
so we explicitly quantify over "numbers" and implicitly quantify over "properties"
the available properties must have the same name in each different number type
  that way we can make use of Agda's record update syntax
  (well, there can be exceptions since it is possible to rename stuff on the fly, but it'd be more convenient if the names already match)
we might decide NOT (!) to overload operations such as _<_ and similar
  because having both overloaded - operations and numbers - is likely to generate resolving issues
AND we must be very aware when a type depends on a hidden argument
  because in that case, we need to add an explicit coercion to our result
  so we just accept that "inconvenience" and embrace a style where these "important" arguments/instances are treated differently
    especially they should not be used anonymously
    and this might also embrace an anonymous-module style to create a scope that is shared by both: the declaration and the definition of something
      This might look ugly at first but that's okay if it works out

-}

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
  -- we also often use ℂ in the application
  -- we might often use ℝ in places where ℚ would suffice
  -- we use 𝕂 for "ℝ or ℂ"
  -- and we use ℕ, Fin k, ℤ of course
  -- then, there is (exterior) algebra

-- NOTE: one could bring different "variants" of the reals into scope like so
--       but we are likely to omit populating the scope with overlapping reals as much as possible

open ℝField ℝF using () renaming
  ( Carrier to ℝ
  )

open ℝ₀⁺Field ℝ₀⁺F using () renaming
  ( Carrier to ℝ₀⁺
  ; 0f to 0f₀⁺
  )

open ℝ⁺Field ℝ⁺F using () renaming
  ( Carrier to ℝ⁺
  )

---------- application -------------

{-
-- ∅ : ⊥ → 

-- topology on a set X
record IsTopology
  (X : Type ℓ)
  (isOpen : X → Type ℓ')
  (_∪_ : X → X → X)
  (_∩_ : X → X → X)
  : Type _ where
  field

record TopologicalSpace : Type _ where
-}

record IsMetric {ℓ} {X : Type ℓ} (d : X → X → ℝ₀⁺) : Type (ℓ-max ℓ (ℓ-max ℝℓ ℝℓ')) where
  open ℝ₀⁺Field ℝ₀⁺F
  field
    -- identity of indiscernibles
    isPositiveOnNonzero      : ∀ x y → 0f ≡ d x y → x ≡ y
    isPositiveOnNonzero-back : ∀ x y → x ≡ y → 0f ≡ d x y
    isSym                    : ∀ x y → d x y ≡ d y x
    -- subadditivity / triangle inequality
    isTriangleIneq           : ∀ x y z → d x y ≤ d x z + d z y

record MetricSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℝℓ' ℝℓ)) where
  field
    Carrier  : Type ℓ
    d        : Carrier → Carrier → ℝ₀⁺
    isMetric : IsMetric d
  open IsMetric isMetric public

𝕂ℓ  = ℝℓ
𝕂ℓ' = ℝℓ'

module _ (𝕂F : 𝕂Field {𝕂ℓ} {𝕂ℓ'}) where
  open 𝕂Field 𝕂F renaming (Carrier to 𝕂; 0f to 0ₛ; _+_ to _+ₛ_)
  postulate
    ∣_∣ᵣ : 𝕂 → ℝ₀⁺
  record IsVectorAddition {X : Type ℓ} (0v : X) (_+_ : X → X → X) (-_ : X → X) : Type (ℓ-max ℓ (ℓ-max 𝕂ℓ 𝕂ℓ')) where
    field
      isCommutative : ∀ x y → x + y ≡ y + x
      isAssociative : ∀ x y z → (x + y) + z ≡ x + (y + z)
      rid           : ∀ x → x + 0v ≡ x
      rid-back      : ∀ x y → x + y ≡ x → y ≡ 0v
      invr          : ∀ x → x + (- x) ≡ 0v

  record IsScalarMultiplication {X : Type ℓ} (0v : X) (_+_ : X → X → X) (-_ : X → X) (_·ₛ_ : 𝕂 → X → X) : Type (ℓ-max ℓ (ℓ-max 𝕂ℓ 𝕂ℓ')) where
    field
      ·ₛ-dist-+ : ∀ α x y → α ·ₛ (x + y) ≡ (α ·ₛ x) + (α ·ₛ y)
      0-left-nullifies : ∀ x → 0ₛ ·ₛ x ≡ 0v
      +ₛ-dist-· : ∀ α β x → (α +ₛ β) ·ₛ x ≡ (α ·ₛ x) + (β ·ₛ x)

  record VectorSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max 𝕂ℓ 𝕂ℓ')) where
    field
      Carrier : Type ℓ
      0v      : Carrier
      _+_     : Carrier → Carrier → Carrier
      -_      : Carrier → Carrier
      _·ₛ_    : 𝕂 → Carrier → Carrier
      isVectorAddition : IsVectorAddition 0v _+_ (-_)
      isScalarMultiplication : IsScalarMultiplication 0v _+_ -_ _·ₛ_

    open IsVectorAddition isVectorAddition public
    open IsScalarMultiplication isScalarMultiplication public

  module _ (VS : VectorSpace {ℓ}) where
    open VectorSpace VS using (_+_; _·ₛ_) renaming (Carrier to V; 0v to 0ᵥ)
    open ℝ₀⁺Field ℝ₀⁺F using () renaming (0f to 0ᵣ; _≤_ to _≤ᵣ_; _+_ to _+ᵣ_; _·_ to _·ᵣ_)
    record IsNorm (‖_‖ᵥ : V → ℝ₀⁺) : Type (ℓ-max ℓ (ℓ-max 𝕂ℓ 𝕂ℓ')) where
      field
        idToIndisc      : ∀ x → ‖ x ‖ᵥ ≡ 0ᵣ → x ≡ 0ᵥ
        idToIndisc-back : ∀ x → x ≡ 0ᵥ → ‖ x ‖ᵥ ≡ 0ᵣ
        triangleIneq    : ∀ x y → ‖ x + y ‖ᵥ ≤ᵣ ‖ x ‖ᵥ +ᵣ ‖ y ‖ᵥ
        absLinear       : ∀ α x → ‖ α ·ₛ x ‖ᵥ ≡ ∣ α ∣ᵣ ·ᵣ ‖ x ‖ᵥ
        
  record NormedVectorSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max 𝕂ℓ 𝕂ℓ')) where
    field
      VS : VectorSpace {ℓ}
    open VectorSpace VS public
    field
      ‖_‖ᵥ : Carrier → ℝ₀⁺
      isNorm : IsNorm VS ‖_‖ᵥ
    open IsNorm isNorm public

-- cauchy w.r.t. a distance function
-- NOTE: Booij defines cauchy w.r.t. the rationals ℚ

IsCauchy : {X : Type ℓ} (d : X → X → ℝ₀⁺) → IsMetric d → (x : ℕ → X) → Type (ℓ-max ℝℓ ℝℓ')
IsCauchy d isMetric x =
  let open ℝ₀⁺Field ℝ₀⁺F using () renaming (0f to 0ᵣ; _<_ to _<ᵣ_; _≤_ to _≤ᵣ_; _+_ to _+ᵣ_; _·_ to _·ᵣ_)
  in ∀(ε : ℝ₀⁺) → 0ᵣ <ᵣ ε → Σ[ I ∈ ℕ ] ∀ m n → I ≤ₙ m → I ≤ₙ n → d (x m) (x n) <ᵣ ε

-- limit w.r.t. a metric
IsLimit : {X : Type ℓ} {d : X → X → ℝ₀⁺} → (isMetric : IsMetric d) → (x : ℕ → X) → X → Type (ℓ-max ℝℓ ℝℓ')
IsLimit {d = d} isMetric x a =
  let open ℝ₀⁺Field ℝ₀⁺F using () renaming (0f to 0ᵣ; _<_ to _<ᵣ_; _≤_ to _≤ᵣ_; _+_ to _+ᵣ_; _·_ to _·ᵣ_)
  in ∀(ε : ℝ₀⁺) → 0ᵣ <ᵣ ε → Σ[ I ∈ ℕ ] ∀ m → I ≤ₙ m → d (x m) a <ᵣ ε

IsCauchyConvergent : {X : Type ℓ} (d : X → X → ℝ₀⁺) → (isMetric : IsMetric d) → (x : ℕ → X) → IsCauchy d isMetric x → Type (ℓ-max ℓ (ℓ-max ℝℓ ℝℓ'))
IsCauchyConvergent {X = X} d isMetric x isCauchy = Σ[ a ∈ X ] IsLimit isMetric x a

record CompleteMetricSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max ℝℓ' ℝℓ)) where
  field
    MS : MetricSpace {ℓ}

  open MetricSpace MS public
  
  field
    isCauchyComplete : ∀ x → (isCauchy : IsCauchy d isMetric x) → Σ[ a ∈ Carrier ] IsLimit isMetric x a

module Lemma-1 (𝕂F : 𝕂Field {𝕂ℓ} {𝕂ℓ'}) (NVS : NormedVectorSpace 𝕂F {ℓ}) where
  open NormedVectorSpace NVS renaming (Carrier to V)
  open ℝ₀⁺Field ℝ₀⁺F using () renaming (_≤_ to _≤ᵣ_; _+_ to _+ᵣ_)
  
  d : V → V → ℝ₀⁺
  d x y = ‖ x + (- y) ‖ᵥ
  
  lemma-1 : IsMetric d 
  lemma-1 = record
    { isPositiveOnNonzero      = {!!}
    ; isPositiveOnNonzero-back = {!!}
    ; isSym                    = {! λ x y → ?!}
    ; isTriangleIneq           = {!!}
    }

  IsNormMetric : (V → V → ℝ₀⁺) → Type (ℓ-max ℓ ℝℓ)
  IsNormMetric d' = ∀ x y → d' x y ≡ d x y

module _ (𝕂F : 𝕂Field {𝕂ℓ} {𝕂ℓ'}) where
  record CompleteNormedVectorSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max 𝕂ℓ' 𝕂ℓ)) where
    field
      NVS : NormedVectorSpace 𝕂F {ℓ}
    
    open NormedVectorSpace NVS public

    d : Carrier → Carrier → ℝ₀⁺
    d x y = ‖ x + (- y) ‖ᵥ

    isMetric : IsMetric d
    isMetric = Lemma-1.lemma-1 𝕂F NVS

    field
      isCauchyComplete : ∀ x → (isCauchy : IsCauchy d isMetric x) → Σ[ a ∈ Carrier ] IsLimit isMetric x a

  BanachSpace = CompleteNormedVectorSpace

module _ (𝕂F : 𝕂Field {𝕂ℓ} {𝕂ℓ'}) (VS : VectorSpace 𝕂F {ℓ}) where
  open 𝕂Field 𝕂F using (conj) renaming (Carrier to 𝕂; _·_ to _·ₖ_; _+_ to _+ₖ_)
  open VectorSpace VS renaming (Carrier to V)
  
  record IsInnerProduct (‹_,_›ᵥ : V → V → 𝕂) : Type (ℓ-max ℓ (ℓ-max 𝕂ℓ' 𝕂ℓ)) where
    field
      -- pos-definite : ∀ x → x ≠ 0v → ‹ x , x › ∈ ℝ⁺ -- TODO
      conj-sym  : ∀ x y → ‹ x , y ›ᵥ ≡ conj (‹ y , x ›ᵥ)
      lin₁      : ∀ α x y → ‹ α ·ₛ x , y ›ᵥ ≡ α ·ₖ ‹ x , y ›ᵥ
      +distrib₁ : ∀ x y z → ‹ x + y , z ›ᵥ ≡ ‹ x , z ›ᵥ +ₖ ‹ y , z ›ᵥ

  -- If the positive-definite condition is replaced by merely requiring that ⟨ x , x ⟩ ≥ 0 for all x,
  --   then one obtains the definition of positive semi-definite Hermitian form. 

module _ (𝕂F : 𝕂Field {𝕂ℓ} {𝕂ℓ'}) where
  open 𝕂Field 𝕂F using (conj) renaming (Carrier to 𝕂; _·_ to _·ₖ_; _+_ to _+ₖ_)
  
  record InnerProductSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max 𝕂ℓ' 𝕂ℓ)) where
    field
      VS : VectorSpace 𝕂F {ℓ}
    open VectorSpace VS public
    field
      ‹_,_›ᵥ : Carrier → Carrier → 𝕂
      isInnerProduct : IsInnerProduct 𝕂F VS ‹_,_›ᵥ
    open IsInnerProduct isInnerProduct public

    -- ‖_‖ᵥ : Carrier →  ℝ₀⁺
    -- ‖ x ‖ᵥ = sqrt (‹ x , x ›ᵥ)

    -- isNorm : IsNorm VS ‖_‖ᵥ
    -- isNorm = ?

    -- d : Carrier → Carrier → ℝ₀⁺
    -- d x y = ‖ x + (- y) ‖ᵥ

    -- isMetric : IsMetric d
    -- isMetric = Lemma-1.lemma-1 𝕂F NVS

  -- NOTE: there are a lot of properties for InnerProductSpaces: https://en.wikipedia.org/wiki/Inner_product_space#Norm

  record HilbertSpace : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max 𝕂ℓ' 𝕂ℓ)) where
    field
      VS : VectorSpace 𝕂F {ℓ}
    open VectorSpace VS public

    field
      ‹_,_›ᵥ : Carrier → Carrier → 𝕂
      isInnerProduct : IsInnerProduct 𝕂F VS ‹_,_›ᵥ
    open IsInnerProduct isInnerProduct public

    -- ‖_‖ᵥ : Carrier →  ℝ₀⁺
    -- ‖ x ‖ᵥ = sqrt (‹ x , x ›ᵥ)

    -- isNorm : IsNorm VS ‖_‖ᵥ
    -- isNorm = ?

    -- d : Carrier → Carrier → ℝ₀⁺
    -- d x y = ‖ x + (- y) ‖ᵥ

    -- isMetric : IsMetric d
    -- isMetric = Lemma-1.lemma-1 𝕂F NVS
    
    -- field
    --   isCauchyComplete : ∀ x → (isCauchy : IsCauchy d isMetric x) → Σ[ a ∈ Carrier ] IsLimit isMetric x a

-- NOTE:
--   we observe that stronger structure "replaces" weaker structure in the sequence
--     InnerProductSpace < NormedVectorSpace < MetricSpace
--   when we add Cauchy completeness, we get
--     HilbertSpace < BanachSpace < CompleteMetricSpace

-- next up: EuclideanSpace ?
--   see "Hölzl, Immler, Huffman 2013 - Type Classes and Filters for Mathematical Analysis in Isabelle/HOL"
--   here, they start with topological spaces, where we start with the real numbers

-- what about subspaces? How to formulate these?


{-

observed issues
- subspaces
- inclusions/coercions between different variants of "numbers"
- conj
- sqrt
- topological spaces (do we need them after all?)
  - can we follow "Hölzl 2013" ?
- size issues:
  the "amount" of ℓs is "high" and we are not ℓ-suc-ing to 𝕂ℓ and 𝕂ℓ'
  but we are ℓ-suc-ing to ℓ in the definition of PoorField
  so PoorField cannot be in ℓ-zero
- is IsCauchy defined for ε ∈ ℚ or for ε ∈ ℝ ?

in `Cubical.Data.Fin.Base` is written

  Finite types.

  Currently it is most convenient to define these as a subtype of the
  natural numbers, because indexed inductive definitions don't behave
  well with cubical Agda. This definition also has some more general
  attractive properties, of course, such as easy conversion back to ℕ.

and then they state

  Fin : ℕ → Type₀
  Fin n = Σ[ k ∈ ℕ ] k < n

so Σ[ x ∈ 𝕏 ] (P x) kind of falls under what is called a "subtype"

next-up
- infimum and supremum on posets (and sub-posets / sub-lattices ?)
  - we do only really need these on ℝ
  - these do not necessarily exist in the subspace that we regard
- morphisms on these spaces
- (potentially) unbounded linear operators
- algebraic and continuous dual spaces
- Formulation of Riesz representation Theorem on Hilbert spaces

-}
