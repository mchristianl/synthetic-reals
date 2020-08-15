{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module Number.Bundles where

private
  variable
    ℓ ℓ' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Binary.Base -- Rel
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)

open import MoreAlgebra
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
  
  -- Remark 6.7.7. As we define absolute values by | x | = max(x, -x), as is common in constructive analysis,
  -- if x has a locator, then so does | x |, and we use this fact in the proof of the above theorem.

  abs : Carrier → Carrier
  abs x = max x (- x)

  -- -flips-≤0 : ∀ x   → x  ≤ 0f →    0f ≤ (- x)
  -- -flips-0≤ : ∀ x   → 0f ≤ x  → (- x) ≤    0f

  -- glb      : ∀ x y z → z ≤ min x y → z ≤ x × z ≤ y
  -- glb-back : ∀ x y z → z ≤ x × z ≤ y → z ≤ min x y
  -- lub      : ∀ x y z → max x y ≤ z → x ≤ z × y ≤ z
  -- lub-back : ∀ x y z → x ≤ z × y ≤ z → max x y ≤ z
  -- ≤-antisym : ∀ a b → R a b → R b a → a ≡ b
  -- ≤-refl
  -- ≤-trans

  -- Remark 4.1.9.
  --
  -- 1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that
  -- for every x and y,
  -- 
  --   max(x, y) = x  ∨  max(x, y) = y,
  -- 
  -- which would hold in a linear order.
  -- However, in Lemma 6.7.1 we characterize max as
  -- 
  --   z < max(x, y) ⇔ z < x ∨ z < y,
  -- 
  -- and similarly for min.

  max-sym : ∀ x y → max x y ≡ max y x
  max-sym x y = {!!}

  max-id : ∀ x → max x x ≡ x
  max-id x = {!!}

  abs0≡0 : abs 0f ≡ 0f
  abs0≡0 = {!!}

  abs-preserves-· : ∀ x y → abs (x · y) ≡ abs x · abs y
  abs-preserves-· x y = {!!}
  
  triangle-ineq : ∀ x y → abs (x + y) ≤ (abs x + abs y)
  triangle-ineq = {!!}

  abs-≤      : ∀ x y → abs x ≤ y → (x ≤ y) × ((- x) ≤ y)
  abs-≤ x y  = {!!}
  
  abs-≤-back : ∀ x y → (x ≤ y) × ((- x) ≤ y) → abs x ≤ y
  abs-≤-back x y = {!!}

  0≤abs : ∀ x → 0f ≤ abs x
  0≤abs x = {! triangle-ineq x (- x) !}

  {- from: https://isabelle.in.tum.de/doc/tutorial.pdf "8.4.5 The Numeric Type Classes"

    Absolute Value.

    The absolute value function `abs` is available for all ordered rings, including types int, rat and real.
    It satisfies many properties, such as the following:

      | x * y | ≡ | x | * | y |         (abs_mult)

      | a | ≤ b ⇔ (a ≤ b) ∧ (- a) ≤ b   (abs_le_iff)

      | a + b | ≤ | a | + | b |         (abs_triangle_ineq)
  -}

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

