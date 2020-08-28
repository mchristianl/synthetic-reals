{-# OPTIONS --cubical  #-} --no-import-sorts

module Test2 where
-- open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Data.Empty            -- ⊥
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; ⊥ to ⊥ᵖ)

-- data ⊥ : Set where
-- ¬_ : ∀{ℓ} → Set ℓ → Set ℓ
-- ¬ A = A → ⊥

inst-¬ : ∀{ℓ} {A : Set ℓ} → (A → ⊥) → {{a : A }} → ⊥
inst-¬ f {{a}} = f a

-- record SquareRootSpace {ℓ ℓ' : Level} : Set (ℓ-suc (ℓ-max ℓ ℓ')) where
--   field
--     X : Set ℓ
--     0ˣ : X
--     _<_ : X → X → Set ℓ'

module _ {ℓ ℓ'} (X : Set ℓ) (0ˣ : X) (_<_ : X → X → Set ℓ') where

  _≤_ : X → X → Set ℓ'
  a ≤ b = (b < a) → ⊥ -- ¬(b < a)

  _≤ᵢ_ : X → X → Set ℓ'
  a ≤ᵢ b = {{p : b < a}} → ⊥

  -- postulate _≤'_ : X → X → Set ℓ'

  _≤'_ : X → X → Set ℓ'
  abstract a ≤' b = (b < a) → ⊥

  -- field
  postulate
    sqrt  : (x : X) → {{p : (0ˣ ≤ᵢ x)}} → X
    sqrt' : (x : X) → {{p : (0ˣ ≤' x)}} → X

-- module _ {ℓ ℓ'} (SQS : SquareRootSpace {ℓ} {ℓ'}) where
--   open SquareRootSpace SQS
  test1 : (x : X) → (0ˣ ≤ x) → X
  test1 x 0≤x = let instance _ = inst-¬ 0≤x
                in sqrt x -- works!

  -- test2 : (x y z : X) → (0ˣ ≤ x) → (0ˣ ≤ y) → (0ˣ ≤ z) → X
  -- test2 x y z 0≤x 0≤y 0≤z =
  --   let instance 0≤xᵢ : 0ˣ ≤ᵢ x
  --                0≤xᵢ = inst-¬ 0≤x
  --                0≤yᵢ : 0ˣ ≤ᵢ y
  --                0≤yᵢ = inst-¬ 0≤y
  --                0≤zᵢ : 0ˣ ≤ᵢ z
  --                0≤zᵢ = inst-¬ 0≤z
  --   -- Goal: X
  --   -- Have: ⦃ p : 0ˣ ≤ᵢ x ⦄ → X
  --   in sqrt y -- error!

  test3 : (x y z : X) → (0ˣ ≤' x) → (0ˣ ≤' y) → (0ˣ ≤' z) → X
  test3 x y z 0≤x 0≤y 0≤z =
    let instance _ = 0≤x ; _ = 0≤y ; _ = 0≤z
    in sqrt' y -- works!

-- _p_51 : 0ˣ ≤ᵢ y
-- errorFailed to solve the following constraints:
--   Resolve instance argument
--     _p_51
--       : {ℓ = ℓ₁ : Agda.Primitive.Level} {ℓ' = ℓ'' : Agda.Primitive.Level}
--         (X₁ : Set ℓ₁) (0ˣ₁ : X₁) (_<₁_ : X₁ → X₁ → Set ℓ'') (x₁ y₁ z₁ : X₁)
--         (0≤x₁ : 0ˣ₁ ≤ x₁) (0≤y₁ : 0ˣ₁ ≤ y₁) (0≤z₁ : 0ˣ₁ ≤ z₁) →
--         0ˣ₁ ≤ᵢ y₁
--   Candidates
--     λ ⦃ a ⦄ → z a : ⦃ p : 0ˣ _<_ X ⦄ → ⊥
--     λ ⦃ a ⦄ → 0≤x a : ⦃ p : 0ˣ x X ⦄ → ⊥
--     λ ⦃ a ⦄ → 0≤y a : ⦃ p : 0ˣ y X ⦄ → ⊥


-- Instance arguments with explicit arguments are never considered by
-- instance search, so having an instance argument ⦃ p : 0ˣ ≤ x ⦄ has
-- no effect.
-- when checking that the expression ⦃ p : 0ˣ ≤ x ⦄ → X is a type


{- there is an email of Apostolis Xekoukoulotakis from 03.11.17, 11:52

data ⊥ : Set where

infix 3 ¬ᵢ_

¬ᵢ_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ᵢ P = {{p : P}} → ⊥

infix 3 ¬_

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ P = (p : P) → ⊥

-}
