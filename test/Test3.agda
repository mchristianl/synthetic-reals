{-# OPTIONS --cubical --no-import-sorts #-}

module Test3 where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic

abstract
  !_ : ∀{ℓ} {X : Type ℓ} → X → X
  ! x = x

  !-≡ : ∀{ℓ} {X : Type ℓ} → (! X) ≡ X
  !-≡ = refl -- makes use of the definition of `!_` within this block

  !!_ : ∀{ℓ} {X : Type ℓ} → X → ! X
  !!_ {X = X} x = transport (sym (!-≡ {X = X})) x

  !!⁻¹_ : ∀{ℓ} {X : Type ℓ} → ! X → X
  !!⁻¹_ {X = X} x = transport (!-≡ {X = X}) x

  infix 1 !_
  infix 1 !!_
  infix 1 !!⁻¹_

-- !-≡' : ∀{ℓ} {X : Type ℓ} → (! X) ≡ X
-- !-≡' = refl -- cannot make use of the definition of `!_` anymore

hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
hPropRel A B ℓ' = A → B → hProp ℓ'

module TestB {ℓ ℓ'} (X : Type ℓ)
             (0ˣ : X) (_+_ _·_ : X → X → X) (_<_ : hPropRel X X ℓ')
             (let infixl 5 _+_; _+_ = _+_) where

  _≤_ : hPropRel X X ℓ'
  x ≤ y = ¬(y < x)

  postulate
    sqrt : (x : X) → {{ ! [ 0ˣ ≤ x ] }} → X
    0≤x² : ∀ x → [ 0ˣ ≤ (x · x) ]

  instance -- module-scope instances
    _ = λ {x} → !! 0≤x² x

  test4 : (x y z : X) → [ 0ˣ ≤ x ] → [ 0ˣ ≤ y ] → X
  test4 x y z 0≤x 0≤y =
    let instance -- let-scope instances
          _ = !! 0≤x
          _ = !! 0≤y
          _ = !! 0≤x² x -- preferred over the instance from module-scope
    in ( (sqrt x)       -- works
       + (sqrt y)       -- also works
       + (sqrt (z · z)) -- uses instance from module scope
       + (sqrt (x · x)) -- uses instance from let-scope (?) -- NOTE: see https://github.com/agda/agda/issues/4688
       )
