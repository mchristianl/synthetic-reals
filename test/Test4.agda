{-# OPTIONS --cubical --no-import-sorts #-}

module Test4 where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

record !_ {ℓ} (X : Type ℓ) : Type ℓ where
  inductive
  constructor !!_
  field x : X

open !_ hiding (x)
infix 1 !!_
infix 1 !_

!-iso : ∀{ℓ} {X : Type ℓ} → Iso (! X) X
Iso.fun      !-iso = !_.x
Iso.inv      !-iso = !!_
Iso.rightInv !-iso = λ      x  → refl
Iso.leftInv  !-iso = λ{ (!! x) → refl }

!-≡ : ∀{ℓ} {X : Type ℓ} → (! X) ≡ X
!-≡ {X = X} = isoToPath !-iso

!-equiv : ∀{ℓ} {X : Type ℓ} → (! X) ≃ X
!-equiv = !_.x , λ where .equiv-proof x → ((!! x) , refl) , λ{ ((!! y) , p) → λ i → (!! p (~ i)) , (λ j → p (~ i ∨ j)) }

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
       + (sqrt (x · x)) -- uses instance from let-scope (?)
       )
