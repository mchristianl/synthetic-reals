{-# OPTIONS --cubical --no-import-sorts  #-}

module Utils where -- thing that currently do not belong anywhere and do not have many dependencies

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

swap : ∀{x : Type ℓ} {y : Type ℓ'} → x ⊎ y → y ⊎ x
swap (inl x) = inr x
swap (inr x) = inl x

curry : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → (b : B a) → Type ℓ''}
        → ((p : Σ A B) → C (fst p) (snd p))
        → ((x : A) → (y : B x) → C x y)
curry f x y = f (x , y)

-- NOTE: this is non-hProp logic

-- contraposition : {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ¬ Q → ¬ P
-- contraposition f ¬q p = ⊥-elim (¬q (f p))

deMorgan₂' : {P : Type ℓ} {Q : Type ℓ'} → ¬(P ⊎ Q) → (¬ P) × (¬ Q)
deMorgan₂' {P = P} {Q = Q} ¬[p⊎q] = (λ p → ⊥-elim (¬[p⊎q] (inl p))) , λ q → ⊥-elim (¬[p⊎q] (inr q))

-- hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
-- hPropRel A B ℓ' = A → B → hProp ℓ'

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
