{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (_∋_; _$_)

import Data.Sum
import Cubical.Data.Sigma

import Cubical.Structures.CommRing

import Cubical.Core.Primitives
import Agda.Builtin.Cubical.Glue
import Cubical.Foundations.Id

open import MoreLogic.Reasoning
open import MoreLogic.Definitions
open import MoreLogic.Properties

open import Utils -- deMorgan₂'

open import MorePropAlgebra.Definitions as Defs hiding (_≤''_)

module MorePropAlgebra.Bridges1999 {ℓ ℓ'} {A : Type ℓ} (_<_ : hPropRel A A ℓ')
  (let _≤_ : hPropRel A A ℓ'; x ≤ y = ¬(y < x)) -- Booij's  definition of _≤_
  (let _≤''_ = Defs._≤''_ {_<_ = _<_})          -- Bridges' definition of _≤_
  (is-set : isSet A)
  (0f : A)
  (<-irrefl  : [ isIrrefl   _<_        ])
  (<-cotrans : [ isCotrans  _<_        ])
  (≤-antisym : [ isAntisymˢ _≤_ is-set ])
  where

-- bridges-R3-3 : ∀ x y z → (x > y ∧ y > z) ⇒ x > z -- NOTE: this is transitivity
-- Since x > y, either x > z or z > y. The latter is ruled out by axiom R2(1).

bridges-R3-4 : ∀ x y → [ ¬((x < y) ⊓ (y ≤ x)) ]
bridges-R3-4 x y (x<y , y≤x) = y≤x x<y

bridges-R3-5 : ∀ x y z → [ x ≤ y ] → [ y < z ] → [ x < z ]
-- Either x < z or y < x. The latter is ruled out by 4.
bridges-R3-5 x y z x≤y y<z = ⊔-elim (y < x) (x < z) (λ _ → x < z) (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z) (<-cotrans y z y<z x)

bridges-R3-6 : ∀ x y z → [ x < y ] → [ y ≤ z ] → [ x < z ]
bridges-R3-6 x y z x<y y≤z = ⊔-elim (x < z) (z < y) (λ _ → x < z) (λ x<z → x<z) (λ z<y → ⊥-elim (y≤z z<y)) (<-cotrans _ _ x<y z)

-- suppose that x < ε for all ε > 0. If x > 0, then x < x, a contradiction; so 0 ≥ x. Thus x ≥ 0 and 0 ≥ x, and therefore x = 0.
bridges-R3-12 : ∀ x → [ 0f ≤ x ] → (∀ ε → [ 0f < ε ] → [ x < ε ]) → x ≡ 0f
bridges-R3-12 x 0≤x [∀ε>0∶x<ε] =
  let x≤0 : [ x ≤ 0f ]
      x≤0 0<x = <-irrefl x ([∀ε>0∶x<ε] x 0<x)
  in ≤-antisym x 0f x≤0 0≤x

≤''⇒≤ : ∀ x y → [ x ≤'' y ] → [ x ≤ y ]
≤''⇒≤ x y x≤''y y<x = <-irrefl x (x≤''y x y<x)

≤⇒≤'' : ∀ x y → [ x ≤ y ] → [ x ≤'' y ]
≤⇒≤'' x y x≤y ε y<ε = bridges-R3-5 x y ε x≤y y<ε

-- NOTE: it seems that `_⇔_` might be the "preferred" / "most performant" / "least cluttered" way to "store" a path when hProps are available
≤-⇔-≤'' : ∀ x y → [ (x ≤ y) ⇔ (x ≤'' y) ]
≤-⇔-≤'' x y = (≤⇒≤'' x y) , (≤''⇒≤ x y)

≤-≡-≤'' : ∀ x y → (Liftᵖ {ℓ'} {ℓ} (x ≤ y)) ≡ (x ≤'' y)
≤-≡-≤'' x y = ⇔toPath
            ((≤⇒≤'' x y) ∘ (unliftᵖ (x ≤ y))) -- (λ{ (lift p) → ≤⇒≤'' x y p})
            ((liftᵖ (x ≤ y)) ∘ (≤''⇒≤ x y))

-- ≤+preserves-<⇒≡ ... this is just antisymmetry for different ≤s : ∀ x y → [ x ≤ y ] → [ y ≤'' x ] → x ≡ y
bridges-R3-12' : ∀ x y → [ x ≤ y ] → (∀ ε → [ x < ε ] → [ y < ε ]) → x ≡ y
bridges-R3-12' x y x≤y [∀x<ε→y<ε] =
  let y≤x : [ y ≤ x ]
      y≤x x<y = <-irrefl y ([∀x<ε→y<ε] y x<y)
  in ≤-antisym x y x≤y y≤x
