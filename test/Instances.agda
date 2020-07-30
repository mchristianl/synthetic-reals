{-# OPTIONS --cubical --no-import-sorts #-}

module Instances where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ)
open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Foundations.Logic

variable
  ℓ ℓ' ℓ'' : Level

PropRel' : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropRel' A B ℓ' = Σ[ R ∈ Rel A B ℓ' ] ∀ a b → isProp (R a b)

record PoorField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    F : Type ℓ
    0f 1f : F
    #-rel : PropRel F F ℓ'

  _#_ = {! #-rel !}
  field
    _+_ _·_ : F → F → F
    _⁻¹ᶠ : (x : F) → {{ {! x # 0f !} }} → F
    -- ·-rinv     : (x : F) → (p : [ x # 0f ]) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    -- ·-linv     : (x : F) → (p : [ x # 0f ]) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    -- ·-inv-back : (x y : F) → (x · y ≡ 1f) → [ x # 0f ] × [ y # 0f ]

  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infixl 5 _+_
  infixl 4 _#_
