{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_; it; typeOf)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax  to infix -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix -4 ∃[∶]-syntax  --
  ; ∀[∶]-syntax to infix -4 ∀[∶]-syntax  --
  ; ∀[]-syntax  to infix -4 ∀[]-syntax   --
  )
-- open import Cubical.Data.Unit.Base using (Unit)
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣

open import Utils
open import MoreLogic.Reasoning
open import MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax  to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax  to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax   to infix -4 ∀〚∶〛-syntax
  ; Σᵖ[]-syntax   to infix -4 Σᵖ[]-syntax
  ; Σᵖ[∶]-syntax  to infix -4 Σᵖ[∶]-syntax
  ) hiding (≡ˢ-syntax)
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions hiding (_≤''_)
open import MorePropAlgebra.Consequences
open import MorePropAlgebra.Structures
open import MorePropAlgebra.Bundles

module MorePropAlgebra.Properties.PartiallyOrderedField {ℓ ℓ'} (assumptions : PartiallyOrderedField {ℓ} {ℓ'}) where

import MorePropAlgebra.Properties.AlmostPartiallyOrderedField
module AlmostPartiallyOrderedField'Properties  = MorePropAlgebra.Properties.AlmostPartiallyOrderedField   record { PartiallyOrderedField assumptions }
module AlmostPartiallyOrderedField'            =                            AlmostPartiallyOrderedField   record { PartiallyOrderedField assumptions }
-- (      AlmostPartiallyOrderedField')           =                            AlmostPartiallyOrderedField ∋ record { PartiallyOrderedField assumptions }

-- open PartiallyOrderedField assumptions renaming (Carrier to F; _-_ to _-_)

import MorePropAlgebra.Booij2020
open MorePropAlgebra.Booij2020.Chapter4 (record { PartiallyOrderedField assumptions })
open +-<-ext+·-preserves-<⇒ (PartiallyOrderedField.+-<-ext assumptions) (PartiallyOrderedField.·-preserves-< assumptions)
-- open AlmostPartiallyOrderedField'
open MorePropAlgebra.Properties.AlmostPartiallyOrderedField (record { PartiallyOrderedField assumptions })
open PartiallyOrderedField assumptions renaming (Carrier to F; _-_ to _-_) hiding (_#_; _≤_)
open AlmostPartiallyOrderedField' using (_#_; _≤_)

abstract
  #-tight : ∀ a b → [ ¬(a # b) ] → a ≡ b; _ : [ isTightˢ''' _#_ is-set ]; _ = #-tight
  #-tight = isTightˢ'''⇔isAntisymˢ _<_ is-set <-asym .snd ≤-antisym

  +-#-ext : ∀ w x y z → [ (w + x) # (y + z) ] → [ (w # y) ⊔ (x # z) ]; _ : [ is-+-#-Extensional _+_ _#_ ]; _ = +-#-ext
  -- Consider the case w + x < y + z, so that we can use (†) to obtain w < y ∨ x < z,
  --   which gives w # y ∨ x # z in either case.
  +-#-ext w x y z (inl w+x<y+z) = case +-<-ext _ _ _ _ w+x<y+z as (w < y) ⊔ (x < z) ⇒ ((w # y) ⊔ (x # z)) of λ
    { (inl w<y) → inlᵖ (inl w<y)
    ; (inr x<z) → inrᵖ (inl x<z) }
  -- The case w + x > y + z is similar.
  +-#-ext w x y z (inr y+z<w+x) = case +-<-ext _ _ _ _ y+z<w+x as (y < w) ⊔ (z < x) ⇒ ((w # y) ⊔ (x # z)) of λ
    { (inl y<w) → inlᵖ (inr y<w)
    ; (inr z<x) → inrᵖ (inr z<x) }

-- Properties.PartiallyOrderedField assumptions
--   opens PartiallyOrderedField assumptions
--     opens IsPartiallyOrderedField is-PartiallyOrderedField public
--       opens IsAlmostPartiallyOrderedField is-AlmostPartiallyOrderedField public
--         contains definition of _#_
--           becomes `_#_`
--   opens MorePropAlgebra.Properties.AlmostPartiallyOrderedField assumptions
--     opens AlmostPartiallyOrderedField assumptions
--       opens IsAlmostPartiallyOrderedField is-AlmostPartiallyOrderedField public
--         contains definition of _#_
--           becomes `AlmostPartiallyOrderedField'._#_`

-- all these become `_#_`
--   _#_
--   PartiallyOrderedField._#_ assumptions
--   IsPartiallyOrderedField._#_ (PartiallyOrderedField.is-PartiallyOrderedField assumptions)
--   IsAlmostPartiallyOrderedField._#_ (IsPartiallyOrderedField.is-AlmostPartiallyOrderedField (PartiallyOrderedField.is-PartiallyOrderedField assumptions))
-- but
--   PartiallyOrderedField._#_ (record { PartiallyOrderedField assumptions })
-- becomes
--   PartiallyOrderedField._#_ record { Carrier = F ; 0f = 0f ; 1f = 1f ; _+_ = _+_ ; -_ = -_ ; _·_ = _·_ ; min = min ; max = max ; _<_ = _<_ ; is-PartiallyOrderedField = is-PartiallyOrderedField }
-- when we define
--   foo = PartiallyOrderedField ∋ (record { PartiallyOrderedField assumptions })
-- then
--   PartiallyOrderedField._#_ foo
-- becomes
--   (foo PartiallyOrderedField.# x)

-- foo = PartiallyOrderedField ∋ (record { PartiallyOrderedField assumptions })
--
-- test : ∀ x y → [ (PartiallyOrderedField._#_ foo) x y ]
-- test = {! ·-inv''  !}
