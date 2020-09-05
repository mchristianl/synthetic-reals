{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax to infix  -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix  -4 ∃[∶]-syntax --
  ; ∀[∶]-syntax to infix  -4 ∀[∶]-syntax --
  ; ∀[]-syntax to infix  -4 ∀[]-syntax   --
  )
open import Cubical.Data.Unit.Base using (Unit)

import Data.Sum
import Cubical.Data.Sigma

import Cubical.Structures.CommRing

import Cubical.Core.Primitives
import Agda.Builtin.Cubical.Glue
import Cubical.Foundations.Id

open import MoreLogic.Reasoning
open import MoreLogic.Definitions renaming (_ᵗ⇒_ to infixr 0 _ᵗ⇒_; ∀ᵖ[∶]-syntax to infix  -4 ∀ᵖ[∶]-syntax)
open import MoreLogic.Properties

open import Utils -- deMorgan₂'

open import MorePropAlgebra.Definitions as Defs hiding (_≤''_)

module MorePropAlgebra.Booij2020 where

record BooijAssumptions {ℓ ℓ'} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier   : Type ℓ
    0f        : Carrier
    1f        : Carrier
    _<_       : hPropRel Carrier Carrier ℓ'
    min       : Carrier → Carrier → Carrier
    max       : Carrier → Carrier → Carrier
    _+_       : Carrier → Carrier → Carrier
    _·_       : Carrier → Carrier → Carrier
    -_        : Carrier → Carrier
    <-asym    : [ isAsym     _<_ ]
    <-irrefl  : [ isIrrefl   _<_ ]
    <-trans   : [ isTrans    _<_ ]
    <-cotrans : [ isCotrans  _<_ ]
    is-set    : isSet Carrier

  _-_ : Carrier → Carrier → Carrier
  a - b = a + (- b)

  _#_   : hPropRel Carrier Carrier ℓ'
  x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x) -- Booij's and Bridges' definition of _#_

  _≤_   : hPropRel Carrier Carrier ℓ'
  x ≤ y = ¬(y < x)                          -- Booij's  definition of _≤_

  _≤''_ : hPropRel Carrier Carrier (ℓ-max ℓ ℓ')
  x ≤'' y = ∀[ ε ] (y < ε) ⇒ (x < ε)        -- Bridges' definition of _≤_

  -- _>_ = flip _<_
  -- _≥_ = flip _≤_

  field
    _⁻¹       : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier
    ≤-refl    : [ isRefl _≤_ ]
    ≤-antisym : [ isAntisymˢ _≤_ is-set ]

  _/_ : (x y : Carrier) → {{p : [ y # 0f ]}} → Carrier
  (x / y) {{p}} = x · (y ⁻¹) {{p}}

  infix  9 _⁻¹
  infixl 7 _·_
  infixl 7 _/_
  infix  6 -_
  infix  5 _-_
  infixl 5 _+_
  infixl 4 _#_
  infixl 4 _≤_
  infixl 4 _<_
  -- infixl 4 _≥_
  -- infixl 4 _>_

module BooijResults {ℓ ℓ'} (assumptions : BooijAssumptions {ℓ} {ℓ'}) where
  open BooijAssumptions assumptions -- atlernative to module telescope

  -- R2-2 = ∀[ x ] ∀[ y ]   ( x < y)            ⇒ (∀[ z ]    (z < y) ⊔ (x < z))

  +-<-extensional-disjointness = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ] (x + y) < (z + w) ⇒ (x < z) ⇒ ¬ (y < w)
  -- NOTE: we cannot proof disjointness of `(x < z) ⊔ (y < w)` at this state, given only 1., 2., 3., 4. and 5. from Booij2020
  --       because we do not have a single theorem that relates `_+_` and `_<_`
  --       only `+-<-extensional` establishes these properties, so we need to bootstrap the ⊎-version of `+-<-extensional` with itself
  --       we will need only item-4 for this
  --       well... we have +-#-Extensional. Maybe that suffices?
  -- 6. (†)
  +-<-extensional = λ(disj : [ +-<-extensional-disjointness ])
                  → ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ] ∀ᵖ[ p ∶ (x + y) < (z + w) ] [ disj w x y z p ] (x < z) ⊎ᵖ (y < w)
  -- 6. (∗)
  ·-preserves-<   = ∀[ x ] ∀[ y ] ∀[ z ]        0f < z ⇒ x < y ⇒ (x · z) < (y · z)

  item-1  = ∀[ x ] ∀[ y ]                                 x ≤ y ⇔ ¬(y < x)
  item-2  = ∀[ x ] ∀[ y ]                                 x # y ⇔ [ <-asym x y ] (x < y) ⊎ᵖ (y < x)
  item-3  = ∀[ x ] ∀[ y ] ∀[ z ]                          x ≤ y ⇔ x + z ≤ y + z
  item-4  = ∀[ x ] ∀[ y ] ∀[ z ]                          x < y ⇔ x + z < y + z
  item-5  = ∀[ x ] ∀[ y ]        0f < x + y          ⇒ (0f < x) ⊔ (0f < y)
  item-6  = ∀[ x ] ∀[ y ] ∀[ z ]  x < y     ⇒  y ≤ z ⇒    x     <     z
  item-7  = ∀[ x ] ∀[ y ] ∀[ z ]  x ≤ y     ⇒  y < z ⇒    x     <     z
  item-8  = ∀[ x ] ∀[ y ] ∀[ z ]  x ≤ y     ⇒ 0f ≤ z ⇒    x · z ≤ y · z
  item-9  = ∀[ x ] ∀[ y ] ∀[ z ] 0f < z     ⇒            (x < y ⇔ x · z < y · z)
  item-10 =                      0f < 1f
