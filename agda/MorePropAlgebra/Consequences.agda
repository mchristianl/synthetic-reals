{-# OPTIONS --cubical --no-import-sorts  #-}

module MorePropAlgebra.Consequences where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

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

-- NOTE: hProps need to be explicit arguments (that is not a necessity, but we need to give them completely and not just their witnesses)
-- NOTE: I think one can make all `isProp` implementations `abstract` to save some compilation time
--         because we have `isPropIsProp` anyways
--       but for the logic part, it depends on how coslty
--         ⊔-elim, ⊥-elim, ⇒∶_⇐∶_, isoToPath, hProp≡, etc.
--       are and whether they could actually reduce some terms

open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
open import Cubical.HITs.PropositionalTruncation.Properties using (propTruncIsProp) renaming (elim to ∣∣-elim)

open import MorePropAlgebra.Definitions

module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ')
  (let _<_ = R)
  (let _≤_ = R)
  (let _#_ = R)
  where
  -- abstract
  irrefl+trans⇒asym    : [ isIrrefl  R ] → [ isTrans  R ] → [ isAsym  R ]
  irrefl+trans⇒asym'   : [ isIrrefl  R ] → [ isTrans  R ] → [ isAsym' R ]

  isAsym⇔isAsym'       :                              [ isAsym     R  ⇔ isAsym'                    R                           ]
  isTight⇔isTight'     :                              [ isTight    R  ⇔ isTight'                   R                           ]
  isTight'⇔isTight''   :                              [ isTight'   R  ⇔ isTight''                  R                           ]
  isTight'⇔isTight'''  :                              [ isTight'  _<_ ⇔ isTight''' (λ x y →                (x < y) ⊔  (y < x)) ]
  isTight''⇔isTight''' : (<-asym : [ isAsym  _<_ ]) → [ isTight'' _<_ ⇔ isTight''' (λ x y → [ <-asym x y ] (x < y) ⊎ᵖ (y < x)) ]
  isTight⇔isAntisym    :                              [ isTight   _<_ ⇔ isAntisym  (λ x y →                   ¬ (y < x))       ]

  irrefl+trans⇒asym isIrrefl isTrans a b a<b b<a = isIrrefl _ (isTrans _ _ _ a<b b<a)

  irrefl+trans⇒asym' isIrrefl isTrans a b (a<b , b<a) = isIrrefl _ (isTrans _ _ _ a<b b<a)

  isAsym⇔isAsym' .fst <-asym a b (a<b , b<a) = <-asym a b a<b b<a
  isAsym⇔isAsym' .snd <-asym a b = fst (¬-⊓-distrib (a < b) (b < a) (<-asym a b))

  isTight⇔isTight' .fst <-tightᵖ  a b ¬ᵗ[a<b⊔b<a]     = let (¬ᵗ[a<b] , ¬ᵗ[b<a]) = deMorgan₂ (a < b) (b < a) ¬ᵗ[a<b⊔b<a] in <-tightᵖ a b ¬ᵗ[a<b] ¬ᵗ[b<a]
  isTight⇔isTight' .snd <-tightᵖ' a b ¬ᵗ[a<b] ¬ᵗ[b<a] = <-tightᵖ' a b (deMorgan₂-back (a < b) (b < a) (¬ᵗ[a<b] , ¬ᵗ[b<a]))

  isTight'⇔isTight'' .fst <-tightᵖ'  a b ¬ᵗ[a<b⊎b<a] = <-tightᵖ'  a b (pathTo⇒ (∥¬A∥≡¬∥A∥ _) ∣ ¬ᵗ[a<b⊎b<a] ∣)
  isTight'⇔isTight'' .snd <-tightᵖ'' a b ¬ᵗ[a<b⊔b<a] = <-tightᵖ'' a b (λ [a<b⊎b<a] → ¬ᵗ[a<b⊔b<a] (⊎⇒⊔ (a < b) (b < a) [a<b⊎b<a]))

  isTight'⇔isTight''' .fst x = x
  isTight'⇔isTight''' .snd x = x

  isTight''⇔isTight''' <-asym .fst x = x
  isTight''⇔isTight''' <-asym .snd x = x

  isTight⇔isAntisym .fst <-tight   a b a≤b b≤a = <-tight   a b b≤a a≤b
  isTight⇔isAntisym .snd ≤-antisym a b b≤a a≤b = ≤-antisym a b a≤b b≤a

  -- consequences on sets
  module _ (is-set : isSet A) where
    -- abstract
    isAntisymˢ⇔isAntisym    :                               [ isAntisymˢ  R is-set ⇔ isAntisym  R ]
    isAntisymˢ'⇔isAntisym'  :                               [ isAntisymˢ' R is-set ⇔ isAntisym' R ]
    isTightˢ⇔isTight        :                               [ isTightˢ    R is-set ⇔ isTight    R ]
    isTightˢ'⇔isTight'      :                               [ isTightˢ'   R is-set ⇔ isTight'   R ]
    isTightˢ''⇔isTight''    :                               [ isTightˢ''  R is-set ⇔ isTight''  R ]
    isTightˢ'''⇔isTight'''  :                               [ isTightˢ''' R is-set ⇔ isTight''' R ]
    isTightˢ'''⇔isAntisymˢ  : (<-asym : [ isAsym  _<_ ])  → [ isTightˢ''' (λ x y → [ <-asym x y ] (x < y) ⊎ᵖ (y < x)) is-set
                                                            ⇔ isAntisymˢ  (λ x y →                   ¬ (y < x)      ) is-set ]

    isAntisymˢ⇔isAntisym .fst ≤-antisymˢ a b a≤b b≤a = ∣ ≤-antisymˢ a b a≤b b≤a ∣
    isAntisymˢ⇔isAntisym .snd ≤-antisym  a b a≤b b≤a = ∣∣-elim (λ c → is-set a b) (λ x → x) (≤-antisym  a b a≤b b≤a)

    isAntisymˢ'⇔isAntisym' .fst ≤-antisymˢ' a b a≤b ¬ᵗa≡b = ≤-antisymˢ' a b a≤b (λ  z  → ¬ᵗa≡b ∣ z ∣)
    isAntisymˢ'⇔isAntisym' .snd ≤-antisym'  a b a≤b ¬ᵗa≡b = ≤-antisym'  a b a≤b (λ ∣z∣ → ∣∣-elim {P = λ _ → ⊥⊥} (λ _ → isProp⊥) ¬ᵗa≡b ∣z∣)

    isTightˢ⇔isTight .fst <-tightˢ a b a<b b<a = ∣ <-tightˢ a b a<b b<a ∣
    isTightˢ⇔isTight .snd <-tightᵖ a b a<b b<a = ∣∣-elim (λ c → is-set a b) (λ x → x) (<-tightᵖ a b a<b b<a)

    isTightˢ'⇔isTight' .fst <-tightˢ' a b ¬ᵗ[a<b⊔b<a] = ∣ <-tightˢ' a b ¬ᵗ[a<b⊔b<a] ∣
    isTightˢ'⇔isTight' .snd <-tightᵖ' a b ¬ᵗ[a<b⊔b<a] = ∣∣-elim (λ c → is-set a b) (λ x → x) (<-tightᵖ' a b ¬ᵗ[a<b⊔b<a])

    isTightˢ''⇔isTight'' .fst <-tightˢ'' a b ¬ᵗ[a<b⊎b<a] = ∣ <-tightˢ'' a b ¬ᵗ[a<b⊎b<a] ∣
    isTightˢ''⇔isTight'' .snd <-tightᵖ'' a b ¬ᵗ[a<b⊎b<a] = ∣∣-elim (λ c → is-set a b) (λ x → x) (<-tightᵖ'' a b ¬ᵗ[a<b⊎b<a])

    isTightˢ'''⇔isTight''' .fst #-tightˢ''' a b ¬ᵗ[a#b] = ∣ #-tightˢ''' a b ¬ᵗ[a#b] ∣
    isTightˢ'''⇔isTight''' .snd #-tightᵖ''' a b ¬ᵗ[a#b] = ∣∣-elim (λ c → is-set a b) (λ x → x) (#-tightᵖ''' a b ¬ᵗ[a#b])

    isTightˢ'''⇔isAntisymˢ <-asym .fst #-tight a b a≤b b≤a = #-tight a b (deMorgan₂-back' (b≤a , a≤b))
    isTightˢ'''⇔isAntisymˢ <-asym .snd ≤-antisym a b ¬ᵗa#b = let (b≤a , a≤b) = deMorgan₂' ¬ᵗa#b in ≤-antisym a b a≤b b≤a

-- for these pathes, `A` and `hProp.fst` need to be in the same universe to omit ugly lifting into `ℓ-max ℓ ℓ'`
--   although this would be possible to have (with lifting)
module _ {ℓ : Level} {A : Type ℓ} (R : hPropRel A A ℓ)
  (let _<_ = R)
  (let _≤_ = R)
  (let _#_ = R)
  where
  -- equivalence of "not apart" and "equal"
  [¬ᵗ#]⇔[≡]  : hProp ℓ
  [¬ᵗ#]⇔[≡]  = ∀[ a ] ∀[ b ] ¬ (a # b) ⇔ a ≡ₚ b
  [¬ᵗ#]⇔[≡]ᵗ : Type (ℓ-suc ℓ)
  [¬ᵗ#]⇔[≡]ᵗ = ∀ a b → (¬ᵗ [ a # b ]) ≡ (a ≡ b)

  -- double negation elimination over _≡_
  dne-over-≡ᵗ : Type (ℓ-suc ℓ)
  dne-over-≡ᵗ = ∀(a b : A) → (¬ᵗ ¬ᵗ (a ≡ b)) ≡ (a ≡ b)

  abstract
    irrefl+tight⇒[¬ᵗ#]⇔[≡] : [ isIrrefl  _#_ ] → [ isTight''' _#_ ] → [ [¬ᵗ#]⇔[≡] ]
    irrefl+tight⇒[¬ᵗ#]⇔[≡] #-irrefl #-tight a b .fst ¬ᵗ[a#b] = #-tight a b ¬ᵗ[a#b]
    irrefl+tight⇒[¬ᵗ#]⇔[≡] #-irrefl #-tight a b .snd a≡b a#b = #-irrefl b (substₚ (λ x → x # b) a≡b a#b)

    [¬ᵗ#]≡[≡]⇒dne-over-≡ : [¬ᵗ#]⇔[≡]ᵗ → dne-over-≡ᵗ
    [¬ᵗ#]≡[≡]⇒dne-over-≡ [¬ᵗ#]≡[≡] a b =
      (    ¬ᵗ ¬ᵗ ( a ≡ b ) ≡⟨ (λ i → ¬ᵗ ¬ᵗ [¬ᵗ#]≡[≡] a b (~ i)) ⟩
        ¬ᵗ ¬ᵗ ¬ᵗ [ a # b ] ≡⟨ ¬¬-involutiveᵗ [ a # b ] ⟩
              ¬ᵗ [ a # b ] ≡⟨ [¬ᵗ#]≡[≡] a b ⟩
                   a ≡ b   ∎)

  -- consequences on sets
  module _ (is-set : isSet A) where
    -- equivalence of "not apart" and "equal" on sets
    [¬ᵗ#]⇔[≡ˢ] = ∀[ a ] ∀[ b ]             ¬ (a # b) ⇔ [ is-set ] a ≡ˢ b

    -- double negation elimination over _≡_ on sets
    dne-over-≡ˢ  = ∀[ a ] ∀[ b ] ¬ ¬ [ is-set ] a ≡ˢ b ⇔ [ is-set ] a ≡ˢ b

    irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ]   : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → [ [¬ᵗ#]⇔[≡ˢ] ]
    [¬ᵗ#]⇔[≡ˢ]⇒dne-over-≡ˢ    : [ [¬ᵗ#]⇔[≡ˢ] ]                                 → [ dne-over-≡ˢ ]
    irrefl+tight⇒dne-over-≡ˢ  : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → [ dne-over-≡ˢ ]
    irrefl+tight⇒[¬ᵗ#]≡[≡ˢ]   : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → ∀ a b → (¬ᵗ [ a # b ]) ≡ (a ≡ b)
    irrefl+tight⇒dne-over-≡ˢᵗ : [ isIrrefl  _#_ ] → [ isTightˢ''' _#_ is-set ] → ∀(a b : A) → (¬ᵗ ¬ᵗ (a ≡ b)) ≡ (a ≡ b)

    irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ] #-irrefl #-tight a b .fst ¬ᵗ[a#b] = #-tight a b ¬ᵗ[a#b]
    irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ] #-irrefl #-tight a b .snd a≡b a#b = #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)

    irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] #-irrefl #-tight a b = isoToPath γ where
      γ : Iso _ _
      γ .Iso.fun      ¬ᵗ[a#b] = #-tight a b ¬ᵗ[a#b]
      γ .Iso.inv      a≡b a#b = #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)
      γ .Iso.rightInv f       = is-set a b _ f
      γ .Iso.leftInv  g       = isProp[] (¬ (a #  b)) _ g

    [¬ᵗ#]⇔[≡ˢ]⇒dne-over-≡ˢ [¬ᵗ#]⇔[≡ˢ] a b = snd ( -- this first proof works better with `_≡⟨_⟩_`
       ¬ ¬ [ is-set ]      a ≡ˢ b  ⇔⟨ (map-× (λ z z₁ z₂ → z₂ (λ z₃ → z₁ (λ z₄ → z z₄ z₃))) (λ z z₁ z₂ → z₂ (z (λ z₃ → z₁ (λ z₄ → z₄ z₃)))) $ swap $ [¬ᵗ#]⇔[≡ˢ] a b) ⟩
       ¬              ¬ ¬ (a #  b) ⇔⟨ ¬¬-involutive (a # b) ⟩
       ¬                  (a #  b) ⇔⟨ [¬ᵗ#]⇔[≡ˢ] a b ⟩
           [ is-set ]      a ≡ˢ b  ∎ᵖ)

    irrefl+tight⇒dne-over-≡ˢ  #-irrefl #-tight = [¬ᵗ#]⇔[≡ˢ]⇒dne-over-≡ˢ (irrefl+tight⇒[¬ᵗ#]⇔[≡ˢ] #-irrefl #-tight)

    irrefl+tight⇒dne-over-≡ˢᵗ #-irrefl #-tight = [¬ᵗ#]≡[≡]⇒dne-over-≡   (irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] #-irrefl #-tight)

abstract
  -- Lemma 4.1.7.
  -- Given a strict partial order < on a set X:
  -- 1. we have an apartness relation defined by
  --    x # y := (x < y) ∨ (y < x), and

  #'-isApartnessRel : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → (isSPO : [ isStrictPartialOrder  _<_ ]) → [ isApartnessRel  (_#'_ {_<_ = _<_}) ]
  #'-isApartnessRel {ℓ} {ℓ'} {X = X} {_<_ = _<_} <-SPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
    in λ where
      .IsApartnessRel.is-irrefl  a   p   → ⊔-elim (a < a) (a < a) (λ p → ⊥)
                                          (λ a<a → <-irrefl _ a<a)
                                          (λ a<a → <-irrefl _ a<a)
                                          p
      .IsApartnessRel.is-sym     a b p   → pathTo⇒ (⊔-comm (a < b) (b < a)) p
      -- NOTE: it would be much nicer to have case splitting on _⊔_
      .IsApartnessRel.is-cotrans a b p x → let _#''_ = _#'_ {_<_ = _<_} in
                                          ⊔-elim (a < b) (b < a) (λ p → (a #'' x) ⊔ (x #'' b))
                                          ( λ a<b → ⊔-elim (a < x) (x < b) (λ q → (a #'' x) ⊔ (x #'' b))
                                                    (λ a<x → inlᵖ (inlᵖ a<x))
                                                    (λ x<b → inrᵖ (inlᵖ x<b))
                                                    (<-cotrans _ _ a<b x)
                                          )
                                          ( λ b<a → ⊔-elim (b < x) (x < a) (λ q → (a #'' x) ⊔ (x #'' b))
                                                    (λ b<x → inrᵖ (inrᵖ b<x))
                                                    (λ x<a → inlᵖ (inrᵖ x<a))
                                                    (<-cotrans _ _ b<a x)
                                          )
                                          p
    -- .IsApartnessRel.isCotrans a b (inl a<b) x → case (<-cotrans _ _ a<b x) of λ where -- case x of f = f x
    --   (inl a<x) → inl (inl a<x)
    --   (inr x<b) → inr (inl x<b)
    -- .IsApartnessRel.isCotrans a b (inr b<a) x → case (<-cotrans _ _ b<a x) of λ where
    --   (inl b<x) → inr (inr b<x)
    --   (inr x<a) → inl (inr x<a)


  -- variant without copatterns: "just" move the `λ where` "into" the record
  #'-isApartnessRel' : ∀{X : Type ℓ} (_<_ : hPropRel X X ℓ') → [ isStrictPartialOrder  _<_ ] → [ isApartnessRel  (_#'_ {_<_ = _<_}) ]
  #'-isApartnessRel' {X = X} _<_ <-SPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
        _#''_ = _#'_ {_<_ = _<_}
    in record
      { is-irrefl  = λ a a#a → case[ a < a ⊔ a < a ] a#a return (λ _ → ⊥) of λ where
                            (inl a<a) → <-irrefl _ a<a
                            (inr a<a) → <-irrefl _ a<a
      ; is-sym     = λ a b p → pathTo⇒ (⊔-comm (a < b) (b < a)) p
      ; is-cotrans = λ a b p → case[ a < b ⊔ b < a ] p return (λ _ → ∀[ x ] (a #'' x) ⊔ (x #'' b)) of λ where
          (inl a<b) x → case[ a < x ⊔ x < b ] (<-cotrans _ _ a<b x) return (λ _ → (a #'' x) ⊔ (x #'' b)) of λ where
            (inl a<x) → inlᵖ (inlᵖ a<x)
            (inr x<b) → inrᵖ (inlᵖ x<b)
          (inr b<a) x → case[ b < x ⊔ x < a ] (<-cotrans _ _ b<a x) return (λ _ → (a #'' x) ⊔ (x #'' b)) of λ where
            (inl b<x) → inrᵖ (inrᵖ b<x)
            (inr x<a) → inlᵖ (inrᵖ x<a)
       -- NOTE: this makes a disjointness-proof necessary, so using _⊎_ in the first place would be better
       --       or would it be better to use _⊔_ and provide a disjointness proof?
       --       well, cotransitivity does not care about the disjointness of cases
       --         it only arises from our specific properties of _<_ in a context of b < a that b < x is disjoint with x < b
       --         so, the ⊔-elim is still preferred here
       -- (inr b<a) x → case ⊔⇒⊎ (b < x) (x < a) {! <-trans b x a!} (<-cotrans _ _ b<a x) of λ where
       --   (inl b<x) → inrᵖ (inrᵖ b<x)
       --   (inr x<a) → inlᵖ (inrᵖ x<a)
      }

  -- 2. we have a preorder defined by
  --    x ≤ y := ¬ᵗ(y < x).

  ≤-isPreorder' : ∀{X : Type ℓ} (_<_ : hPropRel X X ℓ') → [ isStrictPartialOrder  _<_ ] → [ isPreorder  (_≤'_ {_<_ = _<_}) ]
  ≤-isPreorder' {X = X} _<_ <-SPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
    in λ where
     .IsPreorder.is-refl → <-irrefl
     .IsPreorder.is-trans a b c ¬ᵗb<a ¬ᵗc<b c<a →
       ⊔-elim (c < b) (b < a) (λ _ → ⊥)
       (λ c<b → ¬ᵗc<b c<b)
       (λ b<a → ¬ᵗb<a b<a)
       (<-cotrans _ _ c<a b)
