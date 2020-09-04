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
open import Function.Base using (_∋_)

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
  abstract
    irrefl+trans⇒asym : [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ R ]
    irrefl+trans⇒asym isIrrefl isTrans a b a<b b<a = isIrrefl _ (isTrans _ _ _ a<b b<a)

    irrefl+trans⇒asym' : [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ' R ]
    irrefl+trans⇒asym' isIrrefl isTrans a b (a<b , b<a) = isIrrefl _ (isTrans _ _ _ a<b b<a)

    isAsymᵖ≡ᵖ' : isAsymᵖ R ≡ isAsymᵖ' R
    isAsymᵖ≡ᵖ' =
      ⇒∶ (λ{ <-asym a b (a<b , b<a) → <-asym a b a<b b<a })
      ⇐∶ (λ  <-asym a b → fst (¬-⊓-distrib (a < b) (b < a) (<-asym a b)) )

    isAntisym-ˢ≡ᵖ : (isset : isSet A) → isAntisymˢ R isset ≡ isAntisymᵖ R
    isAntisym-ˢ≡ᵖ isset = hProp≡ (isoToPath (record
      { fun      = λ ≤-antisymˢ a b a≤b b≤a → ∣ ≤-antisymˢ a b a≤b b≤a ∣
      ; inv      = λ ≤-antisymᵖ a b a≤b b≤a → ∣∣-elim (λ c → isset a b) (λ x → x) (≤-antisymᵖ a b a≤b b≤a)
      ; rightInv = λ f → isProp[] (isAntisymᵖ R      ) _ f
      ; leftInv  = λ g → isProp[] (isAntisymˢ R isset) _ g
      }))

    isAntisym-ˢ'≡ᵖ' : (isset : isSet A) → isAntisymˢ' R isset ≡ isAntisymᵖ' R
    isAntisym-ˢ'≡ᵖ' isset =
      ⇒∶ (λ ≤-antisymˢ' a b a≤b ¬ᵗa≡b → ≤-antisymˢ' a b a≤b (λ  z  → ¬ᵗa≡b ∣ z ∣))
      ⇐∶ (λ ≤-antisymᵖ' a b a≤b ¬ᵗa≡b → ≤-antisymᵖ' a b a≤b (λ ∣z∣ → ∣∣-elim {P = λ _ → ⊥⊥} (λ _ → isProp⊥) ¬ᵗa≡b ∣z∣))

    isTight-ˢ≡ᵖ : (isset : isSet A) → isTightˢ R isset ≡ isTightᵖ R
    isTight-ˢ≡ᵖ isset = hProp≡ (isoToPath (record
      { fun      = λ <-tightˢ a b a<b b<a → ∣ <-tightˢ a b a<b b<a ∣
      ; inv      = λ <-tightᵖ a b a<b b<a → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ a b a<b b<a)
      ; rightInv = λ f → isProp[] (isTightᵖ _<_      ) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ _<_ isset) _ g
      }))

    isTight-ˢ'≡ᵖ' : (isset : isSet A) → isTightˢ' R isset ≡ isTightᵖ' R
    isTight-ˢ'≡ᵖ' isset = hProp≡ (isoToPath (record
      { fun      = λ <-tightˢ' a b ¬ᵗ[a<b⊔b<a] → ∣ <-tightˢ' a b ¬ᵗ[a<b⊔b<a] ∣
      ; inv      = λ <-tightᵖ' a b ¬ᵗ[a<b⊔b<a] → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ' a b ¬ᵗ[a<b⊔b<a])
      ; rightInv = λ f → isProp[] (isTightᵖ' _<_      ) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ' _<_ isset) _ g
      }))

    isTight-ˢ''≡ᵖ'' : (isset : isSet A) → isTightˢ'' R isset ≡ isTightᵖ'' R
    isTight-ˢ''≡ᵖ'' isset = hProp≡ (isoToPath (record
      { fun      = λ <-tightˢ'' a b ¬ᵗ[a<b⊎b<a] → ∣ <-tightˢ'' a b ¬ᵗ[a<b⊎b<a] ∣
      ; inv      = λ <-tightᵖ'' a b ¬ᵗ[a<b⊎b<a] → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ'' a b ¬ᵗ[a<b⊎b<a])
      ; rightInv = λ f → isProp[] (isTightᵖ'' _<_      ) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ'' _<_ isset) _ g
      }))

    isTight-ˢ'''≡ᵖ''' : (isset : isSet A) → isTightˢ''' R isset ≡ isTightᵖ''' R
    isTight-ˢ'''≡ᵖ''' isset = hProp≡ (isoToPath (record
      { fun      = λ #-tightˢ''' a b ¬ᵗ[a#b] → ∣ #-tightˢ''' a b ¬ᵗ[a#b] ∣
      ; inv      = λ #-tightᵖ''' a b ¬ᵗ[a#b] → ∣∣-elim (λ c → isset a b) (λ x → x) (#-tightᵖ''' a b ¬ᵗ[a#b])
      ; rightInv = λ f → isProp[] (isTightᵖ''' _#_      ) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ''' _#_ isset) _ g
      }))

    isTight-ᵖ≡ᵖ' : isTightᵖ R ≡ isTightᵖ' R
    isTight-ᵖ≡ᵖ' = hProp≡ (isoToPath (record
      { fun      = λ <-tightᵖ  a b ¬ᵗ[a<b⊔b<a]    → let (¬ᵗ[a<b] , ¬ᵗ[b<a]) = deMorgan₂ (a < b) (b < a) ¬ᵗ[a<b⊔b<a] in <-tightᵖ a b ¬ᵗ[a<b] ¬ᵗ[b<a]
      ; inv      = λ <-tightᵖ' a b ¬ᵗ[a<b] ¬ᵗ[b<a] → <-tightᵖ' a b (deMorgan₂-back (a < b) (b < a) (¬ᵗ[a<b] , ¬ᵗ[b<a]))
      ; rightInv = λ f → isProp[] (isTightᵖ' _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightᵖ  _<_) _ g
      }))

    isTight-ᵖ'≡ᵖ'' : isTightᵖ' R ≡ isTightᵖ'' R
    isTight-ᵖ'≡ᵖ'' = hProp≡ (isoToPath (record
      { fun      = λ <-tightᵖ'  a b ¬ᵗ[a<b⊎b<a] → <-tightᵖ'  a b (pathTo⇒ (∥¬A∥≡¬∥A∥ _) ∣ ¬ᵗ[a<b⊎b<a] ∣)
      ; inv      = λ <-tightᵖ'' a b ¬ᵗ[a<b⊔b<a] → <-tightᵖ'' a b (λ [a<b⊎b<a] → ¬ᵗ[a<b⊔b<a] (⊎⇒⊔ (a < b) (b < a) [a<b⊎b<a]))
      ; rightInv = λ f → isProp[] (isTightᵖ'' _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightᵖ'  _<_) _ g
      }))

    module _ (let _#_ = λ x y → (x < y) ⊔ (y < x) ) where
      abstract -- this actually holds definitionally with `refl`, but due to our frequent use of `abstract` for the prop, we need `isPropIsProp`
        isTight-ᵖ'≡ᵖ''' : isTightᵖ' _<_ ≡ isTightᵖ''' _#_
        isTight-ᵖ'≡ᵖ''' = ΣPathP (refl , isPropIsProp _ _)

    module _ (<-asym : [ isAsymᵖ _<_ ]) (let _#_ = _#''_ {_<_ = _<_} {<-asym = <-asym}) where
      abstract -- this actually holds definitionally with `refl`, but due to our frequent use of `abstract` for the prop, we need `isPropIsProp`
        isTight-ᵖ''≡ᵖ''' : isTightᵖ'' _<_ ≡ isTightᵖ''' _#_
        isTight-ᵖ''≡ᵖ''' = ΣPathP (refl , isPropIsProp _ _)

    module _ (let _≤_ = λ x y → ¬ (y < x))  where
      abstract
        isTightᵖ≡isAntisymᵖ : isTightᵖ _<_ ≡ isAntisymᵖ _≤_
        isTightᵖ≡isAntisymᵖ = hProp≡ (isoToPath (record
          { fun      = λ <-tight   a b a≤b b≤a → <-tight   a b b≤a a≤b
          ; inv      = λ ≤-antisym a b b≤a a≤b → ≤-antisym a b a≤b b≤a
          ; rightInv = λ f → isProp[] (isAntisymᵖ _≤_) _ f
          ; leftInv  = λ g → isProp[] (isTightᵖ   _<_) _ g
          }))

    module _ (isset : isSet A) (<-asym : [ isAsymᵖ _<_ ])
             (let _≤_ = λ x y → ¬ (y < x))
             (let _#_ = _#''_ {_<_ = _<_} {<-asym = <-asym}) where
      abstract
        isTightˢ'''≡isAntisymˢ : (isTightˢ''' _#_ isset) ≡ (isAntisymˢ _≤_ isset)
        isTightˢ'''≡isAntisymˢ = hProp≡ (isoToPath (record
          { fun      = λ #-tight a b a≤b b≤a → #-tight a b (deMorgan₂-back' (b≤a , a≤b))
          ; inv      = λ ≤-antisym a b ¬ᵗa#b → let (b≤a , a≤b) = deMorgan₂' ¬ᵗa#b in ≤-antisym a b a≤b b≤a
          ; rightInv = λ f → isProp[] (isAntisymˢ  _≤_ isset) _ f
          ; leftInv  = λ g → isProp[] (isTightˢ''' _#_ isset) _ g
          }))

-- for these pathes, `A` and `hProp.fst` need to be in the same universe to omit ugly lifting into `ℓ-max ℓ ℓ'`
--   although this would be possible to have (with lifting)
module _ {ℓ : Level} {A : Type ℓ} (R : hPropRel A A ℓ)
  (let _<_ = R)
  (let _≤_ = R)
  (let _#_ = R)
  where
  abstract
    irrefl+tight⇒[¬ᵗ#]≡[≡ᵖ] : [ isIrreflᵖ _#_ ] → [ isTightᵖ''' _#_ ] → ∀ a b → ¬ (a # b) ≡ (a ≡ₚ b)
    irrefl+tight⇒[¬ᵗ#]≡[≡ᵖ] #-irrefl #-tight a b = hProp≡ (isoToPath (record
      { fun      = λ ¬ᵗ[a#b] → #-tight a b ¬ᵗ[a#b]
      ; inv      = λ a≡b a#b → #-irrefl b (substₚ (λ x → x # b) a≡b a#b)
      ; rightInv = λ f → isProp[] (    a ≡ₚ b) _ f
      ; leftInv  = λ g → isProp[] (¬ (a #  b)) _ g
      }))

    irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] : (isset : isSet A) → [ isIrreflᵖ _#_ ] → [ isTightˢ''' _#_ isset ]
                                 → ∀ a b → (¬ᵗ [ a # b ]) ≡ (a ≡ b)
    irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] isset #-irrefl #-tight a b = (isoToPath (record
      { fun      = λ ¬ᵗ[a#b] → #-tight a b ¬ᵗ[a#b]
      ; inv      = λ a≡b a#b → #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)
      ; rightInv = λ f → isset a b _ f
      ; leftInv  = λ g → isProp[] (¬ (a #  b)) _ g
      }))

    [¬ᵗ#]≡[≡]⇒dne-on-≡ : (∀ a b → (¬ᵗ [ a # b ]) ≡ (a ≡ b))
                             → ∀(a b : A) → (¬ᵗ ¬ᵗ (a ≡ b)) ≡ (a ≡ b)
    [¬ᵗ#]≡[≡]⇒dne-on-≡ [¬ᵗ#]≡[≡] a b =
      (    ¬ᵗ ¬ᵗ ( a ≡ b ) ≡⟨ (λ i → ¬ᵗ ¬ᵗ [¬ᵗ#]≡[≡] a b (~ i)) ⟩
        ¬ᵗ ¬ᵗ ¬ᵗ [ a # b ] ≡⟨ ¬¬-involutive [ a # b ] ⟩
              ¬ᵗ [ a # b ] ≡⟨ [¬ᵗ#]≡[≡] a b ⟩
                   a ≡ b   ∎)

    irrefl+tight⇒dne-on-≡ˢ : (isset : isSet A) → [ isIrreflᵖ _#_ ] → [ isTightˢ''' _#_ isset ]
                                   → ∀(a b : A) → (¬ᵗ ¬ᵗ (a ≡ b)) ≡ (a ≡ b)
    irrefl+tight⇒dne-on-≡ˢ isset #-irrefl #-tight = [¬ᵗ#]≡[≡]⇒dne-on-≡ (irrefl+tight⇒[¬ᵗ#]≡[≡ˢ] isset #-irrefl #-tight)

abstract
  -- Lemma 4.1.7.
  -- Given a strict partial order < on a set X:
  -- 1. we have an apartness relation defined by
  --    x # y := (x < y) ∨ (y < x), and

  #'-isApartnessRel : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → (isSPO : [ isStrictPartialOrderᵖ _<_ ]) → [ isApartnessRelᵖ (_#'_ {_<_ = _<_}) ]
  #'-isApartnessRel {ℓ} {ℓ'} {X = X} {_<_ = _<_} <-SPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
    in λ where
      .IsApartnessRel.isIrrefl  a   p   → ⊔-elim (a < a) (a < a) (λ p → ⊥)
                                          (λ a<a → <-irrefl _ a<a)
                                          (λ a<a → <-irrefl _ a<a)
                                          p
      .IsApartnessRel.isSym     a b p   → pathTo⇒ (⊔-comm (a < b) (b < a)) p
      -- NOTE: it would be much nicer to have case splitting on _⊔_
      .IsApartnessRel.isCotrans a b p x → let _#''_ = _#'_ {_<_ = _<_} in
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
  #'-isApartnessRel' : ∀{X : Type ℓ} (_<_ : hPropRel X X ℓ') → [ isStrictPartialOrderᵖ _<_ ] → [ isApartnessRelᵖ (_#'_ {_<_ = _<_}) ]
  #'-isApartnessRel' {X = X} _<_ <-SPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
        _#''_ = _#'_ {_<_ = _<_}
    in record
      { isIrrefl  = λ a a#a → case[ a < a ⊔ a < a ] a#a return (λ _ → ⊥) of λ where
                            (inl a<a) → <-irrefl _ a<a
                            (inr a<a) → <-irrefl _ a<a
      ; isSym     = λ a b p → pathTo⇒ (⊔-comm (a < b) (b < a)) p
      ; isCotrans = λ a b p → case[ a < b ⊔ b < a ] p return (λ _ → ∀[ x ] (a #'' x) ⊔ (x #'' b)) of λ where
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

  ≤-isPreorder' : ∀{X : Type ℓ} (_<_ : hPropRel X X ℓ') → [ isStrictPartialOrderᵖ _<_ ] → [ isPreorderᵖ (_≤'_ {_<_ = _<_}) ]
  ≤-isPreorder' {X = X} _<_ <-SPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
    in λ where
     .IsPreorder.isRefl → <-irrefl
     .IsPreorder.isTrans a b c ¬ᵗb<a ¬ᵗc<b c<a →
       ⊔-elim (c < b) (b < a) (λ _ → ⊥)
       (λ c<b → ¬ᵗc<b c<b)
       (λ b<a → ¬ᵗb<a b<a)
       (<-cotrans _ _ c<a b)
