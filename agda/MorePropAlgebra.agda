{-# OPTIONS --cubical --no-import-sorts  #-}

module MorePropAlgebra where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (_∋_)

import Data.Sum
import Cubical.Data.Sigma

import Cubical.Structures.CommRing

import Cubical.Core.Primitives
import Agda.Builtin.Cubical.Glue
import Cubical.Foundations.Id

import MoreLogic
open MoreLogic.Definitions
open MoreLogic.Properties
open MoreLogic.Reasoning

open import Utils -- deMorgan₂'

-- open import Cubical.Foundations.Id using (Id)
-- test20 : {A : Type ℓ} → (a b : A) (p : Id a b) → A
-- test20 a b p = {!!}

open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
open import Cubical.HITs.PropositionalTruncation.Properties using (propTruncIsProp) renaming (elim to ∣∣-elim)

-- NOTE: hProps need to be explicit arguments (that is not a necessity, but we need to give them completely and not just their witnesses)
-- NOTE: I think one can make all `isProp` implementations `abstract` to save some compilation time
--         because we have `isPropIsProp` anyways
--       but for the logic part, it depends on how coslty
--         ⊔-elim, ⊥-elim, ⇒∶_⇐∶_, isoToPath, hProp≡, etc.
--       are and whether they could actually reduce some terms

module Definitions where

  -- hProps of relations
  module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where

    isReflᵖ     =                      ∀[ a ]     R a a
    isIrreflᵖ   =                      ∀[ a ] ¬ᵖ (R a a)

    isTransᵖ    =                      ∀[ a ] ∀[ b ] ∀[ x ] R a b ⇒         R b x ⇒ R a x
    isCotransᵖ  =                      ∀[ a ] ∀[ b ]        R a b ⇒ (∀[ x ] R a x ⊔ R x b)

    -- two variants of asymmetry
    --
    --   IsAsym  R = ∀ a b → [     R a b   ⇒ ¬ᵖ R b a ]
    --   IsAsym' R = ∀ a b → [ ¬ᵖ (R a b   ⊓    R b a) ]
    --
    -- which are equivalent
    --
    --   isAsymᵖ≡ᵖ' :  isAsymᵖ R ≡ isAsymᵖ' R
    --
    -- but it seems that this one is not equivalent:
    --
    --   ∀ a b → [ (¬ᵖ R b a) ⇒ R a b ]

    isSymᵖ      =                      ∀[ a ] ∀[ b ]     R a b ⇒    R b a
    isAsymᵖ     =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬ᵖ R b a
    isAsymᵖ'    =                      ∀[ a ] ∀[ b ] ¬ᵖ (R a b ⊓    R b a)
    isAsymᵖ''   =                      ∀[ a ] ∀[ b ] ¬ᵖ  R a b ⇒    R b a  -- not equivalent! (weaker)

    isAntisymᵖ  =                      ∀[ a ] ∀[ b ]     R a b ⇒              R b a   ⇒            a ≡ₚ b
    isAntisymˢ  = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒              R b a   ⇒ ([ isset ] a ≡ˢ b)
    isAntisymᵖ' =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬ᵖ(          a ≡ₚ b) ⇒            R b a
    isAntisymˢ' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒ ¬ᵖ([ isset ] a ≡ˢ b) ⇒            R b a

    -- tightness is closely related to antisymmetry:
    --
    --   R-antisym : [    R a b ] → [    R b a ] → a ≡ b
    --   R-tight   : [ ¬ᵖ R a b ] → [ ¬ᵖ R b a ] → a ≡ b
    --
    -- this becomes even more obvious if we regard the intended use: when _≤_ and _#_ are derived from _<_
    --
    --    a ≤ b = ¬ᵖ (b < a)
    --    a # b = ¬ᵖ ([ a < b ] ⊎ [ b < a ])
    --
    -- and indeed, we get
    --
    --   isTightᵖ  _<_ ≡ isAntisymᵖ  (λ a b → ¬ᵖ (b < a))
    --   isTightᵖ' _<_ ≡ isTightᵖ''' (λ a b → (a < b) ⊔ (b < a))
    --
    -- In that case, `≤-antisym` and `#-tight` are almost the same, definitionally:
    --
    --   ≤-antisym : [ ¬ᵖ (b < a) ] → [ ¬ᵖ (a < b) ] → a ≡ b
    --   ≤-antisym : [ ¬ᵖ (b < a) ] × [ ¬ᵖ (a < b) ] → a ≡ b -- by curry/uncurry
    --   ≤-antisym : ¬ ( [ b < a ]  ⊎     [ a < b ]) → a ≡ b -- by deMorgan
    --   #-tight   : [ ¬ᵖ (a < b) ] → [ ¬ᵖ (b < a) ] → a ≡ b
    --   #-tight   : [ ¬ᵖ (a < b) ] × [ ¬ᵖ (b < a) ] → a ≡ b -- by curry/uncurry
    --   #-tight   : ¬ ( [ a < b ]  ⊎     [ b < a ]) → a ≡ b -- by deMorgan
    --
    -- We provide a few variants of tightness
    --
    --   IsTight           R = ∀ a b → [ ¬ᵖ    R a b   ⇒   ¬ᵖ R b a      ⇒   a ≡ₚ b ] -- on _<_, "canonical"
    --   IsTightˢ    isset R = ∀ a b → [ ¬ᵖ    R a b ] → [ ¬ᵖ R b a ]    →   a ≡  b   -- on _<_
    --   IsTight'          R = ∀ a b → [ ¬ᵖ (  R a b   ⊔      R b a  )   ⇒   a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ'≡ᵖ'''`
    --   IsTightˢ'   isset R = ∀ a b → [ ¬ᵖ (  R a b   ⊔      R b a  ) ] →   a ≡  b   -- on _<_
    --   IsTight''         R = ∀ a b →   ¬  ([ R a b ] ⊎ [    R b a ])   → [ a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ''≡ᵖ'''`
    --   IsTightˢ''  isset R = ∀ a b →   ¬  ([ R a b ] ⊎ [    R b a ])   →   a ≡  b   -- on _<_, "convenient"
    --   IsTight'''        R = ∀ a b → [ ¬ᵖ    R a b                     ⇒   a ≡ₚ b ] -- on _#_
    --   IsTightˢ''' isset R = ∀ a b →   ¬   [ R a b ]                   →   a ≡  b   -- on _#_, also "convenient"
    --
    -- where the very first one, `IsTight` corresponds to a "canonical" definition,
    -- the later one, `IsTightˢ''` is the "most convenient" one to use for `a # b = ¬ᵖ ([ a < b ] ⊎ [ b < a ])` on sets.
    -- and the last ones `IsTight'''` and `IsTightˢ'''` are for "_#_" instead of "_<_".
    --
    -- These tightness definitions are all equivalent in the following sense:
    --
    --   isTight-ˢ≡ᵖ       : (isset : isSet A)          → isTightˢ    isset _<_ ≡ isTightᵖ    _<_
    --   isTight-ˢ'≡ᵖ'     : (isset : isSet A)          → isTightˢ'   isset _<_ ≡ isTightᵖ'   _<_
    --   isTight-ˢ''≡ᵖ''   : (isset : isSet A)          → isTightˢ''  isset _<_ ≡ isTightᵖ''  _<_
    --   isTight-ˢ'''≡ᵖ''' : (isset : isSet A)          → isTightˢ''' isset _#_ ≡ isTightᵖ''' _#_
    --   isTight-ᵖ≡ᵖ'      :                              isTightᵖ          _<_ ≡ isTightᵖ'   _<_
    --   isTight-ᵖ'≡ᵖ''    :                              isTightᵖ'         _<_ ≡ isTightᵖ''  _<_
    --   isTight-ᵖ'≡ᵖ'''   :                              isTightᵖ'         _<_ ≡ isTightᵖ''' (λ a b →  ( a < b ) ⊔ ( b < a )   )
    --   isTight-ᵖ''≡ᵖ'''  : (<-asym : [ isAsymᵖ _<_ ]) → isTightᵖ''        _<_ ≡ isTightᵖ''' (λ a b → ([ a < b ] ⊎ [ b < a ]) , ⊎-isProp (a < b) (b < a) (inl (<-asym a b)))
    --
    -- where `isTight-ᵖ'≡ᵖ'''` and `isTight-ᵖ''≡ᵖ'''` hold definitionally.

    isTightᵖ    =                      ∀[ a ] ∀[ b ]     ¬ᵖ R a b   ⇒ ¬ᵖ R b a      ⇒           a ≡ₚ b
    isTightˢ    = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     ¬ᵖ R a b   ⇒ ¬ᵖ R b a      ⇒ [ isset ] a ≡ˢ b
    isTightᵖ'   =                      ∀[ a ] ∀[ b ]  ¬ᵖ (  R a b   ⊔    R b a   )  ⇒           a ≡ₚ b
    isTightˢ'   = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬ᵖ (  R a b   ⊔    R b a   )  ⇒ [ isset ] a ≡ˢ b
    isTightᵖ''  =                      ∀[ a ] ∀[ b ] (¬  ([ R a b ] ⊎  [ R b a ])) ᵗ⇒           a ≡ₚ b
    isTightˢ''  = λ(isset : isSet A) → ∀[ a ] ∀[ b ] (¬  ([ R a b ] ⊎  [ R b a ])) ᵗ⇒ [ isset ] a ≡ˢ b
    isTightᵖ''' =                      ∀[ a ] ∀[ b ]  ¬ᵖ    R a b                   ⇒           a ≡ₚ b
    isTightˢ''' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬ᵖ    R a b                   ⇒ [ isset ] a ≡ˢ b

  -- common definitions of less equal _≤_ and apartness _#_ with respect to _<_
  module _ {X : Type ℓ} {_<_ : hPropRel X X ℓ'} where

    _#'_ : hPropRel X X ℓ'
    _#'_ x y = (x < y) ⊔ (y < x)

    -- a variant that omits propositional truncation by using asymmetry of _<_
    _#''_ : {<-asym : [ isAsymᵖ _<_ ]} → hPropRel X X ℓ'
    _#''_ {<-asym = <-asym} x y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

    _≤'_ : hPropRel X X ℓ'
    _≤'_ x y = ¬ᵖ (y < x)

    -- this is how Bridges 1999 defines _≤_
    _≤''_ : hPropRel X X (ℓ-max ℓ ℓ')
    x ≤'' y = (∀ ε → [ y < ε ] → [ x < ε ]) , isPropΠ2 (λ ε y<ε → isProp[] (x < ε))

  -- combined hProps of relations
  module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where

    record IsApartnessRel : Type (ℓ-max ℓ ℓ') where
      constructor isapartnessrel
      field
        isIrrefl  : [ isIrreflᵖ  R ]
        isSym     : [ isSymᵖ     R ]
        isCotrans : [ isCotransᵖ R ]

    isApartnessRelᵖ : hProp (ℓ-max ℓ ℓ')
    isApartnessRelᵖ .fst = IsApartnessRel
    isApartnessRelᵖ .snd (isapartnessrel a₀ b₀ c₀) (isapartnessrel a₁ b₁ c₁) = φ where
      abstract φ = λ i → isapartnessrel (snd (isIrreflᵖ R) a₀ a₁ i) (snd (isSymᵖ R) b₀ b₁ i) (snd (isCotransᵖ R) c₀ c₁ i)

    record IsStrictPartialOrder : Type (ℓ-max ℓ ℓ') where
      constructor isstrictpartialorder
      field
        isIrrefl  : [ isIrreflᵖ  R ]
        isTrans   : [ isTransᵖ   R ]
        isCotrans : [ isCotransᵖ R ]

    isStrictPartialOrderᵖ : hProp (ℓ-max ℓ ℓ')
    isStrictPartialOrderᵖ .fst = IsStrictPartialOrder
    isStrictPartialOrderᵖ .snd (isstrictpartialorder a₀ b₀ c₀) (isstrictpartialorder a₁ b₁ c₁) = φ where
      abstract φ = λ i → isstrictpartialorder (snd (isIrreflᵖ R) a₀ a₁ i) (snd (isTransᵖ R) b₀ b₁ i) (snd (isCotransᵖ R) c₀ c₁ i)

    record IsPreorder : Type (ℓ-max ℓ ℓ') where
      constructor ispreorder
      field
        isRefl    : [ isReflᵖ  R ]
        isTrans   : [ isTransᵖ R ]

    isPreorderᵖ : hProp (ℓ-max ℓ ℓ')
    isPreorderᵖ .fst = IsPreorder
    isPreorderᵖ .snd (ispreorder a₀ b₀) (ispreorder a₁ b₁) = φ where
      abstract φ = λ i → ispreorder (snd (isReflᵖ R) a₀ a₁ i) (snd (isTransᵖ R) b₀ b₁ i)

    record IsPartialOrder : Type (ℓ-max ℓ ℓ') where
      constructor ispartialorder
      field
        isRefl    : [ isReflᵖ    R ]
        isAntisym : [ isAntisymᵖ R ]
        isTrans   : [ isTransᵖ   R ]

    isParialOrderᵖ : hProp (ℓ-max ℓ ℓ')
    isParialOrderᵖ .fst = IsPartialOrder
    isParialOrderᵖ .snd (ispartialorder a₀ b₀ c₀) (ispartialorder a₁ b₁ c₁) = φ where
      abstract φ = λ i → ispartialorder (snd (isReflᵖ R) a₀ a₁ i) (snd (isAntisymᵖ R) b₀ b₁ i) (snd (isTransᵖ R) c₀ c₁ i)

-- NOTE: there is `Properties` and `Consequences`
--       the difference somehow is, that we do want to open `Consequences` directly
--       but we do not want to open `Properties` directly, because it might have a name clash
--       e.g. there is `Properties.Group` which clashes with `Cubical.Structures.Group.Group` when opening `Properties`
--       but it is totally fine to open `Properties.Group` directly because it does not export a `Group`
-- TODO: check whether this matches the wording of the (old) standard library
module Consequences where
  open Definitions

  module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ')
    (let _<_ = R)
    (let _≤_ = R)
    (let _#_ = R)
    where
    abstract
      irrefl+trans-implies-asym : [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ R ]
      irrefl+trans-implies-asym isIrrefl isTrans a b a<b b<a = isIrrefl _ (isTrans _ _ _ a<b b<a)

      irrefl+trans-implies-asym' : [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ' R ]
      irrefl+trans-implies-asym' isIrrefl isTrans a b (a<b , b<a) = isIrrefl _ (isTrans _ _ _ a<b b<a)

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
        ⇒∶ (λ ≤-antisymˢ' a b a≤b ¬a≡b → ≤-antisymˢ' a b a≤b (λ  z  → ¬a≡b ∣ z ∣))
        ⇐∶ (λ ≤-antisymᵖ' a b a≤b ¬a≡b → ≤-antisymᵖ' a b a≤b (λ ∣z∣ → ∣∣-elim {P = λ _ → ⊥⊥} (λ _ → isProp⊥) ¬a≡b ∣z∣))

      isTight-ˢ≡ᵖ : (isset : isSet A) → isTightˢ R isset ≡ isTightᵖ R
      isTight-ˢ≡ᵖ isset = hProp≡ (isoToPath (record
        { fun      = λ <-tightˢ a b a<b b<a → ∣ <-tightˢ a b a<b b<a ∣
        ; inv      = λ <-tightᵖ a b a<b b<a → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ a b a<b b<a)
        ; rightInv = λ f → isProp[] (isTightᵖ _<_      ) _ f
        ; leftInv  = λ g → isProp[] (isTightˢ _<_ isset) _ g
        }))

      isTight-ˢ'≡ᵖ' : (isset : isSet A) → isTightˢ' R isset ≡ isTightᵖ' R
      isTight-ˢ'≡ᵖ' isset = hProp≡ (isoToPath (record
        { fun      = λ <-tightˢ' a b ¬[a<b⊔b<a] → ∣ <-tightˢ' a b ¬[a<b⊔b<a] ∣
        ; inv      = λ <-tightᵖ' a b ¬[a<b⊔b<a] → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ' a b ¬[a<b⊔b<a])
        ; rightInv = λ f → isProp[] (isTightᵖ' _<_      ) _ f
        ; leftInv  = λ g → isProp[] (isTightˢ' _<_ isset) _ g
        }))

      isTight-ˢ''≡ᵖ'' : (isset : isSet A) → isTightˢ'' R isset ≡ isTightᵖ'' R
      isTight-ˢ''≡ᵖ'' isset = hProp≡ (isoToPath (record
        { fun      = λ <-tightˢ'' a b ¬[a<b⊎b<a] → ∣ <-tightˢ'' a b ¬[a<b⊎b<a] ∣
        ; inv      = λ <-tightᵖ'' a b ¬[a<b⊎b<a] → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ'' a b ¬[a<b⊎b<a])
        ; rightInv = λ f → isProp[] (isTightᵖ'' _<_      ) _ f
        ; leftInv  = λ g → isProp[] (isTightˢ'' _<_ isset) _ g
        }))

      isTight-ˢ'''≡ᵖ''' : (isset : isSet A) → isTightˢ''' R isset ≡ isTightᵖ''' R
      isTight-ˢ'''≡ᵖ''' isset = hProp≡ (isoToPath (record
        { fun      = λ #-tightˢ''' a b ¬[a#b] → ∣ #-tightˢ''' a b ¬[a#b] ∣
        ; inv      = λ #-tightᵖ''' a b ¬[a#b] → ∣∣-elim (λ c → isset a b) (λ x → x) (#-tightᵖ''' a b ¬[a#b])
        ; rightInv = λ f → isProp[] (isTightᵖ''' _#_      ) _ f
        ; leftInv  = λ g → isProp[] (isTightˢ''' _#_ isset) _ g
        }))

      isTight-ᵖ≡ᵖ' : isTightᵖ R ≡ isTightᵖ' R
      isTight-ᵖ≡ᵖ' = hProp≡ (isoToPath (record
        { fun      = λ <-tightᵖ  a b ¬[a<b⊔b<a]    → let (¬[a<b] , ¬[b<a]) = deMorgan₂ (a < b) (b < a) ¬[a<b⊔b<a] in <-tightᵖ a b ¬[a<b] ¬[b<a]
        ; inv      = λ <-tightᵖ' a b ¬[a<b] ¬[b<a] → <-tightᵖ' a b (deMorgan₂-back (a < b) (b < a) (¬[a<b] , ¬[b<a]))
        ; rightInv = λ f → isProp[] (isTightᵖ' _<_) _ f
        ; leftInv  = λ g → isProp[] (isTightᵖ  _<_) _ g
        }))

      isTight-ᵖ'≡ᵖ'' : isTightᵖ' R ≡ isTightᵖ'' R
      isTight-ᵖ'≡ᵖ'' = hProp≡ (isoToPath (record
        { fun      = λ <-tightᵖ'  a b ¬[a<b⊎b<a] → <-tightᵖ'  a b (pathTo⇒ (∥¬A∥≡¬∥A∥ _) ∣ ¬[a<b⊎b<a] ∣)
        ; inv      = λ <-tightᵖ'' a b ¬[a<b⊔b<a] → <-tightᵖ'' a b (λ [a<b⊎b<a] → ¬[a<b⊔b<a] (⊎-implies-⊔ (a < b) (b < a) [a<b⊎b<a]))
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

      module _ (let _≤_ = λ x y → ¬ᵖ (y < x))  where
        abstract
          isTightᵖ≡isAntisymᵖ : isTightᵖ _<_ ≡ isAntisymᵖ _≤_
          isTightᵖ≡isAntisymᵖ = hProp≡ (isoToPath (record
            { fun      = λ <-tight   a b a≤b b≤a → <-tight   a b b≤a a≤b
            ; inv      = λ ≤-antisym a b b≤a a≤b → ≤-antisym a b a≤b b≤a
            ; rightInv = λ f → isProp[] (isAntisymᵖ _≤_) _ f
            ; leftInv  = λ g → isProp[] (isTightᵖ   _<_) _ g
            }))

      module _ (isset : isSet A) (<-asym : [ isAsymᵖ _<_ ])
               (let _≤_ = λ x y → ¬ᵖ (y < x))
               (let _#_ = _#''_ {_<_ = _<_} {<-asym = <-asym}) where
        abstract
          isTightˢ'''≡isAntisymˢ : (isTightˢ''' _#_ isset) ≡ (isAntisymˢ _≤_ isset)
          isTightˢ'''≡isAntisymˢ = hProp≡ (isoToPath (record
            { fun      = λ #-tight a b a≤b b≤a → #-tight a b (deMorgan₂-back' (b≤a , a≤b))
            ; inv      = λ ≤-antisym a b ¬a#b → let (b≤a , a≤b) = deMorgan₂' ¬a#b in ≤-antisym a b a≤b b≤a
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
      irrefl+tight-implies-¬#-≡-≡ᵖ : [ isIrreflᵖ _#_ ] → [ isTightᵖ''' _#_ ] → ∀ a b → ¬ᵖ (a # b) ≡ (a ≡ₚ b)
      irrefl+tight-implies-¬#-≡-≡ᵖ #-irrefl #-tight a b = hProp≡ (isoToPath (record
        { fun      = λ ¬[a#b] → #-tight a b ¬[a#b]
        ; inv      = λ a≡b a#b → #-irrefl b (substₚ (λ x → x # b) a≡b a#b)
        ; rightInv = λ f → isProp[] (    a ≡ₚ b) _ f
        ; leftInv  = λ g → isProp[] (¬ᵖ (a #  b)) _ g
        }))

      irrefl+tight-implies-¬#-≡-≡ˢ : (isset : isSet A) → [ isIrreflᵖ _#_ ] → [ isTightˢ''' _#_ isset ]
                                   → ∀ a b → (¬ [ a # b ]) ≡ (a ≡ b)
      irrefl+tight-implies-¬#-≡-≡ˢ isset #-irrefl #-tight a b = (isoToPath (record
        { fun      = λ ¬[a#b] → #-tight a b ¬[a#b]
        ; inv      = λ a≡b a#b → #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)
        ; rightInv = λ f → isset a b _ f
        ; leftInv  = λ g → isProp[] (¬ᵖ (a #  b)) _ g
        }))

      ¬#-≡-≡-implies-dne-on-≡ : (∀ a b → (¬ [ a # b ]) ≡ (a ≡ b))
                               → ∀(a b : A) → (¬ ¬ (a ≡ b)) ≡ (a ≡ b)
      ¬#-≡-≡-implies-dne-on-≡ ¬#-≡-≡ a b =
        (   ¬ ¬ ( a ≡ b ) ≡⟨ (λ i → ¬ ¬ ¬#-≡-≡ a b (~ i)) ⟩
          ¬ ¬ ¬ [ a # b ] ≡⟨ ¬¬-involutive [ a # b ] ⟩
              ¬ [ a # b ] ≡⟨ ¬#-≡-≡ a b ⟩
                  a ≡ b   ∎)

      irrefl+tight-implies-dne-on-≡ˢ : (isset : isSet A) → [ isIrreflᵖ _#_ ] → [ isTightˢ''' _#_ isset ]
                                     → ∀(a b : A) → (¬ ¬ (a ≡ b)) ≡ (a ≡ b)
      irrefl+tight-implies-dne-on-≡ˢ isset #-irrefl #-tight = ¬#-≡-≡-implies-dne-on-≡ (irrefl+tight-implies-¬#-≡-≡ˢ isset #-irrefl #-tight)

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
         -- (inr b<a) x → case ⊔-implies-⊎ (b < x) (x < a) {! <-trans b x a!} (<-cotrans _ _ b<a x) of λ where
         --   (inl b<x) → inrᵖ (inrᵖ b<x)
         --   (inr x<a) → inlᵖ (inrᵖ x<a)
        }

    -- 2. we have a preorder defined by
    --    x ≤ y := ¬(y < x).

    ≤-isPreorder' : ∀{X : Type ℓ} (_<_ : hPropRel X X ℓ') → [ isStrictPartialOrderᵖ _<_ ] → [ isPreorderᵖ (_≤'_ {_<_ = _<_}) ]
    ≤-isPreorder' {X = X} _<_ <-SPO =
      let (isstrictpartialorder <-irrefl <-trans <-cotrans) = <-SPO
      in λ where
       .IsPreorder.isRefl → <-irrefl
       .IsPreorder.isTrans a b c ¬b<a ¬c<b c<a →
         ⊔-elim (c < b) (b < a) (λ _ → ⊥)
         (λ c<b → ¬c<b c<b)
         (λ b<a → ¬b<a b<a)
         (<-cotrans _ _ c<a b)

module Properties where

  module _ where
    open import Cubical.Structures.Group
    -- import Cubical.Structures.Group.Properties

    module GroupProperties (G : Group {ℓ}) where
      open Group G
      private
        simplR = GroupLemmas.simplR G

      invUniqueL : {g h : Carrier} → g + h ≡ 0g → g ≡ - h
      invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h))

      -- ported from `Algebra.Properties.Group`
      right-helper : ∀ x y → y ≡ - x + (x + y)
      right-helper x y = (
        y               ≡⟨ sym (snd (identity y)) ⟩
        0g          + y ≡⟨ cong₂ _+_ (sym (snd (inverse x))) refl  ⟩
        ((- x) + x) + y ≡⟨ sym (assoc (- x) x y) ⟩
        (- x) + (x + y) ∎)

      -- alternative:
      --   follows from uniqueness of -
      --     (a + -a) ≡ 0
      --     ∃! b . a + b = 0
      --   show that a is an additive inverse of - a then it must be THE additive inverse of - a and has to be called - - a which is a by uniqueness
      -involutive : ∀ x → - - x ≡ x
      -involutive x = (
        (- (- x))             ≡⟨ sym (fst (identity _)) ⟩
        (- (- x)) + 0g        ≡⟨ cong₂ _+_ refl (sym (snd (inverse _))) ⟩
        (- (- x)) + (- x + x) ≡⟨ sym (right-helper (- x) x) ⟩
        x                    ∎)

  module _ where
    open import Cubical.Structures.Ring
    module RingProperties (R : Ring {ℓ}) where
      open Ring R
      open Cubical.Structures.Ring.Theory R

      -- NOTE: a few facts about rings that might be collected from elsewhere
      a+b-b≡a : ∀ a b → a ≡ (a + b) - b
      a+b-b≡a a b = let P = sym (fst (+-inv b))
                        Q = sym (fst (+-identity a))
                        R = transport (λ i → a ≡ a + P i) Q
                        S = transport (λ i → a ≡ (+-assoc a b (- b)) i ) R
                    in S

      -- NOTE: this is called `simplL` and `simplL` in `Cubical.Structures.Group.Properties.GroupLemmas`
      +-preserves-≡ : ∀{a b} → ∀ c → a ≡ b → a + c ≡ b + c
      +-preserves-≡ c a≡b i = a≡b i + c

      +-preserves-≡-l : ∀{a b} → ∀ c → a ≡ b → c + a ≡ c + b
      +-preserves-≡-l c a≡b i = c + a≡b i

      a+b≡0→a≡-b : ∀{a b} → a + b ≡ 0r → a ≡ - b
      a+b≡0→a≡-b {a} {b} a+b≡0 = transport
        (λ i →
          let RHS = snd (+-identity (- b))
              LHS₁ : a + (b + - b) ≡ a + 0r
              LHS₁ = +-preserves-≡-l a (fst (+-inv b))
              LHS₂ : (a + b) - b ≡ a
              LHS₂ = transport (λ j →  (+-assoc a b (- b)) j ≡ fst (+-identity a) j) LHS₁
              in  LHS₂ i ≡ RHS i
        ) (+-preserves-≡ (- b) a+b≡0)

      -- NOTE: there is already
      -- -commutesWithRight-· : (x y : R) →  x · (- y) ≡ - (x · y)

      a·-b≡-a·b : ∀ a b → a · (- b) ≡ - (a · b)
      a·-b≡-a·b a b =
        let P : a · 0r ≡ 0r
            P = 0-rightNullifies a
            Q : a · (- b + b) ≡ 0r
            Q = transport (λ i →  a · snd (+-inv b) (~ i) ≡ 0r) P
            R : a · (- b) + a · b ≡ 0r
            R = transport (λ i → ·-rdist-+ a (- b) b i ≡ 0r) Q
        in a+b≡0→a≡-b R

      a·b-a·c≡a·[b-c] : ∀ a b c → a · b - (a · c) ≡ a · (b - c)
      a·b-a·c≡a·[b-c] a b c =
        let P : a · b + a · (- c) ≡ a · (b + - c)
            P = sym (·-rdist-+ a b (- c))
            Q : a · b - a · c ≡ a · (b + - c)
            Q = transport (λ i →  a · b + a·-b≡-a·b a c i ≡ a · (b + - c) ) P
        in  Q

  -- exports
  module Group = GroupProperties
  module Ring  = RingProperties
