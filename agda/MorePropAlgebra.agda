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
  module OnRelations {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where
    isReflᵖ     =                      ∀[ a ]     R a a
    isIrreflᵖ   =                      ∀[ a ] ¬ᵖ (R a a)

    isTransᵖ    =                      ∀[ a ] ∀[ b ] ∀[ x ] R a b ⇒         R b x ⇒ R a x
    isCotransᵖ  =                      ∀[ a ] ∀[ b ]        R a b ⇒ (∀[ x ] R a x ⊔ R x b)

    isSymᵖ      =                      ∀[ a ] ∀[ b ]     R a b ⇒    R b a
    isAsymᵖ     =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬ᵖ R b a
    isAsymᵖ'    =                      ∀[ a ] ∀[ b ] ¬ᵖ (R a b ⊓    R b a)

    isAntisymᵖ  =                      ∀[ a ] ∀[ b ]     R a b ⇒              R b a   ⇒            a ≡ₚ b
    isAntisymˢ  = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒              R b a   ⇒ ([ isset ] a ≡ˢ b)
    isAntisymᵖ' =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬ᵖ(          a ≡ₚ b) ⇒            R b a
    isAntisymˢ' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒ ¬ᵖ([ isset ] a ≡ˢ b) ⇒            R b a

    isTightᵖ    =                      ∀[ a ] ∀[ b ]     ¬ᵖ R a b   ⇒ ¬ᵖ R b a      ⇒           a ≡ₚ b
    isTightˢ    = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     ¬ᵖ R a b   ⇒ ¬ᵖ R b a      ⇒ [ isset ] a ≡ˢ b
    isTightᵖ'   =                      ∀[ a ] ∀[ b ]  ¬ᵖ (  R a b   ⊔    R b a   )  ⇒           a ≡ₚ b
    isTightˢ'   = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬ᵖ (  R a b   ⊔    R b a   )  ⇒ [ isset ] a ≡ˢ b
    isTightᵖ''  =                      ∀[ a ] ∀[ b ] (¬  ([ R a b ] ⊎  [ R b a ])) ᵗ⇒           a ≡ₚ b
    isTightˢ''  = λ(isset : isSet A) → ∀[ a ] ∀[ b ] (¬  ([ R a b ] ⊎  [ R b a ])) ᵗ⇒ [ isset ] a ≡ˢ b
    isTightᵖ''' =                      ∀[ a ] ∀[ b ]  ¬ᵖ    R a b                   ⇒           a ≡ₚ b
    isTightˢ''' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬ᵖ    R a b                   ⇒ [ isset ] a ≡ˢ b

  isReflᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isReflᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a : A) → [ R a a ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ (λ(a : A) → isProp[] (R a a))
  isReflᵖ R = ∀[ a ] R a a

  -- IsRefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsRefl R = [ isReflᵖ R ]

  isIrreflᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isIrreflᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a : A) → [ ¬ᵖ (R a a) ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ (λ(a : A) → isProp[] (¬ᵖ (R a a)))
  isIrreflᵖ R = ∀[ a ] ¬ᵖ (R a a)

  -- IsIrrefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsIrrefl R = [ isIrreflᵖ R ]

  -- isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isCotransᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
  --   where
  --     φ : Type (ℓ-max ℓ ℓ')
  --     φ = (a b : A) → [ R a b ⇒ (∀[ x ∶ A ] (R a x) ⊔ (R x b)) ]
  --     φ-prop : isProp φ
  --     abstract φ-prop = isPropΠ2 λ a b → snd (R a b ⇒ (∀[ x ∶ A ] (R a x) ⊔ (R x b)))

  -- isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isCotransᵖ R .fst =                                 ∀ a b →     [ R a b ⇒ (∀[ x ] R a x ⊔ R x b) ]
  -- isCotransᵖ R .snd = φp where abstract φp = isPropΠ2 λ a b → snd ( R a b ⇒ (∀[ x ] R a x ⊔ R x b) )

  -- rm MorePropAlgebra.agdai; time agda -v profile:7 MorePropAlgebra.agda
  -- Total                        6,452ms           |   6,784ms
  -- Miscellaneous                  219ms           |     259ms
  -- Deserialization              3,565ms (4,000ms) |   3,697ms (4,142ms)
  -- Deserialization.Compaction     435ms           |     444ms
  -- Typing                          75ms   (874ms) |      81ms (1,001ms)
  -- Typing.CheckRHS                517ms           |     616ms
  -- Typing.TypeSig                 167ms           |     179ms
  -- Typing.CheckLHS                 49ms           |      52ms
  -- Typing.Generalize               36ms           |      40ms
  -- Typing.OccursCheck              28ms           |      31ms
  -- Parsing                         59ms   (519ms) |      59ms   (517ms)
  -- Parsing.OperatorsExpr          421ms           |     420ms
  -- Parsing.OperatorsPattern        37ms           |      37ms
  -- Serialization                  316ms   (459ms) |     237ms   (482ms)
  -- Serialization.BinaryEncode     102ms           |     203ms
  -- Serialization.Compress          16ms           |      17ms
  -- Serialization.BuildInterface    14ms           |      15ms
  -- Import                         182ms           |     174ms
  -- Scoping                         95ms   (109ms) |      95ms   (111ms)
  -- Scoping.InverseScopeLookup      13ms           |      15ms
  -- Highlighting                    35ms           |      38ms
  -- Positivity                      26ms           |      30ms
  -- Coverage                        17ms           |      19ms
  -- DeadCode                        16ms           |      16ms


  isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isCotransᵖ R = ∀[ a ] ∀[ b ] R a b ⇒ (∀[ x ] R a x ⊔ R x b)
  -- isCotransᵖ {A = A} R =
  --   ( ((a b : A) → fst (R a b) → (x : A) → ∥ fst (R a x) ⊎ fst (R x b) ∥)
  --   , (λ f g i a b aRb c → squash (f a b aRb c) (g a b aRb c) i)
  --   )
  -- isCotransᵖ {A = A} R .fst = (a b : A) → fst (R a b) → (x : A) → ∥ fst (R a x) ⊎ fst (R x b) ∥
  -- isCotransᵖ {A = A} R .snd f g i a b aRb c = squash (f a b aRb c) (g a b aRb c) i

  -- _ = {! λ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → isCotransᵖ R  !}

  -- IsCotrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsCotrans R = [ isCotransᵖ R ]

  isSymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isSymᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ R a b ⇒ R b a ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ R b a))
  isSymᵖ R = ∀[ a ] ∀[ b ] R a b ⇒ R b a

  -- IsSym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsSym R = [ isSymᵖ R ]

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

  isAsymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAsymᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ R a b ⇒ ¬ᵖ R b a ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ ¬ᵖ R b a))
  isAsymᵖ R = ∀[ a ] ∀[ b ] R a b ⇒ ¬ᵖ R b a

  -- IsAsym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsAsym R = [ isAsymᵖ R ]

  isAsymᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAsymᵖ' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ ¬ᵖ (R a b ⊓ R b a) ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ (R a b ⊓ R b a)))
  isAsymᵖ' R = ∀[ a ] ∀[ b ] ¬ᵖ (R a b ⊓ R b a)

  -- IsAsym' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsAsym' R = [ isAsymᵖ' R ]

  isAsymᵖ≡ᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → isAsymᵖ R ≡ isAsymᵖ' R
  abstract isAsymᵖ≡ᵖ' _<_ =
             ⇒∶ (λ{ <-asym a b (a<b , b<a) → <-asym a b a<b b<a })
             ⇐∶ (λ  <-asym a b → fst (¬-⊓-distrib (a < b) (b < a) (<-asym a b)) )

  -- NOTE: this is tricky somehow and might not be equivalent to the other ones
  --
  -- isAsymᵖ² : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAsymᵖ² {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ ¬ᵖ R b a ⇒ R a b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ R b a ⇒ R a b))
  --
  -- isAsymᵖ⇒² : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isAsymᵖ' R ] → [ isAsymᵖ² R ]
  -- isAsymᵖ⇒² _<_ <-asym a b ¬b<a = {! ¬-⊓-distrib (a < b) (b < a) (<-asym a b)  !}

  -- do we have `R a b ≡ ¬ᵖ R b a` ?

  -- isAsymᵖ-back : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAsymᵖ-back {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ ¬ᵖ R b a ⇒ R a b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ R b a ⇒ R a b))

  -- foo : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isAsymᵖ' R ] → ∀ a b → [ ¬ᵖ R a b ⇒ R b a ]
  -- foo _<_ <-asym a b = {! contraposition  !}

  -- isAsymᵖ⇔isAsymᵖ-back : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → isAsymᵖ' R ≡ isAsymᵖ-back R
  -- isAsymᵖ⇔isAsymᵖ-back _<_ =
  --   ⇒∶ (λ f a b → {! [P⇒¬Q]⇒[Q⇒¬P] _ _ (f a b)  !})
  --   ⇐∶ (λ f a b → {! [P⇒¬Q]⇒[Q⇒¬P] (b < a) (a < b)  !})

  isTransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTransᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
  --   where
  --     φ : Type (ℓ-max ℓ ℓ')
  --     φ = (a b c : A) → [ R a b ⇒ R b c ⇒ R a c ]
  --     φ-prop : isProp φ
  --     abstract φ-prop = isPropΠ3 λ a b c → snd (R a b ⇒ R b c ⇒ R a c)
  isTransᵖ R = ∀[ a ] ∀[ b ] ∀[ c ] R a b ⇒ R b c ⇒ R a c

  -- IsTrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTrans R = [ isTransᵖ R ]

  irrefl+trans-implies-asym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ R ]
  abstract irrefl+trans-implies-asym _<_ isIrrefl isTrans a b a<b b<a = isIrrefl _ (isTrans _ _ _ a<b b<a)

  irrefl+trans-implies-asym' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ' R ]
  abstract irrefl+trans-implies-asym' _<_ isIrrefl isTrans a b (a<b , b<a) = isIrrefl _ (isTrans _ _ _ a<b b<a)

  record IsApartnessRel {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isapartnessrel
    field
      isIrrefl  : [ isIrreflᵖ  R ]
      isSym     : [ isSymᵖ     R ]
      isCotrans : [ isCotransᵖ R ]

  isApartnessRelᵖ : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isApartnessRelᵖ R = IsApartnessRel R , φ-prop where
    abstract
      φ-prop : isProp (IsApartnessRel R)
      φ-prop (isapartnessrel isIrrefl₀ isSym₀ isCotrans₀)
             (isapartnessrel isIrrefl₁ isSym₁ isCotrans₁) =
        λ i → isapartnessrel (isProp[] (isIrreflᵖ  R) isIrrefl₀  isIrrefl₁  i)
                             (isProp[] (isSymᵖ     R) isSym₀     isSym₁     i)
                             (isProp[] (isCotransᵖ R) isCotrans₀ isCotrans₁ i)

  record IsStrictPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorder
    field
      isIrrefl  : [ isIrreflᵖ  R ]
      isTrans   : [ isTransᵖ   R ]
      isCotrans : [ isCotransᵖ R ]

  isStrictPartialOrderᵖ : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isStrictPartialOrderᵖ R = IsStrictPartialOrder R , φ-prop where
    abstract
      φ-prop :      isProp (IsStrictPartialOrder R)
      φ-prop (isstrictpartialorder isIrrefl₀ isTrans₀ isCotrans₀)
             (isstrictpartialorder isIrrefl₁ isTrans₁ isCotrans₁) =
        λ i → isstrictpartialorder (isProp[] (isIrreflᵖ  R) isIrrefl₀  isIrrefl₁  i)
                                   (isProp[] (isTransᵖ   R) isTrans₀   isTrans₁   i)
                                   (isProp[] (isCotransᵖ R) isCotrans₀ isCotrans₁ i)

  record IsPreorder {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor ispreorder
    field
      isRefl    : [ isReflᵖ  R ]
      isTrans   : [ isTransᵖ R ]

  isPreorderᵖ : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isPreorderᵖ R =     IsPreorder R , φ-prop where
    abstract
      φ-prop : isProp (IsPreorder R)
      φ-prop (ispreorder isRefl₀ isTrans₀)
             (ispreorder isRefl₁ isTrans₁) =
        λ i → ispreorder (isProp[] (isReflᵖ  R) isRefl₀  isRefl₁  i)
                         (isProp[] (isTransᵖ R) isTrans₀ isTrans₁ i)

  -- antisymmetry and antisymmetry on sets
  --
  --   IsAntisym        R = ∀ a b → [ R a b   ⇒   R b a   ⇒ a ≡ₚ b ]
  --   IsAntisymˢ isset R = ∀ a b → [ R a b ] → [ R b a ] → a ≡  b
  --
  -- both are equivalent (on sets):
  --
  --   isAntisym-ˢ≡ᵖ : (isset : isSet A) → isAntisymˢ isset R ≡ isAntisymᵖ R
  --
  -- Wikipedia writes that
  --
  --   if R(a, b) with a ≠ b, then R(b, a) must not hold,
  --
  -- is equivalent to
  --
  --   if R(a, b) and R(b, a), then a = b.
  --
  -- but is this an equivalence constructively?
  -- I guess that `[ R a b ] → [ R b a ] → a ≡ b` implies `[ R a b ] →  [ a # b ] → [ ¬ R b a ]` in the following way:
  --
  --   [ R a b ] → [ R b a ] → a ≡ b        --
  --   [ R a b ] × [ R b a ] → a ≡ b        -- by curry/uncurry
  --   [ R a b   ⊓   R b a ] → a ≡ b        -- definitionally
  --   ¬(a ≡ b) → ¬ [ R a b ⊓ R b a ]       -- by contraposition (NOTE: contraposition is not an equivalence)
  --   ¬(a ≡ b) →   [ R a b ] → [ ¬ R b a ] -- by [P⇒¬Q]≡¬[P⊓Q]
  --   [ R a b ] →  ¬(a ≡ b)  → [ ¬ R b a ] -- swap arguments
  --   [ R a b ] →  [ a # b ] → [ ¬ R b a ] -- when `a # b ⇒ ¬(a ≡ b)` (by #-irrefl) (NOTE: also not an equivalence)
  --
  -- Here we see that antisymmetry + irreflexivity ⇒ asymmetry
  --   wikipedia also writes trans + irrefl ⇒ asym
  -- isTightᵖ _<_ ≡ isAntisymᵖ  (λ a b → ¬ᵖ (b < a))
  -- #-tight : [ ¬ (a < b) ] → [ ¬ (b < a) ] → a ≡ b
  --           [ ¬ (a # b) ]                 → a ≡ b
  -- <-irrefl ⇒ #-irrefl
  --   which gives a ≡ b → [ ¬ (a # b) ]
  -- so we do have ¬#-≡-≡ when # is tight?
  -- on ¬# we do have double negation elimintation (¬¬¬# ≡ ¬#)
  -- so # gives us ≡-dne ?? hmm......
  --
  -- the other way could be
  --
  --   [ R a b ] → [ a # b ] → [ ¬ R b a  ]     --
  --   [ R a b ] → [ a # b ] → [   R b a  ] → ⊥ -- by ¬
  --   [ R a b ] → [ R b a ] → [   a # b  ] → ⊥ -- swap arguments
  --   [ R a b ] → [ R b a ] → [ ¬(a # b) ]     -- by ¬
  --   [ R a b ] → [ R b a ] →     a ≡ b        -- when `¬(a # b) ⇒ a ≡ b` (by #-tight)
  --
  --   [ R a b ] →   ¬(a ≡ b)   → [   ¬ R b a   ]     --
  --   [ R a b ] →   ¬(a ≡ b)   → [     R b a   ] → ⊥ -- by ¬
  --   [ R a b ] → [   R b a  ] →     ¬(a ≡ b)    → ⊥ -- swap arguments
  --   [ R a b ] → [   R b a  ] →   ¬(¬(a ≡ b))       -- by ¬
  --   [ R a b ] → [   R b a  ] →       a ≡ b        -- when `¬(¬(a ≡ b)) ⇒ a ≡ b`

  -- let's call the weaker one isAntisym'
  -- we have then
  --   isIrrefl _<_ → isAntisym _≤_ ≡ (isAntisym' _≤_ + dne-on-≡) ≡ isTight''' _#_
  --   isIrrefl _<_ ≡ isIrrefl _#_
  --   isIrrefl _#_ → isTight''' _#_ → dne-on-≡

  -- ≡-dne : ∀{ℓ} {a b : Type ℓ} → ¬ ¬ (a ≡ b) → a ≡ b
  -- ≡-dne ¬¬[a≡b] = {!   !}

  isAntisymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAntisymᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ R a b ⇒ R b a ⇒ a ≡ₚ b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ R b a ⇒ a ≡ₚ b))
  isAntisymᵖ R = ∀[ a ] ∀[ b ] R a b ⇒ R b a ⇒ a ≡ₚ b

  -- IsAntisym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsAntisym R = [ isAntisymᵖ R ]

  -- a variant on sets to resolve ≡ₚ
  isAntisymˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAntisymˢ {ℓ = ℓ} {ℓ' = ℓ'} {A = A} isset R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ R a b ] → [ R b a ] → a ≡ b
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ2 λ a<b b<a → isset a b)
  isAntisymˢ isset R = ∀[ a ] ∀[ b ] R a b ⇒ R b a ⇒ ([ isset ] a ≡ˢ b)

  -- IsAntisymˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsAntisymˢ isset R = [ isAntisymˢ isset R ]

  -- NOTE: we also have isProp→Iso in `Cubical.Foundations.Isomorphism`
  isAntisym-ˢ≡ᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isAntisymˢ isset R ≡ isAntisymᵖ R
  abstract
    isAntisym-ˢ≡ᵖ isset R = hProp≡ (isoToPath (record
      { fun      = λ ≤-antisymˢ a b a≤b b≤a → ∣ ≤-antisymˢ a b a≤b b≤a ∣
      ; inv      = λ ≤-antisymᵖ a b a≤b b≤a → ∣∣-elim (λ c → isset a b) (λ x → x) (≤-antisymᵖ a b a≤b b≤a)
      ; rightInv = λ f → isProp[] (isAntisymᵖ       R) _ f
      ; leftInv  = λ g → isProp[] (isAntisymˢ isset R) _ g
      }))

  isAntisymᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAntisymᵖ' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ R a b ⇒ ¬ᵖ (a ≡ₚ b) ⇒ R b a ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ ¬ᵖ (a ≡ₚ b) ⇒ R b a))
  isAntisymᵖ' R = ∀[ a ] ∀[ b ] R a b ⇒ ¬ᵖ (a ≡ₚ b) ⇒ R b a

  -- IsAntisym' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsAntisym' R = [ isAntisymᵖ' R ]

  isAntisymˢ' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAntisymˢ' {ℓ = ℓ} {ℓ' = ℓ'} {A = A} isset R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ R a b ] → ¬(a ≡ b) → [ R b a ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ2 λ a<b ¬a≡b → isProp[] (R b a))
  isAntisymˢ' isset R = ∀[ a ] ∀[ b ] R a b ⇒ ¬ᵖ([ isset ] a ≡ˢ b) ⇒ R b a

  -- IsAntisymˢ' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsAntisymˢ' isset R = [ isAntisymˢ' isset R ]

  isAntisym-ˢ'≡ᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isAntisymˢ' isset R ≡ isAntisymᵖ' R
  abstract
    isAntisym-ˢ'≡ᵖ' {A = A} isset _≤_ =
      ⇒∶ (λ ≤-antisymˢ' a b a≤b ¬a≡b → ≤-antisymˢ' a b a≤b (λ  z  → ¬a≡b ∣ z ∣))
      ⇐∶ (λ ≤-antisymᵖ' a b a≤b ¬a≡b → ≤-antisymᵖ' a b a≤b (λ ∣z∣ → ∣∣-elim {P = λ _ → ⊥⊥} (λ _ → isProp⊥) ¬a≡b ∣z∣))

  -- test'' : {A B : Type ℓ} (f : A → B) → (a : A) → f a ≡ a .f
  -- test'' f a = refl

  -- Σ≡Prop' pB {u} {v} p i = (p i) , isProp→PathP (λ i → pB (p i)) (u .snd) (v .snd) i

  {- tightness is closely related to antisymmetry:
   -
   -   R-antisym : [    R a b ] → [    R b a ] → a ≡ b
   -   R-tight   : [ ¬ᵖ R a b ] → [ ¬ᵖ R b a ] → a ≡ b
   -
   - this becomes even more obvious if we regard the intended use: when _≤_ and _#_ are derived from _<_
   -
   -    a ≤ b = ¬ᵖ (b < a)
   -    a # b = ¬ᵖ ([ a < b ] ⊎ [ b < a ])
   -
   - and indeed, we get
   -
   -   isTightᵖ  _<_ ≡ isAntisymᵖ  (λ a b → ¬ᵖ (b < a))
   -   isTightᵖ' _<_ ≡ isTightᵖ''' (λ a b → (a < b) ⊔ (b < a))
   -
   - In that case, `≤-antisym` and `#-tight` are almost the same, definitionally:
   -
   -   ≤-antisym : [ ¬ᵖ (b < a) ] → [ ¬ᵖ (a < b) ] → a ≡ b
   -   ≤-antisym : [ ¬ᵖ (b < a) ] × [ ¬ᵖ (a < b) ] → a ≡ b -- by curry/uncurry
   -   ≤-antisym : ¬ ( [ b < a ]  ⊎     [ a < b ]) → a ≡ b -- by deMorgan
   -   #-tight   : [ ¬ᵖ (a < b) ] → [ ¬ᵖ (b < a) ] → a ≡ b
   -   #-tight   : [ ¬ᵖ (a < b) ] × [ ¬ᵖ (b < a) ] → a ≡ b -- by curry/uncurry
   -   #-tight   : ¬ ( [ a < b ]  ⊎     [ b < a ]) → a ≡ b -- by deMorgan
   -
   - We provide a few variants of tightness
   -
   -   IsTight           R = ∀ a b → [ ¬ᵖ    R a b   ⇒   ¬ᵖ R b a      ⇒   a ≡ₚ b ] -- on _<_, "canonical"
   -   IsTightˢ    isset R = ∀ a b → [ ¬ᵖ    R a b ] → [ ¬ᵖ R b a ]    →   a ≡  b   -- on _<_
   -   IsTight'          R = ∀ a b → [ ¬ᵖ (  R a b   ⊔      R b a  )   ⇒   a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ'≡ᵖ'''`
   -   IsTightˢ'   isset R = ∀ a b → [ ¬ᵖ (  R a b   ⊔      R b a  ) ] →   a ≡  b   -- on _<_
   -   IsTight''         R = ∀ a b →   ¬  ([ R a b ] ⊎ [    R b a ])   → [ a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ''≡ᵖ'''`
   -   IsTightˢ''  isset R = ∀ a b →   ¬  ([ R a b ] ⊎ [    R b a ])   →   a ≡  b   -- on _<_, "convenient"
   -   IsTight'''        R = ∀ a b → [ ¬ᵖ    R a b                     ⇒   a ≡ₚ b ] -- on _#_
   -   IsTightˢ''' isset R = ∀ a b →   ¬   [ R a b ]                   →   a ≡  b   -- on _#_, also "convenient"
   -
   - where the very first one, `IsTight` corresponds to a "canonical" definition,
   - the later one, `IsTightˢ''` is the "most convenient" one to use for `a # b = ¬ᵖ ([ a < b ] ⊎ [ b < a ])` on sets.
   - and the last ones `IsTight'''` and `IsTightˢ'''` are for "_#_" instead of "_<_".
   -
   - These tightness definitions are all equivalent in the following sense:
   -
   -   isTight-ˢ≡ᵖ       : (isset : isSet A)          → isTightˢ    isset _<_ ≡ isTightᵖ    _<_
   -   isTight-ˢ'≡ᵖ'     : (isset : isSet A)          → isTightˢ'   isset _<_ ≡ isTightᵖ'   _<_
   -   isTight-ˢ''≡ᵖ''   : (isset : isSet A)          → isTightˢ''  isset _<_ ≡ isTightᵖ''  _<_
   -   isTight-ˢ'''≡ᵖ''' : (isset : isSet A)          → isTightˢ''' isset _#_ ≡ isTightᵖ''' _#_
   -   isTight-ᵖ≡ᵖ'      :                              isTightᵖ          _<_ ≡ isTightᵖ'   _<_
   -   isTight-ᵖ'≡ᵖ''    :                              isTightᵖ'         _<_ ≡ isTightᵖ''  _<_
   -   isTight-ᵖ'≡ᵖ'''   :                              isTightᵖ'         _<_ ≡ isTightᵖ''' (λ a b →  ( a < b ) ⊔ ( b < a )   )
   -   isTight-ᵖ''≡ᵖ'''  : (<-asym : [ isAsymᵖ _<_ ]) → isTightᵖ''        _<_ ≡ isTightᵖ''' (λ a b → ([ a < b ] ⊎ [ b < a ]) , ⊎-isProp (a < b) (b < a) (inl (<-asym a b)))
   -
   - where `isTight-ᵖ'≡ᵖ'''` and `isTight-ᵖ''≡ᵖ'''` hold definitionally.
   -}

  isTightᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ ¬ᵖ R a b ⇒ ¬ᵖ R b a ⇒ a ≡ₚ b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ R a b ⇒ ¬ᵖ R b a ⇒ a ≡ₚ b))
  isTightᵖ R = ∀[ a ] ∀[ b ] ¬ᵖ R a b ⇒ ¬ᵖ R b a ⇒ a ≡ₚ b

  -- IsTight : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTight R = [ isTightᵖ R ]

  isTightˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightˢ {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ ¬ᵖ R a b ] → [ ¬ᵖ R b a ] → a ≡ b
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ2 λ ¬a<b ¬b<a → isset a b)
  isTightˢ isset R = ∀[ a ] ∀[ b ] ¬ᵖ R a b ⇒ ¬ᵖ R b a ⇒ [ isset ] a ≡ˢ b

  -- IsTightˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTightˢ isset R = [ isTightˢ isset R ]

  isTight-ˢ≡ᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isTightˢ isset R ≡ isTightᵖ R
  abstract
    isTight-ˢ≡ᵖ isset _<_ = hProp≡ (isoToPath (record -- ΣPathP
      { fun      = λ <-tightˢ a b a<b b<a → ∣ <-tightˢ a b a<b b<a ∣
      ; inv      = λ <-tightᵖ a b a<b b<a → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ a b a<b b<a)
      ; rightInv = λ f → isProp[] (isTightᵖ       _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ isset _<_) _ g
      }))

  isTightᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightᵖ' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ ¬ᵖ (R a b ⊔ R b a) ⇒ a ≡ₚ b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ (R a b ⊔ R b a) ⇒ a ≡ₚ b))
  isTightᵖ' R = ∀[ a ] ∀[ b ] ¬ᵖ (R a b ⊔ R b a) ⇒ a ≡ₚ b

  -- IsTight' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTight' R = [ isTightᵖ' R ]

  isTightˢ' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightˢ' {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ ¬ᵖ (R a b ⊔ R b a) ] → a ≡ b
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ λ ¬[a<b⊔b<a] → isset a b)
  isTightˢ' isset R = ∀[ a ] ∀[ b ] ¬ᵖ (R a b ⊔ R b a) ⇒ [ isset ] a ≡ˢ b

  -- IsTightˢ' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTightˢ' isset R = [ isTightˢ' isset R ]

  isTight-ˢ'≡ᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isTightˢ' isset R ≡ isTightᵖ' R
  abstract
    isTight-ˢ'≡ᵖ' isset _<_ = hProp≡ (isoToPath (record -- ΣPathP
      { fun      = λ <-tightˢ' a b ¬[a<b⊔b<a] → ∣ <-tightˢ' a b ¬[a<b⊔b<a] ∣
      ; inv      = λ <-tightᵖ' a b ¬[a<b⊔b<a] → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ' a b ¬[a<b⊔b<a])
      ; rightInv = λ f → isProp[] (isTightᵖ'       _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ' isset _<_) _ g
      }))

  isTightᵖ'' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightᵖ'' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → ¬ ([ R a b ] ⊎ [ R b a ]) → [ a ≡ₚ b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ3 (λ a b p → isProp[] (a ≡ₚ b))
  isTightᵖ'' R = ∀[ a ] ∀[ b ] (¬ ([ R a b ] ⊎ [ R b a ])) ᵗ⇒ a ≡ₚ b

  -- IsTight'' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTight'' R = [ isTightᵖ'' R ]

  isTightˢ'' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightˢ'' {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → ¬ ([ R a b ] ⊎ [ R b a ]) → a ≡ b
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ λ ¬[a<b⊎b<a] → isset a b)
  isTightˢ'' isset R = ∀[ a ] ∀[ b ] (¬ ([ R a b ] ⊎ [ R b a ])) ᵗ⇒ [ isset ] a ≡ˢ b

  -- IsTightˢ'' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTightˢ'' isset R = [ isTightˢ'' isset R ]

  isTight-ˢ''≡ᵖ'' : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isTightˢ'' isset R ≡ isTightᵖ'' R
  abstract
    isTight-ˢ''≡ᵖ'' {A = A} isset _<_ = hProp≡ (isoToPath (record
      { fun      = λ <-tightˢ'' a b ¬[a<b⊎b<a] → ∣ <-tightˢ'' a b ¬[a<b⊎b<a] ∣
      ; inv      = λ <-tightᵖ'' a b ¬[a<b⊎b<a] → ∣∣-elim (λ c → isset a b) (λ x → x) (<-tightᵖ'' a b ¬[a<b⊎b<a])
      ; rightInv = λ f → isProp[] (isTightᵖ''       _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ'' isset _<_) _ g
      }))

  isTightᵖ''' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightᵖ''' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → [ ¬ᵖ R a b ⇒ a ≡ₚ b ]
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ λ p → isProp[] (a ≡ₚ b))
  isTightᵖ''' R = ∀[ a ] ∀[ b ] ¬ᵖ R a b ⇒ a ≡ₚ b

  -- IsTight''' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTight''' R = [ isTightᵖ''' R ]

  isTightˢ''' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isTightˢ''' {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = ∀ a b → ¬ [ R a b ] → a ≡ b
  --   φ-prop : isProp φ
  --   abstract φ-prop = isPropΠ2 (λ a b → isPropΠ λ _ → isset a b)
  isTightˢ''' isset R = ∀[ a ] ∀[ b ] ¬ᵖ R a b ⇒ [ isset ] a ≡ˢ b

  -- IsTightˢ''' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  -- IsTightˢ''' isset R = [ isTightˢ''' isset R ]

  isTight-ˢ'''≡ᵖ''' : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isTightˢ''' isset R ≡ isTightᵖ''' R
  abstract
    isTight-ˢ'''≡ᵖ''' {A = A} isset _#_ = hProp≡ (isoToPath (record
      { fun      = λ #-tightˢ''' a b ¬[a#b] → ∣ #-tightˢ''' a b ¬[a#b] ∣
      ; inv      = λ #-tightᵖ''' a b ¬[a#b] → ∣∣-elim (λ c → isset a b) (λ x → x) (#-tightᵖ''' a b ¬[a#b])
      ; rightInv = λ f → isProp[] (isTightᵖ'''       _#_) _ f
      ; leftInv  = λ g → isProp[] (isTightˢ''' isset _#_) _ g
      }))

  isTight-ᵖ≡ᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → isTightᵖ R ≡ isTightᵖ' R
  abstract
    isTight-ᵖ≡ᵖ' {A = A} _<_ = hProp≡ (isoToPath (record
      { fun      = λ <-tightᵖ  a b ¬[a<b⊔b<a]    → let (¬[a<b] , ¬[b<a]) = deMorgan₂ (a < b) (b < a) ¬[a<b⊔b<a] in <-tightᵖ a b ¬[a<b] ¬[b<a]
      ; inv      = λ <-tightᵖ' a b ¬[a<b] ¬[b<a] → <-tightᵖ' a b (deMorgan₂-back (a < b) (b < a) (¬[a<b] , ¬[b<a]))
      ; rightInv = λ f → isProp[] (isTightᵖ' _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightᵖ  _<_) _ g
      }))

  isTight-ᵖ'≡ᵖ'' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → isTightᵖ' R ≡ isTightᵖ'' R
  abstract
    isTight-ᵖ'≡ᵖ'' {A = A} _<_ = hProp≡ (isoToPath (record
      { fun      = λ <-tightᵖ'  a b ¬[a<b⊎b<a] → <-tightᵖ'  a b (pathTo⇒ (∥¬A∥≡¬∥A∥ _) ∣ ¬[a<b⊎b<a] ∣)
      ; inv      = λ <-tightᵖ'' a b ¬[a<b⊔b<a] → <-tightᵖ'' a b (λ [a<b⊎b<a] → ¬[a<b⊔b<a] (⊎-implies-⊔ (a < b) (b < a) [a<b⊎b<a]))
      ; rightInv = λ f → isProp[] (isTightᵖ'' _<_) _ f
      ; leftInv  = λ g → isProp[] (isTightᵖ'  _<_) _ g
      }))

  _#'_ : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → hPropRel X X ℓ'
  _#'_ {_<_ = _<_} x y = (x < y) ⊔ (y < x)

  _#''_ : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} {<-asym : [ isAsymᵖ _<_ ]} → hPropRel X X ℓ'
  -- _#''_ {_<_ = _<_} {<-asym = <-asym} x y = ([ x < y ] ⊎ [ y < x ]) , ⊎-isProp (x < y) (y < x) (inl (<-asym x y))
  _#''_ {_<_ = _<_} {<-asym = <-asym} x y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

  module _ {ℓ ℓ' : Level} {A : Type ℓ} (_<_ : hPropRel A A ℓ') (let _#_ = λ x y → (x < y) ⊔ (y < x) ) {- (let _#_ = _#'_ {_<_ = _<_}) -} where
    isTight-ᵖ'≡ᵖ''' : isTightᵖ' _<_ ≡ isTightᵖ''' _#_
    -- isTight-ᵖ'≡ᵖ''' = refl -- this actually holds definitionally, but due to our use of `abstract` for the prop, we need `isPropIsProp`
    abstract isTight-ᵖ'≡ᵖ''' = ΣPathP (refl , isPropIsProp _ _)

  module _ {ℓ ℓ' : Level} {A : Type ℓ} (_<_ : hPropRel A A ℓ') (<-asym : [ isAsymᵖ _<_ ]) (let _#_ = _#''_ {_<_ = _<_} {<-asym = <-asym}) where
    isTight-ᵖ''≡ᵖ''' : isTightᵖ'' _<_ ≡ isTightᵖ''' _#_
    -- isTight-ᵖ''≡ᵖ''' = refl -- this actually holds definitionally, but due to our use of `abstract` for the prop, we need `isPropIsProp`
    abstract isTight-ᵖ''≡ᵖ''' = ΣPathP (refl , isPropIsProp _ _)

    -- isTight-ᵖ''≡ᵖ'''ᵇ : isTightᵖ'' _<_ ≡ isTightᵖ''' (λ x y → ([ x < y ] ⊎ [ y < x ]) , ⊎-isProp (x < y) (y < x) (inl (<-asym x y)))
    -- isTight-ᵖ''≡ᵖ'''ᵇ = refl -- holds definitionally

  _≤'_ : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → hPropRel X X ℓ'
  _≤'_ {_<_ = _<_} x y = ¬ᵖ (y < x)

  module _ {ℓ ℓ' : Level} {A : Type ℓ} (_<_ : hPropRel A A ℓ') (let _≤_ = λ x y → ¬ᵖ (y < x))  where
    abstract
      isTightᵖ≡isAntisymᵖ : isTightᵖ _<_ ≡ isAntisymᵖ _≤_
      isTightᵖ≡isAntisymᵖ = hProp≡ (isoToPath (record
        { fun      = λ <-tight   a b a≤b b≤a → <-tight   a b b≤a a≤b
        ; inv      = λ ≤-antisym a b b≤a a≤b → ≤-antisym a b a≤b b≤a
        ; rightInv = λ f → isProp[] (isAntisymᵖ _≤_) _ f
        ; leftInv  = λ g → isProp[] (isTightᵖ   _<_) _ g
        }))

  module _ {ℓ ℓ' : Level} {A : Type ℓ} (isset : isSet A) (_<_ : hPropRel A A ℓ') (<-asym : [ isAsymᵖ _<_ ])
           (let _≤_ = λ x y → ¬ᵖ (y < x))
           (let _#_ = _#''_ {_<_ = _<_} {<-asym = <-asym}) where
    abstract
      isTightˢ'''≡isAntisymˢ : (isTightˢ''' isset _#_) ≡ (isAntisymˢ isset _≤_)
      isTightˢ'''≡isAntisymˢ = hProp≡ (isoToPath (record
        { fun      = λ #-tight a b a≤b b≤a → #-tight a b (deMorgan₂-back' (b≤a , a≤b))
        ; inv      = λ ≤-antisym a b ¬a#b → let (b≤a , a≤b) = deMorgan₂' ¬a#b in ≤-antisym a b a≤b b≤a
        ; rightInv = λ f → isProp[] (isAntisymˢ  isset _≤_) _ f
        ; leftInv  = λ g → isProp[] (isTightˢ''' isset _#_) _ g
        }))

  abstract
    irrefl+tight-implies-¬#-≡-≡ᵖ : {ℓ : Level} {A : Type ℓ}
                                 → (_#_ : hPropRel A A ℓ) → [ isIrreflᵖ _#_ ] → [ isTightᵖ''' _#_ ]
                                 → ∀ a b → ¬ᵖ (a # b) ≡ (a ≡ₚ b)
    irrefl+tight-implies-¬#-≡-≡ᵖ _#_ #-irrefl #-tight a b = hProp≡ (isoToPath (record
      { fun      = λ ¬[a#b] → #-tight a b ¬[a#b]
      ; inv      = λ a≡b a#b → #-irrefl b (substₚ (λ x → x # b) a≡b a#b)
      ; rightInv = λ f → isProp[] (    a ≡ₚ b) _ f
      ; leftInv  = λ g → isProp[] (¬ᵖ (a #  b)) _ g
      }))

    irrefl+tight-implies-¬#-≡-≡ˢ : {ℓ : Level} {A : Type ℓ}
                                 → (isset : isSet A) → (_#_ : hPropRel A A ℓ) → [ isIrreflᵖ _#_ ] → [ isTightˢ''' isset _#_ ]
                                 → ∀ a b → (¬ [ a # b ]) ≡ (a ≡ b)
    irrefl+tight-implies-¬#-≡-≡ˢ isset _#_ #-irrefl #-tight a b = (isoToPath (record
      { fun      = λ ¬[a#b] → #-tight a b ¬[a#b]
      ; inv      = λ a≡b a#b → #-irrefl b (subst (λ x → [ x # b ]) a≡b a#b)
      ; rightInv = λ f → isset a b _ f
      ; leftInv  = λ g → isProp[] (¬ᵖ (a #  b)) _ g
      }))

    ¬#-≡-≡-implies-dne-on-≡ : {ℓ : Level} {A : Type ℓ}
                             → (_#_ : hPropRel A A ℓ) → (∀ a b → (¬ [ a # b ]) ≡ (a ≡ b))
                             → ∀(a b : A) → (¬ ¬ (a ≡ b)) ≡ (a ≡ b)
    ¬#-≡-≡-implies-dne-on-≡ _#_ ¬#-≡-≡ a b =
      (   ¬ ¬ ( a ≡ b ) ≡⟨ (λ i → ¬ ¬ ¬#-≡-≡ a b (~ i)) ⟩
        ¬ ¬ ¬ [ a # b ] ≡⟨ ¬¬-involutive [ a # b ] ⟩
            ¬ [ a # b ] ≡⟨ ¬#-≡-≡ a b ⟩
                a ≡ b   ∎)

    irrefl+tight-implies-dne-on-≡ˢ : {ℓ : Level} {A : Type ℓ} → (isset : isSet A) → (_#_ : hPropRel A A ℓ)
                                   → [ isIrreflᵖ _#_ ] → [ isTightˢ''' isset _#_ ]
                                   → ∀(a b : A) → (¬ ¬ (a ≡ b)) ≡ (a ≡ b)
    irrefl+tight-implies-dne-on-≡ˢ isset _#_ #-irrefl #-tight = ¬#-≡-≡-implies-dne-on-≡ _#_ (irrefl+tight-implies-¬#-≡-≡ˢ isset _#_ #-irrefl #-tight)


  -- irrefl-implies-tight-≡-dne-on-≡ˢ : {ℓ : Level} {A : Type ℓ} → (isset : isSet A) → (_#_ : hPropRel A A ℓ)
  --                          → [ isIrreflᵖ _#_ ]
  --                          → ∀(a b : A) → ((¬ [ a # b ]) ≡ (a ≡ b)) ≡ ((¬ ¬ (a ≡ b)) ≡ (a ≡ b))
  -- irrefl-implies-tight-≡-dne-on-≡ˢ isset _#_ #-irrefl a b = (isoToPath (record
  --   { fun      = λ x → {! (λ i → ¬ (#-irrefl _ (~ i)) ∙ x  !}
  --   ; inv      = λ x → {!   !}
  --   ; rightInv = λ f → {! isset a b _ f !}
  --   ; leftInv  = λ g → {! isProp[] (¬ᵖ (a #  b)) _ g !}
  --   }))

  -- irrefl+dne-on-≡ˢ-implies-tight : {ℓ : Level} {A : Type ℓ} → (isset : isSet A) → (_#_ : hPropRel A A ℓ)
  --                                → [ isIrreflᵖ _#_ ] → (∀(a b : A) → (¬ ¬ (a ≡ b)) ≡ (a ≡ b))
  --                                → [ isTightˢ''' isset _#_ ]
  -- irrefl+dne-on-≡ˢ-implies-tight isset _#_ #-irrefl dne-on-≡ˢ a b =
  --   ( ¬ [ a # b ] ⇒⟨ {!   !} ⟩
  --     ¬ ¬ (a ≡ b) ⇒⟨ transport (dne-on-≡ˢ a b) ⟩
  --         a ≡ b ◼)

  -- trans→antisymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isTransᵖ R ] → [ isAntisymᵖ R ]
  -- trans→antisymᵖ _≤_ ≤-trans a b a≤b b≤a = {!   !}

  -- isPropΠ2 {! isProp[] (isAntisymᵖ R)  !} {!  !} f
  --  λ f → uncurry-reflects-≡ _ f (uncurry-reflects-≡ _ _ (uncurry-reflects-≡ _ _ {! uncurry (uncurry (uncurry f))  !}))
  -- λ ≤-antisymᵖ i a b a≤b b≤a → {! ≤-antisymᵖ    !} -- transport {!  !} (≤-antisymᵖ a b a≤b b≤a)

  -- isSetΣ ? ? (isAntisymˢ R isset) (isAntisymᵖ R)

  -- (b : (a b₁ : A) → fst (R a b₁) → fst (R b₁ a) → ∥ a ≡ b₁ ∥) → (λ a b₁ a≤b b≤a → ∣ ∣∣-elim (λ c → isset a b₁) (λ x → x) (b a b₁ a≤b b≤a) ∣) ≡ b

  -- transp (λ i → ∥ a ≡ b ∥) i0 (≤-antisymᵖ a b x x₁) != ∣ ∣∣-elim (λ c → isset a b) (λ x₂ → x₂) (≤-antisymᵖ a b x x₁) ∣ of type ∥ a ≡ b ∥
  -- need to show ≡ of these two terms of ∥ a ≡ b ∥:
  --   ≤-antisymᵖ a b a≤b b≤a
  --   ∣ ∣∣-elim (λ c → isset a b) (λ x → x) (≤-antisymᵖ a b a≤b b≤a) ∣
  -- with
  ---  propTruncIsProp (≤-antisymᵖ a b a≤b b≤a) (∣ ∣∣-elim (λ c → isset a b) (λ x → x) (≤-antisymᵖ a b a≤b b≤a) ∣)

  record IsPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor ispartialorder
    field
      isRefl    : [ isReflᵖ    R ]
      isAntisym : [ isAntisymᵖ R ]
      isTrans   : [ isTransᵖ   R ]

  isParialOrderᵖ : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isParialOrderᵖ R =  IsPartialOrder R , φ-prop where
    abstract
      φ-prop : isProp (IsPartialOrder R)
      φ-prop (ispartialorder isRefl₀ isAntisym₀ isTrans₀)
             (ispartialorder isRefl₁ isAntisym₁ isTrans₁) =
        λ i → ispartialorder (isProp[] (isReflᵖ    R) isRefl₀    isRefl₁    i)
                             (isProp[] (isAntisymᵖ R) isAntisym₀ isAntisym₁ i)
                             (isProp[] (isTransᵖ   R) isTrans₀   isTrans₁   i)

-- NOTE: there is `Properties` and `Consequences`
--       the difference somehow is, that we do want to open `Consequences` directly
--       but we do not want to open `Properties` directly, because it might have a name clash
--       e.g. there is `Properties.Group` which clashes with `Cubical.Structures.Group.Group` when opening `Properties`
--       but it is totally fine to open `Properties.Group` directly because it does not export a `Group`
-- TODO: check whether this matches the wording of the (old) standard library
module Consequences where
  open Definitions

  -- Lemma 4.1.7.
  -- Given a strict partial order < on a set X:
  -- 1. we have an apartness relation defined by
  --    x # y := (x < y) ∨ (y < x), and

  #'-isApartnessRel : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → (isSPO : [ isStrictPartialOrderᵖ _<_ ]) → [ isApartnessRelᵖ (_#'_ {_<_ = _<_}) ]
  abstract
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
  abstract
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
  abstract
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
