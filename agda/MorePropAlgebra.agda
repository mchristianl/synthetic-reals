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

-- open import Cubical.Foundations.Id using (Id)
-- test20 : {A : Type ℓ} → (a b : A) (p : Id a b) → A
-- test20 a b p = {!!}

open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
open import Cubical.HITs.PropositionalTruncation.Properties using (propTruncIsProp) renaming (elim to ∣∣-elim)

{-
⊔⊎-iso : (P : hProp ℓ) (Q : hProp ℓ') → Iso ([ P ⊔ Q ]) ([ P ] ⊎ [ Q ])
⊔⊎-iso P Q =
  let f : [ P ⊔ Q ] → [ P ] ⊎ [ Q ]
      f = ⊔-elim P Q (λ p → {!!}) (λ x → inl x) (λ y → inr y)
      g : [ P ] ⊎ [ Q ] → [ P ⊔ Q ]
      g p = ∣ p ∣
      γ : section f g
      γ = {!!}
      κ : retract f g
      κ = {!!}
  in iso f g γ κ
-}

-- case₂ᵖ_of_ : ∀ {ℓ ℓ'} {P : hProp ℓ} {Q : hProp ℓ'} → (p : [ P ⊔ Q ]) → {B : [ P ] ⊎ [ Q ] → Type ℓ''} → (∀(q : [ P ] ⊎ [ Q ]) → B q) → B p
-- case₂ᵖ x of f = f x

-- NOTE: hProps need to be explicit arguments (that is not a necessity, but we need to give them completely and not just their witnesses)

{-

⊎-implies-⊔ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ P ] ⊎ [ Q ] → [ P ⊔ Q ]
⊎-implies-⊔ P Q (inl x) = inlᵖ x
⊎-implies-⊔ P Q (inr x) = inrᵖ x

case[_⊔_]_return_of_ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ')
                  → (z : [ P ⊔ Q ])
                  → (R : [ P ⊔ Q ] → hProp ℓ'')
                  → (S : (x : [ P ] ⊎ [ Q ]) → [ R (⊎-implies-⊔ P Q x) ] )
                  → [ R z ]
case[_⊔_]_return_of_ P Q z R S = ⊔-elim P Q R (λ p → S (inl p)) (λ q → S (inr q)) z

-- hProp-union and Σ-Type-union are equivalent when the two disjuncts are disjoint such that one disproves the other and vice versa

⊎-Level : ∀{A : Type ℓ}{B : Type ℓ'} → A ⊎ B → Level
⊎-Level {ℓ  = ℓ } (inl x) = ℓ
⊎-Level {ℓ' = ℓ'} (inr x) = ℓ'

⊎-Type : ∀{A : Type ℓ}{B : Type ℓ'}(x : A ⊎ B) → Type (⊎-Level x)
⊎-Type {A = A} (inl x) = A
⊎-Type {B = B} (inr x) = B

⊎-pred : ∀{A : Type ℓ}{B : Type ℓ'}(x : A ⊎ B) → ⊎-Type x
⊎-pred (inl x) = x
⊎-pred (inr x) = x

⊎-predˡ : ∀{A : Type ℓ}{B : Type ℓ'}(z : A ⊎ B) → {y : A} → z ≡ inl y → A
⊎-predˡ (inl x) {y} p = x
⊎-predˡ (inr x) {y} p = y

-- ⊎-pred-congˡ :
--        {A : Type ℓ}
--        {B : Type ℓ'}
--        {x y : A}
--        → (p : ((A ⊎ B) ∋ inl x) ≡ inl y) →
--        PathP (λ i → A) (⊎-pred {B = B} (inl x)) (⊎-pred {B = B} (inl y))
-- ⊎-pred-congˡ p i = {! ⊎-pred (p i) !}

inl-reflects-≡ : ∀{A : Type ℓ}{B : Type ℓ'} {x y : A} → ((A ⊎ B) ∋ inl x) ≡ inl y → x ≡ y
inl-reflects-≡ {A = A} {B = B} {x = x} {y = y} p =  cong γ p where
  γ : (z : A ⊎ B) → A
  γ (inl y) = y
  γ (inr y) = x

inr-reflects-≡ : ∀{A : Type ℓ}{B : Type ℓ'} {x y : B} → ((A ⊎ B) ∋ inr x) ≡ inr y → x ≡ y
inr-reflects-≡ {A = A} {B = B} {x = x} {y = y} p = cong γ p where
  γ : (z : A ⊎ B) → B
  γ (inl y) = x
  γ (inr y) = y

isProp⊎ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → ¬ B) ⊎ (B → ¬ A) → isProp (A ⊎ B)
isProp⊎ pA pB      X⇒¬Y  (inl x) (inl y) = cong inl (pA x y)
isProp⊎ pA pB      X⇒¬Y  (inr x) (inr y) = cong inr (pB x y)
isProp⊎ pA pB (inl A⇒¬B) (inl x) (inr y) = ⊥-elim (A⇒¬B x y)
isProp⊎ pA pB (inr B⇒¬A) (inl x) (inr y) = ⊥-elim (B⇒¬A y x)
isProp⊎ pA pB (inl A⇒¬B) (inr x) (inl y) = ⊥-elim (A⇒¬B y x)
isProp⊎ pA pB (inr B⇒¬A) (inr x) (inl y) = ⊥-elim (B⇒¬A x y)

-- open import Cubical.HITs.PropositionalTruncation.Base

module _ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ')
         (X⇒¬Y : [ P ⇒ ¬ᵖ Q ] ⊎ [ Q ⇒ ¬ᵖ P ]) where

  isProp-P⊎Q : isProp ([ P ] ⊎ [ Q ])
  isProp-P⊎Q = isProp⊎ (isProp[] P) (isProp[] Q) X⇒¬Y

  P⊎Qᵖ : hProp (ℓ-max ℓ ℓ')
  P⊎Qᵖ = ([ P ] ⊎ [ Q ]) , isProp-P⊎Q

  -- ⊎-implies-⊔' : [ P⊎Qᵖ ] → [ P ⊔ Q ]
  -- ⊎-implies-⊔' x = ∣ x ∣

  ⊔-implies-⊎ : [ P ⊔ Q ] → [ P⊎Qᵖ ]
  ⊔-implies-⊎ x = ⊔-elim P Q (λ x → ([ P ] ⊎ [ Q ]) , isProp-P⊎Q) (λ p → inl p) (λ q → inr q) x

  ⊔⊎-equiv : [ P⊎Qᵖ ⇔ P ⊔ Q ]
  ⊔⊎-equiv = ⊎-implies-⊔ P Q , ⊔-implies-⊎

  ⊔⊎-≡ : P⊎Qᵖ ≡ P ⊔ Q
  ⊔⊎-≡ with ⊔⊎-equiv
  ... | p , q = ⇔toPath p q


-- _ = {!⊔⊎-≡!}

-- ⊔-elim : (P : hProp ℓ)
--          (Q : hProp ℓ')
--          (R : [ P ⊔ Q ] → hProp ℓ'')
--        → (∀ x → [ R (inl x) ])
--        → (∀ y → [ R (inr y) ])
--        → (∀ z → [ R z ])
-- ⊔-elim _ _ R P⇒R Q⇒R = PropTrunc.elim (snd ∘ R) (⊎.elim P⇒R Q⇒R)

--  ⇒∶ {! (⊔-elim P Q (\ _ → (Q ⊔ P)) inr inl) !}
--  ⇐∶ {! (⊔-elim Q P (\ _ → (P ⊔ Q)) inr inl) !}

-}

module Definitions where
  isReflᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isReflᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = (a : A) → [ R a a ]
    φ-prop : isProp φ
    φ-prop = isPropΠ (λ(a : A) → isProp[] (R a a))

  IsRefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsRefl R = [ isReflᵖ R ]

  isIrreflᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isIrreflᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = (a : A) → [ ¬ᵖ (R a a) ]
    φ-prop : isProp φ
    φ-prop = isPropΠ (λ(a : A) → isProp[] (¬ᵖ (R a a)))

  IsIrrefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsIrrefl R = [ isIrreflᵖ R ]

  isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isCotransᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
    where
      φ : Type (ℓ-max ℓ ℓ')
      φ = (a b : A) → [ R a b ⇒ (∀[ x ∶ A ] (R a x) ⊔ (R x b)) ]
      φ-prop : isProp φ
      φ-prop = isPropΠ2 λ a b → snd (R a b ⇒ (∀[ x ∶ A ] (R a x) ⊔ (R x b)))

  IsCotrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsCotrans R = [ isCotransᵖ R ]

  isSymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isSymᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = (a b : A) → [ R a b ⇒ R b a ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ R b a))

  IsSym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsSym R = [ isSymᵖ R ]

  -- NOTE: we have ∀ a b → [ ¬ (R a b ⊓ R b a) ] which is stronger than [ R a b ⇒ ¬ R b a ]
  --       because it implies also [ ¬ R b a ⇒ R a b ]

  isAsymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isAsymᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = (a b : A) → [ R a b ⇒ ¬ᵖ R b a ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ ¬ᵖ R b a))

  IsAsym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsAsym R = [ isAsymᵖ R ]

  isAsymᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isAsymᵖ' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = (a b : A) → [ ¬ᵖ (R a b ⊓ R b a) ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ (R a b ⊓ R b a)))

  IsAsym' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsAsym' R = [ isAsymᵖ' R ]

  -- isAsym'⇒ᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isAsymᵖ' R ] → [ isAsymᵖ R ]
  -- isAsym'⇒ᵖ _<_ <-asym a b = fst (¬-⊓-distrib (a < b) (b < a) (<-asym a b))
  --
  -- isAsymᵖ⇒' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isAsymᵖ R ] → [ isAsymᵖ' R ]
  -- isAsymᵖ⇒' _<_ <-asym a b (a<b , b<a) = <-asym a b a<b b<a

  isAsymᵖ≡' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → isAsymᵖ R ≡ isAsymᵖ' R
  isAsymᵖ≡' _<_ =
    ⇒∶ (λ{ <-asym a b (a<b , b<a) → <-asym a b a<b b<a })
    ⇐∶ (λ  <-asym a b → fst (¬-⊓-distrib (a < b) (b < a) (<-asym a b)) )

  -- NOTE: this is tricky somehow and might not be equivalent to the other ones
  --
  -- isAsymᵖ² : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAsymᵖ² {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ ¬ᵖ R b a ⇒ R a b ]
  --   φ-prop : isProp φ
  --   φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ R b a ⇒ R a b))
  --
  -- isAsymᵖ⇒² : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isAsymᵖ' R ] → [ isAsymᵖ² R ]
  -- isAsymᵖ⇒² _<_ <-asym a b ¬b<a = {! ¬-⊓-distrib (a < b) (b < a) (<-asym a b)  !}

  -- do we have `R a b ≡ ¬ᵖ R b a` ?

  -- isAsymᵖ-back : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  -- isAsymᵖ-back {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
  --   φ : Type (ℓ-max ℓ ℓ')
  --   φ = (a b : A) → [ ¬ᵖ R b a ⇒ R a b ]
  --   φ-prop : isProp φ
  --   φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ R b a ⇒ R a b))

  -- foo : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isAsymᵖ' R ] → ∀ a b → [ ¬ᵖ R a b ⇒ R b a ]
  -- foo _<_ <-asym a b = {! contraposition  !}

  -- isAsymᵖ⇔isAsymᵖ-back : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → isAsymᵖ' R ≡ isAsymᵖ-back R
  -- isAsymᵖ⇔isAsymᵖ-back _<_ =
  --   ⇒∶ (λ f a b → {! [P⇒¬Q]⇒[Q⇒¬P] _ _ (f a b)  !})
  --   ⇐∶ (λ f a b → {! [P⇒¬Q]⇒[Q⇒¬P] (b < a) (a < b)  !})

  isTransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTransᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop
    where
      φ : Type (ℓ-max ℓ ℓ')
      φ = (a b c : A) → [ R a b ⇒ R b c ⇒ R a c ]
      φ-prop : isProp φ
      φ-prop = isPropΠ3 λ a b c → snd (R a b ⇒ R b c ⇒ R a c)

  IsTrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTrans R = [ isTransᵖ R ]

  irrefl+trans→asym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ R ]
  irrefl+trans→asym _<_ isIrrefl isTrans a b a<b b<a = isIrrefl _ (isTrans _ _ _ a<b b<a)

  irrefl+trans→asym' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → [ isIrreflᵖ R ] → [ isTransᵖ R ] → [ isAsymᵖ' R ]
  irrefl+trans→asym' _<_ isIrrefl isTrans a b (a<b , b<a) = isIrrefl _ (isTrans _ _ _ a<b b<a)

  record IsApartnessRel {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') : Type (ℓ-max ℓ ℓ') where
    constructor isapartnessrel
    field
      isIrrefl  : [ isIrreflᵖ  R ]
      isSym     : [ isSymᵖ     R ]
      isCotrans : [ isCotransᵖ R ]

  isApartnessRel : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isApartnessRel R = IsApartnessRel R , φ-prop where
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

  isStrictParialOrder : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isStrictParialOrder R = IsStrictPartialOrder R , φ-prop where
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

  isPreorder : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isPreorder R =     IsPreorder R , φ-prop where
    φ-prop : isProp (IsPreorder R)
    φ-prop (ispreorder isRefl₀ isTrans₀)
           (ispreorder isRefl₁ isTrans₁) =
      λ i → ispreorder (isProp[] (isReflᵖ  R) isRefl₀  isRefl₁  i)
                       (isProp[] (isTransᵖ R) isTrans₀ isTrans₁ i)

  isAntisymᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isAntisymᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → [ R a b ⇒ R b a ⇒ a ≡ₚ b ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isProp[] (R a b ⇒ R b a ⇒ a ≡ₚ b))

  IsAntisym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsAntisym R = [ isAntisymᵖ R ]

  isAntisymˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isAntisymˢ {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → [ R a b ] → [ R b a ] → a ≡ b
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isPropΠ2 λ a<b b<a → isset a b)

  IsAntisymˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsAntisymˢ isset R = [ isAntisymˢ isset R ]

  -- NOTE: we also have isProp→Iso in `Cubical.Foundations.Isomorphism`
  isAntisym-ˢ≡ᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isAntisymˢ isset R ≡ isAntisymᵖ R
  isAntisym-ˢ≡ᵖ isset R = hProp≡ (isoToPath (record -- ΣPathP
    { fun      = λ ≤-antisymˢ a b a≤b b≤a → ∣ ≤-antisymˢ a b a≤b b≤a ∣
    ; inv      = λ ≤-antisymᵖ a b a≤b b≤a → ∣∣-elim (λ c → isset a b) (λ x → x) (≤-antisymᵖ a b a≤b b≤a)
    ; rightInv = λ f → isProp[] (isAntisymᵖ       R) _ f
    ; leftInv  = λ g → isProp[] (isAntisymˢ isset R) _ g
    })) -- , {! isPropIsProp {?} {?} ? ?  !}) -- isPropIsProp

  isTightᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTightᵖ {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → [ ¬ᵖ R a b ⇒ ¬ᵖ R b a ⇒ a ≡ₚ b ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ R a b ⇒ ¬ᵖ R b a ⇒ a ≡ₚ b))

  IsTight : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTight R = [ isTightᵖ R ]

  isTightˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTightˢ {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → [ ¬ᵖ R a b ] → [ ¬ᵖ R b a ] → a ≡ b
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isPropΠ2 λ ¬a<b ¬b<a → isset a b)

  IsTightˢ : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTightˢ isset R = [ isTightˢ isset R ]

  isTight-ˢ≡ᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isTightˢ isset R ≡ isTightᵖ R
  isTight-ˢ≡ᵖ isset R = hProp≡ (isoToPath (record -- ΣPathP
    { fun      = λ ≤-tightˢ a b a≤b b≤a → ∣ ≤-tightˢ a b a≤b b≤a ∣
    ; inv      = λ ≤-tightᵖ a b a≤b b≤a → ∣∣-elim (λ c → isset a b) (λ x → x) (≤-tightᵖ a b a≤b b≤a)
    ; rightInv = λ f → isProp[] (isTightᵖ       R) _ f
    ; leftInv  = λ g → isProp[] (isTightˢ isset R) _ g
    }))

  isTightᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTightᵖ' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → [ ¬ᵖ (R a b ⊔ R b a) ⇒ a ≡ₚ b ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isProp[] (¬ᵖ (R a b ⊔ R b a) ⇒ a ≡ₚ b))

  IsTight' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTight' R = [ isTightᵖ' R ]

  isTightˢ' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTightˢ' {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → [ ¬ᵖ (R a b ⊔ R b a) ] → a ≡ b
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isPropΠ λ ¬[a<b⊔b<a] → isset a b)

  IsTightˢ' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTightˢ' isset R = [ isTightˢ' isset R ]

  isTight-ˢ'≡ᵖ' : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → isTightˢ' isset R ≡ isTightᵖ' R
  isTight-ˢ'≡ᵖ' isset _≤_ = hProp≡ (isoToPath (record -- ΣPathP
    { fun      = λ ≤-tightˢ' a b ¬[a≤b⊔b≤a] → ∣ ≤-tightˢ' a b ¬[a≤b⊔b≤a] ∣
    ; inv      = λ ≤-tightᵖ' a b ¬[a≤b⊔b≤a] → ∣∣-elim (λ c → isset a b) (λ x → x) (≤-tightᵖ' a b ¬[a≤b⊔b≤a])
    ; rightInv = λ f → isProp[] (isTightᵖ'       _≤_) _ f
    ; leftInv  = λ g → isProp[] (isTightˢ' isset _≤_) _ g
    }))

  isTightᵖ'' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTightᵖ'' {ℓ} {ℓ'} {A = A} R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → ¬ ([ R a b ] ⊎ [ R b a ]) → [ a ≡ₚ b ]
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isPropΠ λ p → isProp[] (a ≡ₚ b))

  IsTight'' : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTight'' R = [ isTightᵖ'' R ]

  isTightˢ'' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isTightˢ'' {ℓ} {ℓ'} {A = A} isset R = φ , φ-prop where
    φ : Type (ℓ-max ℓ ℓ')
    φ = ∀ a b → ¬ ([ R a b ] ⊎ [ R b a ]) → a ≡ b
    φ-prop : isProp φ
    φ-prop = isPropΠ2 (λ a b → isPropΠ λ ¬[a<b⊎b<a] → isset a b)

  IsTightˢ'' : {ℓ ℓ' : Level} {A : Type ℓ} → isSet A → (R : hPropRel A A ℓ') → Type (ℓ-max ℓ ℓ')
  IsTightˢ'' isset R = [ isTightˢ'' isset R ]

  -- TODO: this is not what we want
  isTight-ˢ''≡ᵖ'' : {ℓ ℓ' : Level} {A : Type ℓ} → (isset : isSet A) → (R : hPropRel A A ℓ') → [ isIrreflᵖ R ] → isTightˢ'' isset R ≡ isTightᵖ'' R
  isTight-ˢ''≡ᵖ'' {A = A} isset _≤_ ≤-irrefl = hProp≡ (isoToPath (record -- ΣPathP
    { fun      = λ ≤-tightˢ'' a b ¬[a≤b⊎b≤a] → ∣ ≤-tightˢ'' a b ¬[a≤b⊎b≤a] ∣
    ; inv      = λ ≤-tightᵖ'' a b ¬[a≤b⊎b≤a] → ∣∣-elim (λ c → isset a b) (λ x → x) (≤-tightᵖ'' a b ¬[a≤b⊎b≤a])
    ; rightInv = λ f → isProp[] (isTightᵖ''       _≤_) _ f
    ; leftInv  = λ g → isProp[] (isTightˢ'' isset _≤_) _ g
    }))


  -- TODO: isTightᵖ _#_ ≡ isAntisymˢ _≤_

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

  isParialOrder : {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
  isParialOrder R =  IsPartialOrder R , φ-prop where
    φ-prop : isProp (IsPartialOrder R)
    φ-prop (ispartialorder isRefl₀ isAntisym₀ isTrans₀)
           (ispartialorder isRefl₁ isAntisym₁ isTrans₁) =
      λ i → ispartialorder (isProp[] (isReflᵖ    R) isRefl₀    isRefl₁    i)
                           (isProp[] (isAntisymᵖ R) isAntisym₀ isAntisym₁ i)
                           (isProp[] (isTransᵖ   R) isTrans₀   isTrans₁   i)

  _#'_ : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → hPropRel X X ℓ'
  _#'_ {_<_ = _<_} x y = (x < y) ⊔ (y < x)

  _≤'_ : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → hPropRel X X ℓ'
  _≤'_ {_<_ = _<_} x y = ¬ᵖ (y < x)

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

  #'-isApartnessRel : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → (isSPO : IsStrictPartialOrder _<_) → IsApartnessRel (_#'_ {_<_ = _<_})
  #'-isApartnessRel {ℓ} {ℓ'} {X = X} {_<_ = _<_} isSPO =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
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
  #'-isApartnessRel' : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → {IsStrictPartialOrder _<_} → IsApartnessRel (_#'_ {_<_ = _<_})
  #'-isApartnessRel' {X = X} {_<_ = _<_} {isSPO} =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
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

  ≤-isPreorder' : ∀{X : Type ℓ} {_<_ : hPropRel X X ℓ'} → {IsStrictPartialOrder _<_} → IsPreorder (_≤'_ {_<_ = _<_})
  ≤-isPreorder' {X = X} {_<_ = _<_} {isSPO} =
    let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
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
