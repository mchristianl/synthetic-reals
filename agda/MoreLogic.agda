{-# OPTIONS --cubical --no-import-sorts #-}

module MoreLogic where -- hProp logic

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Foundations.Prelude
open import Function.Base using (_∋_)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty renaming (elim to ⊥-elim) renaming (⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Data.Empty.Properties -- isProp⊥

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Base

-- "implicational" reaoning

module Reasoning where

  infix  3 _◼ᵖ
  infixr 2 _⇒ᵖ⟨_⟩_

  _⇒ᵖ⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : hProp ℓ'} {R : hProp ℓ''} → (P : hProp ℓ) → [ P ⇒ Q ] → [ Q ⇒ R ] → [ P ⇒ R ]
  _ ⇒ᵖ⟨ pq ⟩ qr = qr ∘ pq

  _◼ᵖ : ∀{ℓ} (A : hProp ℓ) → [ A ] → [ A ]
  _ ◼ᵖ = λ x → x

  infix  3 _◼
  infixr 2 _⇒⟨_⟩_

  _⇒⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : Type ℓ'} {R : Type ℓ''} → (P : Type ℓ) → (P → Q) → (Q → R) → (P → R)
  _ ⇒⟨ pq ⟩ qr = qr ∘ pq

  _◼ : ∀{ℓ} (A : Type ℓ) → A → A
  _ ◼ = λ x → x


-- lifted versions of ⊥ and ⊤

module Definitions where

  hPropRel : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  hPropRel A B ℓ' = A → B → hProp ℓ'

  ⊥↑ : ∀{ℓ} → hProp ℓ
  ⊥↑ = Lift Empty.⊥ , λ ()

  ⊤↑ : ∀{ℓ} → hProp ℓ
  ⊤↑ = Lift Unit , isOfHLevelLift 1 (λ _ _ _ → tt)

  infix 10 ¬↑_
  ¬↑_ : hProp ℓ → hProp ℓ
  ¬↑_ {ℓ} A = ([ A ] → Lift {j = ℓ} Empty.⊥) , isPropΠ λ _ → isOfHLevelLift 1 Empty.isProp⊥

  isPropΠⁱ : ∀{ℓ ℓ'} {A : Type ℓ} {B : {{p : A}} → Type ℓ'} (h : (x : A) → isProp (B {{x}})) → isProp ({{x : A}} → B {{x}})
  isPropΠⁱ h f g i {{x}} = (h x) (f {{x}}) (g {{x}}) i

  ¬ⁱ_ : ∀{ℓ} → hProp ℓ → hProp ℓ
  ¬ⁱ A = ({{p : [ A ]}} → ⊥⊥) , isPropΠⁱ {A = [ A ]} λ _ → isProp⊥

  ¬-≡-¬ⁱ : ∀{ℓ} (P : hProp ℓ) → ¬ P ≡ ¬ⁱ P
  ¬-≡-¬ⁱ P =
    ⇒∶ (λ f {{p}} → f   p  )
    ⇐∶ (λ f   p   → f {{p}})

module Properties where
  open Reasoning
  open Definitions

  ⊔-identityˡ-↑ : (P : hProp ℓ) → ⊥↑ {ℓ} ⊔ P ≡ P
  ⊔-identityˡ-↑ P =
    ⇒∶ (⊔-elim ⊥↑ P (λ _ → P) (λ ()) (λ x → x))
    ⇐∶ inrᵖ

  ⊔-identityʳ-↑ : (P : hProp ℓ) → P ⊔ ⊥↑ {ℓ} ≡ P
  ⊔-identityʳ-↑ P = ⇔toPath (⊔-elim P ⊥↑ (λ _ → P) (λ x → x) λ ()) inlᵖ

  ⊓-identityˡ-↑ : (P : hProp ℓ) → ⊤↑ {ℓ} ⊓ P ≡ P
  ⊓-identityˡ-↑ _ = ⇔toPath snd  λ x → lift tt , x

  ⊓-identityʳ-↑ : (P : hProp ℓ) → P ⊓ ⊤↑ {ℓ} ≡ P
  ⊓-identityʳ-↑ _ = ⇔toPath fst λ x → x , lift tt

  ¬↑≡¬ : ∀{ℓ} → {P : hProp ℓ} → (¬↑ P) ≡ (¬ P)
  ¬↑≡¬ =
   ⇒∶ (λ ¬↑P P → lower (¬↑P P))
   ⇐∶ (λ  ¬P P → lift  ( ¬P P))

  ¬¬-intro : (P : hProp ℓ) → [ P ] → [ ¬ ¬ P ]
  ¬¬-intro _ p ¬p = ¬p p

  ¬¬-elim : (P : hProp ℓ) → [ ¬ ¬ ¬ P ] → [ ¬ P ]
  ¬¬-elim _ ¬¬¬p p = ¬¬¬p (λ ¬p → ¬p p)

  ¬¬-involutive : (P : hProp ℓ) → ¬ ¬ ¬ P ≡ ¬ P
  ¬¬-involutive P =
   ⇒∶ ¬¬-elim     P
   ⇐∶ ¬¬-intro (¬ P)

  -- taken from https://ncatlab.org/nlab/show/excluded+middle#DoubleNegatedPEM
  -- Double-negated PEM
  weak-LEM : ∀(P : hProp ℓ) → [ ¬ ¬ (P ⊔ ¬ P) ]
  weak-LEM _ ¬[p⊔¬p] = ¬[p⊔¬p] (inrᵖ (λ p → ¬[p⊔¬p] (inlᵖ p)))

  ⊤-introᵖ : {P : hProp ℓ} → [ P ] → P ≡ ⊤↑
  ⊤-introᵖ {ℓ = ℓ} {P = P} p = let
   P⇔⊤↑ : [ P ⇔ ⊤↑ {ℓ} ]
   P⇔⊤↑ = (λ _ → lift tt) , (λ _ → p)
   in ⇔toPath (fst P⇔⊤↑) (snd P⇔⊤↑)

  ⊤-elimᵖ : {P : hProp ℓ} → P ≡ ⊤↑ → [ P ]
  ⊤-elimᵖ {ℓ = ℓ} {P = P} p≡⊤ = (
   [ ⊤↑ {ℓ} ] ⇒⟨ transport ( λ i → [ p≡⊤ (~ i) ]) ⟩
   [ P     ] ◼) (lift tt)

  instanceFunExt : {A : Type ℓ} {B : A → I → Type ℓ'}
                   {f : {{x : A}} → B x i0} {g : {{x : A}} → B x i1}
                 → ({{x : A}} → PathP (B x) (f {{x}}) (g {{x}}))
                 → PathP (λ i → {{x : A}} → B x i) f g
  instanceFunExt p i {{x}} = p {{x}} i

  funExt-⊥ : {A : Type ℓ} (f g : A → Empty.⊥) → f ≡ g
  funExt-⊥ f g = funExt (λ x → ⊥-elim {A = λ _ →  f x ≡ g x} (f x)) -- ⊥-elim needed a hint here

  -- uncurry-preserves-≡
  --   : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
  --   → (f : (a : A) → (b : B a) → C a b)
  --   -------------------------------------------------------------
  --   → ∀ a b → f a b ≡ (uncurry f) (a , b)
  -- uncurry-preserves-≡ f a b = refl

  Σ-preserves-≡ :
        {A : Type ℓ}
        {B : A → Type ℓ'}
        {C : (a : A) → (b : B a) → Type ℓ''}
        {f g : ((a , b) : Σ A B) → C a b}
      → ((a : A) (b : B a) → (f (a , b)) ≡ (g (a , b)))
      → ((ab : Σ A B)      → (f   ab   ) ≡ (g   (ab) ))
  Σ-preserves-≡ p (a , b) = p a b

  uncurry-preserves-≡-back
    : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
    → (f g : (a : A) → (b : B a) → C a b)
    -------------------------------------------------------------
    → (uncurry f ≡ uncurry g) → f ≡ g
  uncurry-preserves-≡-back f g p = funExt (λ x →
    f x                         ≡⟨ refl ⟩
    (λ y → (uncurry f) (x , y)) ≡⟨ ( λ i → λ y → (p i) (x , y)) ⟩
    (λ y → (uncurry g) (x , y)) ≡⟨ refl ⟩
    g x                         ∎)

  -- "constant" version of funExt
  funExt₂ᶜ :
        {A : Type ℓ}
        {B : A → Type ℓ'}
        {C : (a : A) → (b : B a) → Type ℓ''}
        {f g : (a : A) → (b : B a) → C a b}
        → ((a : A) → (b : B a) → (f a b) ≡ (g a b)) → f ≡ g
  funExt₂ᶜ {A = A} {B = B} {C = C} {f = f} {g = g} = (
   ((a : A) (b : B a) → (         f   a   b)  ≡ (         g   a   b) ) ⇒⟨ (λ z → z) ⟩ -- holds definitionally
   ((a : A) (b : B a) → ((uncurry f) (a , b)) ≡ ((uncurry g) (a , b))) ⇒⟨ Σ-preserves-≡ ⟩
   ((ab : Σ A B)      → ((uncurry f)   ab   ) ≡ ((uncurry g) ( ab  ))) ⇒⟨ funExt ⟩
                         (uncurry f)          ≡  (uncurry g)           ⇒⟨ uncurry-preserves-≡-back f g ⟩
                                  f           ≡           g            ◼)

  funExt-⊥₂ : {A B : Type ℓ} (f g : A → B → Empty.⊥) → f ≡ g
  funExt-⊥₂ f g =  funExt₂ᶜ λ a b → ⊥-elim {A = λ _ → f a b ≡ g a b} (g a b)

  implicationᵖ : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ P ⇒ ¬ Q ]
  implicationᵖ {ℓ = ℓ} P Q ¬[p⊓q] p q = ⊥-elim (¬[p⊓q] (p , q))

  contrapositionᵖ : {P Q : hProp ℓ} → ( [ P ⇒ Q ] ) → [ ¬ Q ⇒ ¬ P ]
  contrapositionᵖ f ¬q p = ⊥-elim (¬q (f p))

  -- weak deMorgan laws: only these three hold without further assumptions

  deMorgan₂ : (P Q : hProp ℓ) → [ ¬ (P ⊔ Q) ] → [ ¬ P ⊓ ¬ Q ]
  deMorgan₂ P Q ¬[p⊔q] = (λ p →  ⊥-elim (¬[p⊔q] (inlᵖ p))) , λ q → ⊥-elim (¬[p⊔q] (inrᵖ q))

  deMorgan₂-back : (P Q : hProp ℓ) → [ ¬ P ⊓ ¬ Q ] → [ ¬ (P ⊔ Q) ]
  deMorgan₂-back P Q (¬p , ¬q) p⊔q = ⊔-elim P Q (λ p⊔q → ⊥) ¬p ¬q p⊔q

  deMorgan₁-back : (P Q : hProp ℓ) → [ ¬ P ⊔ ¬ Q ] → [ ¬ (P ⊓ Q) ]
  deMorgan₁-back {ℓ = ℓ} P Q [¬p⊔¬q] (p , q) = ⊔-elim (¬ P) (¬ Q) (λ [¬p⊔¬q] → ⊥) (λ ¬p → ¬p p) (λ ¬q → ¬q q) [¬p⊔¬q]

  -- more logic

  ⊓-⊔-distribʳ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
    → (Q ⊔ R) ⊓ P ≡ (Q ⊓ P) ⊔ (R ⊓ P)
  ⊓-⊔-distribʳ P Q R = (
    (Q ⊔ R) ⊓ P       ≡⟨ ⊓-comm _ _ ⟩
     P ⊓ (Q ⊔ R)      ≡⟨ ⊓-⊔-distribˡ P Q R ⟩
    (P ⊓ Q) ⊔ (P ⊓ R) ≡⟨ ( λ i → ⊓-comm P Q i ⊔ ⊓-comm P R i) ⟩
    (Q ⊓ P) ⊔ (R ⊓ P) ∎)

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

  isProp⊎ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → ¬ᵗ B) ⊎ (B → ¬ᵗ A) → isProp (A ⊎ B)
  isProp⊎ pA pB      X⇒¬Y  (inl x) (inl y) = cong inl (pA x y)
  isProp⊎ pA pB      X⇒¬Y  (inr x) (inr y) = cong inr (pB x y)
  isProp⊎ pA pB (inl A⇒¬B) (inl x) (inr y) = ⊥-elim (A⇒¬B x y)
  isProp⊎ pA pB (inr B⇒¬A) (inl x) (inr y) = ⊥-elim (B⇒¬A y x)
  isProp⊎ pA pB (inl A⇒¬B) (inr x) (inl y) = ⊥-elim (A⇒¬B y x)
  isProp⊎ pA pB (inr B⇒¬A) (inr x) (inl y) = ⊥-elim (B⇒¬A x y)

  module _ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ')
           (X⇒¬Y : [ P ⇒ ¬ Q ] ⊎ [ Q ⇒ ¬ P ]) where

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

  [P⇒¬Q]≡[Q⇒¬P] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → (P ⇒ ¬ Q) ≡ (Q ⇒ ¬ P)
  [P⇒¬Q]≡[Q⇒¬P] P Q =
    ⇒∶ (λ p⇒¬q q p → p⇒¬q p q)
    ⇐∶ (λ q⇒¬p p q → q⇒¬p q p)

  [P⇒¬Q]⇒[Q⇒¬P] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ (P ⇒ ¬ Q) ] → [ (Q ⇒ ¬ P) ]
  [P⇒¬Q]⇒[Q⇒¬P] P Q = pathTo⇒ ([P⇒¬Q]≡[Q⇒¬P] P Q)
