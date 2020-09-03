{-# OPTIONS --cubical --no-import-sorts #-}

module MoreLogic where -- hProp logic

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
-- open import Cubical.Data.Sigma.Properties
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

open import Utils

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

  -- hProp-syntax for Σ types of hProps to omit propositional truncation
  -- this should be equivalent to ∃! from the standard library but ∃! is not an hProp
  -- proof sketch:
  --   `∃! A B = isContr (Σ A B) = Σ[ x ∈ Σ A B ] ∀(  y : Σ A B) → x ≡ y`
  --   `Σᵖ[]-syntax A B          ≈ Σ[ c ∈ Σ A B ] ∀(x y : Σ A B) → x ≡ y`

  Σᵖ[]-syntax : ∀{ℓ'} → {A : hProp ℓ'} → ([ A ] → hProp ℓ) → hProp _
  Σᵖ[]-syntax {A = A} P = Σ [ A ] ([_] ∘ P) , isPropΣ (isProp[] A) (isProp[] ∘ P)

  syntax Σᵖ[]-syntax (λ x → P) = Σᵖ[ x ] P

  Σᵖ[∶]-syntax : ∀{ℓ'} → {A : hProp ℓ'} → ([ A ] → hProp ℓ) → hProp _
  Σᵖ[∶]-syntax {A = A} P = Σ [ A ] ([_] ∘ P) , isPropΣ (isProp[] A) (isProp[] ∘ P)

  syntax Σᵖ[∶]-syntax {A = A} (λ x → P) = Σᵖ[ x ∶ A ] P

  isProp⊎ˡ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → ¬ᵗ B) → isProp (A ⊎ B)
  isProp⊎ˡ pA pB A⇒¬B (inl x) (inl y) = cong inl (pA x y)
  isProp⊎ˡ pA pB A⇒¬B (inr x) (inr y) = cong inr (pB x y)
  isProp⊎ˡ pA pB A⇒¬B (inl x) (inr y) = ⊥-elim (A⇒¬B x y)
  isProp⊎ˡ pA pB A⇒¬B (inr x) (inl y) = ⊥-elim (A⇒¬B y x)

  -- hProp-syntax for disjoint unions to omit propositional truncation
  ⊎ᵖ-syntax : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → {[ P ] → ¬ᵗ [ Q ]} → hProp _
  ⊎ᵖ-syntax P Q {P⇒¬Q} = ([ P ] ⊎ [ Q ]) , isProp⊎ˡ (isProp[] P) (isProp[] Q) P⇒¬Q

  syntax ⊎ᵖ-syntax P Q {P⇒¬Q} = [ P⇒¬Q ] P ⊎ᵖ Q

  -- hProp-syntax for equality on sets to omit propositional truncation
  ≡ˢ-syntax : {ℓ : Level} {A : Type ℓ} → A → A → {isset : isSet A} → hProp ℓ
  ≡ˢ-syntax a b {isset} = (a ≡ b) , isset a b

  syntax ≡ˢ-syntax a b {isset} = [ isset ] a ≡ˢ b

  -- for a function, to be an hProp, it suffices that the result is an hProp
  -- so in principle we might inject any non-hProps as arguments with `_ᵗ⇒_`
  _ᵗ⇒_ : (A : Type ℓ) → (B : hProp ℓ') → hProp _
  A ᵗ⇒ B = (A → [ B ]) , isPropΠ λ _ → isProp[] B

  infixr 6 _ᵗ⇒_

  -- lifting of hProps to create "universe-homogeneous" pathes
  --   this is not necessary when using _⇔_ which is universe-inhomogeneous
  --   because `_⇔_` can "cross" universes, where `PathP` needs to stay in the same universe

  Liftᵖ : ∀{i j : Level} → hProp i → hProp (ℓ-max i j)
  Liftᵖ {i} {j} P = Lift {i} {j} [ P ] , λ{ (lift p) (lift q) → λ i → lift (isProp[] P p q i) }

  liftᵖ : ∀{i j : Level} → (P : hProp i) → [ P ] → [ Liftᵖ {i} {j} P ]
  liftᵖ P p = lift p

  unliftᵖ : ∀{i j : Level} → (P : hProp i) → [ Liftᵖ {i} {j} P ] → [ P ]
  unliftᵖ P (lift p) = p

  ⊥↑ : ∀{ℓ} → hProp ℓ
  ⊥↑ = Lift Empty.⊥ , λ ()

  ⊤↑ : ∀{ℓ} → hProp ℓ
  ⊤↑ = Lift Unit , isOfHLevelLift 1 (λ _ _ _ → tt)

  infix 10 ¬↑_
  ¬↑_ : hProp ℓ → hProp ℓ
  ¬↑_ {ℓ} A = ([ A ] → Lift {j = ℓ} Empty.⊥) , isPropΠ λ _ → isOfHLevelLift 1 Empty.isProp⊥

  -- isPropΠ for a function with an instance argument
  isPropΠⁱ : ∀{ℓ ℓ'} {A : Type ℓ} {B : {{p : A}} → Type ℓ'} (h : (x : A) → isProp (B {{x}})) → isProp ({{x : A}} → B {{x}})
  isPropΠⁱ h f g i {{x}} = (h x) (f {{x}}) (g {{x}}) i

  -- negation with an instance argument
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

  ¬¬-involutiveᵖ : (P : hProp ℓ) → ¬ ¬ ¬ P ≡ ¬ P
  abstract
    ¬¬-involutiveᵖ P =
     ⇒∶ ¬¬-elim     P
     ⇐∶ ¬¬-intro (¬ P)

  ¬¬-involutive : (A : Type ℓ) → (¬ᵗ ¬ᵗ ¬ᵗ A) ≡ (¬ᵗ A)
  abstract
    ¬¬-involutive A = isoToPath λ where
      .Iso.fun      ¬¬¬a a → ¬¬¬a (λ ¬a → ¬a a)
      .Iso.inv      ¬a ¬¬a → ¬¬a ¬a
      .Iso.rightInv ¬a     → refl
      -- the following proof is `... ≡ ¬¬¬a` and uses funext to reduce this to a proof `∀ x → ... x ≡ ¬¬¬a x`
      -- but this does not matter, since we have `¬¬¬a x` which is `⊥` and then we can use ⊥-elim to obtain whatever is necessary
      -- `⊥-elim` needed a detailed hint what to produce and this might not be the most elegant way to proof this
      .Iso.leftInv  ¬¬¬a   →
        funExt {A = (¬ᵗ ¬ᵗ A)} {B = λ _ i → ⊥⊥} {f = (λ ¬¬a → ¬¬a (λ a → ¬¬¬a (λ ¬a → ¬a a)))} {g = ¬¬¬a}
               (λ x → ⊥-elim {A = λ _ → (x (λ a → ¬¬¬a (λ ¬a → ¬a a)) ≡ ¬¬¬a x)} (¬¬¬a x))

  -- taken from https://ncatlab.org/nlab/show/excluded+middle#DoubleNegatedPEM
  -- Double-negated PEM
  weak-LEM : ∀(P : hProp ℓ) → [ ¬ ¬ (P ⊔ ¬ P) ]
  weak-LEM _ ¬[p⊔¬p] = ¬[p⊔¬p] (inrᵖ (λ p → ¬[p⊔¬p] (inlᵖ p)))

  weak-LEMᵗ : ∀(P : Type ℓ) → ¬ᵗ ¬ᵗ (P ⊎ (¬ᵗ P))
  weak-LEMᵗ _ ¬[p⊔¬p] = ¬[p⊔¬p] (inr (λ p → ¬[p⊔¬p] (inl p)))

  ⊤-introᵖ : {P : hProp ℓ} → [ P ] → P ≡ ⊤↑
  ⊤-introᵖ {ℓ = ℓ} {P = P} p = let
    P⇔⊤↑ : [ P ⇔ ⊤↑ {ℓ} ]
    P⇔⊤↑ = (λ _ → lift tt) , (λ _ → p)
    in ⇔toPath (fst P⇔⊤↑) (snd P⇔⊤↑)

  ⊤-elimᵖ : {P : hProp ℓ} → P ≡ ⊤↑ → [ P ]
  ⊤-elimᵖ {ℓ = ℓ} {P = P} p≡⊤ = (
    [ ⊤↑ {ℓ} ] ⇒⟨ transport ( λ i → [ p≡⊤ (~ i) ]) ⟩
    [ P     ] ◼) (lift tt)

  contraposition : (P : hProp ℓ) (Q : hProp ℓ') → [ P ⇒ Q ] → [ ¬ Q ⇒ ¬ P ]
  contraposition P Q f ¬q p = ⊥-elim (¬q (f p))

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

  Σ-reflects-≡ :
        {A : Type ℓ}
        {B : A → Type ℓ'}
        {a b : Σ A B}
      → a ≡ b
      → Σ[ p ∈ (fst a ≡ fst b) ] transport (λ i → B (p i)) (snd a) ≡ snd b
      --  Σ[ q ∈ (fst a ≡ fst b) ] (PathP (λ i → B (q i)) (snd a) (snd b))
  Σ-reflects-≡ a≡b with PathΣ→ΣPathTransport _ _ a≡b
  ... | fst≡fst , snd≡snd = fst≡fst , snd≡snd

  uncurry-reflects-≡
    : {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
    → (f g : (a : A) → (b : B a) → C a b)
    -------------------------------------------------------------
    → (uncurry f ≡ uncurry g) → f ≡ g
  uncurry-reflects-≡ f g p = funExt (λ x →
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
                         (uncurry f)          ≡  (uncurry g)           ⇒⟨ uncurry-reflects-≡ f g ⟩
                                  f           ≡           g            ◼)

  funExt-⊥₂ : {A B : Type ℓ} (f g : A → B → Empty.⊥) → f ≡ g
  funExt-⊥₂ f g =  funExt₂ᶜ λ a b → ⊥-elim {A = λ _ → f a b ≡ g a b} (g a b)

  -- weak deMorgan laws: only these three hold without further assumptions

  deMorgan₂ : (P Q : hProp ℓ) → [ ¬ (P ⊔ Q) ] → [ ¬ P ⊓ ¬ Q ]
  abstract deMorgan₂ P Q ¬[p⊔q] = (λ p →  ⊥-elim (¬[p⊔q] (inlᵖ p))) , λ q → ⊥-elim (¬[p⊔q] (inrᵖ q))

  deMorgan₂-back : (P Q : hProp ℓ) → [ ¬ P ⊓ ¬ Q ] → [ ¬ (P ⊔ Q) ]
  abstract deMorgan₂-back P Q (¬p , ¬q) p⊔q = ⊔-elim P Q (λ p⊔q → ⊥) ¬p ¬q p⊔q

  deMorgan₁-back : (P Q : hProp ℓ) → [ ¬ P ⊔ ¬ Q ] → [ ¬ (P ⊓ Q) ]
  abstract deMorgan₁-back {ℓ = ℓ} P Q [¬p⊔¬q] (p , q) = ⊔-elim (¬ P) (¬ Q) (λ [¬p⊔¬q] → ⊥) (λ ¬p → ¬p p) (λ ¬q → ¬q q) [¬p⊔¬q]

  ¬-⊓-distrib  : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ (P ⇒ ¬ Q) ⊓ (Q ⇒ ¬ P) ]
  ¬-⊓-distrib P Q ¬p⊓q = (λ p q → ¬p⊓q (p , q)) , (λ q p → ¬p⊓q (p , q))

  implicationᵖ : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ P ⇒ ¬ Q ]
  implicationᵖ {ℓ = ℓ} P Q ¬[p⊓q] p q = ⊥-elim (¬[p⊓q] (p , q))

  contrapositionᵖ : (P Q : hProp ℓ) → [ P ⇒ Q ] → [ ¬ Q ⇒ ¬ P ]
  abstract contrapositionᵖ P Q f ¬q p = ⊥-elim (¬q (f p))

  -- Q and P are disjoint if P ⇒ ¬ Q or equivalently Q ⇒ ¬ P

  abstract
    -- we have that  (P ⇒ ¬ Q)   ≡ (Q ⇒ ¬ P)
    -- normalizes to (P ⇒ Q ⇒ ⊥) ≡ (Q ⇒ P ⇒ ⊥)
    -- which is just flipping of the arguments
    [P⇒¬Q]≡[Q⇒¬P] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → (P ⇒ ¬ Q) ≡ (Q ⇒ ¬ P)
    [P⇒¬Q]≡[Q⇒¬P] P Q = ⇒∶ flip ⇐∶ flip
      -- ⇒∶ (λ p⇒¬q q p → p⇒¬q p q)
      -- ⇐∶ (λ q⇒¬p p q → q⇒¬p q p)

    [P⇒¬Q]⇒[Q⇒¬P] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ (P ⇒ ¬ Q) ] → [ (Q ⇒ ¬ P) ]
    [P⇒¬Q]⇒[Q⇒¬P] P Q = flip -- pathTo⇒ ([P⇒¬Q]≡[Q⇒¬P] P Q)

    [P⇒¬Q]≡¬[P⊓Q] : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → (P ⇒ ¬ Q) ≡ ¬ (P ⊓ Q)
    [P⇒¬Q]≡¬[P⊓Q] P Q = ⇒∶ uncurry ⇐∶ curry
      -- ⇒∶ (λ{ p⇒¬q (p , q) →  p⇒¬q   p   q })
      -- ⇐∶ (λ ¬[p⊓q] p   q  → ¬[p⊓q] (p , q) )

  -- [¬P⇒Q]⇒[¬Q⇒¬¬P]
  -- [¬P⇒¬¬Q]≡[¬Q⇒¬¬P]
  --         ≡¬[¬P⊓¬Q]
  --         ≡¬¬[P⊔Q]
  -- [¬P≡Q]⇒¬[P⊓Q]≡¬[P⊓¬P]

  ¬[P⊓¬P] : ∀{ℓ} (P : hProp ℓ) → [ ¬ (P ⊓ ¬ P) ]
  ¬[P⊓¬P] P (p , ¬p) = ¬p p

  -- NOTE: I think that we do not have ¬ P ≡ ¬ Q → P ≡ Q
  --       since this might be equivalent to some LEM ?

  -- ¬-reflects-≡ : ∀{ℓ} (P Q : hProp ℓ) → ¬ P ≡ ¬ Q → P ≡ Q
  -- ¬-reflects-≡ P Q ¬p≡¬q with Σ-reflects-≡ ¬p≡¬q
  -- ... | fst≡fst , snd≡snd = ΣPathP ({!   !} , {!   !})
  --
  -- -- (∀ x → P x ≡ P y) → x ≡ y
  --
  -- postulate dne : ∀{ℓ} (P : hProp ℓ) → ¬ ¬ P ≡ P
  --
  -- ¬-isEquiv : ∀ ℓ → isEquiv (¬_ {ℓ = ℓ})
  -- ¬-isEquiv ℓ = λ where
  --   .equiv-proof P → ((¬ P) , dne P) , λ{ (Q , ¬Q≡P) →
  --     let γ = {! isPropIsProp (isProp[] Q) (isProp[] Q)  !}
  --     in {!   !} }

  -- fst (fst (equiv-proof (¬-isEquiv ℓ) P)) = ¬ P
  -- snd (fst (equiv-proof (¬-isEquiv ℓ) P)) = dne P
  -- snd (equiv-proof (¬-isEquiv ℓ) P) (Q , ¬Q≡P) = {!   !}

  -- ¬[P⊓¬P]≡¬[P⊓Q]⇒[¬P≡Q] : ∀{ℓ } (P Q : hProp ℓ) → [ ¬ (P ⊓ ¬ P) ] ≡ [ ¬ (P ⊓ Q) ] → [ P ] ≡ [ ¬ Q ]
  -- ¬[P⊓¬P]≡¬[P⊓Q]⇒[¬P≡Q] P Q p = {! [P⇒¬Q]≡¬[P⊓Q] P Q  !}
  --
  -- ¬[P⊓¬P]≡¬[P⊓Q]≡[P⇒¬Q]≡[P⇒¬¬P]

  -- foo : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ (P ⇒ ¬ Q) ] → [ (¬ Q ⇒ P) ] → P ≡ ¬ Q

  -- bar : ∀{ℓ} (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → P ≡ ¬ Q
  -- -- ¬-⊓-distrib P Q ¬p⊓q
  -- bar P Q ¬p⊓q = let r1 : [ (P ⇒ ¬ Q) ⊓ (Q ⇒ ¬ P) ]
  --                    r1 =
  --                    r2 : [ (Q ⇒ ¬ P) ⊓ (P ⇒ ¬ Q) ]
  --                    r2 =
  --                in {! ¬-⊓-distrib Q P (transport (λ i → [ ¬ ⊓-comm P Q i ]) ¬p⊓q)  !}

  -- more logic

  ⊓-⊔-distribʳ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
    → (Q ⊔ R) ⊓ P ≡ (Q ⊓ P) ⊔ (R ⊓ P)
  ⊓-⊔-distribʳ P Q R = (
    (Q ⊔ R) ⊓ P       ≡⟨ ⊓-comm _ _ ⟩
     P ⊓ (Q ⊔ R)      ≡⟨ ⊓-⊔-distribˡ P Q R ⟩
    (P ⊓ Q) ⊔ (P ⊓ R) ≡⟨ ( λ i → ⊓-comm P Q i ⊔ ⊓-comm P R i) ⟩
    (Q ⊓ P) ⊔ (R ⊓ P) ∎)

  -- NOTE: this is in the standard library
  -- ⊓-∀-distrib :  (P : A → hProp ℓ) (Q : A → hProp ℓ')
  --   → (∀[ a ∶ A ] P a) ⊓ (∀[ a ∶ A ] Q a) ≡ (∀[ a ∶ A ] (P a ⊓ Q a))
  -- ⊓-∀-distrib P Q =
  --   ⇒∶ (λ {(p , q) a → p a , q a})
  --   ⇐∶ λ pq → (fst ∘ pq ) , (snd ∘ pq)

  -- well, we do not have `∀-⊔-distrib`
  -- ∀-⊔-distrib : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} → (P : A → hProp ℓ') → (Q : A → hProp ℓ'')
  --             → ((∀[ x ∶ A ] P x) ⊔ (∀[ x ∶ A ] Q x)) ≡ (∀[ x ∶ A ] (P x ⊔ Q x))
  -- ∀-⊔-distrib {A = A} P Q =
  --   ⇒∶ (λ [∀xPx]⊔[∀xQx] x → ⊔-elim (∀[ x ] P x) (∀[ x ] Q x) (λ _ → P x ⊔ Q x) (λ ∀xPx → inlᵖ (∀xPx x)) (λ ∀xQx → inrᵖ (∀xQx x)) [∀xPx]⊔[∀xQx])
  --   ⇐∶ λ ∀x[Px⊔Qx] → {!   !}

  -- ∀-⊔-distribʳ : ∀{ℓ ℓ' ℓ''} {A : Type ℓ} → (P : hProp ℓ') → (Q : A → hProp ℓ'')
  --             → (P ⊔ (∀[ x ∶ A ] Q x)) ≡ (∀[ x ∶ A ] (P ⊔ Q x))
  -- ∀-⊔-distribʳ {A = A} P Q =
  --   ⇒∶ (λ [P]⊔[∀xQx] x → ⊔-elim P (∀[ x ] Q x) (λ _ → P ⊔ Q x) (λ p → inlᵖ p) (λ ∀xQx → inrᵖ (∀xQx x)) [P]⊔[∀xQx])
  --   ⇐∶ λ ∀x[P⊔Qx] → {!   !}

  -- ∀-⊎-distribʳ : ∀{ℓ ℓ' ℓ''} (a : Type ℓ) {B : Type ℓ'} (f : B → Type ℓ'')
  --              → (a → ∀ b → ¬ᵗ f b) -- a implies that fb is wrong
  --              → (∀ b → f b → ¬ᵗ a) -- b implies that a is wrong
  --              → (∀ b → a ⊎ f b)    -- for all b, either a holds or fb holds
  --              → a ⊎ (∀ b → f b)    -- either a holds or fb holds forall b
  -- ∀-⊎-distribʳ a f a→¬fb fb→¬a g = {!   !}



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

    ⊎-isProp : isProp ([ P ] ⊎ [ Q ])
    ⊎-isProp = isProp⊎ (isProp[] P) (isProp[] Q) X⇒¬Y

    P⊎Qᵖ : hProp (ℓ-max ℓ ℓ')
    P⊎Qᵖ = ([ P ] ⊎ [ Q ]) , ⊎-isProp

    -- ⊎-implies-⊔' : [ P⊎Qᵖ ] → [ P ⊔ Q ]
    -- ⊎-implies-⊔' x = ∣ x ∣

    ⊔-implies-⊎ : [ P ⊔ Q ] → [ P⊎Qᵖ ]
    abstract ⊔-implies-⊎ x = ⊔-elim P Q (λ x → ([ P ] ⊎ [ Q ]) , ⊎-isProp) (λ p → inl p) (λ q → inr q) x

    ⊔⊎-equiv : [ P⊎Qᵖ ⇔ P ⊔ Q ]
    ⊔⊎-equiv = ⊎-implies-⊔ P Q , ⊔-implies-⊎

    ⊔⊎-≡ : P⊎Qᵖ ≡ P ⊔ Q
    abstract
      ⊔⊎-≡ with ⊔⊎-equiv
      ... | p , q = ⇔toPath p q
