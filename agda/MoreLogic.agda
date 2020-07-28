{-# OPTIONS --cubical --no-import-sorts #-}

module MoreLogic where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
-- open import Function.Base

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.Function
open import Function.Base using (_∋_)
open import Cubical.Foundations.Logic
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty renaming (elim to ⊥-elim) hiding (⊥) -- `⊥` and `elim`

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Base


-- "implicational" reasoning

infix  3 _◼ₚ
infixr 2 _⇒ₚ⟨_⟩_

_⇒ₚ⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : hProp ℓ'} {R : hProp ℓ''} → (P : hProp ℓ) → [ P ⇒ Q ] → [ Q ⇒ R ] → [ P ⇒ R ]
_ ⇒ₚ⟨ pq ⟩ qr = qr ∘ pq

_◼ₚ : ∀{ℓ} (A : hProp ℓ) → [ A ] → [ A ]
_ ◼ₚ = λ x → x

infix  3 _◼ -- for a list of unicode symbols in agda, see https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html
infixr 2 _⇒⟨_⟩_

_⇒⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : Type ℓ'} {R : Type ℓ''} → (P : Type ℓ) → (P → Q) → (Q → R) → (P → R)
_ ⇒⟨ pq ⟩ qr = qr ∘ pq

_◼ : ∀{ℓ} (A : Type ℓ) → A → A
_ ◼ = λ x → x


-- lifted versions of ⊥ and ⊤

⊥↑ : ∀{ℓ} → hProp ℓ
⊥↑ = Lift Empty.⊥ , λ () 

⊤↑ : ∀{ℓ} → hProp ℓ
⊤↑ = Lift Unit , isOfHLevelLift 1 (λ _ _ _ → tt)

⊔-identityˡ-↑ : (P : hProp ℓ) → ⊥↑ {ℓ} ⊔ P ≡ P
⊔-identityˡ-↑ P =
  ⇒∶ (⊔-elim ⊥↑ P (λ _ → P) (λ ()) (λ x → x))
  ⇐∶ inr

⊔-identityʳ-↑ : (P : hProp ℓ) → P ⊔ ⊥↑ {ℓ} ≡ P
⊔-identityʳ-↑ P = ⇔toPath (⊔-elim P ⊥↑ (λ _ → P) (λ x → x) λ ()) inl

⊓-identityˡ-↑ : (P : hProp ℓ) → ⊤↑ {ℓ} ⊓ P ≡ P
⊓-identityˡ-↑ _ = ⇔toPath snd  λ x → lift tt , x

⊓-identityʳ-↑ : (P : hProp ℓ) → P ⊓ ⊤↑ {ℓ} ≡ P
⊓-identityʳ-↑ _ = ⇔toPath fst λ x → x , lift tt

infix 10 ¬↑_

¬↑_ : hProp ℓ → hProp ℓ
¬↑_ {ℓ} A = ([ A ] → Lift {j = ℓ} Empty.⊥) , isPropΠ λ _ → isOfHLevelLift 1 Empty.isProp⊥

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

-- taken from  https://ncatlab.org/nlab/show/excluded+middle#DoubleNegatedPEM
weak-LEM : ∀(P : hProp ℓ) → [ ¬ ¬ (P ⊔ ¬ P) ]
weak-LEM _ ¬[p⊔¬p] = ¬[p⊔¬p] (inr (λ p → ¬[p⊔¬p] (inl p)))

⊤-introₚ : {P : hProp ℓ} → [ P ] → P ≡ ⊤↑
⊤-introₚ {ℓ = ℓ} {P = P} p = let
 P⇔⊤↑ : [ P ⇔ ⊤↑ {ℓ} ]
 P⇔⊤↑ = (λ _ → lift tt) , (λ _ → p)
 in ⇔toPath (fst P⇔⊤↑) (snd P⇔⊤↑)

⊤-elimₚ : {P : hProp ℓ} → P ≡ ⊤↑ → [ P ]
⊤-elimₚ {ℓ = ℓ} {P = P} p≡⊤ = (
 [ ⊤↑ {ℓ} ] ⇒⟨ transport ( λ i → [ p≡⊤ (~ i) ]) ⟩
 [ P     ] ◼) (lift tt)

-- ⊥-introₚ : {P : hProp ℓ} → [ ¬ P ] → P ≡ ⊤↑

funExt-⊥ : {A : Type ℓ} (f g : A → Empty.⊥) → f ≡ g
funExt-⊥ f g = funExt (λ x → ⊥-elim {A = λ _ →  f x ≡ g x} (f x)) -- ⊥-elim needed a hint here

-- import Cubical.Structures.Axioms

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
funExt-⊥₂ f g =  funExt₂ᶜ λ a b → ⊥-elim {A = λ _ → f a b ≡ g a b} (g a b)  -- funExt (λ x → {! !})

implicationₚ : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ P ⇒ ¬ Q ]
implicationₚ {ℓ = ℓ} P Q ¬[p⊓q] p q = ⊥-elim (¬[p⊓q] (p , q))
-- the following was an attempt to return `fst` of something in order to help agda resolving some metas when using `implicationₚ` but it did not help
--   so maybe these unresolved metas have a different source
-- yes: we need to pass `snd P` and `snd Q` into `implicationₚ` in order to resolve correctly `[ P ⇒ ¬ Q ]` and alike
{-
 let
 γ : (A : Type ℓ') → [ P ] → [ Q ] → A
 γ A = λ p q → ⊥-elim {A = λ _ → A} (¬[p⊓q] (p , q)) 
 --prop : Σ (Type ℓ) (λ A → (x y : A) → x ≡ y)
 --prop = [ P ⇒ ¬ Q ] ,  λ x y → funExt-⊥₂ x y 
 in fst {B = λ _ → (x y : ⊥.⊥) → x ≡ y} (γ ⊥.⊥ , λ x ())  -- (⊥-elim ⊥) , (⊥-elim ⊥)
-}

-- NOTE: when using "mere propositions" like `[ P ]`, for P being an hProp, we need to pass in `snd P` to get it resolved correctly
--       therefore we might follow the convention to pass P as an explicit argument (and not an implicit one)

contrapositionₚ : {P Q : hProp ℓ} → ( [ P ⇒ Q ] ) → [ ¬ Q ⇒ ¬ P ]
contrapositionₚ f ¬q p = ⊥-elim (¬q (f p))

-- weak deMorgan laws: only these two hold without further assumptions

deMorgan₂ : (P Q : hProp ℓ) → [ ¬ (P ⊔ Q) ] → [ ¬ P ⊓ ¬ Q ]
deMorgan₂ P Q ¬[p⊔q] = (λ p →  ⊥-elim (¬[p⊔q] (inl p))) , λ q → ⊥-elim (¬[p⊔q] (inr q))

deMorgan₁-back : (P Q : hProp ℓ) → [ ¬ P ⊔ ¬ Q ] → [ ¬ (P ⊓ Q) ]
deMorgan₁-back {ℓ = ℓ} P Q [¬p⊔¬q] (p , q) = ⊔-elim (¬ P) (¬ Q) (λ [¬p⊔¬q] → ⊥) (λ ¬p → ¬p p) (λ ¬q → ¬q q) [¬p⊔¬q]


{-
deMorgan₁ : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ ¬ P ⊔ ¬ Q ]
deMorgan₁ {ℓ = ℓ} P Q ¬[p⊓q] = let
  ¬[q⊓p] : [ ¬ (Q ⊓ P) ]
  ¬[q⊓p] = (transport (λ i →  [ ¬ (⊓-comm P Q i) ] ) ¬[p⊓q] )
  a : [ P ⇒ ¬ Q ]
  a = implicationₚ P Q  ¬[p⊓q] 
  b : [ Q ⇒ ¬ P ]
  b = implicationₚ Q P ¬[q⊓p]
  in {! !}
-}

 -- (
  -- [ ¬(x ⊓   y) ] ⇒⟨  transport (λ i → [ doublenegation (x ⊓ y) (~ i) ]) ⟩
  -- [ ¬ ¬ ¬(x ⊓ y) ] ⇒⟨ {!!} ⟩
--  [ ¬ ¬ (¬(x ⊓  y) ⊔ ¬ ¬(x ⊓ y)) ] ⇒⟨ {!!} ⟩
--  [ ¬ x ⊔ ¬ y  ] ◼) ( LEMʷ (¬(x ⊓  y)))

-- f = ¬¬-elim λ g → g $ inl( λ a → g (inr λ b → ¬[x⊓y] (a , b)))

--deMorgan₂ʷ : (x y : hProp ℓ) → [ ¬ (x ⊔ y) ] → [ ¬ x ⊓ ¬ y ]
--deMorgan₂ʷ {ℓ = ℓ} x y = (
--  ¬(x ⊔ y)  ⇒ₚ⟨ {!!} ⟩
--  ¬ x ⊓ ¬ y ◼ₚ)

⊓-⊔-distribʳ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → (Q ⊔ R) ⊓ P ≡ (Q ⊓ P) ⊔ (R ⊓ P)
⊓-⊔-distribʳ P Q R = (
  (Q ⊔ R) ⊓ P       ≡⟨ ⊓-comm _ _ ⟩
   P ⊓ (Q ⊔ R)      ≡⟨ ⊓-⊔-distribˡ P Q R ⟩
  (P ⊓ Q) ⊔ (P ⊓ R) ≡⟨ ( λ i → ⊓-comm P Q i ⊔ ⊓-comm P R i) ⟩
  (Q ⊓ P) ⊔ (R ⊓ P) ∎)


{-

-- the following does only hold when LEM is available

import Algebra.Properties.BooleanAlgebra
import Algebra.Consequences.Setoid

⊔-complementˡ : (x : hProp ℓ) → ¬ x ⊔ x ≡ ⊤↑
⊔-complementˡ = {! comm+invʳ⇒invˡ ⊔-comm ⊔-complementʳ !}

⊔-complementʳ : (x : hProp ℓ) → x ⊔ ¬ x ≡ ⊤↑
⊔-complementʳ x =
 ⇒∶ (λ _ → lift tt) -- we can always create a ⊤↑
 ⇐∶ λ _ → {!!}

⊔-complement : ((x : hProp ℓ) → ¬ x ⊔ x ≡ ⊤↑) × ((x : hProp ℓ) → x ⊔ ¬ x ≡ ⊤↑)
⊔-complement = ⊔-complementˡ , ⊔-complementʳ 

⊓-complementˡ : (x : hProp ℓ) → ¬ x ⊓ x ≡ ⊥↑
⊓-complementˡ = {! isProp!} -- comm+invʳ⇒invˡ ⊓-comm ⊓-complementʳ 

⊓-complementʳ : (x : hProp ℓ) → x ⊓ ¬ x ≡ ⊥↑
⊓-complementʳ = {!!}

⊓-complement : ((x : hProp ℓ) → ¬ x ⊓ x ≡ ⊥↑) × ((x : hProp ℓ) → x ⊓ ¬ x ≡ ⊥↑)
⊓-complement = ⊓-complementˡ , ⊓-complementʳ 


private
  lemma : (x y : hProp ℓ) → x ⊓ y ≡ ⊥↑ → x ⊔ y ≡ ⊤↑ → ¬ x ≡ y
  lemma x y x⊓y=⊥ x⊔y=⊤ = (
    ¬ x                    ≡⟨ sym (⊓-identityʳ-↑ _) ⟩
    ¬ x ⊓ ⊤↑               ≡⟨ (λ i → ¬ x ⊓ x⊔y=⊤ (~ i) ) ⟩
    ¬ x ⊓ (x ⊔ y)          ≡⟨ ⊓-⊔-distribˡ (¬ x) x y  ⟩
    (¬ x ⊓ x) ⊔ (¬ x ⊓ y)  ≡⟨ (λ i → ⊓-complementˡ x i ⊔ (¬ x ⊓ y)) ⟩
    ⊥↑ ⊔ (¬ x ⊓ y)         ≡⟨ (λ i → x⊓y=⊥ (~ i) ⊔ (¬ x ⊓ y)) ⟩
    (x ⊓ y) ⊔ (¬ x ⊓ y)    ≡⟨  sym (⊓-⊔-distribʳ y x (¬ x)) ⟩
    (x ⊔ ¬ x) ⊓ y          ≡⟨ (λ i → (⊔-complementʳ x) i ⊓ y ) ⟩
    ⊤↑ ⊓ y                 ≡⟨ ⊓-identityˡ-↑ _ ⟩
    y                      ∎)

-}

-- https://en.wikipedia.org/wiki/De_Morgan_algebra
--   In a De Morgan algebra, the laws
--
--     ¬x ∨ x = 1 (law of the excluded middle), and
--     ¬x ∧ x = 0 (law of noncontradiction)
--   
--   do not always hold.
--   In the presence of the De Morgan laws, either law implies the other, and an algebra which satisfies them becomes a Boolean algebra.
-- https://ncatlab.org/nlab/show/weak+excluded+middle#de_morgans_law
--   In intuitionistic logic, de Morgan’s law often refers to the one of de Morgan's four laws that is not an intuitionistic tautology,
--   namely ¬(P ∧ Q) → (¬ P ∨ ¬ Q) for any P,Q.
--   Theorem. De Morgan’s law is equivalent to weak excluded middle.




