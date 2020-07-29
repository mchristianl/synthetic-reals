{-# OPTIONS --cubical --no-import-sorts --prop #-}

module Utils where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Function.Base

variable
  ℓ ℓ' ℓ'' : Level

module Test where
  import Algebra.Properties.BooleanAlgebra

  open import Algebra.Bundles
  

  module _ (B : BooleanAlgebra ℓ ℓ') where
    open BooleanAlgebra B
    open import Algebra.Definitions _≈_  

    ∨-complementˡ : LeftInverse ⊤ ¬_ _∨_ 
    ∨-complementˡ = {! comm+invʳ⇒invˡ ∨-comm ∨-complementʳ !}
    
    ∨-complement : Inverse ⊤ ¬_ _∨_
    ∨-complement = {! ∨-complementˡ , ∨-complementʳ !}
  
    ∧-complementˡ : LeftInverse ⊥ ¬_ _∧_
    ∧-complementˡ = {! comm+invʳ⇒invˡ ∧-comm ∧-complementʳ !}
  
    ∧-complement : Inverse ⊥ ¬_ _∧_
    ∧-complement = {! ∧-complementˡ , ∧-complementʳ !}
    

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
-- open import Cubical.Structures.CommRing
-- open import Cubical.Relation.Nullary.Base -- ¬_
-- open import Cubical.Relation.Binary.Base
-- open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
-- open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- -- open import Cubical.Structures.Poset
-- open import Cubical.Foundations.Function
-- open import Function.Base using (_∋_)
-- open import Function.Base using (it) -- instance search

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Logic
-- open import Algebra.Definitions
-- open import Cubical.Data.Empty
open import Cubical.HITs.PropositionalTruncation

import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit.Base



⊥↑ : ∀{ℓ} → hProp ℓ
⊥↑ = Lift ⊥.⊥ , λ () 

⊤↑ : ∀{ℓ} → hProp ℓ
⊤↑ = Lift Unit , isOfHLevelLift 1 (λ _ _ _ → tt)

-- _ = {! ⇔toPath!}

⊔-complementˡ :  ∀ x → ¬ x ⊔ x ≡ ⊤↑ -- LeftInverse _≡_ ⊤ ¬_ _⊔_
⊔-complementˡ = {! comm+invʳ⇒invˡ ⊔-comm ⊔-complementʳ !}

-- ⊔-complementʳ : ∀ x → x ⊔ ¬ x ≡ ∥ [ ⊤ ] ∥ₚ
-- ⊔-complementʳ : ∀(x : hProp ℓ) → x ⊔ ¬ x ≡ ((hProp ℓ) ∋ ⊤)
⊔-complementʳ : ∀(x : hProp ℓ) → x ⊔ ¬ x ≡ ⊤↑
⊔-complementʳ x =  λ i → {! ⊔-comm x (¬ x) i !} 

⊔-complement : (∀ x → ¬ x ⊔ x ≡ ⊤↑) × (∀ x → x ⊔ ¬ x ≡ ⊤↑) -- Inverse _≡_ ⊤ ¬_ _⊔_
⊔-complement = ⊔-complementˡ , {! ⊔-complementʳ !}

-- agda deduces
--         Σ Type (λ A → (x y : A) → x ≡ y)
-- hProp normalizes to
--    λ ℓ → Σ (Type ℓ) (λ A → (x y : A) → x ≡ y)
-- 
⊓-complementˡ :  ∀ x → ¬ x ⊓ x ≡ ⊥ -- LeftInverse _≡_ ⊥ ¬_ _⊓_
⊓-complementˡ = {! isProp!} -- comm+invʳ⇒invˡ ⊓-comm ⊓-complementʳ 

⊓-complementʳ :  ∀ x → x ⊓ ¬ x ≡ ⊥
⊓-complementʳ = {!!}

⊓-complement : (∀ x → ¬ x ⊓ x ≡ ⊥) × (∀ x → x ⊓ ¬ x ≡ ⊥) -- Inverse _≡_ ⊥ ¬_ _⊓_
⊓-complement = ⊓-complementˡ , ⊓-complementʳ 

⊓-⊔-distribʳ : (P : hProp ℓ) (Q : hProp ℓ')(R : hProp ℓ'')
  → (Q ⊔ R) ⊓ P ≡ (Q ⊓ P) ⊔ (R ⊓ P)
⊓-⊔-distribʳ P Q R = (
  (Q ⊔ R) ⊓ P       ≡⟨ ⊓-comm _ _ ⟩
   P ⊓ (Q ⊔ R)      ≡⟨ ⊓-⊔-distribˡ P Q R ⟩
  (P ⊓ Q) ⊔ (P ⊓ R) ≡⟨ ( λ i → ⊓-comm P Q i ⊔ ⊓-comm P R i) ⟩
  (Q ⊓ P) ⊔ (R ⊓ P) ∎)

_ : isProp ≡ (λ(A : Type ℓ) → (x y : A) → x ≡ y)
_ = refl

-- `sq` stands for "squashed" and |_| is the constructor for ∥_∥
-- 
--   data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
--     ∣_∣ : A → ∥ A ∥
--     squash : ∀ (x y : ∥ A ∥) → x ≡ y
--
-- (see https://ice1000.org/2018/12-06-CubicalAgda.html#propositional-truncation )
-- we also have
--
--   hProp    ℓ  = Σ[ A ∈ Type ℓ ]  (∀( x  y : A)    → x ≡ y)
--   isContr {ℓ} = λ( A : Type ℓ ) → Σ[ x ∈ A ] (∀ y → x ≡ y)
--   isProp  {ℓ} = λ( A : Type ℓ ) → ∀( x  y : A)    → x ≡ y
--
-- and in `Cubical.Foundations.Id` we have
--
--   postulate
--     Id : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
--   _≡_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
--   _≡_ = Id
--
-- which is imported in `Cubical.Foundations.Everything`, but _≡_ is hidden in favour of the _≡_ from `Agda.Builtin.Cubical.Path`:
--
--   _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
--   _≡_ {A = A} = PathP (λ i → A)
--
-- we have conversion functions between `Id` and `PathP`

-- recall from https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
--
--   is-center                X c = (x   : X) → c ≡ x
--   is-singleton             X   = Σ  c ꞉ X , is-center X c
--   is-subsingleton          X   = (x y : X) → x ≡ y
--   𝟘-is-subsingleton            : is-subsingleton 𝟘
--   singletons-are-subsingletons : (X : 𝓤 ̇ ) → is-singleton X → is-subsingleton X
--   𝟙-is-subsingleton            : is-subsingleton 𝟙
--
-- now,
--   see https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#axiomatic-approach
--   see https://ice1000.org/2018/12-06-CubicalAgda.html#propositional-truncation
--     However I would not only use recPropTrunc explicitly as we can just use pattern-matching to define functions out of HITs.
--   see https://cstheory.stackexchange.com/questions/30542/squash-type-vs-propositional-truncation-type
--     Squash types correspond to judgmental truncation, not propositional truncation.
--     In a type theory without a type for judgmental equality, there's non much of a way to make use of an inhabitant of a squash type;
--     there's no way to write an eliminator into any type except another squash type.
--     Relatedly, having squash types, as presented in the book you linked, makes typechecking undecidable;
--     having propositional truncation types does not result in this drawback.
--   there is https://github.com/agda/cubical/pull/136
--     Elimination of propositional truncation to higher types

import Cubical.Foundations.Id
import Cubical.HITs.PropositionalTruncation.Properties -- look here for examples

∥∥-isProp : {A : Type ℓ} → ∀ (x y : ∥ A ∥) → x ≡ y
∥∥-isProp {ℓ = ℓ} {A = A} x y = (squash x y)

_ = propTruncIsProp

propTruncIsProp' : {A : Type ℓ} → isProp ∥ A ∥
propTruncIsProp' x y = squash x y

{-

t0 : {A : Type ℓ} → (x y : ∥ A ∥) → x ≡ y -- isProp (∥ A ∥)
t0 x ∣ y ∣ = squash x ∣ y ∣
-- Goal: ∥ A ∥
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ t0 x y₀ j
-- i = i1 ⊢ t0 x y₁ j
-- j = i0 ⊢ x
-- j = i1 ⊢ squash y₀ y₁ i
t0 x (squash y₀ y₁ i) j = {! t0  !}

-}

{-
-- Goal: ∣ x ∣ ≡ ∣ y ∣
t0 ∣ x ∣ ∣ y ∣ = squash ∣ x ∣ ∣ y ∣

-- Goal: ∣ x ∣ ≡ squash y₀ y₁ i
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ t0 ∣ x ∣ y₀
-- i = i1 ⊢ t0 ∣ x ∣ y₁
t0 ∣ x ∣ (squash y₀ y₁ i) = squash ∣ x ∣ (squash y₀ y₁ i) -- {! squash ∣ x ∣ (squash y₀ y₁ i)!} -- {! λ j → squash ∣ x ∣ (squash y₁ y₂ j) {!  !}  !}
t0 (squash x₁ x₂ i) ∣ y ∣ = squash (squash x₁ x₂ i) ∣ y ∣
t0 (squash x₁ x₂ i) (squash y₁ y₂ j) = squash (squash x₁ x₂ i) (squash y₁ y₂ j) 
-}

-- Definition 2.4.3. The propositional truncation of a type X
--   is a proposition ∥ X ∥
--   together with a truncation map |_| : X → ∥ X ∥
--   such that for any other proposition Q, given a map g : X → Q, we obtain a map h : ∥ X ∥ → Q.
--
-- Remark 2.4.4. The uniqueness of the obtained map ∥ X ∥ → Q follows from the fact that Q is a proposition, and function extensionality
--
-- The propositional truncation ∥ X ∥ of a type X is a proposition. We may say, quite simply,
-- that we have a constructor sq which is a proof that the type ∥ X ∥ is a squashed to be a propo-
-- sition: it takes two elements of ∥ X ∥ and gives a proof that they are identical, i.e. squashed
-- together.

-- Definition 2.4.7.
-- We refer to types that are propositions as properties.
-- We refer to types that potentially have several witnesses as structure.

{-
module _ {ℓ} (X Y : Type ℓ) (g : X → Y) where

  f : ∥ X ∥ → Y
  f ∣ x ∣ = g x
  f (squash x₀ x₁ i) = {!  !}
-}

-- well, that might not work at all
-- ⊓-unliftˡ : {P : hProp ℓ} {Q : hProp ℓ'} 

import Cubical.HITs.PropositionalTruncation.Properties

-- _ : (P : hProp P.ℓ) (Q : hProp Q.ℓ) (R : hProp R.ℓ) → (hProp P.ℓ → hProp Q.ℓ → hProp R.ℓ) → h
-- _ = ?

--_ = _≡ₚ_

⊓-identityˡ-↑ : (P : hProp ℓ) → ⊤↑ {ℓ} ⊓ P ≡ P
⊓-identityˡ-↑ _ = ⇔toPath snd  λ x → lift tt , x

-- \ is \\
-- ↑ is \u


private
  lemma : ∀ x y → x ⊓ y ≡ ⊥ → x ⊔ y ≡ ⊤ → ¬ x ≡ y
  lemma x y x⊓y=⊥ x⊔y=⊤ = (
    ¬ x                    ≡⟨ sym (⊓-identityʳ _) ⟩
    ¬ x ⊓ ⊤                ≡⟨ (λ i → ¬ x ⊓ x⊔y=⊤ (~ i) ) ⟩
    ¬ x ⊓ (x ⊔ y)          ≡⟨ ⊓-⊔-distribˡ (¬ x) x y  ⟩
    (¬ x ⊓ x) ⊔ (¬ x ⊓ y)  ≡⟨ (λ i → ⊓-complementˡ x i ⊔ (¬ x ⊓ y)) ⟩
    ⊥ ⊔ (¬ x ⊓ y)          ≡⟨ (λ i → x⊓y=⊥ (~ i) ⊔ (¬ x ⊓ y)) ⟩
    (x ⊓ y) ⊔ (¬ x ⊓ y)    ≡⟨  sym (⊓-⊔-distribʳ y x (¬ x)) ⟩
    (x ⊔ ¬ x) ⊓ y          ≡⟨ (λ i → (⊔-complementʳ x) i ⊓ y ) ⟩
    ⊤↑ ⊓ y                 ≡⟨ ⊓-identityˡ-↑ _ ⟩
    y                      ∎)


data Prop2Type (P : Prop ℓ) : Type (ℓ-suc ℓ) where
  inₚ : (p : P) → Prop2Type P

Prop-to-hProp : Prop ℓ → hProp (ℓ-suc ℓ)
Prop-to-hProp P = Prop2Type P ,  λ{ (inₚ x) (inₚ y) → refl }
