{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Function.Base using (_∋_; _$_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
import Cubical.HITs.PropositionalTruncation.Properties as PTrunc
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax  to infix -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix -4 ∃[∶]-syntax  --
  ; ∀[∶]-syntax to infix -4 ∀[∶]-syntax  --
  ; ∀[]-syntax  to infix -4 ∀[]-syntax   --
  )

open import Utils
open import MoreLogic.Reasoning
open import MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax  to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax  to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax   to infix -4 ∀〚∶〛-syntax
  ; Σᵖ[]-syntax   to infix -4 Σᵖ[]-syntax
  ; Σᵖ[∶]-syntax  to infix -4 Σᵖ[∶]-syntax
  ) hiding (≡ˢ-syntax)
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions hiding (_≤''_)
open import MorePropAlgebra.Consequences
open import MorePropAlgebra.Bundles

module MorePropAlgebra.Properties.AlmostOrderedField {ℓ} {ℓ'} (assumptions : AlmostOrderedField {ℓ} {ℓ'})
  (let F = AlmostOrderedField.Carrier assumptions
       _≡ˢ_ = λ(x y : F) → MoreLogic.Definitions.≡ˢ-syntax x y {AlmostOrderedField.is-set assumptions}
       infixl 4 _≡ˢ_
  ) where

import MorePropAlgebra.Properties.Group
module Group'Properties  = MorePropAlgebra.Properties.Group   record { AlmostOrderedField assumptions ; is-Group = AlmostOrderedField.+-Group assumptions }
module Group'            =                            Group   record { AlmostOrderedField assumptions ; is-Group = AlmostOrderedField.+-Group assumptions }
(      Group')           =                            Group ∋ record { AlmostOrderedField assumptions ; is-Group = AlmostOrderedField.+-Group assumptions }
module GroupLemmas'      = Group'Properties.GroupLemmas'

import MorePropAlgebra.Properties.Ring
module Ring'Properties  = MorePropAlgebra.Properties.Ring   record { AlmostOrderedField assumptions }
module Ring'            =                            Ring   record { AlmostOrderedField assumptions }
(      Ring')           =                            Ring ∋ record { AlmostOrderedField assumptions }
module RingTheory'      = Ring'Properties.RingTheory'

open AlmostOrderedField assumptions -- renaming (Carrier to F; _-_ to _-_)

-- Bridges' definition of _≤__
_≤''_ : hPropRel F F (ℓ-max ℓ ℓ')
x ≤'' y = ∀[ ε ] (y < ε) ⇒ (x < ε)
infixl 4 _≤''_

private
  -- infixl 4 _≡ˢ_
  -- _≡ˢ_ = λ(x y : F) → MoreLogic.Definitions.≡ˢ-syntax x y {is-set} -- [ is-set ] x ≡ˢ y

  ≡ˢ-sym : ∀ a b → [ (a ≡ˢ b) ⇔ (b ≡ˢ a) ]
  ≡ˢ-sym a b .fst a≡b = sym a≡b
  ≡ˢ-sym a b .snd b≡a = sym b≡a

  ≡ˢ-symᵗ : ∀ a b → (a ≡ˢ b) ≡ (b ≡ˢ a)
  ≡ˢ-symᵗ a b = let (p , q) = ≡ˢ-sym a b in ⇔toPath p q

abstract
  -dist' : ∀ a b → -(a + b) ≡ (- b) + (- a)
  -dist  : ∀ a b → -(a + b) ≡ (- a) + (- b)

  ·-inv#0 : ∀ x y → x · y ≡ 1f → [ (x # 0f) ⊓ (y # 0f) ]

  ·-reflects-≡ : (a b c : F) → [ c # 0f ⇒ (a · c ≡ˢ b · c) ⇒ (a ≡ˢ b) ]; _ : [ operation _·_ reflects _≡ˢ_ when (λ c → c # 0f) ]; _ = ·-reflects-≡

  ·-rinv-unique'' : (x y z : F) → [ x · y ≡ˢ 1f ] → [ x · z ≡ˢ 1f ] → [ y ≡ˢ z ]

  _⁻¹'' : ∀ x → {{[ x # 0f ]}} → Σ[ y ∈ F ] x · y ≡ 1f
  _⁻¹   : ∀ x → {{[ x # 0f ]}} → F
  infix  9 _⁻¹

  ·-rinv        : ∀ x                    → (p : [ x # 0f ]) → [ x · (x ⁻¹) {{p}} ≡ˢ 1f ]
  ·-linv        : ∀ x                    → (p : [ x # 0f ]) → [ (x ⁻¹) {{p}} · x ≡ˢ 1f ]
  ·-linv-unique : (x y : F) → x · y ≡ 1f → (p : [ y # 0f ]) → x ≡ (y ⁻¹) {{p}}

  <-≤-trans : ∀ x y z → [ x < y ⇒ y ≤ z ⇒ x < z ]
  ≤-<-trans : ∀ x y z → [ x ≤ y ⇒ y < z ⇒ x < z ]
  ≤-⇔-≤''   : ∀ x y   → [  (x ≤ y) ⇔ (x ≤'' y)  ]

  -dist' a b = GroupLemmas'.invDistr a b
  -dist  a b = -dist' a b ∙ +-comm _ _

  ·-inv#0 x y x·y≡1 .fst = ·-inv'' x .fst ∣ (y ,              x·y≡1) ∣
  ·-inv#0 x y x·y≡1 .snd = ·-inv'' y .fst ∣ (x , ·-comm y x ∙ x·y≡1) ∣

  ·-reflects-≡ a b c p = PTrunc.rec (isProp[] ((a · c ≡ˢ b · c) ⇒ (a ≡ˢ b) )) γ (·-inv'' c .snd p) where
    γ : Σ[ c⁻¹ ∈ F ] [ c · c⁻¹ ≡ˢ 1f ] → [ (a · c ≡ˢ b · c) ⇒ a ≡ˢ b ]
    γ (c⁻¹ , c·c⁻¹≡1) a·c≡b·c =
       a              ≡⟨ sym (fst (·-identity a)) ∙ cong (a ·_) (sym c·c⁻¹≡1) ∙ ·-assoc _ _ _ ⟩
      (a · c) · (c⁻¹) ≡⟨ cong (_· c⁻¹) a·c≡b·c ⟩
      (b · c) · (c⁻¹) ≡⟨ sym (·-assoc _ _ _) ∙ cong (b ·_) c·c⁻¹≡1 ∙ fst (·-identity b)  ⟩
       b ∎

  -- uniqueness of inverses from `·-assoc` + `·-comm` + `·-lid` + `·-rid`
  ·-rinv-unique'' x y z x·y≡1 x·z≡1 =
    (      x  · y  ≡ˢ     1f ⇒ᵖ⟨ (λ x·y≡1 i → z · x·y≡1 i) ⟩
      z · (x  · y) ≡ˢ z · 1f ⇒ᵖ⟨ pathTo⇒ (λ i → ·-assoc z x y i ≡ˢ ·-rid z i) ⟩
     (z ·  x) · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → (·-comm z x i) · y  ≡ˢ z) ⟩
     (x ·  z) · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → x·z≡1 i · y  ≡ˢ z) ⟩
        1f    · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → ·-lid y i ≡ˢ z) ⟩
                y  ≡ˢ z      ◼ᵖ) .snd x·y≡1

  -- inverse function from `·-rinv-unique''` and `∀[ x ] (∃[ y ] x · y ≡ˢ 1f) ⇔ x # 0f`
  (x ⁻¹'') {{x#0f}} = PTrunc.rec γ (λ p → p) (·-inv'' x .snd x#0f) where
     γ : isProp (Σ[ y ∈ F ] x · y ≡ 1f)
     γ (a , x·a≡1) (b , x·b≡1) = let a≡b = ·-rinv-unique'' x a b x·a≡1 x·b≡1
                                 in Σ≡Prop (λ c → isProp[] (x · c ≡ˢ 1f)) a≡b

  (x ⁻¹) {{p}} = (x ⁻¹'') .fst


  ·-rinv x p = (x ⁻¹'') {{p}} .snd

  ·-linv x p = ·-comm _ _ ∙ ·-rinv x p

  ·-linv-unique x y x·y≡1 p = sym $ ·-rinv-unique'' y ((y ⁻¹) {{p}}) x (·-rinv y p) (·-comm _ _ ∙ x·y≡1)

  <-≤-trans x y z x<y y≤z = ⊔-elim (x < z) (z < y) (λ _ → x < z) (λ x<z → x<z) (λ z<y → ⊥-elim (y≤z z<y)) (<-cotrans _ _ x<y z)
  ≤-<-trans x y z x≤y y<z = ⊔-elim (y < x) (x < z) (λ _ → x < z) (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z) (<-cotrans y z y<z x)

  -- Booij's _≤_ ⇔ Brigdes' _≤''_
  ≤-⇔-≤'' x y .fst x≤y ε y<ε = ≤-<-trans x y ε x≤y y<ε
  ≤-⇔-≤'' x y .snd x≤''y y<x = <-irrefl x (x≤''y x y<x)
