{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module Number.Instances.QuoInt where

open import Cubical.Foundations.Everything hiding (⋆) renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool using (Bool; not; true; false)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_; _$_)
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation --.Properties

open import Utils using (!_; !!_)
open import MoreLogic.Reasoning
open import MoreLogic.Definitions
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions hiding (_≤''_)
open import MorePropAlgebra.Structures
open import MorePropAlgebra.Bundles
open import MorePropAlgebra.Consequences
open import Number.Structures2
open import Number.Bundles2

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Nat using (suc; zero; ℕ; HasFromNat)
open import Number.Instances.QuoIntFromInt public
open import Cubical.HITs.Ints.QuoInt as QuoInt using
  ( ℤ
  ; HasFromNat
  ; _+_
  ; Int≡ℤ
  ; signed
  ; posneg
  ; ℤ→Int
  ; sucℤ
  ; predℤ
  ; sign
  ; abs
  ; pos
  ; neg
  ; +-comm
  ; +-assoc
  ; sucℤ-+ʳ
  ) renaming
  ( isSetℤ to is-set
  ; _*_ to _·_
  ; -_ to infixl 6 -_
  ; *-comm to ·-comm
  )
open IsLinearlyOrderedCommRing is-LinearlyOrderedCommRing using
  ( _-_
  ; <-irrefl
  ; <-trans
  ; +-<-ext
  ; +-rinv
  ; +-identity
  ; _≤_
  ; ·-preserves-<
  ; <-tricho
  ; <-asym
  )

0<1 : [ 0 < 1 ]
0<1 = 0 , refl

-- TODO: import these properties from somewhere else
+-reflects-<      : ∀ x y z → [ (x + z < y + z) ⇒ (    x < y    ) ]
+-preserves-<     : ∀ x y z → [ (    x < y    ) ⇒ (x + z < y + z) ]
+-creates-<       : ∀ x y z → [ (    x < y    ) ⇔ (x + z < y + z) ]

+-preserves-< a b x = snd (
  ( a            <  b           ) ⇒ᵖ⟨ transport (λ i → [ sym (fst (+-identity a)) i < sym (fst (+-identity b)) i ]) ⟩
  ( a +    0     <  b +    0    ) ⇒ᵖ⟨ transport (λ i → [ a + sym (+-rinv x) i < b + sym (+-rinv x) i ]) ⟩
  ( a + (x  - x) <  b + (x  - x)) ⇒ᵖ⟨ transport (λ i → [ +-assoc a x (- x) i < +-assoc b x (- x) i ]) ⟩
  ((a +  x) - x  < (b +  x) - x ) ⇒ᵖ⟨ +-<-ext (a + x) (- x) (b + x) (- x) ⟩
  ((a + x < b + x) ⊔ (- x < - x)) ⇒ᵖ⟨ (λ q → case q as (a + x < b + x) ⊔ (- x < - x) ⇒ a + x < b + x of λ
                                      { (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                      ; (inr  -x<-x ) → ⊥-elim {A = λ _ → [ a + x < b + x ]} (<-irrefl (- x) -x<-x)
                                      }) ⟩
   a + x < b + x ◼ᵖ)

+-reflects-< x y z = snd
  ( x + z < y + z              ⇒ᵖ⟨ +-preserves-< (x + z) (y + z) (- z) ⟩
    (x + z) - z  < (y + z) - z ⇒ᵖ⟨ transport (λ i → [ +-assoc x z (- z) (~ i) < +-assoc y z (- z) (~ i) ]) ⟩
    x + (z - z) < y + (z - z)  ⇒ᵖ⟨ transport (λ i → [ x + +-rinv z i < y + +-rinv z i ]) ⟩
    x + 0 < y + 0              ⇒ᵖ⟨ transport (λ i → [ fst (+-identity x) i < fst (+-identity y) i ]) ⟩
    x < y                      ◼ᵖ)

+-creates-< x y z .fst = +-preserves-< x y z
+-creates-< x y z .snd = +-reflects-<  x y z

suc-creates-< : ∀ x y → [ (x < y) ⇔ (sucℤ x < sucℤ y) ]
suc-creates-< x y .fst p = substₚ (λ p → sucℤ x < p) (∣ +-comm y (pos 1) ∣) $ substₚ (λ p → p < y + pos 1) (∣ +-comm x (pos 1) ∣) (+-preserves-< x y (pos 1) p)
suc-creates-< x y .snd p = +-reflects-< x y (pos 1) $ substₚ (λ p → p < y + pos 1) (∣ +-comm (pos 1) x ∣) $ substₚ (λ p → sucℤ x < p) (∣ +-comm (pos 1) y ∣) p

·-creates-< : ∀ a b x → [ 0 < x ] → [ (a < b) ⇔ ((a · x) < (b · x)) ]
·-creates-< a b x p .fst q = ·-preserves-< a b x p q
·-creates-< a b x p .snd q = ·-reflects-< a b x p q

+-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ]
+-creates-≤ a b x = {!   !}

·-creates-≤ : ∀ a b x → [ 0 ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ]
·-creates-≤ a b x 0≤x .fst p = {!   !}
·-creates-≤ a b x 0≤x .snd p = {!   !}

·-creates-≤-≡ : ∀ a b x → [ 0 ≤ x ] → (a ≤ b) ≡ ((a · x) ≤ (b · x))
·-creates-≤-≡ a b x 0≤x = uncurry ⇔toPath $ ·-creates-≤ a b x 0≤x

≤-dicho : ∀ x y → [ (x ≤ y) ⊔ (y ≤ x) ]
≤-dicho x y with <-tricho x y
... | inl (inl x<y) = inlᵖ $ <-asym x y x<y
... | inl (inr y<x) = inrᵖ $ <-asym y x y<x
... | inr      x≡y  = inlᵖ $ subst (λ p → [ ¬(p < x) ]) x≡y (<-irrefl x)

ℤlattice : Lattice {ℓ-zero} {ℓ-zero}
ℤlattice = record { LinearlyOrderedCommRing bundle renaming (≤-Lattice to is-Lattice) }

open import MorePropAlgebra.Properties.Lattice ℤlattice
open OnSet is-set hiding (+-min-distribʳ; ·-min-distribʳ; +-max-distribʳ; ·-max-distribʳ)

≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ]
≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ]
≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ]
≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ]

≤-min-+ = OnType.≤-dicho⇒+.≤-min-+ _+_ ≤-dicho
≤-max-+ = OnType.≤-dicho⇒+.≤-max-+ _+_ ≤-dicho
≤-min-· = OnType.≤-dicho⇒·.≤-min-· _·_ ≤-dicho
≤-max-· = OnType.≤-dicho⇒·.≤-max-· _·_ ≤-dicho

+-min-distribʳ : ∀ x y z             → (min x y + z) ≡ min (x + z) (y + z)
·-min-distribʳ : ∀ x y z → [ 0 ≤ z ] → (min x y · z) ≡ min (x · z) (y · z)
+-max-distribʳ : ∀ x y z             → (max x y + z) ≡ max (x + z) (y + z)
·-max-distribʳ : ∀ x y z → [ 0 ≤ z ] → (max x y · z) ≡ max (x · z) (y · z)
+-min-distribˡ : ∀ x y z             → (z + min x y) ≡ min (z + x) (z + y)
·-min-distribˡ : ∀ x y z → [ 0 ≤ z ] → (z · min x y) ≡ min (z · x) (z · y)
+-max-distribˡ : ∀ x y z             → (z + max x y) ≡ max (z + x) (z + y)
·-max-distribˡ : ∀ x y z → [ 0 ≤ z ] → (z · max x y) ≡ max (z · x) (z · y)

+-min-distribʳ = OnSet.+-min-distribʳ is-set _+_ +-creates-≤ ≤-min-+
·-min-distribʳ = OnSet.·-min-distribʳ is-set 0 _·_ ·-creates-≤ ≤-min-·
+-max-distribʳ = OnSet.+-max-distribʳ is-set _+_ +-creates-≤ ≤-max-+
·-max-distribʳ = OnSet.·-max-distribʳ is-set 0 _·_ ·-creates-≤ ≤-max-·

+-min-distribˡ x y z   = +-comm z (min x y) ∙ +-min-distribʳ x y z   ∙ (λ i → min (+-comm x z i) (+-comm y z i))
·-min-distribˡ x y z p = ·-comm z (min x y) ∙ ·-min-distribʳ x y z p ∙ (λ i → min (·-comm x z i) (·-comm y z i))
+-max-distribˡ x y z   = +-comm z (max x y) ∙ +-max-distribʳ x y z   ∙ (λ i → max (+-comm x z i) (+-comm y z i))
·-max-distribˡ x y z p = ·-comm z (max x y) ∙ ·-max-distribʳ x y z p ∙ (λ i → max (·-comm x z i) (·-comm y z i))

pos<pos[suc] : ∀ x → [ pos x < pos (suc x) ]
pos<pos[suc] 0 = 0<1
pos<pos[suc] (suc x) = suc-creates-< (pos x) (pos (suc x)) .fst (pos<pos[suc] x)

0<ᶻpos[suc] : ∀ x → [ 0 < pos (suc x) ]
0<ᶻpos[suc]      0  = 0<1
0<ᶻpos[suc] (suc x) = <-trans 0 (pos (suc x)) (pos (suc (suc x))) (0<ᶻpos[suc] x) (suc-creates-< (pos x) (pos (suc x)) .fst (pos<pos[suc] x))

·-nullifiesˡ : ∀(x : ℤ) → 0 · x ≡ 0
·-nullifiesˡ (pos zero) = refl
·-nullifiesˡ (neg zero) = refl
·-nullifiesˡ (posneg i) = refl
·-nullifiesˡ (pos (suc n)) = refl
·-nullifiesˡ (neg (suc n)) = sym posneg

·-nullifiesʳ : ∀(x : ℤ) → x · 0 ≡ 0
·-nullifiesʳ x = ·-comm x 0 ∙ ·-nullifiesˡ x

·-preserves-<0 : ∀ a b → [ 0 < a ] → [ 0 < b ] → [ 0 < a · b ]
·-preserves-<0 a b p q = subst (λ p → [ p < a · b ]) (·-nullifiesˡ b) (·-preserves-< 0 a b q p)

·-creates-<-≡ : ∀ a b x → [ 0 < x ] → (a < b) ≡ ((a · x) < (b · x))
·-creates-<-≡ a b x p = ⇔toPath (·-creates-< a b x p .fst) (·-creates-< a b x p .snd)
