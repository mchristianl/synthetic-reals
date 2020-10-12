{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Instances.QuoQ where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
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

open import Cubical.Data.Nat using (suc; zero; ℕ) renaming
  ( _*_ to _*ⁿ_
  ; +-comm to +ⁿ-comm
  ; +-assoc to +ⁿ-assoc
  ; *-comm to *ⁿ-comm
  ; *-suc to *ⁿ-suc
  ; *-assoc to *ⁿ-assoc
  ; +-suc to +ⁿ-suc
  ; *-distribˡ to *ⁿ-distribˡ
  ; *-distribʳ to *ⁿ-distribʳ
  ; *-identityʳ to *ⁿ-identityʳ
  ; snotz to snotzⁿ
  ; injSuc to injSucⁿ
  )
open import Cubical.Data.NatPlusOne using (HasFromNat; 1+_; ℕ₊₁; ℕ₊₁→ℕ)
open import Cubical.HITs.Ints.QuoInt using (HasFromNat; signed) renaming
  ( abs to absᶻ
  ; pos to pos
  ; neg to neg
  )

open import Number.Instances.QuoInt using (ℤbundle) renaming
  ( _<ᶠ_ to _<ᶻ_
  ; ·-reflects-<ᶠ to ·ᶻ-reflects-<ᶻ
  )

open import Cubical.Data.Nat.Order using () renaming
  ( ¬-<-zero to ¬-<ⁿ-zero )

module Definitions where
  open import Cubical.HITs.Ints.QuoInt hiding (_+_; -_; +-assoc; +-comm)
  open LinearlyOrderedCommRing ℤbundle
  -- open IsLinearlyOrderedCommRing is-LinearlyOrderedCommRing
  open import Cubical.HITs.Rationals.QuoQ using
    ( ℚ
    ; onCommonDenom
    ; onCommonDenomSym
    ; eq/
    ; _//_
    ; _∼_
    )
    renaming
    ( [_] to [_]ᶠ
    ; ℕ₊₁→ℤ to [1+_ⁿ]ᶻ
    )

  abstract
    0<1 : [ 0 < 1 ]
    0<1 = 0 , refl

    -- TODO: import these properties from somewhere else
    +-reflects-<      : ∀ x y z → [ (x + z < y + z) ⇒ (    x < y    ) ]
    +-preserves-<     : ∀ x y z → [ (    x < y    ) ⇒ (x + z < y + z) ]
    +-creates-<       : ∀ x y z → [ (    x < y    ) ⇔ (x + z < y + z) ]

    +-preserves-< a b x = snd (
      ( a            <  b           ) ⇒ᵖ⟨ transport (λ i → [ sym (fst (+-identity a)) i < sym (fst (+-identity b)) i ]) ⟩
      ( a +    0f    <  b +    0f   ) ⇒ᵖ⟨ transport (λ i → [ a + sym (+-rinv x) i < b + sym (+-rinv x) i ]) ⟩
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
        x + 0f < y + 0f            ⇒ᵖ⟨ transport (λ i → [ fst (+-identity x) i < fst (+-identity y) i ]) ⟩
        x < y                      ◼ᵖ)

    +-creates-< x y z .fst = +-preserves-< x y z
    +-creates-< x y z .snd = +-reflects-<  x y z

    suc-creates-< : ∀ x y → [ (x < y) ⇔ (sucℤ x < sucℤ y) ]
    suc-creates-< x y .fst p = substₚ (λ p → sucℤ x < p) (∣ +-comm y (pos 1) ∣) $ substₚ (λ p → p < y + pos 1) (∣ +-comm x (pos 1) ∣) (+-preserves-< x y (pos 1) p)
    suc-creates-< x y .snd p = +-reflects-< x y (pos 1) $ substₚ (λ p → p < y + pos 1) (∣ +-comm (pos 1) x ∣) $ substₚ (λ p → sucℤ x < p) (∣ +-comm (pos 1) y ∣) p

    +-creates-≤ : ∀ a b x → [ (a ≤ b) ⇔ ((a + x) ≤ (b + x)) ]
    +-creates-≤ a b x = {!   !}

    ·-creates-< : ∀ a b x → [ 0 < x ] → [ (a < b) ⇔ ((a * x) < (b * x)) ]
    ·-creates-< a b x p .fst q = ·-preserves-< a b x p q
    ·-creates-< a b x p .snd q = ·ᶻ-reflects-<ᶻ a b x p q

    ·-creates-≤ : ∀ a b x → [ 0f ≤ x ] → [ (a ≤ b) ⇔ ((a · x) ≤ (b · x)) ]
    ·-creates-≤ a b x 0≤x .fst p = {!   !}
    ·-creates-≤ a b x 0≤x .snd p = {!   !}

    ·-creates-≤-≡ : ∀ a b x → [ 0f ≤ x ] → (a ≤ b) ≡ ((a · x) ≤ (b · x))
    ·-creates-≤-≡ a b x 0≤x = uncurry ⇔toPath $ ·-creates-≤ a b x 0≤x

  ℤlattice : Lattice {ℓ-zero} {ℓ-zero}
  ℤlattice = record { LinearlyOrderedCommRing ℤbundle renaming (≤-Lattice to is-Lattice) }

  open import MorePropAlgebra.Properties.Lattice ℤlattice
  open OnSet is-set hiding (+-min-distribʳ; ·-min-distribʳ; +-max-distribʳ; ·-max-distribʳ)

  abstract
    ≤-dicho : ∀ x y → [ (x ≤ y) ⊔ (y ≤ x) ]
    ≤-dicho x y with <-tricho x y
    ... | inl (inl x<y) = inlᵖ $ <-asym x y x<y
    ... | inl (inr y<x) = inrᵖ $ <-asym y x y<x
    ... | inr      x≡y  = inlᵖ $ subst (λ p → [ ¬(p <ᶻ x) ]) x≡y (<-irrefl x)

    ≤-min-+ : ∀ a b c w → [ w ≤ (a + c) ] → [ w ≤ (b + c) ] → [ w ≤ (min a b + c) ]
    ≤-max-+ : ∀ a b c w → [ (a + c) ≤ w ] → [ (b + c) ≤ w ] → [ (max a b + c) ≤ w ]
    ≤-min-· : ∀ a b c w → [ w ≤ (a · c) ] → [ w ≤ (b · c) ] → [ w ≤ (min a b · c) ]
    ≤-max-· : ∀ a b c w → [ (a · c) ≤ w ] → [ (b · c) ≤ w ] → [ (max a b · c) ≤ w ]

    ≤-min-+ = OnType.≤-dicho⇒+.≤-min-+ _+_ ≤-dicho
    ≤-max-+ = OnType.≤-dicho⇒+.≤-max-+ _+_ ≤-dicho
    ≤-min-· = OnType.≤-dicho⇒·.≤-min-· _·_ ≤-dicho
    ≤-max-· = OnType.≤-dicho⇒·.≤-max-· _·_ ≤-dicho

    +-min-distribʳ : ∀ x y z              → (min x y + z) ≡ min (x + z) (y + z)
    ·-min-distribʳ : ∀ x y z → [ 0f ≤ z ] → (min x y · z) ≡ min (x · z) (y · z)
    +-max-distribʳ : ∀ x y z              → (max x y + z) ≡ max (x + z) (y + z)
    ·-max-distribʳ : ∀ x y z → [ 0f ≤ z ] → (max x y · z) ≡ max (x · z) (y · z)
    +-min-distribˡ : ∀ x y z              → (z + min x y) ≡ min (z + x) (z + y)
    ·-min-distribˡ : ∀ x y z → [ 0f ≤ z ] → (z · min x y) ≡ min (z · x) (z · y)
    +-max-distribˡ : ∀ x y z              → (z + max x y) ≡ max (z + x) (z + y)
    ·-max-distribˡ : ∀ x y z → [ 0f ≤ z ] → (z · max x y) ≡ max (z · x) (z · y)

    +-min-distribʳ = OnSet.+-min-distribʳ is-set _+_ +-creates-≤ ≤-min-+
    ·-min-distribʳ = OnSet.·-min-distribʳ is-set 0f _·_ ·-creates-≤ ≤-min-·
    +-max-distribʳ = OnSet.+-max-distribʳ is-set _+_ +-creates-≤ ≤-max-+
    ·-max-distribʳ = OnSet.·-max-distribʳ is-set 0f _·_ ·-creates-≤ ≤-max-·

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

    -- *-nullifiesʳ : ∀(x : ℤ) → x * 0 ≡ 0
    -- *-nullifiesʳ (pos zero) = refl
    -- *-nullifiesʳ (pos (suc n)) = {! *-nullifiesʳ (pos n)  !}
    -- *-nullifiesʳ (neg zero) = refl
    -- *-nullifiesʳ (neg (suc n)) = {! *-nullifiesʳ (neg n)  !}
    -- *-nullifiesʳ (posneg i) = refl

    *-nullifiesˡ : ∀(x : ℤ) → 0 * x ≡ 0
    *-nullifiesˡ x = {!   !}

    *-preserves-<0 : ∀ a b → [ 0 < a ] → [ 0 < b ] → [ 0 < a * b ]
    *-preserves-<0 a b p q = subst (λ p → [ p < a * b ]) (*-nullifiesˡ b) (·-preserves-< 0 a b q p)

    -- data Trichotomy

    ·-creates-<-≡ : ∀ a b x → [ 0 < x ] → (a < b) ≡ ((a * x) < (b * x))
    ·-creates-<-≡ a b x p = ⇔toPath (·-creates-< a b x p .fst) (·-creates-< a b x p .snd)

  open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

  abstract
    lemma1 : ∀ a b₁ b₂ c → (a * b₁) * (b₂ * c) ≡ (a * c) * (b₂ * b₁)
    lemma1 a b₁ b₂ c =
      (a * b₁) * (b₂ * c) ≡⟨ sym $ ·-assoc a b₁ (b₂ * c) ⟩
      a * (b₁ * (b₂ * c)) ≡⟨ (λ i → a * ·-assoc b₁ b₂ c i) ⟩
      a * ((b₁ * b₂) * c) ≡⟨ (λ i → a * ·-comm (b₁ * b₂) c i) ⟩
      a * (c * (b₁ * b₂)) ≡⟨ ·-assoc a c (b₁ * b₂) ⟩
      (a * c) * (b₁ * b₂) ≡⟨ (λ i → (a * c) * ·-comm b₁ b₂ i) ⟩
      (a * c) * (b₂ * b₁) ∎

  -- TODO: we might extract definition and properties in the where clauses upfront
  infixl 4 _<ᶠ_
  _<ᶠ_ : hPropRel ℚ ℚ ℓ-zero
  a <ᶠ b = SetQuotient.rec2 {R = _∼_} {B = hProp ℓ-zero} isSetHProp _<'_ <'-respects-∼ˡ <'-respects-∼ʳ a b where
    _<'_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → hProp ℓ-zero
    (aᶻ , aⁿ) <' (bᶻ , bⁿ) =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      in (aᶻ * bⁿᶻ) < (bᶻ * aⁿᶻ)
    abstract
      <'-respects-∼ˡ : ∀ a b x → a ∼ b → a <' x ≡ b <' x
      <'-respects-∼ˡ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b = γ where
        aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
        bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
        xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
        0<aⁿᶻ : [ 0 < aⁿᶻ ]
        0<aⁿᶻ = 0<ᶻpos[suc] _
        0<bⁿᶻ : [ 0 < bⁿᶻ ]
        0<bⁿᶻ = 0<ᶻpos[suc] _
        p : aᶻ * bⁿᶻ ≡ bᶻ * aⁿᶻ
        p = a~b
        γ : ((aᶻ * xⁿᶻ) < (xᶻ * aⁿᶻ)) ≡ ((bᶻ * xⁿᶻ) < (xᶻ * bⁿᶻ))
        γ with <-tricho 0 aᶻ
        ... | inl (inl 0<aᶻ) =
          (aᶻ * xⁿᶻ)              < (xᶻ * aⁿᶻ)              ≡⟨ ·-creates-<-≡ (aᶻ * xⁿᶻ) (xᶻ * aⁿᶻ) (aᶻ * bⁿᶻ) (*-preserves-<0 aᶻ bⁿᶻ 0<aᶻ 0<bⁿᶻ) ⟩
          (aᶻ * xⁿᶻ) * (aᶻ * bⁿᶻ) < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) ≡⟨ (λ i → (aᶻ * xⁿᶻ) * p i < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ)) ⟩
          (aᶻ * xⁿᶻ) * (bᶻ * aⁿᶻ) < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) ≡⟨ (λ i → ·-comm (aᶻ * xⁿᶻ) (bᶻ * aⁿᶻ) i < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ)) ⟩
          (bᶻ * aⁿᶻ) * (aᶻ * xⁿᶻ) < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) ≡⟨ (λ i → lemma1 bᶻ aⁿᶻ aᶻ xⁿᶻ i < lemma1 xᶻ aⁿᶻ aᶻ bⁿᶻ i) ⟩
          (bᶻ * xⁿᶻ) * (aᶻ * aⁿᶻ) < (xᶻ * bⁿᶻ) * (aᶻ * aⁿᶻ) ≡⟨ sym $ ·-creates-<-≡ (bᶻ * xⁿᶻ) (xᶻ * bⁿᶻ) (aᶻ * aⁿᶻ) (*-preserves-<0 aᶻ aⁿᶻ 0<aᶻ 0<aⁿᶻ) ⟩
          (bᶻ * xⁿᶻ)              < (xᶻ * bⁿᶻ)              ∎
        ... | inl (inr aᶻ<0) = {!   !}
        ... | inr      0≡aᶻ  =
          (aᶻ * xⁿᶻ) < (xᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
          ( 0 * xⁿᶻ) < (xᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
            0        < (xᶻ * aⁿᶻ) ≡⟨ {! κ   !} ⟩
            0        < (xᶻ * bⁿᶻ) ≡⟨ {!   !} ⟩
          ( 0 * xⁿᶻ) < (xᶻ * bⁿᶻ) ≡⟨ {!   !} ⟩
          (bᶻ * xⁿᶻ) < (xᶻ * bⁿᶻ) ∎ where
            bᶻ≡0 : bᶻ ≡ 0
            bᶻ≡0 = {!   !}
            κ : ∀ x y z → [ 0 < y ] → [ 0 < z ] → (0 < (x * y)) ≡ (0 < (x * z))
            κ x y z p q =
               0      < (x * y) ≡⟨ {!   !} ⟩
              (0 * y) < (x * y) ≡⟨ {!   !} ⟩
               0      <  x      ≡⟨ {!   !} ⟩
              (0 * z) < (x * z) ≡⟨ {!   !} ⟩
               0      < (x * z) ∎
        -- in (aᶻ * xⁿᶻ)              < (xᶻ * aⁿᶻ)              ≡⟨ {!   !} ⟩
        --    (aᶻ * xⁿᶻ) / (aᶻ * bⁿᶻ) < (xᶻ * aⁿᶻ) / (bᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
        --          xⁿᶻ  /       bⁿᶻ  <  xᶻ        /  bᶻ        ≡⟨ {!   !} ⟩
        --    (bᶻ * xⁿᶻ) < (xᶻ * bⁿᶻ) ∎

        -- aᶻ > 0:
    abstract
      <'-respects-∼ʳ : ∀ x a b → a ∼ b → x <' a ≡ x <' b
      <'-respects-∼ʳ x@(xᶻ , xⁿ) a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) a~b =
        let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
            bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
            xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
            p : aᶻ * bⁿᶻ ≡ bᶻ * aⁿᶻ
            p = a~b
        in (xᶻ * aⁿᶻ)              < (aᶻ * xⁿᶻ)              ≡⟨ {!   !} ⟩
           (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) < (aᶻ * xⁿᶻ) * (aᶻ * bⁿᶻ) ≡⟨ {!   !} ⟩
           (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) < (aᶻ * xⁿᶻ) * (bᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
           (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) < (bᶻ * aⁿᶻ) * (aᶻ * xⁿᶻ) ≡⟨ {!   !} ⟩
           (xᶻ * bⁿᶻ) * (aᶻ * aⁿᶻ) < (bᶻ * xⁿᶻ) * (aᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
           (xᶻ * bⁿᶻ)              < (bᶻ * xⁿᶻ)              ∎

  _≤ᶠ_ : hPropRel ℚ ℚ ℓ-zero
  x ≤ᶠ y = ¬ᵖ (y <ᶠ x)

  minᶠ : ℚ → ℚ → ℚ
  minᶠ a b = onCommonDenomSym min' min'-sym min'-respects-∼ a b where
    min' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
    min' (aᶻ , aⁿ) (bᶻ , bⁿ) =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      in min (aᶻ * bⁿᶻ) (bᶻ * aⁿᶻ)
    abstract
      min'-sym : ∀ x y → min' x y ≡ min' y x
      min'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = min-comm (aᶻ * [1+ bⁿ ⁿ]ᶻ) (bᶻ * [1+ aⁿ ⁿ]ᶻ)
      min'-respects-∼ : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
        → a ∼ b
        → [1+ bⁿ ⁿ]ᶻ * min' a x ≡ [1+ aⁿ ⁿ]ᶻ * min' b x
      min'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
        bⁿᶻ * min (aᶻ * xⁿᶻ) (xᶻ * aⁿᶻ)           ≡⟨ ·-min-distribˡ (aᶻ * xⁿᶻ) (xᶻ * aⁿᶻ) bⁿᶻ 0≤bⁿᶻ ⟩
        min (bⁿᶻ * (aᶻ * xⁿᶻ)) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → min (·-assoc bⁿᶻ aᶻ xⁿᶻ i) (bⁿᶻ * (xᶻ * aⁿᶻ))) ⟩
        min ((bⁿᶻ * aᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → min ((·-comm bⁿᶻ aᶻ i) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ))) ⟩
        min ((aᶻ * bⁿᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → min (p i * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ))) ⟩
        min ((bᶻ * aⁿᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → min (·-comm bᶻ aⁿᶻ i * xⁿᶻ) (·-assoc bⁿᶻ xᶻ aⁿᶻ i)) ⟩
        min ((aⁿᶻ * bᶻ) * xⁿᶻ) ((bⁿᶻ * xᶻ) * aⁿᶻ) ≡⟨ (λ i → min (·-assoc aⁿᶻ bᶻ xⁿᶻ (~ i)) (·-comm (bⁿᶻ * xᶻ) aⁿᶻ i)) ⟩
        min (aⁿᶻ * (bᶻ * xⁿᶻ)) (aⁿᶻ * (bⁿᶻ * xᶻ)) ≡⟨ sym $ ·-min-distribˡ (bᶻ * xⁿᶻ) (bⁿᶻ * xᶻ) aⁿᶻ 0≤aⁿᶻ ⟩
        aⁿᶻ * min (bᶻ * xⁿᶻ) (bⁿᶻ * xᶻ)           ≡⟨ (λ i → aⁿᶻ * min (bᶻ * xⁿᶻ) (·-comm bⁿᶻ xᶻ i)) ⟩
        aⁿᶻ * min (bᶻ * xⁿᶻ) (xᶻ * bⁿᶻ)           ∎
        where
          aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
          xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
          p : aᶻ * bⁿᶻ ≡ bᶻ * aⁿᶻ
          p = a~b
          0≤aⁿᶻ : [ 0 ≤ aⁿᶻ ]
          0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
          0≤bⁿᶻ : [ 0 ≤ bⁿᶻ ]
          0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

  -- same proof as for min
  maxᶠ : ℚ → ℚ → ℚ
  maxᶠ a b = onCommonDenomSym max' max'-sym max'-respects-∼ a b where
    max' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
    max' (aᶻ , aⁿ) (bᶻ , bⁿ) =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      in max (aᶻ * bⁿᶻ) (bᶻ * aⁿᶻ)
    abstract
      max'-sym : ∀ x y → max' x y ≡ max' y x
      max'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = max-comm (aᶻ * [1+ bⁿ ⁿ]ᶻ) (bᶻ * [1+ aⁿ ⁿ]ᶻ)
      max'-respects-∼ : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
        → a ∼ b
        → [1+ bⁿ ⁿ]ᶻ * max' a x ≡ [1+ aⁿ ⁿ]ᶻ * max' b x
      max'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
        bⁿᶻ * max (aᶻ * xⁿᶻ) (xᶻ * aⁿᶻ)           ≡⟨ ·-max-distribˡ (aᶻ * xⁿᶻ) (xᶻ * aⁿᶻ) bⁿᶻ 0≤bⁿᶻ ⟩
        max (bⁿᶻ * (aᶻ * xⁿᶻ)) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → max (·-assoc bⁿᶻ aᶻ xⁿᶻ i) (bⁿᶻ * (xᶻ * aⁿᶻ))) ⟩
        max ((bⁿᶻ * aᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → max ((·-comm bⁿᶻ aᶻ i) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ))) ⟩
        max ((aᶻ * bⁿᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → max (p i * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ))) ⟩
        max ((bᶻ * aⁿᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ (λ i → max (·-comm bᶻ aⁿᶻ i * xⁿᶻ) (·-assoc bⁿᶻ xᶻ aⁿᶻ i)) ⟩
        max ((aⁿᶻ * bᶻ) * xⁿᶻ) ((bⁿᶻ * xᶻ) * aⁿᶻ) ≡⟨ (λ i → max (·-assoc aⁿᶻ bᶻ xⁿᶻ (~ i)) (·-comm (bⁿᶻ * xᶻ) aⁿᶻ i)) ⟩
        max (aⁿᶻ * (bᶻ * xⁿᶻ)) (aⁿᶻ * (bⁿᶻ * xᶻ)) ≡⟨ sym $ ·-max-distribˡ (bᶻ * xⁿᶻ) (bⁿᶻ * xᶻ) aⁿᶻ 0≤aⁿᶻ ⟩
        aⁿᶻ * max (bᶻ * xⁿᶻ) (bⁿᶻ * xᶻ)           ≡⟨ (λ i → aⁿᶻ * max (bᶻ * xⁿᶻ) (·-comm bⁿᶻ xᶻ i)) ⟩
        aⁿᶻ * max (bᶻ * xⁿᶻ) (xᶻ * bⁿᶻ)           ∎
        where
          aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
          xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
          p : aᶻ * bⁿᶻ ≡ bᶻ * aⁿᶻ
          p = a~b
          0≤aⁿᶻ : [ 0 ≤ aⁿᶻ ]
          0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
          0≤bⁿᶻ : [ 0 ≤ bⁿᶻ ]
          0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

  -- maxᶠ : ℚ → ℚ → ℚ
  -- maxᶠ a b = onCommonDenom f g h a b where
  --   f : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  --   f (aᶻ , aⁿ) (bᶻ , bⁿ) = max (aᶻ * [1+ bⁿ ⁿ]ᶻ) (bᶻ * [1+ aⁿ ⁿ]ᶻ)
  --   g : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
  --     → aᶻ * [1+ bⁿ ⁿ]ᶻ         ≡ bᶻ * [1+ aⁿ ⁿ]ᶻ
  --     →      [1+ bⁿ ⁿ]ᶻ * f a c ≡      [1+ aⁿ ⁿ]ᶻ * f b c
  --   g a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) aᶻ*bⁿ'≡bᶻ*aⁿ' = let
  --     aⁿ' = [1+ aⁿ ⁿ]ᶻ
  --     bⁿ' = [1+ bⁿ ⁿ]ᶻ
  --     cⁿ' = [1+ cⁿ ⁿ]ᶻ
  --     0<aⁿ' : [ 0 < aⁿ' ]
  --     0<aⁿ' = 0<ᶻpos[suc] _
  --     0<bⁿ' : [ 0 < bⁿ' ]
  --     0<bⁿ' = 0<ᶻpos[suc] _
  --     0<cⁿ' : [ 0 < cⁿ' ]
  --     0<cⁿ' = 0<ᶻpos[suc] _
  --     γ : bⁿ' * max (aᶻ * cⁿ') (cᶻ * aⁿ')
  --       ≡ aⁿ' * max (bᶻ * cⁿ') (cᶻ * bⁿ')
  --     γ = {!   !}
  --     in γ
  --   h : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
  --     →     bᶻ * [1+ cⁿ ⁿ]ᶻ ≡     cᶻ * [1+ bⁿ ⁿ]ᶻ
  --     → f a b  * [1+ cⁿ ⁿ]ᶻ ≡ f a c  * [1+ bⁿ ⁿ]ᶻ
  --   h a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) bᶻ*cⁿ≡cᶻ*bⁿ = {!   !}

open Definitions public renaming
  ( _<ᶠ_ to _<_
  ; _≤ᶠ_ to _≤_
  ; minᶠ to min
  ; maxᶠ to max
  )

open LinearlyOrderedCommRing ℤbundle using () renaming
  ( min to minᶻ
  ; max to maxᶻ
  -- ; _<_ to _<ᶻ_
  ; _≤_ to _≤ᶻ_
  ; <-irrefl to <ᶻ-irrefl
  ; <-trans to <ᶻ-trans
  ; is-min to is-minᶻ
  ; is-max to is-maxᶻ
  ; ·-assoc to ·ᶻ-assoc
  ; ·-comm to ·ᶻ-comm
  ; <-tricho to <ᶻ-tricho
  ; -_ to -ᶻ_
  )

open import Cubical.HITs.Rationals.QuoQ renaming
  ( [_] to [_]ᶠ
  ; eq/ to eq/ᶠ
  ; ℕ₊₁→ℤ to [1+_ⁿ]ᶻ
  )

open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)
open import Cubical.HITs.Ints.QuoInt using (ℤ) renaming (_*_ to _*ᶻ_; sign to signᶻ)
open import Cubical.HITs.PropositionalTruncation renaming (elim to ∣∣-elim)

abstract
  <-irrefl : ∀ a → [ ¬(a < a) ]
  <-irrefl = SetQuotient.elimProp {R = _∼_} (λ a → isProp[] (¬(a < a))) γ where
    γ : (a : ℤ × ℕ₊₁) → [ ¬([ a ]ᶠ < [ a ]ᶠ) ]
    γ a@(aᶻ , aⁿ) = κ where
      aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      κ : [ ¬((aᶻ *ᶻ aⁿᶻ) <ᶻ (aᶻ *ᶻ aⁿᶻ)) ]
      κ = <ᶻ-irrefl (aᶻ *ᶻ aⁿᶻ)

  <-trans : (a b c : ℚ) → [ a < b ] → [ b < c ] → [ a < c ]
  <-trans = SetQuotient.elimProp3 {R = _∼_} (λ a b c → isProp[] ((a < b) ⇒ (b < c) ⇒ (a < c))) γ where
    γ : (a b c : ℤ × ℕ₊₁) → [ [ a ]ᶠ < [ b ]ᶠ ] → [ [ b ]ᶠ < [ c ]ᶠ ] → [ [ a ]ᶠ < [ c ]ᶠ ]
    γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = κ where
      aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      cⁿᶻ = [1+ cⁿ ⁿ]ᶻ
      κ : [ (aᶻ *ᶻ bⁿᶻ) <ᶻ (bᶻ *ᶻ aⁿᶻ) ] → [ (bᶻ *ᶻ cⁿᶻ) <ᶻ (cᶻ *ᶻ bⁿᶻ) ] → [ (aᶻ *ᶻ cⁿᶻ) <ᶻ (cᶻ *ᶻ aⁿᶻ) ]
      -- strategy: multiply with xⁿᶻ and then use <ᶻ-trans
      κ = {!!}

  <-asym : ∀ a b → [ a < b ] → [ ¬(b < a) ]
  <-asym a b a<b b<a = <-irrefl a (<-trans a b a a<b b<a)

  <-irrefl'' : ∀ a b → [ a < b ] ⊎ [ b < a ] → [ ¬(a ≡ₚ b) ]
  <-irrefl'' a b (inl a<b) a≡b = <-irrefl b (substₚ (λ p → p < b) a≡b a<b)
  <-irrefl'' a b (inr b<a) a≡b = <-irrefl b (substₚ (λ p → b < p) a≡b b<a)

  <-tricho : (a b : ℚ) → ([ a < b ] ⊎ [ b < a ]) ⊎ [ a ≡ₚ b ] -- TODO: insert trichotomy definition here
  <-tricho = SetQuotient.elimProp2 {R = _∼_} (λ a b → isProp[] ([ <-irrefl'' a b ] ([ <-asym a b ] (a < b) ⊎ᵖ (b < a)) ⊎ᵖ (a ≡ₚ b))) γ where
    γ : (a b : ℤ × ℕ₊₁) → ([ [ a ]ᶠ < [ b ]ᶠ ] ⊎ [ [ b ]ᶠ < [ a ]ᶠ ]) ⊎ [ [ a ]ᶠ ≡ₚ [ b ]ᶠ ]
    γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) = κ where
      aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      κ : ([ (aᶻ *ᶻ bⁿᶻ) <ᶻ (bᶻ *ᶻ aⁿᶻ) ] ⊎ [ (bᶻ *ᶻ aⁿᶻ) <ᶻ (aᶻ *ᶻ bⁿᶻ) ]) ⊎ [ [ aᶻ , aⁿ ]ᶠ ≡ₚ [ bᶻ , bⁿ ]ᶠ ]
      κ with <ᶻ-tricho (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ)
      ... | inl p = inl p
      ... | inr p = inr ∣ eq/ᶠ {R = _∼_} a b p ∣

  <ᶻ-asym : ∀ a b → [ a <ᶻ b ] → [ ¬(b <ᶻ a) ]
  <ᶻ-asym a b a<b b<a = <ᶻ-irrefl a (<ᶻ-trans a b a a<b b<a)

_#ᶻ_ : hPropRel ℤ ℤ ℓ-zero
x #ᶻ y = [ <ᶻ-asym x y ] (x <ᶻ y) ⊎ᵖ (y <ᶻ x)

_#_ : hPropRel ℚ ℚ ℓ-zero
x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

injᶻⁿ⁺¹ : ∀ x → [ 0 <ᶻ x ] → Σ[ y ∈ ℕ₊₁ ] x ≡ [1+ y ⁿ]ᶻ
injᶻⁿ⁺¹ (signed false zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i0 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (signed true  zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i1 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (ℤ.posneg i)        p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i  ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (signed false (suc n)) p =  1+ n , refl

abstract
  -flips-<ᶻ0 : ∀ x → [ (x <ᶻ 0) ⇔ (0 <ᶻ (-ᶻ x)) ]
  -flips-<ᶻ0 (signed false zero) = (λ x → x) , (λ x → x)
  -flips-<ᶻ0 (signed true  zero) = (λ x → x) , (λ x → x)
  -flips-<ᶻ0 (ℤ.posneg i)        = (λ x → x) , (λ x → x)
  -flips-<ᶻ0 (signed false (suc n)) .fst p  = ¬-<ⁿ-zero p
  -flips-<ᶻ0 (signed true  (suc n)) .fst tt = n , +ⁿ-comm n 1
  -flips-<ᶻ0 (signed true  (suc n)) .snd p  = tt


-- -flips-< : ∀ x y → [ x <ᶻ y ⇔ - y <ᶻ - x ]

-- #-Dichotomyˢ : {A : Type ℓ} (is-set : isSet A) (_#_ : hPropRel A A ℓ) )(#-tight : ∀ x y → [ x # y ⇔ ¬([ is-set ] x ≡ˢ y) ] ) (x : A) → hProp ℓ
-- #-Dichotomyˢ x = [ #-tight x 0 .fst ] x # 0 ⊎ᵖ (x ≡ 0)

#ᶻ-dicho : ∀ x → [ x #ᶻ 0 ] ⊎ (x ≡ 0)
#ᶻ-dicho x = <ᶻ-tricho x 0

⊕-identityʳ : ∀ s → (s Bool.⊕ false) ≡ s
⊕-identityʳ false = refl
⊕-identityʳ true  = refl

abstract
  *ᶻ-preserves-signˡ : ∀ x y → [ 0 <ᶻ y ] → signᶻ (x *ᶻ y) ≡ signᶻ x
  *ᶻ-preserves-signˡ x (signed false zero) p = ⊥-elim {A = λ _ → signᶻ (x *ᶻ ℤ.posneg i0) ≡ signᶻ x} (¬-<ⁿ-zero p)
  *ᶻ-preserves-signˡ x (signed true  zero) p = ⊥-elim {A = λ _ → signᶻ (x *ᶻ ℤ.posneg i1) ≡ signᶻ x} (¬-<ⁿ-zero p)
  *ᶻ-preserves-signˡ x (ℤ.posneg i)        p = ⊥-elim {A = λ _ → signᶻ (x *ᶻ ℤ.posneg i ) ≡ signᶻ x} (¬-<ⁿ-zero p)
  *ᶻ-preserves-signˡ (signed false zero) (signed false (suc n)) p = refl
  *ᶻ-preserves-signˡ (signed true  zero) (signed false (suc n)) p = refl
  *ᶻ-preserves-signˡ (ℤ.posneg i)        (signed false (suc n)) p = refl
  *ᶻ-preserves-signˡ (signed s (suc n₁)) (signed false (suc n)) p = ⊕-identityʳ s


absⁿ⁺¹' : ℤ → ℕ₊₁
absⁿ⁺¹' xᶻ with <ᶻ-tricho 0 xᶻ
... | inl (inl 0<xᶻ) = injᶻⁿ⁺¹ xᶻ 0<xᶻ .fst
... | inl (inr xᶻ<0) = injᶻⁿ⁺¹ (-ᶻ xᶻ) ( -flips-<ᶻ0 xᶻ .fst xᶻ<0) .fst
... | inr      0≡xᶻ  = 1+ 0 -- this case will be excluded lateron, but we keep it here to omit the definition of a nonzero ℚ

-- absⁿ⁺¹'-identity⁺ : ∀ x → signed false (ℕ₊₁→ℕ x) ≡ [1+ absⁿ⁺¹' x ⁿ]ᶻ
-- absⁿ⁺¹'-identity⁺ x = ?

absⁿ⁺¹'-identity⁺ : ∀ x → [1+ absⁿ⁺¹' (pos x) ⁿ]ᶻ ≡ pos x
absⁿ⁺¹'-identity⁺ x with <ᶻ-tricho 0 (pos x)
... | inl (inl 0<xᶻ) = {!!}
... | inl (inr xᶻ<0) = {!!}
... | inr      0≡xᶻ  = {!!}

_⁻¹''' : (x : ℚ) → [ x # 0 ] → ℚ
_⁻¹''' = {! SetQuotient.elim {R = _∼_} {B = λ x → [ x # 0 ] → ℚ} φ _⁻¹'' ⁻¹''-respects-∼   !} where
  φ : ∀ x → isSet ([ x # 0 ] → ℚ)
  φ x = isSetΠ (λ _ → isSetℚ)
  _⁻¹''  : (a : ℤ × ℕ₊₁) → [ [ a ]ᶠ # 0 ] → ℚ
  x ⁻¹'' = {!!}
  ⁻¹''-respects-∼ : (a b : ℤ × ℕ₊₁) (r : a ∼ b)
                  → PathP (λ i → [ eq/ᶠ a b r i # 0 ] → ℚ) (a ⁻¹'') (b ⁻¹'')
  ⁻¹''-respects-∼ a b r = {!!}

isSet→ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (isSet B) → isSet (A → B)
isSet→ {B = B} isset = isSetΠ λ _ → isset

_⁻¹' : ℚ → ℚ
_⁻¹' = SetQuotient.rec {R = _∼_} isSetℚ _⁻¹'' ⁻¹''-respects-∼  where
  _⁻¹'' : ℤ × ℕ₊₁ → ℚ
  (xᶻ , xⁿ) ⁻¹'' = [ signed (signᶻ xᶻ) (ℕ₊₁→ℕ xⁿ) , absⁿ⁺¹' xᶻ ]ᶠ
  ⁻¹''-respects-∼ : (a b : ℤ × ℕ₊₁) → a ∼ b → (a ⁻¹'') ≡ (b ⁻¹'')
  ⁻¹''-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p = κ where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]
    0<aⁿᶻ = ℕ₊₁.n aⁿ , +ⁿ-comm (ℕ₊₁.n aⁿ) 1
    0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]
    0<bⁿᶻ = ℕ₊₁.n bⁿ , +ⁿ-comm (ℕ₊₁.n bⁿ) 1
    q : aᶻ *ᶻ bⁿᶻ ≡ bᶻ *ᶻ aⁿᶻ
    q = p
    sign≡ =
      signᶻ aᶻ          ≡⟨ sym $ *ᶻ-preserves-signˡ aᶻ bⁿᶻ 0<bⁿᶻ ⟩
      signᶻ (aᶻ *ᶻ bⁿᶻ) ≡⟨ (λ i → signᶻ (q i)) ⟩
      signᶻ (bᶻ *ᶻ aⁿᶻ) ≡⟨ *ᶻ-preserves-signˡ bᶻ aⁿᶻ 0<aⁿᶻ ⟩
      signᶻ bᶻ          ∎
    cᶻ dᶻ : ℤ
    cᶻ = signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ)
    dᶻ = signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ)
    cⁿ dⁿ : ℕ₊₁
    cⁿ = absⁿ⁺¹' aᶻ
    dⁿ = absⁿ⁺¹' bᶻ
    t : ∀ s → (signed s (ℕ₊₁→ℕ aⁿ) *ᶻ [1+ absⁿ⁺¹' bᶻ ⁿ]ᶻ) ≡ (signed s (ℕ₊₁→ℕ bⁿ) *ᶻ [1+ absⁿ⁺¹' aᶻ ⁿ]ᶻ)
    t false = {!!}
    t true  = {!!}
    r : (signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) *ᶻ [1+ absⁿ⁺¹' bᶻ ⁿ]ᶻ) ≡ (signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) *ᶻ [1+ absⁿ⁺¹' aᶻ ⁿ]ᶻ)
    r = {!!}
    κ : ([ cᶻ , cⁿ  ]ᶠ) ≡ ([ dᶻ  , dⁿ  ]ᶠ)
    κ = eq/ᶠ {R = _∼_} (cᶻ , cⁿ) (dᶻ  , dⁿ) r

·-inv'' : ∀ x → [ (∃[ y ] ([ isSetℚ ] (x * y) ≡ˢ 1)) ⇔ (x # 0) ]
-- ·-inv'' x .fst p = {!   !}
-- ·-inv'' x .snd p = {!   !}
·-inv'' = SetQuotient.elimProp {R = _∼_} φ {!   !} where
  φ : (x : ℚ) → _
  φ x = isProp[] ((∃[ y ] ([ isSetℚ ] (x * y) ≡ˢ 1)) ⇔ (x # 0))
  κ₁ : ∀ x → [ ∃[ y ] ([ isSetℚ ] (x * y) ≡ˢ 1) ] → [ x # 0 ]
  κ₁ x p = ∣∣-elim (λ _ → φ') (λ{ (y , q) → γ y q } ) p    where
    φ' = isProp[] (x # 0)
    γ : ∀ y → [ [ isSetℚ ] (x * y) ≡ˢ 1 ] → [ x # 0 ]
    γ y q = {!!}
  κ₂ : ∀ x → [ x # 0 ] → [ ∃[ y ] ([ isSetℚ ] (x * y) ≡ˢ 1) ]
  κ₂ x (inl x<0) = {!   !}
  -- well.. we would need ℚ⁺ here
  κ₂ x (inr 0<x) =  ∣ SetQuotient.rec {R = _∼_} isSetℚ {!!} {!!} x , {!!} ∣ where
    _⁻¹⁺ : ℤ × ℕ₊₁ → ℚ
    _⁻¹⁺ (aᶻ , aⁿ) = {!!}

+-Semigroup : [ isSemigroup _+_ ]
+-Semigroup .IsSemigroup.is-set   = isSetℚ
+-Semigroup .IsSemigroup.is-assoc = +-assoc

·-Semigroup : [ isSemigroup _*_ ]
·-Semigroup .IsSemigroup.is-set   = isSetℚ
·-Semigroup .IsSemigroup.is-assoc = *-assoc

+-Monoid : [ isMonoid 0 _+_ ]
+-Monoid .IsMonoid.is-Semigroup  = +-Semigroup
+-Monoid .IsMonoid.is-identity x = +-identityʳ x , +-identityˡ x

·-Monoid : [ isMonoid 1 _*_ ]
·-Monoid .IsMonoid.is-Semigroup  = ·-Semigroup
·-Monoid .IsMonoid.is-identity x = *-identityʳ x , *-identityˡ x

is-Semiring : [ isSemiring 0 1 _+_ _*_ ]
is-Semiring .IsSemiring.+-Monoid = +-Monoid
is-Semiring .IsSemiring.·-Monoid = ·-Monoid
is-Semiring .IsSemiring.+-comm   = +-comm
is-Semiring .IsSemiring.is-dist x y z = sym (*-distribˡ x y z) , sym (*-distribʳ x y z)

is-CommSemiring : [ isCommSemiring 0 1 _+_ _*_ ]
is-CommSemiring .IsCommSemiring.is-Semiring = is-Semiring
is-CommSemiring .IsCommSemiring.·-comm      = *-comm


<-StrictLinearOrder : [ isStrictLinearOrder _<_ ]
<-StrictLinearOrder .IsStrictLinearOrder.is-irrefl = <-irrefl
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  = <-trans
<-StrictLinearOrder .IsStrictLinearOrder.is-tricho = <-tricho

open import Cubical.Data.NatPlusOne using (_*₊₁_)

⇔toPath' : ∀{ℓ} {P Q : hProp ℓ} → [ P ⇔ Q ] → P ≡ Q
⇔toPath' = uncurry ⇔toPath

pathTo⇔ : ∀{ℓ} {P Q : hProp ℓ} → P ≡ Q → [ P ⇔ Q ]
pathTo⇔ p≡q = (pathTo⇒ p≡q , pathTo⇐ p≡q)

⊓⇔⊓ : ∀{ℓ ℓ' ℓ'' ℓ'''} {P : hProp ℓ} {Q : hProp ℓ'} {R : hProp ℓ''} {S : hProp ℓ'''}
   → [ (P ⇔ R) ⊓ (Q ⇔ S) ] → [ (P ⊓ Q) ⇔ (R ⊓ S) ]
⊓⇔⊓ (p⇔r , q⇔s) .fst (p , q) = p⇔r .fst p , q⇔s .fst q
⊓⇔⊓ (p⇔r , q⇔s) .snd (r , s) = p⇔r .snd r , q⇔s .snd s

⊓≡⊓ : ∀{ℓ} {P Q R S : hProp ℓ} → P ≡ R → Q ≡ S → (P ⊓ Q) ≡ (R ⊓ S)
⊓≡⊓ p≡r q≡s i = p≡r i ⊓ q≡s i

abstract
  is-min : (x y z : ℚ) → [ (z ≤ min x y) ⇔ (z ≤ x) ⊓ (z ≤ y) ]
  is-min = SetQuotient.elimProp3  {R = _∼_} (λ x y z → isProp[] ((z ≤ min x y) ⇔ (z ≤ x) ⊓ (z ≤ y))) γ where
    γ : (a b c : ℤ × ℕ₊₁) → [ ([ c ]ᶠ ≤ min [ a ]ᶠ [ b ]ᶠ) ⇔ ([ c ]ᶠ ≤ [ a ]ᶠ) ⊓ ([ c ]ᶠ ≤ [ b ]ᶠ) ]
    γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = pathTo⇔ (sym κ) where
      aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      cⁿᶻ = [1+ cⁿ ⁿ]ᶻ
      0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]
      0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
      0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]
      0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
      0≤cⁿᶻ : [ 0 ≤ᶻ cⁿᶻ ]
      0≤cⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
      -- -- note, that the following holds definitionally (TODO: put this at the definition of `min`)
      -- _ =    min [ aᶻ , aⁿ ]ᶠ [ bᶻ , bⁿ ]ᶠ                 ≡⟨ refl ⟩
      --     [ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) , aⁿ *₊₁ bⁿ) ]ᶠ  ∎
      -- -- and we also have definitionally
      -- _ : [1+ aⁿ *₊₁ bⁿ ⁿ]ᶻ ≡ aⁿᶻ *ᶻ bⁿᶻ
      -- _ = refl
      -- -- therefore, we have for the LHS:
      -- _ = ([ cᶻ , cⁿ ]ᶠ ≤ min [ aᶻ , aⁿ ]ᶠ [ bᶻ , bⁿ ]ᶠ)                      ≡⟨ refl ⟩
      --     ([ cᶻ , cⁿ ]ᶠ ≤ [ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) , aⁿ *₊₁ bⁿ) ]ᶠ)    ≡⟨ refl ⟩
      --     (¬([ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) , aⁿ *₊₁ bⁿ) ]ᶠ < [ cᶻ , cⁿ ]ᶠ)) ≡⟨ refl ⟩
      --     ¬((minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ) <ᶻ (cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)))    ≡⟨ refl ⟩
      --     ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ))     ∎
      -- -- similar for the RHS:
      -- _ =  ([ cᶻ , cⁿ ]ᶠ ≤ [ aᶻ , aⁿ ]ᶠ) ⊓  ([ cᶻ , cⁿ ]ᶠ ≤ [ bᶻ , bⁿ ]ᶠ) ≡⟨ refl ⟩
      --     ¬([ aᶻ , aⁿ ]ᶠ < [ cᶻ , cⁿ ]ᶠ) ⊓ ¬([ bᶻ , bⁿ ]ᶠ < [ cᶻ , cⁿ ]ᶠ) ≡⟨ refl ⟩
      --     ¬((aᶻ *ᶻ cⁿᶻ)  <ᶻ (cᶻ *ᶻ aⁿᶻ)) ⊓ ¬((bᶻ *ᶻ cⁿᶻ)  <ᶻ (cᶻ *ᶻ bⁿᶻ)) ≡⟨ refl ⟩
      --      ((cᶻ *ᶻ aⁿᶻ)  ≤ᶻ (aᶻ *ᶻ cⁿᶻ)) ⊓  ((cᶻ *ᶻ bⁿᶻ)  ≤ᶻ (bᶻ *ᶻ cⁿᶻ)) ∎
      -- -- therfore, only properties on ℤ remain
      -- RHS = [ ((cᶻ *ᶻ aⁿᶻ)  ≤ᶻ (aᶻ *ᶻ cⁿᶻ)) ⊓  ((cᶻ *ᶻ bⁿᶻ)  ≤ᶻ (bᶻ *ᶻ cⁿᶻ)) ]
      -- LHS = [ ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ)) ]
      -- strategy: multiply everything with aⁿᶻ, bⁿᶻ, cⁿᶻ
      κ = (
        ((cᶻ *ᶻ aⁿᶻ)         ≤ᶻ (aᶻ *ᶻ cⁿᶻ)        ) ⊓ ((cᶻ *ᶻ bⁿᶻ)         ≤ᶻ (bᶻ *ᶻ cⁿᶻ)        ) ≡⟨ ⊓≡⊓ (Definitions.·-creates-≤-≡ (cᶻ *ᶻ aⁿᶻ) (aᶻ *ᶻ cⁿᶻ) bⁿᶻ 0≤bⁿᶻ) (Definitions.·-creates-≤-≡ (cᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ cⁿᶻ) aⁿᶻ 0≤aⁿᶻ) ⟩
        ((cᶻ *ᶻ aⁿᶻ) *ᶻ bⁿᶻ  ≤ᶻ (aᶻ *ᶻ cⁿᶻ) *ᶻ bⁿᶻ ) ⊓ ((cᶻ *ᶻ bⁿᶻ) *ᶻ aⁿᶻ  ≤ᶻ (bᶻ *ᶻ cⁿᶻ) *ᶻ aⁿᶻ ) ≡⟨ ⊓≡⊓ (λ i → ·ᶻ-assoc cᶻ aⁿᶻ bⁿᶻ (~ i) ≤ᶻ ·ᶻ-assoc aᶻ cⁿᶻ bⁿᶻ (~ i)) (λ i → ·ᶻ-assoc cᶻ bⁿᶻ aⁿᶻ (~ i) ≤ᶻ ·ᶻ-assoc bᶻ cⁿᶻ aⁿᶻ (~ i)) ⟩
        ( cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ) ≤ᶻ  aᶻ *ᶻ (cⁿᶻ *ᶻ bⁿᶻ)) ⊓ ( cᶻ *ᶻ (bⁿᶻ *ᶻ aⁿᶻ) ≤ᶻ  bᶻ *ᶻ (cⁿᶻ *ᶻ aⁿᶻ)) ≡⟨ ⊓≡⊓ (λ i → cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ) ≤ᶻ  aᶻ *ᶻ (·ᶻ-comm cⁿᶻ bⁿᶻ i)) (λ i → cᶻ *ᶻ (·ᶻ-comm bⁿᶻ aⁿᶻ i) ≤ᶻ  bᶻ *ᶻ (·ᶻ-comm cⁿᶻ aⁿᶻ i)) ⟩
        ( cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ) ≤ᶻ  aᶻ *ᶻ (bⁿᶻ *ᶻ cⁿᶻ)) ⊓ ( cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ) ≤ᶻ  bᶻ *ᶻ (aⁿᶻ *ᶻ cⁿᶻ)) ≡⟨ sym $ ⇔toPath' $ is-minᶻ (aᶻ *ᶻ (bⁿᶻ *ᶻ cⁿᶻ)) (bᶻ *ᶻ (aⁿᶻ *ᶻ cⁿᶻ)) (cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ⟩
        ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ minᶻ (aᶻ *ᶻ (bⁿᶻ *ᶻ cⁿᶻ)) (bᶻ *ᶻ (aⁿᶻ *ᶻ cⁿᶻ)))                    ≡⟨ (λ i → ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ minᶻ (·ᶻ-assoc aᶻ bⁿᶻ cⁿᶻ i) (·ᶻ-assoc bᶻ aⁿᶻ cⁿᶻ i))) ⟩
        ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ minᶻ ((aᶻ *ᶻ bⁿᶻ) *ᶻ cⁿᶻ) ((bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ))                    ≡⟨ (λ i → (cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ Definitions.·-min-distribʳ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) cⁿᶻ 0≤cⁿᶻ (~ i)) ⟩
        ((cᶻ *ᶻ (aⁿᶻ *ᶻ bⁿᶻ)) ≤ᶻ (minᶻ (aᶻ *ᶻ bⁿᶻ) (bᶻ *ᶻ aⁿᶻ) *ᶻ cⁿᶻ))                             ∎)

≤-Lattice : [ isLattice _≤_ min max ]
≤-Lattice .IsLattice.≤-PartialOrder = linearorder⇒partialorder _ (≤'-isLinearOrder <-StrictLinearOrder)
≤-Lattice .IsLattice.is-min         = is-min
≤-Lattice .IsLattice.is-max         = {!   !}

is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0 1 _+_ _*_ _<_ min max ]
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.is-CommSemiring     = is-CommSemiring
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.<-StrictLinearOrder = <-StrictLinearOrder
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.≤-Lattice           = ≤-Lattice
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.+-<-ext             = {!   !}
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.·-preserves-<       = {!   !}

+-inverse : (x : ℚ) → (x + (- x) ≡ 0) × ((- x) + x ≡ 0)
+-inverse x .fst = +-inverseʳ x
+-inverse x .snd = +-inverseˡ x

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _*_ -_ _<_ min max ]
is-LinearlyOrderedCommRing. IsLinearlyOrderedCommRing.is-LinearlyOrderedCommSemiring = is-LinearlyOrderedCommSemiring
is-LinearlyOrderedCommRing. IsLinearlyOrderedCommRing.+-inverse                      = +-inverse

is-LinearlyOrderedField : [ isLinearlyOrderedField 0 1 _+_ _*_ -_ _<_ min max ]
is-LinearlyOrderedField .IsLinearlyOrderedField.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing
is-LinearlyOrderedField .IsLinearlyOrderedField.·-inv''                    = ·-inv''

ℚbundle : LinearlyOrderedField {ℓ-zero} {ℓ-zero}
ℚbundle .LinearlyOrderedField.Carrier                  = ℚ
ℚbundle .LinearlyOrderedField.0f                       = 0
ℚbundle .LinearlyOrderedField.1f                       = 1
ℚbundle .LinearlyOrderedField._+_                      = _+_
ℚbundle .LinearlyOrderedField.-_                       = -_
ℚbundle .LinearlyOrderedField._·_                      = _*_
ℚbundle .LinearlyOrderedField.min                      = min
ℚbundle .LinearlyOrderedField.max                      = max
ℚbundle .LinearlyOrderedField._<_                      = _<_
ℚbundle .LinearlyOrderedField.is-LinearlyOrderedField  = is-LinearlyOrderedField
