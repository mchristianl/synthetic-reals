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
open import Cubical.Data.NatPlusOne using (HasFromNat; 1+_; ℕ₊₁)
open import Cubical.HITs.Ints.QuoInt using (HasFromNat; signed)

open import Number.Instances.QuoInt using (ℤbundle)

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

  -- data Trichotomy

  open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

  lemma1 : ∀ a b₁ b₂ c → (a * b₁) * (b₂ * c) ≡ (a * c) * (b₁ * b₂)
  lemma1 a b₁ b₂ c =
    (a * b₁) * (b₂ * c) ≡⟨ {!   !} ⟩
    a * (b₁ * (b₂ * c)) ≡⟨ {!   !} ⟩
    a * ((b₁ * b₂) * c) ≡⟨ {!   !} ⟩
    a * (c * (b₁ * b₂)) ≡⟨ {!   !} ⟩
    (a * c) * (b₁ * b₂) ∎

  infixl 4 _<ᶠ_
  _<ᶠ_ : hPropRel ℚ ℚ ℓ-zero
  a <ᶠ b = SetQuotient.rec2 {R = _∼_} {B = hProp ℓ-zero} isSetHProp _<'_ <'-respects-∼ˡ <'-respects-∼ʳ a b where
    _<'_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → hProp ℓ-zero
    (aᶻ , aⁿ) <' (bᶻ , bⁿ) =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      in (aᶻ * bⁿᶻ) < (bᶻ * aⁿᶻ)
    <'-respects-∼ˡ : ∀ a b x → a ∼ b → a <' x ≡ b <' x
    <'-respects-∼ˡ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
          xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
          p : aᶻ * bⁿᶻ ≡ bᶻ * aⁿᶻ
          p = a~b
      -- in (aᶻ * xⁿᶻ)              < (xᶻ * aⁿᶻ)              ≡⟨ {!   !} ⟩
      --    (aᶻ * xⁿᶻ) / (aᶻ * bⁿᶻ) < (xᶻ * aⁿᶻ) / (bᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
      --          xⁿᶻ  /       bⁿᶻ  <  xᶻ        /  bᶻ        ≡⟨ {!   !} ⟩
      --    (bᶻ * xⁿᶻ) < (xᶻ * bⁿᶻ) ∎

      -- aᶻ > 0:
      in (aᶻ * xⁿᶻ)              < (xᶻ * aⁿᶻ)              ≡⟨ {!   !} ⟩
         (aᶻ * xⁿᶻ) * (bᶻ * aⁿᶻ) < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) ≡⟨ {!   !} ⟩
         (bᶻ * aⁿᶻ) * (aᶻ * xⁿᶻ) < (xᶻ * aⁿᶻ) * (aᶻ * bⁿᶻ) ≡⟨ {!   !} ⟩
         (bᶻ * xⁿᶻ) * (aᶻ * aⁿᶻ) < (xᶻ * bⁿᶻ) * (aᶻ * aⁿᶻ) ≡⟨ {!   !} ⟩
         (bᶻ * xⁿᶻ)              < (xᶻ * bⁿᶻ)              ∎
    <'-respects-∼ʳ : ∀ x a b → a ∼ b → x <' a ≡ x <' b
    <'-respects-∼ʳ x@(xᶻ , xⁿ) a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) a~b =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
          xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
      in {!   !}


  _≤ᶠ_ : hPropRel ℚ ℚ ℓ-zero
  x ≤ᶠ y = ¬ᵖ (y <ᶠ x)

  minᶠ : ℚ → ℚ → ℚ
  minᶠ a b = onCommonDenomSym min' min'-sym g a b where
    min' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
    min' (aᶻ , aⁿ) (bᶻ , bⁿ) =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      in min (aᶻ * bⁿᶻ) (bᶻ * aⁿᶻ)
    min'-sym : ∀ x y → min' x y ≡ min' y x
    min'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = {! is-min  !}
    g : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
      → a ∼ b
      → [1+ bⁿ ⁿ]ᶻ * min' a x ≡ [1+ aⁿ ⁿ]ᶻ * min' b x
    g a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
      let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
          bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
          xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
          p : aᶻ * bⁿᶻ ≡ bᶻ * aⁿᶻ
          p = a~b
      -- aᶻ > 0
      in bⁿᶻ * min (aᶻ * xⁿᶻ) (xᶻ * aⁿᶻ)           ≡⟨ {!   !} ⟩
         min (bⁿᶻ * (aᶻ * xⁿᶻ)) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ {!   !} ⟩
         min ((aᶻ * bⁿᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ {!   !} ⟩
         min ((bᶻ * aⁿᶻ) * xⁿᶻ) (bⁿᶻ * (xᶻ * aⁿᶻ)) ≡⟨ {!   !} ⟩
         min (aⁿᶻ * (bᶻ * xⁿᶻ)) (aⁿᶻ * (bⁿᶻ * xᶻ)) ≡⟨ {!   !} ⟩
         aⁿᶻ * min (bᶻ * xⁿᶻ) (bⁿᶻ * xᶻ)           ≡⟨ {!   !} ⟩
         aⁿᶻ * min (bᶻ * xⁿᶻ) (xᶻ * bⁿᶻ)           ∎

  pos<pos[suc] : ∀ x → [ pos x < pos (suc x) ]
  pos<pos[suc] 0 = 0<1
  pos<pos[suc] (suc x) = suc-creates-< (pos x) (pos (suc x)) .fst (pos<pos[suc] x)

  0<ᶻpos[suc] : ∀ x → [ 0 < pos (suc x) ]
  0<ᶻpos[suc]      0  = 0<1
  0<ᶻpos[suc] (suc x) = <-trans 0 (pos (suc x)) (pos (suc (suc x))) (0<ᶻpos[suc] x) (suc-creates-< (pos x) (pos (suc x)) .fst (pos<pos[suc] x))

  maxᶠ : ℚ → ℚ → ℚ
  maxᶠ a b = onCommonDenom f g h a b where
    f : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
    f (aᶻ , aⁿ) (bᶻ , bⁿ) = max (aᶻ * [1+ bⁿ ⁿ]ᶻ) (bᶻ * [1+ aⁿ ⁿ]ᶻ)
    g : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
      → aᶻ * [1+ bⁿ ⁿ]ᶻ         ≡ bᶻ * [1+ aⁿ ⁿ]ᶻ
      →      [1+ bⁿ ⁿ]ᶻ * f a c ≡      [1+ aⁿ ⁿ]ᶻ * f b c
    g a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) aᶻ*bⁿ'≡bᶻ*aⁿ' = let
      aⁿ' = [1+ aⁿ ⁿ]ᶻ
      bⁿ' = [1+ bⁿ ⁿ]ᶻ
      cⁿ' = [1+ cⁿ ⁿ]ᶻ
      0<aⁿ' : [ 0 < aⁿ' ]
      0<aⁿ' = 0<ᶻpos[suc] _
      0<bⁿ' : [ 0 < bⁿ' ]
      0<bⁿ' = 0<ᶻpos[suc] _
      0<cⁿ' : [ 0 < cⁿ' ]
      0<cⁿ' = 0<ᶻpos[suc] _
      γ : bⁿ' * max (aᶻ * cⁿ') (cᶻ * aⁿ')
        ≡ aⁿ' * max (bᶻ * cⁿ') (cᶻ * bⁿ')
      γ = {!   !}
      in γ
    h : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
      →     bᶻ * [1+ cⁿ ⁿ]ᶻ ≡     cᶻ * [1+ bⁿ ⁿ]ᶻ
      → f a b  * [1+ cⁿ ⁿ]ᶻ ≡ f a c  * [1+ bⁿ ⁿ]ᶻ
    h a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) bᶻ*cⁿ≡cᶻ*bⁿ = {!   !}

open Definitions public renaming
  ( _<ᶠ_ to _<_
  ; _≤ᶠ_ to _≤_
  ; minᶠ to min
  ; maxᶠ to max
  )

open LinearlyOrderedCommRing ℤbundle using () renaming
  ( min to minᶻ
  ; max to maxᶻ
  ; _<_ to _<ᶻ_
  )

open import Cubical.HITs.Rationals.QuoQ renaming
  ([_] to [_]ᶠ)

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
<-StrictLinearOrder .IsStrictLinearOrder.is-irrefl = {!   !}
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  = {!   !}
<-StrictLinearOrder .IsStrictLinearOrder.is-tricho = {!   !}

≤-isLattice : [ isLattice _≤_ min max ]
≤-isLattice .IsLattice.≤-PartialOrder = linearorder⇒partialorder _ (≤'-isLinearOrder <-StrictLinearOrder)
≤-isLattice .IsLattice.is-min         = {!   !}
≤-isLattice .IsLattice.is-max         = {!   !}

is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0 1 _+_ _*_ _<_ min max ]
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.is-CommSemiring     = is-CommSemiring
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.<-StrictLinearOrder = <-StrictLinearOrder
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.≤-isLattice         = ≤-isLattice
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.+-<-ext             = {!   !}
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.·-preserves-<       = {!   !}

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _*_ -_ _<_ min max ]
is-LinearlyOrderedCommRing. IsLinearlyOrderedCommRing.is-LinearlyOrderedCommSemiring = is-LinearlyOrderedCommSemiring
is-LinearlyOrderedCommRing. IsLinearlyOrderedCommRing.+-inverse                      = {!   !}

is-LinearlyOrderedField : [ isLinearlyOrderedField 0 1 _+_ _*_ -_ _<_ min max ]
is-LinearlyOrderedField .IsLinearlyOrderedField.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing
is-LinearlyOrderedField .IsLinearlyOrderedField.·-inv''                    = {!   !}

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
