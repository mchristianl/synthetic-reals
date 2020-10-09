{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module Number.Instances.QuoQ.Definitions where

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

open import Cubical.Data.NatPlusOne using (HasFromNat; 1+_; ℕ₊₁; ℕ₊₁→ℕ)
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

open import Cubical.Data.Nat.Literals
open import Cubical.Data.Bool
open import Number.Prelude.Nat
open import Number.Prelude.QuoInt
open import Cubical.HITs.Ints.QuoInt using (HasFromNat)
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
  lemma1 : ∀ a b₁ b₂ c → (a ·ᶻ b₁) ·ᶻ (b₂ ·ᶻ c) ≡ (a ·ᶻ c) ·ᶻ (b₂ ·ᶻ b₁)
  lemma1 a b₁ b₂ c =
    (a ·ᶻ b₁) ·ᶻ (b₂ ·ᶻ c) ≡⟨ sym $ ·ᶻ-assoc a b₁ (b₂ ·ᶻ c) ⟩
    a ·ᶻ (b₁ ·ᶻ (b₂ ·ᶻ c)) ≡⟨ (λ i → a ·ᶻ ·ᶻ-assoc b₁ b₂ c i) ⟩
    a ·ᶻ ((b₁ ·ᶻ b₂) ·ᶻ c) ≡⟨ (λ i → a ·ᶻ ·ᶻ-comm (b₁ ·ᶻ b₂) c i) ⟩
    a ·ᶻ (c ·ᶻ (b₁ ·ᶻ b₂)) ≡⟨ ·ᶻ-assoc a c (b₁ ·ᶻ b₂) ⟩
    (a ·ᶻ c) ·ᶻ (b₁ ·ᶻ b₂) ≡⟨ (λ i → (a ·ᶻ c) ·ᶻ ·ᶻ-comm b₁ b₂ i) ⟩
    (a ·ᶻ c) ·ᶻ (b₂ ·ᶻ b₁) ∎

-- < on ℤ × ℕ₊₁ in terms of < on ℤ
_<'_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → hProp ℓ-zero
(aᶻ , aⁿ) <' (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ)

<'-respects-∼ˡ : ∀ a b x → a ∼ b → a <' x ≡ b <' x
<'-respects-∼ˡ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b = γ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
  0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]
  0<aⁿᶻ = 0<ᶻpos[suc] _
  0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]
  0<bⁿᶻ = 0<ᶻpos[suc] _
  p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
  p = a~b
  γ : ((aᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡ ((bᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ bⁿᶻ))
  γ with <ᶻ-tricho 0 aᶻ
  ... | inl (inl 0<aᶻ) =
    (aᶻ ·ᶻ xⁿᶻ)                <ᶻ (xᶻ ·ᶻ aⁿᶻ)                ≡⟨ ·ᶻ-creates-<ᶻ-≡ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ) (aᶻ ·ᶻ bⁿᶻ) (·ᶻ-preserves-<ᶻ0 aᶻ bⁿᶻ 0<aᶻ 0<bⁿᶻ) ⟩
    (aᶻ ·ᶻ xⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) ≡⟨ (λ i → (aᶻ ·ᶻ xⁿᶻ) ·ᶻ p i <ᶻ (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ)) ⟩
    (aᶻ ·ᶻ xⁿᶻ) ·ᶻ (bᶻ ·ᶻ aⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) ≡⟨ (λ i → ·ᶻ-comm (aᶻ ·ᶻ xⁿᶻ) (bᶻ ·ᶻ aⁿᶻ) i <ᶻ (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ)) ⟩
    (bᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) ≡⟨ (λ i → lemma1 bᶻ aⁿᶻ aᶻ xⁿᶻ i <ᶻ lemma1 xᶻ aⁿᶻ aᶻ bⁿᶻ i) ⟩
    (bᶻ ·ᶻ xⁿᶻ) ·ᶻ (aᶻ ·ᶻ aⁿᶻ) <ᶻ (xᶻ ·ᶻ bⁿᶻ) ·ᶻ (aᶻ ·ᶻ aⁿᶻ) ≡⟨ sym $ ·ᶻ-creates-<ᶻ-≡ (bᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ bⁿᶻ) (aᶻ ·ᶻ aⁿᶻ) (·ᶻ-preserves-<ᶻ0 aᶻ aⁿᶻ 0<aᶻ 0<aⁿᶻ) ⟩
    (bᶻ ·ᶻ xⁿᶻ)                <ᶻ (xᶻ ·ᶻ bⁿᶻ)                ∎
  ... | inl (inr aᶻ<0) = {!   !}
  ... | inr      0≡aᶻ  =
    (aᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ) ≡⟨ {!   !} ⟩
    ( 0 ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ) ≡⟨ {!   !} ⟩
      0         <ᶻ (xᶻ ·ᶻ aⁿᶻ) ≡⟨ {! κ   !} ⟩
      0         <ᶻ (xᶻ ·ᶻ bⁿᶻ) ≡⟨ {!   !} ⟩
    ( 0 ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ bⁿᶻ) ≡⟨ {!   !} ⟩
    (bᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ bⁿᶻ) ∎ where
      bᶻ≡0 : bᶻ ≡ 0
      bᶻ≡0 = {!   !}
      κ : ∀ x y z → [ 0 <ᶻ y ] → [ 0 <ᶻ z ] → (0 <ᶻ (x ·ᶻ y)) ≡ (0 <ᶻ (x ·ᶻ z))
      κ x y z p q =
         0       <ᶻ (x ·ᶻ y) ≡⟨ {!   !} ⟩
        (0 ·ᶻ y) <ᶻ (x ·ᶻ y) ≡⟨ {!   !} ⟩
         0       <ᶻ  x       ≡⟨ {!   !} ⟩
        (0 ·ᶻ z) <ᶻ (x ·ᶻ z) ≡⟨ {!   !} ⟩
         0       <ᶻ (x ·ᶻ z) ∎
  -- in (aᶻ ·ᶻ xⁿᶻ)              <ᶻ (xᶻ ·ᶻ aⁿᶻ)              ≡⟨ {!   !} ⟩
  --    (aᶻ ·ᶻ xⁿᶻ) / (aᶻ ·ᶻ bⁿᶻ) <ᶻ (xᶻ ·ᶻ aⁿᶻ) / (bᶻ ·ᶻ aⁿᶻ) ≡⟨ {!   !} ⟩
  --          xⁿᶻ  /       bⁿᶻ  <ᶻ  xᶻ        /  bᶻ        ≡⟨ {!   !} ⟩
  --    (bᶻ ·ᶻ xⁿᶻ) <ᶻ (xᶻ ·ᶻ bⁿᶻ) ∎

  -- aᶻ > 0:
<'-respects-∼ʳ : ∀ x a b → a ∼ b → x <' a ≡ x <' b
<'-respects-∼ʳ x@(xᶻ , xⁿ) a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) a~b =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
      xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
      p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
      p = a~b
  in (xᶻ ·ᶻ aⁿᶻ)                <ᶻ (aᶻ ·ᶻ xⁿᶻ)                ≡⟨ {!   !} ⟩
     (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (aᶻ ·ᶻ xⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) ≡⟨ {!   !} ⟩
     (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (aᶻ ·ᶻ xⁿᶻ) ·ᶻ (bᶻ ·ᶻ aⁿᶻ) ≡⟨ {!   !} ⟩
     (xᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ) ·ᶻ (aᶻ ·ᶻ xⁿᶻ) ≡⟨ {!   !} ⟩
     (xᶻ ·ᶻ bⁿᶻ) ·ᶻ (aᶻ ·ᶻ aⁿᶻ) <ᶻ (bᶻ ·ᶻ xⁿᶻ) ·ᶻ (aᶻ ·ᶻ aⁿᶻ) ≡⟨ {!   !} ⟩
     (xᶻ ·ᶻ bⁿᶻ)                <ᶻ (bᶻ ·ᶻ xⁿᶻ)              ∎

-- TODO: we might extract definition and properties in the where clauses upfront
infixl 4 _<_
_<_ : hPropRel ℚ ℚ ℓ-zero
a < b = SetQuotient.rec2 {R = _∼_} {B = hProp ℓ-zero} isSetHProp _<'_ <'-respects-∼ˡ <'-respects-∼ʳ a b

_≤_ : hPropRel ℚ ℚ ℓ-zero
x ≤ y = ¬ᵖ (y < x)

min' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
min' (aᶻ , aⁿ) (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in minᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ)

max' : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
max' (aᶻ , aⁿ) (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in maxᶻ (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ)

min'-sym : ∀ x y → min' x y ≡ min' y x
min'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = minᶻ-comm (aᶻ ·ᶻ [1+ bⁿ ⁿ]ᶻ) (bᶻ ·ᶻ [1+ aⁿ ⁿ]ᶻ)

max'-sym : ∀ x y → max' x y ≡ max' y x
max'-sym (aᶻ , aⁿ) (bᶻ , bⁿ) = maxᶻ-comm (aᶻ ·ᶻ [1+ bⁿ ⁿ]ᶻ) (bᶻ ·ᶻ [1+ aⁿ ⁿ]ᶻ)

min'-respects-∼ : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
                → a ∼ b
                → [1+ bⁿ ⁿ]ᶻ ·ᶻ min' a x ≡ [1+ aⁿ ⁿ]ᶻ ·ᶻ min' b x
min'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
  bⁿᶻ ·ᶻ minᶻ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ)            ≡⟨ ·ᶻ-minᶻ-distribˡ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0≤bⁿᶻ ⟩
  minᶻ (bⁿᶻ ·ᶻ (aᶻ ·ᶻ xⁿᶻ)) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ (·ᶻ-assoc bⁿᶻ aᶻ xⁿᶻ i) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  minᶻ ((bⁿᶻ ·ᶻ aᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ ((·ᶻ-comm bⁿᶻ aᶻ i) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  minᶻ ((aᶻ ·ᶻ bⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ (p i ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  minᶻ ((bᶻ ·ᶻ aⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → minᶻ (·ᶻ-comm bᶻ aⁿᶻ i ·ᶻ xⁿᶻ) (·ᶻ-assoc bⁿᶻ xᶻ aⁿᶻ i)) ⟩
  minᶻ ((aⁿᶻ ·ᶻ bᶻ) ·ᶻ xⁿᶻ) ((bⁿᶻ ·ᶻ xᶻ) ·ᶻ aⁿᶻ) ≡⟨ (λ i → minᶻ (·ᶻ-assoc aⁿᶻ bᶻ xⁿᶻ (~ i)) (·ᶻ-comm (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ i)) ⟩
  minᶻ (aⁿᶻ ·ᶻ (bᶻ ·ᶻ xⁿᶻ)) (aⁿᶻ ·ᶻ (bⁿᶻ ·ᶻ xᶻ)) ≡⟨ sym $ ·ᶻ-minᶻ-distribˡ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ 0≤aⁿᶻ ⟩
  aⁿᶻ ·ᶻ minᶻ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ)            ≡⟨ (λ i → aⁿᶻ ·ᶻ minᶻ (bᶻ ·ᶻ xⁿᶻ) (·ᶻ-comm bⁿᶻ xᶻ i)) ⟩
  aⁿᶻ ·ᶻ minᶻ (bᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ bⁿᶻ)            ∎
  where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
    p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
    p = a~b
    0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]
    0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
    0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]
    0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

-- same proof as for min
max'-respects-∼ : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) : ℤ × ℕ₊₁)
  → a ∼ b
  → [1+ bⁿ ⁿ]ᶻ ·ᶻ max' a x ≡ [1+ aⁿ ⁿ]ᶻ ·ᶻ max' b x
max'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) x@(xᶻ , xⁿ) a~b =
  bⁿᶻ ·ᶻ maxᶻ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ)            ≡⟨ ·ᶻ-maxᶻ-distribˡ (aᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ aⁿᶻ) bⁿᶻ 0≤bⁿᶻ ⟩
  maxᶻ (bⁿᶻ ·ᶻ (aᶻ ·ᶻ xⁿᶻ)) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ (·ᶻ-assoc bⁿᶻ aᶻ xⁿᶻ i) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  maxᶻ ((bⁿᶻ ·ᶻ aᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ ((·ᶻ-comm bⁿᶻ aᶻ i) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  maxᶻ ((aᶻ ·ᶻ bⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ (p i ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ))) ⟩
  maxᶻ ((bᶻ ·ᶻ aⁿᶻ) ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ (xᶻ ·ᶻ aⁿᶻ)) ≡⟨ (λ i → maxᶻ (·ᶻ-comm bᶻ aⁿᶻ i ·ᶻ xⁿᶻ) (·ᶻ-assoc bⁿᶻ xᶻ aⁿᶻ i)) ⟩
  maxᶻ ((aⁿᶻ ·ᶻ bᶻ) ·ᶻ xⁿᶻ) ((bⁿᶻ ·ᶻ xᶻ) ·ᶻ aⁿᶻ) ≡⟨ (λ i → maxᶻ (·ᶻ-assoc aⁿᶻ bᶻ xⁿᶻ (~ i)) (·ᶻ-comm (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ i)) ⟩
  maxᶻ (aⁿᶻ ·ᶻ (bᶻ ·ᶻ xⁿᶻ)) (aⁿᶻ ·ᶻ (bⁿᶻ ·ᶻ xᶻ)) ≡⟨ sym $ ·ᶻ-maxᶻ-distribˡ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ) aⁿᶻ 0≤aⁿᶻ ⟩
  aⁿᶻ ·ᶻ maxᶻ (bᶻ ·ᶻ xⁿᶻ) (bⁿᶻ ·ᶻ xᶻ)            ≡⟨ (λ i → aⁿᶻ ·ᶻ maxᶻ (bᶻ ·ᶻ xⁿᶻ) (·ᶻ-comm bⁿᶻ xᶻ i)) ⟩
  aⁿᶻ ·ᶻ maxᶻ (bᶻ ·ᶻ xⁿᶻ) (xᶻ ·ᶻ bⁿᶻ)            ∎
  where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    xⁿᶻ = [1+ xⁿ ⁿ]ᶻ
    p : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
    p = a~b
    0≤aⁿᶻ : [ 0 ≤ᶻ aⁿᶻ ]
    0≤aⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p
    0≤bⁿᶻ : [ 0 ≤ᶻ bⁿᶻ ]
    0≤bⁿᶻ (k , p) = snotzⁿ $ sym (+ⁿ-suc k _) ∙ p

minᶠ : ℚ → ℚ → ℚ
minᶠ a b = onCommonDenomSym min' min'-sym min'-respects-∼ a b

maxᶠ : ℚ → ℚ → ℚ
maxᶠ a b = onCommonDenomSym max' max'-sym max'-respects-∼ a b
