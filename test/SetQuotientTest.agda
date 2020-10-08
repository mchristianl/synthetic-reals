{-# OPTIONS --cubical --no-import-sorts #-}

module SetQuotientTest where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.NatPlusOne using (HasFromNat; 1+_; ℕ₊₁; ℕ₊₁→ℕ)
open import Cubical.HITs.Ints.QuoInt using (HasFromNat; signed) renaming
  ( abs to absᶻ
  ; pos to pos
  ; neg to neg
  )
open import Cubical.HITs.Ints.QuoInt hiding (_+_; -_; +-assoc; +-comm)
open import Cubical.HITs.Rationals.QuoQ using
    ( ℚ
    ; onCommonDenom
    ; onCommonDenomSym
    ; eq/
    ; _//_
    ; _∼_
    ; isSetℚ
    )
    renaming
    ( [_] to [_]ᶠ
    ; ℕ₊₁→ℤ to [1+_ⁿ]ᶻ
    )
open import Cubical.HITs.SetQuotients as SetQuotient using () renaming (_/_ to _//_)

postulate
  _<ᶻ_ : ℤ → ℤ → hProp ℓ-zero

_<'_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → hProp ℓ-zero
(aᶻ , aⁿ) <' (bᶻ , bⁿ) =
  let aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
      bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  in (aᶻ * bⁿᶻ) <ᶻ (bᶻ * aⁿᶻ)

postulate
  <'-respects-∼ˡ : ∀ a b x → a ∼ b → a <' x ≡ b <' x
  <'-respects-∼ʳ : ∀ x a b → a ∼ b → x <' a ≡ x <' b

_<_ : ℚ → ℚ → hProp ℓ-zero
a < b = SetQuotient.rec2 {R = _∼_} {B = hProp ℓ-zero} isSetHProp _<'_ <'-respects-∼ˡ <'-respects-∼ʳ a b

isProp⊎ˡ : ∀{ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isProp A → isProp B → (A → ¬ᵗ B) → isProp (A ⊎ B)
isProp⊎ˡ pA pB A⇒¬B (inl x) (inl y) = cong inl (pA x y)
isProp⊎ˡ pA pB A⇒¬B (inr x) (inr y) = cong inr (pB x y)
isProp⊎ˡ pA pB A⇒¬B (inl x) (inr y) = ⊥-elim (A⇒¬B x y)
isProp⊎ˡ pA pB A⇒¬B (inr x) (inl y) = ⊥-elim (A⇒¬B y x)

⊎ᵖ-syntax : ∀{ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → {[ P ] → [ ¬ Q ]} → hProp _
⊎ᵖ-syntax P Q {P⇒¬Q} = ([ P ] ⊎ [ Q ]) , isProp⊎ˡ (isProp[] P) (isProp[] Q) P⇒¬Q

syntax ⊎ᵖ-syntax P Q {P⇒¬Q} = [ P⇒¬Q ] P ⊎ᵖ Q

postulate
  <-asym : ∀ x y → [ x < y ] → [ ¬(y < x) ]

_#_ : ℚ → ℚ → hProp ℓ-zero
x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

_⁻¹''' : (x : ℚ) → [ x # 0 ] → ℚ
_⁻¹''' = SetQuotient.elim {R = _∼_} {B = λ x → [ x # 0 ] → ℚ} φ _⁻¹'' ⁻¹''-respects-∼ where
  φ : ∀ x → isSet ([ x # 0 ] → ℚ)
  φ x = isSetΠ (λ _ → isSetℚ)
  _⁻¹''  : (a : ℤ × ℕ₊₁) → [ [ a ]ᶠ # 0 ] → ℚ
  x ⁻¹'' = {!!}
  ⁻¹''-respects-∼ : (a b : ℤ × ℕ₊₁) (r : a ∼ b)
                  → PathP (λ i → [ eq/ a b r i # 0 ] → ℚ) (a ⁻¹'') (b ⁻¹'')
  ⁻¹''-respects-∼ a b r = {!!}
