{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Instances.QuoQ.Instance where


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
  ; isSetℚ
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

open import Number.Instances.QuoQ.Definitions

<-irrefl : ∀ a → [ ¬(a < a) ]
<-irrefl = SetQuotient.elimProp {R = _∼_} (λ a → isProp[] (¬(a < a))) γ where
  γ : (a : ℤ × ℕ₊₁) → [ ¬([ a ]ᶠ < [ a ]ᶠ) ]
  γ a@(aᶻ , aⁿ) = κ where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    κ : [ ¬((aᶻ ·ᶻ aⁿᶻ) <ᶻ (aᶻ ·ᶻ aⁿᶻ)) ]
    κ = <ᶻ-irrefl (aᶻ ·ᶻ aⁿᶻ)

<-trans : (a b c : ℚ) → [ a < b ] → [ b < c ] → [ a < c ]
<-trans = SetQuotient.elimProp3 {R = _∼_} (λ a b c → isProp[] ((a < b) ⇒ (b < c) ⇒ (a < c))) γ where
  γ : (a b c : ℤ × ℕ₊₁) → [ [ a ]ᶠ < [ b ]ᶠ ] → [ [ b ]ᶠ < [ c ]ᶠ ] → [ [ a ]ᶠ < [ c ]ᶠ ]
  γ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) = κ where
    aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
    bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
    cⁿᶻ = [1+ cⁿ ⁿ]ᶻ
    κ : [ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ) ] → [ (bᶻ ·ᶻ cⁿᶻ) <ᶻ (cᶻ ·ᶻ bⁿᶻ) ] → [ (aᶻ ·ᶻ cⁿᶻ) <ᶻ (cᶻ ·ᶻ aⁿᶻ) ]
    -- strategy: multiply with xⁿᶻ and then use <ᶻ-trans
    κ = {!  !}

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
    κ : ([ (aᶻ ·ᶻ bⁿᶻ) <ᶻ (bᶻ ·ᶻ aⁿᶻ) ] ⊎ [ (bᶻ ·ᶻ aⁿᶻ) <ᶻ (aᶻ ·ᶻ bⁿᶻ) ]) ⊎ [ [ aᶻ , aⁿ ]ᶠ ≡ₚ [ bᶻ , bⁿ ]ᶠ ]
    κ with <ᶻ-tricho (aᶻ ·ᶻ bⁿᶻ) (bᶻ ·ᶻ aⁿᶻ)
    ... | inl p = inl p
    ... | inr p = inr ∣ eq/ {R = _∼_} a b p ∣

_#_ : hPropRel ℚ ℚ ℓ-zero
x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

injᶻⁿ⁺¹ : ∀ x → [ 0 <ᶻ x ] → Σ[ y ∈ ℕ₊₁ ] x ≡ [1+ y ⁿ]ᶻ
injᶻⁿ⁺¹ (signed false zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i0 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (signed true  zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i1 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (ℤ.posneg i)        p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i  ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (signed false (suc n)) p =  1+ n , refl

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

·ᶻ-preserves-signˡ : ∀ x y → [ 0 <ᶻ y ] → signᶻ (x ·ᶻ y) ≡ signᶻ x
·ᶻ-preserves-signˡ x (signed false zero) p = ⊥-elim {A = λ _ → signᶻ (x ·ᶻ ℤ.posneg i0) ≡ signᶻ x} (¬-<ⁿ-zero p)
·ᶻ-preserves-signˡ x (signed true  zero) p = ⊥-elim {A = λ _ → signᶻ (x ·ᶻ ℤ.posneg i1) ≡ signᶻ x} (¬-<ⁿ-zero p)
·ᶻ-preserves-signˡ x (ℤ.posneg i)        p = ⊥-elim {A = λ _ → signᶻ (x ·ᶻ ℤ.posneg i ) ≡ signᶻ x} (¬-<ⁿ-zero p)
·ᶻ-preserves-signˡ (signed false zero) (signed false (suc n)) p = refl
·ᶻ-preserves-signˡ (signed true  zero) (signed false (suc n)) p = refl
·ᶻ-preserves-signˡ (ℤ.posneg i)        (signed false (suc n)) p = refl
·ᶻ-preserves-signˡ (signed s (suc n₁)) (signed false (suc n)) p = ⊕-identityʳ s


_⁻¹''' : (x : ℚ) → [ x # 0 ] → ℚ
_⁻¹''' = SetQuotient.elim {R = _∼_} {B = λ x → [ x # 0 ] → ℚ} φ _⁻¹'' ⁻¹''-respects-∼ where
  φ : ∀ x → isSet ([ x # 0 ] → ℚ)
  φ x = isSetΠ (λ _ → isSetℚ)
  _⁻¹''  : (a : ℤ × ℕ₊₁) → [ [ a ]ᶠ # 0 ] → ℚ
  x ⁻¹'' = {! !}
  ⁻¹''-respects-∼ : (a b : ℤ × ℕ₊₁) (r : a ∼ b)
                  → PathP (λ i → [ eq/ a b r i # 0 ] → ℚ) (a ⁻¹'') (b ⁻¹'')
  ⁻¹''-respects-∼ a b r = {!!}
