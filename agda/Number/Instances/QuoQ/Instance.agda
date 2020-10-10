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
open import Number.Instances.QuoQ.Definitions
open import Cubical.HITs.Rationals.QuoQ using
  ( ℚ
  ; HasFromNat
  ; isSetℚ
  ; onCommonDenom
  ; onCommonDenomSym
  ; eq/
  ; _//_
  ; _∼_
  ) renaming
  ( [_] to [_]ᶠ
  ; ℕ₊₁→ℤ to [1+_ⁿ]ᶻ
  )


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
injᶻⁿ⁺¹ (signed spos zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i0 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (signed sneg  zero) p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i1 ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (ℤ.posneg i)        p = ⊥-elim {A = λ _ → Σ[ y ∈ ℕ₊₁ ] ℤ.posneg i  ≡ [1+ y ⁿ]ᶻ}  (¬-<ⁿ-zero p)
injᶻⁿ⁺¹ (signed spos (suc n)) p =  1+ n , refl

-flips-<ᶻ0 : ∀ x → [ (x <ᶻ 0) ⇔ (0 <ᶻ (-ᶻ x)) ]
-flips-<ᶻ0 (signed spos zero) = (λ x → x) , (λ x → x)
-flips-<ᶻ0 (signed sneg  zero) = (λ x → x) , (λ x → x)
-flips-<ᶻ0 (ℤ.posneg i)        = (λ x → x) , (λ x → x)
-flips-<ᶻ0 (signed spos (suc n)) .fst p  = ¬-<ⁿ-zero p
-flips-<ᶻ0 (signed sneg  (suc n)) .fst tt = n , +ⁿ-comm n 1
-flips-<ᶻ0 (signed sneg  (suc n)) .snd p  = tt


-- -flips-< : ∀ x y → [ x <ᶻ y ⇔ - y <ᶻ - x ]

-- #-Dichotomyˢ : {A : Type ℓ} (is-set : isSet A) (_#_ : hPropRel A A ℓ) )(#-tight : ∀ x y → [ x # y ⇔ ¬([ is-set ] x ≡ˢ y) ] ) (x : A) → hProp ℓ
-- #-Dichotomyˢ x = [ #-tight x 0 .fst ] x # 0 ⊎ᵖ (x ≡ 0)

#ᶻ-dicho : ∀ x → [ x #ᶻ 0 ] ⊎ (x ≡ 0)
#ᶻ-dicho x = <ᶻ-tricho x 0

⊕-identityʳ : ∀ s → (s Bool.⊕ spos) ≡ s
⊕-identityʳ spos = refl
⊕-identityʳ sneg  = refl

·ᶻ-preserves-signˡ : ∀ x y → [ 0 <ᶻ y ] → signᶻ (x ·ᶻ y) ≡ signᶻ x
·ᶻ-preserves-signˡ x (signed spos zero) p = ⊥-elim {A = λ _ → signᶻ (x ·ᶻ ℤ.posneg i0) ≡ signᶻ x} (¬-<ⁿ-zero p)
·ᶻ-preserves-signˡ x (signed sneg  zero) p = ⊥-elim {A = λ _ → signᶻ (x ·ᶻ ℤ.posneg i1) ≡ signᶻ x} (¬-<ⁿ-zero p)
·ᶻ-preserves-signˡ x (ℤ.posneg i)        p = ⊥-elim {A = λ _ → signᶻ (x ·ᶻ ℤ.posneg i ) ≡ signᶻ x} (¬-<ⁿ-zero p)
·ᶻ-preserves-signˡ (signed spos zero) (signed spos (suc n)) p = refl
·ᶻ-preserves-signˡ (signed sneg  zero) (signed spos (suc n)) p = refl
·ᶻ-preserves-signˡ (ℤ.posneg i)        (signed spos (suc n)) p = refl
·ᶻ-preserves-signˡ (signed s (suc n₁)) (signed spos (suc n)) p = ⊕-identityʳ s

-- funExt' : {ℓ : Level} {A : Type ℓ} {ℓ' : Level}
--       {B : I → Type ℓ'} {f : B x i0}
--       {g : B i1} →
--       ((x : A) → PathP (B x) (f x) (g x)) →
--       PathP (λ i₁ → (x : A) → B x i₁) f g

-- funExt : {B : A → I → Type ℓ'}
--   {f : (x : A) → B x i0} {g : (x : A) → B x i1}
--   → ((x : A) → PathP (B x) (f x) (g x))
--   → PathP (λ i → (x : A) → B x i) f g
-- funExt p i x = p x i

-- funExt' : ∀{ℓ' ℓ} {A₁ A₂ : Type ℓ} (A : A₁ ≡ A₂) {B : I → Type ℓ'}
--   {f : (x : A i0) → B i0} {g : (x : A i1) → B i1}
--   → ((x : A) → PathP B (f x) (g x))
--   → PathP (λ i → (x : A) → B i) f g
-- funExt' p i x = p x i

-- funExt' : ∀{ℓ ℓ'} {A B : Type ℓ} {C : Type ℓ'} (A≡B : A ≡ B) (f : A → C) (g : B → C)
--         → ∀ x y → (x≡y : PathP (λ i → A≡B i) x y)
--         → f x ≡ g y → PathP (λ i → A≡B i → C) f g
-- funExt' A≡B f g x y p q i = λ(z : A≡B i) → {! q   !}

absⁿ⁺¹' : ℤ → ℕ₊₁
absⁿ⁺¹' (pos zero)    = 1+ 0
absⁿ⁺¹' (neg zero)    = 1+ 0
absⁿ⁺¹' (posneg i)    = 1+ 0
absⁿ⁺¹' (pos (suc n)) = 1+ n
absⁿ⁺¹' (neg (suc n)) = 1+ n

-- absⁿ⁺¹'-identity⁺ : ∀ x → signed spos (ℕ₊₁→ℕ x) ≡ [1+ absⁿ⁺¹' x ⁿ]ᶻ
-- absⁿ⁺¹'-identity⁺ x = ?

absⁿ⁺¹'-identity⁺ : ∀ x → [ 0 <ⁿ x ] → [1+ absⁿ⁺¹' (pos x) ⁿ]ᶻ ≡ pos x
absⁿ⁺¹'-identity⁺ zero    p = ⊥-elim {A = λ _ → [1+ absⁿ⁺¹' (pos zero) ⁿ]ᶻ ≡ pos zero} (<ⁿ-irrefl 0 p)
absⁿ⁺¹'-identity⁺ (suc x) p = refl

absⁿ⁺¹'-identity⁻ : ∀ x → [ 0 <ⁿ x ] → [1+ absⁿ⁺¹' (neg x) ⁿ]ᶻ ≡ pos x
absⁿ⁺¹'-identity⁻ zero p = ⊥-elim {A = λ _ → [1+ absⁿ⁺¹' (neg zero) ⁿ]ᶻ ≡ pos zero} (<ⁿ-irrefl 0 p)
absⁿ⁺¹'-identity⁻ (suc x) p = refl

#ᶻ⇒≢ : ∀ x → [ x #ᶻ 0 ] → ¬ᵗ(0 ≡ x)
#ᶻ⇒≢ x (inl p) q = <ᶻ-irrefl 0 $ subst (λ p → [ p <ᶻ pos 0 ]) (sym q) p
#ᶻ⇒≢ x (inr p) q = <ᶻ-irrefl 0 $ subst (λ p → [ pos 0 <ᶻ p ]) (sym q) p

absⁿ⁺¹'-identity : ∀ x → [ x #ᶻ 0 ] → [1+ absⁿ⁺¹' x ⁿ]ᶻ ≡ pos (absᶻ x)
absⁿ⁺¹'-identity (pos zero)    p = ⊥-elim {A = λ _ → pos 1 ≡ pos 0} $ #ᶻ⇒≢ (posneg i0) p refl
absⁿ⁺¹'-identity (neg zero)    p = ⊥-elim {A = λ _ → pos 1 ≡ pos 0} $ #ᶻ⇒≢ (posneg i1) p posneg
absⁿ⁺¹'-identity (posneg i)    p = ⊥-elim {A = λ _ → pos 1 ≡ pos 0} $ #ᶻ⇒≢ (posneg i ) p (λ j → posneg (i ∧ j))
absⁿ⁺¹'-identity (pos (suc n)) p = refl
absⁿ⁺¹'-identity (neg (suc n)) p = refl

absⁿ⁺¹'-identityⁿ : ∀ x → [ x #ᶻ 0 ] → suc (ℕ₊₁.n (absⁿ⁺¹' x)) ≡ absᶻ x
absⁿ⁺¹'-identityⁿ x p i = absᶻ (absⁿ⁺¹'-identity x p i)

<ᶻ-split-pos : ∀ z → [ 0 <ᶻ z ] → Σ[ n ∈ ℕ ] z ≡ pos (suc n)
<ᶻ-split-pos (pos zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i0 ≡ pos (suc n)} (<ᶻ-irrefl 0 p)
<ᶻ-split-pos (neg zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i1 ≡ pos (suc n)} (<ᶻ-irrefl 0 p)
<ᶻ-split-pos (posneg i)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i  ≡ pos (suc n)} (<ᶻ-irrefl 0 p)
<ᶻ-split-pos (pos (suc n)) p = n , refl

<ᶻ-split-neg : ∀ z → [ z <ᶻ 0 ] → Σ[ n ∈ ℕ ] z ≡ neg (suc n)
<ᶻ-split-neg (pos zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i0   ≡ neg (suc n)} (<ᶻ-irrefl 0 p)
<ᶻ-split-neg (neg zero)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i1   ≡ neg (suc n)} (<ᶻ-irrefl 0 p)
<ᶻ-split-neg (posneg i)    p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] posneg i    ≡ neg (suc n)} (<ᶻ-irrefl 0 p)
<ᶻ-split-neg (pos (suc m)) p = ⊥-elim {A = λ _ → Σ[ n ∈ ℕ ] pos (suc m) ≡ neg (suc n)} (¬suc<ⁿ0 m p)
<ᶻ-split-neg (neg (suc m)) p = m , refl

0<ᶻ-signᶻ : ∀ z → [ 0 <ᶻ z ] → signᶻ z ≡ spos
0<ᶻ-signᶻ z p i = signᶻ $ <ᶻ-split-pos z p .snd i

<ᶻ0-signᶻ : ∀ z → [ z <ᶻ 0 ] → signᶻ z ≡ sneg
<ᶻ0-signᶻ z p i = signᶻ $ <ᶻ-split-neg z p .snd i

signᶻ-pos : ∀ n → signᶻ (pos n) ≡ spos
signᶻ-pos zero = refl
signᶻ-pos (suc n) = refl

sign' : ℤ × ℕ₊₁ → Sign
sign' (z , n) = signᶻ z

-- ⊕-identityʳ : ∀ s → s ⊕ spos ≡ s
-- ⊕-identityʳ s = ?

-- ·ᶻ-reflects-signᶻ : ∀ a b → signᶻ (a ·ᶻ pos (suc b)) ≡ signᶻ a
-- ·ᶻ-reflects-signᶻ (pos zero) b = refl
-- ·ᶻ-reflects-signᶻ (neg zero) b = refl
-- ·ᶻ-reflects-signᶻ (posneg i) b = refl
-- ·ᶻ-reflects-signᶻ (pos (suc n)) b = refl
-- ·ᶻ-reflects-signᶻ (neg (suc n)) b = refl

sign'-preserves-∼ : (a b : ℤ × ℕ₊₁) → a ∼ b → sign' a ≡ sign' b
sign'-preserves-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p =  sym (lem aᶻ bⁿ) ∙ ψ ∙ lem bᶻ aⁿ where
  a' = absᶻ aᶻ ·ⁿ suc (ℕ₊₁.n bⁿ)
  b' = absᶻ bᶻ ·ⁿ suc (ℕ₊₁.n aⁿ)
  γ : signed (signᶻ aᶻ ⊕ spos) a' ≡ signed (signᶻ bᶻ ⊕ spos) b'
  γ = p
  ψ : signᶻ (signed (signᶻ aᶻ ⊕ spos) a') ≡ signᶻ (signed (signᶻ bᶻ ⊕ spos) b')
  ψ i = signᶻ (γ i)
  lem : ∀ x y → signᶻ (signed (signᶻ x ⊕ spos) (absᶻ x ·ⁿ suc (ℕ₊₁.n y))) ≡ signᶻ x
  lem (pos zero)    y = refl
  lem (neg zero)    y = refl
  lem (posneg i)    y = refl
  lem (pos (suc n)) y = refl
  lem (neg (suc n)) y = refl

sign : ℚ → Sign
sign = SetQuotient.rec {R = _∼_} {B = Sign} Bool.isSetBool sign' sign'-preserves-∼

sign-signᶻ-identity : ∀ z n → sign [ z , n ]ᶠ ≡ signᶻ z
sign-signᶻ-identity z n = refl

#-split' : ∀ z n → [ [ z , n ]ᶠ # 0 ] → [ z <ᶻ 0 ] ⊎ [ 0 <ᶻ z ]
#-split' (pos zero) _ p = p
#-split' (neg zero) _ p = p
#-split' (posneg i) _ p = p
#-split' (pos (suc n)) _ p = transport (λ i → [ suc (·ⁿ-identityʳ n i) <ⁿ 0 ] ⊎ [ 0 <ⁿ suc (·ⁿ-identityʳ n i) ]) p
#-split' (neg (suc n)) _ p = p

∼-preserves-< : ∀ aᶻ aⁿ bᶻ bⁿ → (aᶻ , aⁿ) ∼ (bᶻ , bⁿ) → [ ((aᶻ <ᶻ 0) ⇒ (bᶻ <ᶻ 0)) ⊓ ((0 <ᶻ aᶻ) ⇒ (0 <ᶻ bᶻ)) ]
∼-preserves-< aᶻ aⁿ bᶻ bⁿ r = γ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]
  0<aⁿᶻ = ℕ₊₁.n aⁿ , +ⁿ-comm (ℕ₊₁.n aⁿ) 1
  0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]
  0<bⁿᶻ = ℕ₊₁.n bⁿ , +ⁿ-comm (ℕ₊₁.n bⁿ) 1
  γ : [ ((aᶻ <ᶻ 0) ⇒ (bᶻ <ᶻ 0)) ⊓ ((0 <ᶻ aᶻ) ⇒ (0 <ᶻ bᶻ)) ]
  γ .fst aᶻ<0 = (
    aᶻ <ᶻ 0               ⇒ᵖ⟨ ·ᶻ-preserves-<ᶻ aᶻ 0 bⁿᶻ 0<bⁿᶻ ⟩
    aᶻ ·ᶻ bⁿᶻ <ᶻ 0 ·ᶻ bⁿᶻ ⇒ᵖ⟨ (subst (λ p → [ aᶻ ·ᶻ bⁿᶻ <ᶻ p ]) $ ·ᶻ-nullifiesˡ bⁿᶻ) ⟩
    aᶻ ·ᶻ bⁿᶻ <ᶻ 0        ⇒ᵖ⟨ subst (λ p → [ p <ᶻ 0 ]) r ⟩
    bᶻ ·ᶻ aⁿᶻ <ᶻ 0        ⇒ᵖ⟨ subst (λ p → [ bᶻ ·ᶻ aⁿᶻ <ᶻ p ]) (sym (·ᶻ-nullifiesˡ aⁿᶻ)) ⟩
    bᶻ ·ᶻ aⁿᶻ <ᶻ 0 ·ᶻ aⁿᶻ ⇒ᵖ⟨ ·ᶻ-reflects-<ᶻ bᶻ 0 aⁿᶻ 0<aⁿᶻ ⟩
    bᶻ        <ᶻ 0        ◼ᵖ) .snd aᶻ<0
  γ .snd 0<aᶻ = (
    0        <ᶻ aᶻ        ⇒ᵖ⟨ ·ᶻ-preserves-<ᶻ 0 aᶻ bⁿᶻ 0<bⁿᶻ ⟩
    0 ·ᶻ bⁿᶻ <ᶻ aᶻ ·ᶻ bⁿᶻ ⇒ᵖ⟨ (subst (λ p → [ p <ᶻ aᶻ ·ᶻ bⁿᶻ ]) $ ·ᶻ-nullifiesˡ bⁿᶻ) ⟩
    0        <ᶻ aᶻ ·ᶻ bⁿᶻ ⇒ᵖ⟨ subst (λ p → [ 0 <ᶻ p ]) r ⟩
    0        <ᶻ bᶻ ·ᶻ aⁿᶻ ⇒ᵖ⟨ subst (λ p → [ p <ᶻ bᶻ ·ᶻ aⁿᶻ ]) (sym (·ᶻ-nullifiesˡ aⁿᶻ)) ⟩
    0 ·ᶻ aⁿᶻ <ᶻ bᶻ ·ᶻ aⁿᶻ ⇒ᵖ⟨ ·ᶻ-reflects-<ᶻ 0 bᶻ aⁿᶻ 0<aⁿᶻ ⟩
    0        <ᶻ bᶻ        ◼ᵖ) .snd 0<aᶻ

_⁻¹'  : (x : ℤ × ℕ₊₁) → [ [ x ]ᶠ # 0 ] → ℚ
(xᶻ , xⁿ) ⁻¹' = λ _ → [ signed (signᶻ xᶻ) (ℕ₊₁→ℕ xⁿ) , absⁿ⁺¹' xᶻ ]ᶠ

⁻¹'-respects-∼ : (a b : ℤ × ℕ₊₁) (p : a ∼ b)
                → PathP (λ i → [ eq/ a b p i # 0 ] → ℚ) (a ⁻¹') (b ⁻¹')
⁻¹'-respects-∼ a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) p = κ where
  aⁿᶻ = [1+ aⁿ ⁿ]ᶻ
  bⁿᶻ = [1+ bⁿ ⁿ]ᶻ
  0<aⁿᶻ : [ 0 <ᶻ aⁿᶻ ]
  0<aⁿᶻ = ℕ₊₁.n aⁿ , +ⁿ-comm (ℕ₊₁.n aⁿ) 1
  0<bⁿᶻ : [ 0 <ᶻ bⁿᶻ ]
  0<bⁿᶻ = ℕ₊₁.n bⁿ , +ⁿ-comm (ℕ₊₁.n bⁿ) 1
  η : signᶻ aᶻ ≡ signᶻ bᶻ
  η i = sign (eq/ a b p i)
  s : aᶻ ·ᶻ bⁿᶻ ≡ bᶻ ·ᶻ aⁿᶻ
  s = p
  r : [ [ aᶻ , aⁿ ]ᶠ # 0 ] → (signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) , absⁿ⁺¹' aᶻ) ∼ (signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) , absⁿ⁺¹' bᶻ)
  r q = φ where
    φ : signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) ·ᶻ [1+ absⁿ⁺¹' bᶻ ⁿ]ᶻ ≡ signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) ·ᶻ [1+ absⁿ⁺¹' aᶻ ⁿ]ᶻ
    φ with #-split' aᶻ aⁿ q
    ... | inl aᶻ<0 =
      signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) ·ᶻ [1+ absⁿ⁺¹' bᶻ ⁿ]ᶻ ≡⟨ (λ i → signed (<ᶻ0-signᶻ aᶻ aᶻ<0 i) (ℕ₊₁→ℕ aⁿ) ·ᶻ absⁿ⁺¹'-identity bᶻ (inl bᶻ<0) i) ⟩
      signed  sneg      (ℕ₊₁→ℕ aⁿ) ·ᶻ pos (absᶻ bᶻ)      ≡⟨ cong₂ signed (λ i → sneg ·ˢ q₁ i) q₂ ⟩
      signed  sneg      (ℕ₊₁→ℕ bⁿ) ·ᶻ pos (absᶻ aᶻ)      ≡⟨ (λ i → signed (<ᶻ0-signᶻ bᶻ bᶻ<0 (~ i)) (ℕ₊₁→ℕ bⁿ) ·ᶻ absⁿ⁺¹'-identity aᶻ (inl aᶻ<0) (~ i)) ⟩
      signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) ·ᶻ [1+ absⁿ⁺¹' aᶻ ⁿ]ᶻ ∎ where
      bᶻ<0 : [ bᶻ <ᶻ 0 ]
      bᶻ<0 = ∼-preserves-< aᶻ aⁿ bᶻ bⁿ p .fst aᶻ<0
      abstract
        c      = suc (<ᶻ-split-neg aᶻ aᶻ<0 .fst)
        d      = suc (<ᶻ-split-neg bᶻ bᶻ<0 .fst)
        aᶻ≡-c  : aᶻ ≡ neg c
        aᶻ≡-c  = <ᶻ-split-neg aᶻ aᶻ<0 .snd
        bᶻ≡-d  : bᶻ ≡ neg d
        bᶻ≡-d  = <ᶻ-split-neg bᶻ bᶻ<0 .snd
        absa≡c : absᶻ aᶻ ≡ c
        absa≡c i = absᶻ (aᶻ≡-c i)
        absb≡d : absᶻ bᶻ ≡ d
        absb≡d i = absᶻ (bᶻ≡-d i)
      q₁ : signᶻ (pos (absᶻ bᶻ)) ≡ signᶻ (pos (absᶻ aᶻ))
      q₁ = transport (λ i → signᶻ-pos (absᶻ bᶻ) (~ i) ≡ signᶻ-pos (absᶻ aᶻ) (~ i)) refl
      s' = bᶻ ·ᶻ aⁿᶻ    ≡ aᶻ ·ᶻ bⁿᶻ                       ≡⟨ (λ i → ·ᶻ-comm bᶻ aⁿᶻ i ≡ ·ᶻ-comm aᶻ bⁿᶻ i) ⟩
           aⁿᶻ ·ᶻ bᶻ    ≡ bⁿᶻ ·ᶻ aᶻ                       ≡⟨ (λ i → aⁿᶻ ·ᶻ bᶻ≡-d i ≡ bⁿᶻ ·ᶻ aᶻ≡-c i) ⟩
           aⁿᶻ ·ᶻ neg d ≡ bⁿᶻ ·ᶻ neg c                    ≡⟨ refl ⟩
             signed (signᶻ (neg d)) (suc (ℕ₊₁.n aⁿ) ·ⁿ d)
           ≡ signed (signᶻ (neg c)) (suc (ℕ₊₁.n bⁿ) ·ⁿ c) ∎
      q₂ = (suc (ℕ₊₁.n aⁿ) ·ⁿ       d ≡ suc (ℕ₊₁.n bⁿ) ·ⁿ      c  ⇒⟨ transport (λ i → suc (ℕ₊₁.n aⁿ) ·ⁿ absb≡d (~ i) ≡ suc (ℕ₊₁.n bⁿ) ·ⁿ absa≡c (~ i)) ⟩
            suc (ℕ₊₁.n aⁿ) ·ⁿ absᶻ bᶻ ≡ suc (ℕ₊₁.n bⁿ) ·ⁿ absᶻ aᶻ ◼) (λ i → absᶻ (transport s' (sym s) i))
    ... | inr 0<aᶻ =
      signed (signᶻ aᶻ ⊕ spos) (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' bᶻ))) ≡⟨ (λ i → signed (0<ᶻ-signᶻ aᶻ 0<aᶻ i ⊕ spos) (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' bᶻ)))) ⟩
      signed             spos  (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' bᶻ))) ≡⟨ transport s' (sym s) ⟩
      signed             spos  (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' aᶻ))) ≡⟨ (λ i → signed (0<ᶻ-signᶻ bᶻ 0<bᶻ (~ i) ⊕ spos) (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' aᶻ)))) ⟩
      signed (signᶻ bᶻ ⊕ spos) (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' aᶻ))) ∎ where
      0<bᶻ : [ 0 <ᶻ bᶻ ]
      0<bᶻ = ∼-preserves-< aᶻ aⁿ bᶻ bⁿ p .snd 0<aᶻ
      abstract
        c       = <ᶻ-split-pos aᶻ 0<aᶻ .fst
        d       = <ᶻ-split-pos bᶻ 0<bᶻ .fst
        aᶻ≡sc   : aᶻ ≡ pos (suc c)
        aᶻ≡sc   = <ᶻ-split-pos aᶻ 0<aᶻ .snd
        bᶻ≡sd   : bᶻ ≡ pos (suc d)
        bᶻ≡sd   = <ᶻ-split-pos bᶻ 0<bᶻ .snd
        absa≡sc : absᶻ aᶻ ≡ suc c
        absa≡sc i = absᶻ (aᶻ≡sc i)
        absb≡sd : absᶻ bᶻ ≡ suc d
        absb≡sd i = absᶻ (bᶻ≡sd i)
      s' = bᶻ  ·ᶻ aⁿᶻ         ≡ aᶻ  ·ᶻ bⁿᶻ         ≡⟨ (λ i → ·ᶻ-comm bᶻ aⁿᶻ i ≡ ·ᶻ-comm aᶻ bⁿᶻ i) ⟩
           aⁿᶻ ·ᶻ bᶻ          ≡ bⁿᶻ ·ᶻ aᶻ          ≡⟨ (λ i → aⁿᶻ ·ᶻ bᶻ≡sd i ≡ bⁿᶻ ·ᶻ aᶻ≡sc i) ⟩
           aⁿᶻ ·ᶻ pos (suc d) ≡ bⁿᶻ ·ᶻ pos (suc c) ≡⟨ refl ⟩
             pos (suc (ℕ₊₁.n aⁿ) ·ⁿ suc d)
           ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ suc c) ≡⟨ (λ i → pos (suc (ℕ₊₁.n aⁿ) ·ⁿ absb≡sd (~ i)) ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ absa≡sc (~ i))) ⟩
             pos (suc (ℕ₊₁.n aⁿ) ·ⁿ absᶻ bᶻ)
           ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ absᶻ aᶻ) ≡⟨ (λ i → pos (suc (ℕ₊₁.n aⁿ) ·ⁿ absⁿ⁺¹'-identityⁿ bᶻ (inr 0<bᶻ) (~ i)) ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ absⁿ⁺¹'-identityⁿ aᶻ (inr 0<aᶻ) (~ i))) ⟩
             pos (suc (ℕ₊₁.n aⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' bᶻ)))
           ≡ pos (suc (ℕ₊₁.n bⁿ) ·ⁿ suc (ℕ₊₁.n (absⁿ⁺¹' aᶻ))) ∎
  -- eq/ a b r : [ a ]ᶠ ≡ [ b ]ᶠ
  γ : [ [ a ]ᶠ # 0 ] ≡ [ [ b ]ᶠ # 0 ]
  γ i = [ eq/ a b p i # 0 ]
  κ : PathP _ (a ⁻¹') (b ⁻¹')
  κ i = λ(q : [ eq/ a b p i # 0 ]) → eq/ (signed (signᶻ aᶻ) (ℕ₊₁→ℕ aⁿ) , absⁿ⁺¹' aᶻ) (signed (signᶻ bᶻ) (ℕ₊₁→ℕ bⁿ) , absⁿ⁺¹' bᶻ) (r (ψ q)) i where
    ψ : [ eq/ a b p i # 0 ] → [ eq/ a b p i0 # 0 ]
    ψ p = transport (λ j → γ (i ∧ ~ j)) p

_⁻¹ : (x : ℚ) → [ x # 0 ] → ℚ
_⁻¹ = SetQuotient.elim {R = _∼_} {B = λ x → [ x # 0 ] → ℚ} φ _⁻¹' ⁻¹'-respects-∼ where
  φ : ∀ x → isSet ([ x # 0 ] → ℚ)
  φ x = isSetΠ (λ _ → isSetℚ)
