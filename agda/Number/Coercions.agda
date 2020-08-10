{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module Number.Coercions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Data.Maybe.Base

module _ where
  open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
  open import Cubical.Data.Nat.Properties using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)
  open import Function.Base using (_$_)

  k+x+sy≢x : ∀ k x y → ¬(k +ₙ (x +ₙ suc y) ≡ x)
  k+x+sy≢x k x y p = snotz $ sym (+-suc k y) ∙ inj-m+ {x} (+-assoc x k (suc y) ∙ (λ i → (+-comm x k) i +ₙ (suc y)) ∙ sym (+-assoc k x (suc y)) ∙ p ∙ sym (+-zero x))


-- open import Bundles

open import Number.Postulates
open import Number.Structures
open import Number.Bundles
open import Number.Inclusions
open import Number.Blueprint

-- tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
-- tmp (x ,, p) = {! x ℕ.+ x !}

-- open ℕⁿ ℕ.bundle
open ℕⁿ
open ℤᶻ ℤ.bundle
open ℚᶠ ℚ.bundle
open ℝʳ ℝ.bundle
open ℂᶜ ℂ.bundle

-- tmp' : Number (isNat ,, isNonnegative) → 0ⁿ <ⁿ 1ⁿ → Number (isNat ,, isPositive)
-- tmp' (x ,, p) q = {! 1ⁿ !} -- x +ⁿ x

-- module _ where
--   open ℕ
--   -- open ℕ'
--   tmp'' : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
--   tmp'' (x ,, p) = {! x · x !} -- x + x

{-

Now, we have explored a state where

  open ℕⁿ
  tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
  tmp (x ,, p) = {!! x +ⁿ x !}

creates on `C-c C-.`

  Have: ℕ
  p : 0ⁿ ≤ⁿ x
  x : ℕ

and on `C-u C-c C-.`

  Have: ROrderedCommSemiring.Carrier bundle
  p : Ip isNat isNonnegative x
  x : Il isNat

and on `C-u C-u C-c C-.`

  Have: Lift ℕ₀
  p : Lift (Σ ℕ₀ (λ k → (k Agda.Builtin.Nat.+ 0) ≡ lower x))
  x : Lift ℕ₀

where additionally opening ℕ brings _+_ into scope (as _+ⁿ_)

  open ℕⁿ
  open ℕ hiding (ℕ; ℕ₀)
  tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
  tmp (x ,, p) = {! x + x !}

creates on `C-c C-.`

  Have: ℕ
  p : 0ⁿ ≤ⁿ x
  x : ℕ

and on `C-u C-c C-.`

  Have: ROrderedCommSemiring.Carrier ℕⁿ.bundle
  p : Ip isNat isNonnegative x
  x : Il isNat

and on `C-u C-u C-c C-.`

  Have: Lift ℕ₀
  p : Lift (Σ ℕ₀ (λ k → (k Agda.Builtin.Nat.+ 0) ≡ lower x))
  x : Lift ℕ₀


-}

{-
private
  -- ordered ring
  pattern ⁇x⁇ = anyPositivityᵒʳ
  pattern x#0 = isNonzeroᵒʳ
  pattern 0≤x = isNonnegativeᵒʳ
  pattern 0<x = isPositiveᵒʳ
  pattern x<0 = isNegativeᵒʳ
  pattern x≤0 = isNonpositiveᵒʳ
  -- field (overlapping)
  pattern ⁇x⁇ = anyPositivityᶠ
  pattern x#0 = isNonzeroᶠ
-}

open PatternsProp

module Coerce-ℕ↪ℤ where
  open ℤ
  open IsROrderedCommSemiringInclusion ℕ↪ℤinc
  private f = ℕ↪ℤ
  abstract
    coerce-ℕ↪ℤ : ∀{p} → (x : Number (isNat , p)) → PositivityLevelInterpretation isInt (coerce-PositivityLevel isNat isInt p) (ℕ↪ℤ (num x))
    coerce-ℕ↪ℤ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℤ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℤ {0≤x} (x ,, q) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℤ {0<x} (x ,, q) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) 
    coerce-ℕ↪ℤ {x≤0} (x ,, q) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℕ↪ℚ where
  open ℚ
  open IsROrderedCommSemiringInclusion ℕ↪ℚinc
  private f = ℕ↪ℚ
  abstract
    coerce-ℕ↪ℚ : ∀{p} → (x : Number (isNat , p)) → PositivityLevelInterpretation isRat (coerce-PositivityLevel isNat isRat p) (ℕ↪ℚ (num x))
    coerce-ℕ↪ℚ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℚ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
    coerce-ℕ↪ℚ {0≤x} (x ,, q) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q) 
    coerce-ℕ↪ℚ {0<x} (x ,, q) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) 
    coerce-ℕ↪ℚ {x≤0} (x ,, q) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℕ↪ℝ where
  open ℝ
  open IsROrderedCommSemiringInclusion ℕ↪ℝinc
  private f = ℕ↪ℝ
  abstract
    coerce-ℕ↪ℝ : ∀{p} → (x : Number (isNat , p)) → PositivityLevelInterpretation isReal (coerce-PositivityLevel isNat isReal p) (ℕ↪ℝ (num x))
    coerce-ℕ↪ℝ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℝ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
    coerce-ℕ↪ℝ {0≤x} (x ,, q) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℝ {0<x} (x ,, q) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) 
    coerce-ℕ↪ℝ {x≤0} (x ,, q) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℕ↪ℂ where
  open ℂ
  open Isℕ↪ℂ ℕ↪ℂinc
  private f = ℕ↪ℂ
  abstract
    coerce-ℕ↪ℂ : ∀{p} → (x : Number (isNat , p)) → PositivityLevelInterpretation isComplex (coerce-PositivityLevel isNat isComplex p) (ℕ↪ℂ (num x))
    coerce-ℕ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℕ↪ℂ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℕ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ (ℕ.#-sym _ _ (ℕ.<-implies-# _ _ q))) 
    coerce-ℕ↪ℂ {x≤0} (x ,, q) = lift tt

module Coerce-ℤ↪ℚ where
  open ℚ
  open IsROrderedCommRingInclusion ℤ↪ℚinc
  private f = ℤ↪ℚ
  abstract
    coerce-ℤ↪ℚ : ∀{p} → (x : Number (isInt , p)) → PositivityLevelInterpretation isRat (coerce-PositivityLevel isInt isRat p) (ℤ↪ℚ (num x))
    coerce-ℤ↪ℚ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℤ↪ℚ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
    coerce-ℤ↪ℚ {0≤x} (x ,, q) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℤ↪ℚ {0<x} (x ,, q) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) 
    coerce-ℤ↪ℚ {x<0} (x ,, q) = transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
    coerce-ℤ↪ℚ {x≤0} (x ,, q) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℤ↪ℝ where
  open ℝ
  open IsROrderedCommRingInclusion ℤ↪ℝinc
  private f = ℤ↪ℝ
  abstract
    coerce-ℤ↪ℝ : ∀{p} → (x : Number (isInt , p)) → PositivityLevelInterpretation isReal (coerce-PositivityLevel isInt isReal p) (ℤ↪ℝ (num x))
    coerce-ℤ↪ℝ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℤ↪ℝ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℤ↪ℝ {0≤x} (x ,, q) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℤ↪ℝ {0<x} (x ,, q) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℤ↪ℝ {x<0} (x ,, q) = transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
    coerce-ℤ↪ℝ {x≤0} (x ,, q) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℤ↪ℂ where
  open ℂ
  open Isℤ↪ℂ ℤ↪ℂinc
  private f = ℤ↪ℂ
  abstract
    coerce-ℤ↪ℂ : ∀{p} → (x : Number (isInt , p)) → PositivityLevelInterpretation isComplex (coerce-PositivityLevel isInt isComplex p) (ℤ↪ℂ (num x))
    coerce-ℤ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℤ↪ℂ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℤ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℤ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ (ℤ.#-sym _ _ (ℤ.<-implies-# _ _ q)))
    coerce-ℤ↪ℂ {x<0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _              (ℤ.<-implies-# _ _ q) )
    coerce-ℤ↪ℂ {x≤0} (x ,, q) = lift tt

module Coerce-ℚ↪ℝ where
  open ℝ
  open IsROrderedFieldInclusion ℚ↪ℝinc
  private f = ℚ↪ℝ
  abstract
    coerce-ℚ↪ℝ : ∀{p} → (x : Number (isRat , p)) → PositivityLevelInterpretation isReal (coerce-PositivityLevel isRat isReal p) (ℚ↪ℝ (num x))
    coerce-ℚ↪ℝ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℚ↪ℝ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℚ↪ℝ {0≤x} (x ,, q) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℚ↪ℝ {0<x} (x ,, q) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℚ↪ℝ {x<0} (x ,, q) = transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
    coerce-ℚ↪ℝ {x≤0} (x ,, q) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module Coerce-ℚ↪ℂ where
  open ℂ
  open IsRFieldInclusion ℚ↪ℂinc
  private f = ℚ↪ℂ
  abstract
    coerce-ℚ↪ℂ : ∀{p} → (x : Number (isRat , p)) → PositivityLevelInterpretation isComplex (coerce-PositivityLevel isRat isComplex p) (ℚ↪ℂ (num x))
    coerce-ℚ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℚ↪ℂ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℚ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℚ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ (ℚ.#-sym _ _ (ℚ.<-implies-# _ _ q)))
    coerce-ℚ↪ℂ {x<0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _              (ℚ.<-implies-# _ _ q) )
    coerce-ℚ↪ℂ {x≤0} (x ,, q) = lift tt

module Coerce-ℝ↪ℂ where
  open ℂ
  open IsRFieldInclusion ℝ↪ℂinc
  private f = ℝ↪ℂ
  abstract
    coerce-ℝ↪ℂ : ∀{p} → (x : Number (isReal , p)) → PositivityLevelInterpretation isComplex (coerce-PositivityLevel isReal isComplex p) (ℝ↪ℂ (num x))
    coerce-ℝ↪ℂ {⁇x⁇} (x ,, q) = lift tt
    coerce-ℝ↪ℂ {x#0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℝ↪ℂ {0≤x} (x ,, q) = lift tt
    coerce-ℝ↪ℂ {0<x} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ (ℝ.#-sym _ _ (ℝ.<-implies-# _ _ q)))
    coerce-ℝ↪ℂ {x<0} (x ,, q) = transport (λ i → f x # preserves-0 i) (preserves-# _ _              (ℝ.<-implies-# _ _ q) )
    coerce-ℝ↪ℂ {x≤0} (x ,, q) = lift tt



-- does this make anything faster?
open Coerce-ℕ↪ℤ public
open Coerce-ℕ↪ℚ public
open Coerce-ℕ↪ℝ public
open Coerce-ℕ↪ℂ public
open Coerce-ℤ↪ℚ public
open Coerce-ℤ↪ℝ public
open Coerce-ℤ↪ℂ public
open Coerce-ℚ↪ℝ public
open Coerce-ℚ↪ℂ public
open Coerce-ℝ↪ℂ public

coerce : (from : NumberKind)
       → (to   : NumberKind)
       → from ≤ₙₗ to
       → ∀{p}
       → Number (from , p)
       → Number (to   , coerce-PositivityLevel from to p)
coerce isNat     isNat     q {p} x = x 
coerce isInt     isInt     q {p} x = x
coerce isRat     isRat     q {p} x = x
coerce isReal    isReal    q {p} x = x
coerce isComplex isComplex q {p} x = x
coerce isNat     isInt     q {p} x = (ℕ↪ℤ (num x) ,, coerce-ℕ↪ℤ x)
coerce isNat     isRat     q {p} x = (ℕ↪ℚ (num x) ,, coerce-ℕ↪ℚ x)
coerce isNat     isReal    q {p} x = (ℕ↪ℝ (num x) ,, coerce-ℕ↪ℝ x)
coerce isNat     isComplex q {p} x = (ℕ↪ℂ (num x) ,, coerce-ℕ↪ℂ x)
coerce isInt     isRat     q {p} x = (ℤ↪ℚ (num x) ,, coerce-ℤ↪ℚ x)
coerce isInt     isReal    q {p} x = (ℤ↪ℝ (num x) ,, coerce-ℤ↪ℝ x)
coerce isInt     isComplex q {p} x = (ℤ↪ℂ (num x) ,, coerce-ℤ↪ℂ x)
coerce isRat     isReal    q {p} x = (ℚ↪ℝ (num x) ,, coerce-ℚ↪ℝ x)
coerce isRat     isComplex q {p} x = (ℚ↪ℂ (num x) ,, coerce-ℚ↪ℂ x)
coerce isReal    isComplex q {p} x = (ℝ↪ℂ (num x) ,, coerce-ℝ↪ℂ x)
--coerce x         y         = nothing
coerce isInt     isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , p)} (k+x+sy≢x _ _ _ q)
coerce isRat     isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , p)} (k+x+sy≢x _ _ _ q)  
coerce isRat     isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  , p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  , p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isRat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  , p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  , coerce-PositivityLevel isComplex isNat  p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  , coerce-PositivityLevel isComplex isInt  p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isRat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  , coerce-PositivityLevel isComplex isRat  p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isReal (k , q) {p} x = ⊥-elim {A = λ _ → Number (isReal , coerce-PositivityLevel isComplex isReal p)} (k+x+sy≢x _ _ _ q)
