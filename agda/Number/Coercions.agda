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
-- open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Data.Maybe.Base

-- open import Bundles

open import Number.Postulates
open import Number.Structures ℝℓ ℝℓ'
open import Number.Bundles    ℝℓ ℝℓ'
open import Number.Inclusions ℝℓ ℝℓ'
open import Number.Blueprint

tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
tmp (number (x , p)) = {! x ℕ.+ x !}

-- open ℕⁿ ℕ.bundle
open ℕⁿ
open ℤᶻ ℤ.bundle
open ℚᶠ ℚ.bundle
open ℝʳ ℝ.bundle
open ℂᶜ ℂ.bundle

tmp' : Number (isNat ,, isNonnegative) → 0ⁿ <ⁿ 1ⁿ → Number (isNat ,, isPositive)
tmp' (number (x , p)) q = {! 1ⁿ !} -- x +ⁿ x

module _ where
  open ℕ
  -- open ℕ'
  tmp'' : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
  tmp'' (number (x , p)) = {! x · x !} -- x + x

{-

Now, we have explored a state where

  open ℕⁿ
  tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
  tmp (number (x , p)) = {!! x +ⁿ x !}

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
  tmp (number (x , p)) = {! x + x !}

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

private
  pattern ⁇x⁇ = anyPositivity
  pattern x#0 = isNonzero
  pattern 0≤x = isNonnegative
  pattern 0<x = isPositive
  pattern x<0 = isNegative
  pattern x≤0 = isNonpositive

module _ where
  open ℤ
  open IsROrderedCommSemiringInclusion ℕ↪ℤinc
  private f = ℕ↪ℤ
  coerce-ℕ↪ℤ : ∀{p} → (x : Number (isNat ,, p)) → Ip isInt p (ℕ↪ℤ (num x))
  coerce-ℕ↪ℤ {⁇x⁇} (number (x , q)) = lift tt
  coerce-ℕ↪ℤ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
  coerce-ℕ↪ℤ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
  coerce-ℕ↪ℤ {0<x} (number (x , q)) = {! transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) !}
  coerce-ℕ↪ℤ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module _ where
  open ℚ
  open IsROrderedCommSemiringInclusion ℕ↪ℚinc
  private f = ℕ↪ℚ
  coerce-ℕ↪ℚ : ∀{p} → (x : Number (isNat ,, p)) → Ip isRat p (ℕ↪ℚ (num x))
  coerce-ℕ↪ℚ {⁇x⁇} (number (x , q)) = lift tt
  coerce-ℕ↪ℚ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
  coerce-ℕ↪ℚ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q) 
  coerce-ℕ↪ℚ {0<x} (number (x , q)) = {! transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) !}
  coerce-ℕ↪ℚ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module _ where
  open ℝ.Bundle ℝ.bundle
  open IsROrderedCommSemiringInclusion ℕ↪ℝinc
  private f = ℕ↪ℝ
  coerce-ℕ↪ℝ : ∀{p} → (x : Number (isNat ,, p)) → Ip isReal p (ℕ↪ℝ (num x))
  coerce-ℕ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
  coerce-ℕ↪ℝ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
  coerce-ℕ↪ℝ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
  coerce-ℕ↪ℝ {0<x} (number (x , q)) = {! transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) !}
  coerce-ℕ↪ℝ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

module _ where
  open ℂ.Bundle ℂ.bundle renaming (Carrier to ℂ)
  open Isℕ↪ℂ ℕ↪ℂinc
  private f = ℕ↪ℂ
  coerce-ℕ↪ℂ : ∀{p} → (x : Number (isNat ,, p)) → Ip isComplex (availablePositivity isComplex p) (ℕ↪ℂ (num x))
  coerce-ℕ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
  coerce-ℕ↪ℂ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
  coerce-ℕ↪ℂ {0≤x} (number (x , q)) = lift tt
  coerce-ℕ↪ℂ {0<x} (number (x , q)) = {! transport (λ i → f x # preserves-0 i) (preserves-# _ _ (ℕ.#-sym _ _ (ℕ.<-implies-# _ _ q))) !}
  coerce-ℕ↪ℂ {x≤0} (number (x , q)) = lift tt

module _ where
  open ℚ.Bundle ℚ.bundle
  open IsROrderedCommRingInclusion ℤ↪ℚinc
  private f = ℤ↪ℚ
  coerce-ℤ↪ℚ : ∀{p} → (x : Number (isInt ,, p)) → Ip isRat p (ℤ↪ℚ (num x))
  coerce-ℤ↪ℚ {⁇x⁇} (number (x , q)) = lift tt
  coerce-ℤ↪ℚ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
  coerce-ℤ↪ℚ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
  coerce-ℤ↪ℚ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
  coerce-ℤ↪ℚ {x<0} (number (x , q)) = transport (λ i → f x < preserves-0 i) (preserves-< _ _ q)
  coerce-ℤ↪ℚ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

coerce-ℤ↪ℝ : ∀{p} → (x : Number (isInt ,, p)) → Ip isReal p (ℤ↪ℝ (num x))
coerce-ℤ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
coerce-ℤ↪ℝ {x#0} (number (x , q)) = {!!}
coerce-ℤ↪ℝ {0≤x} (number (x , q)) = {!!}
coerce-ℤ↪ℝ {0<x} (number (x , q)) = {!!}
coerce-ℤ↪ℝ {x<0} (number (x , q)) = {!!}
coerce-ℤ↪ℝ {x≤0} (number (x , q)) = {!!}

coerce-ℤ↪ℂ : ∀{p} → (x : Number (isInt ,, p)) → Ip isComplex p (ℤ↪ℂ (num x))
coerce-ℤ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
coerce-ℤ↪ℂ {x#0} (number (x , q)) = {!!}
coerce-ℤ↪ℂ {0≤x} (number (x , q)) = {!!}
coerce-ℤ↪ℂ {0<x} (number (x , q)) = {!!}
coerce-ℤ↪ℂ {x<0} (number (x , q)) = {!!}
coerce-ℤ↪ℂ {x≤0} (number (x , q)) = {!!}

coerce-ℚ↪ℝ : ∀{p} → (x : Number (isRat ,, p)) → Ip isReal p (ℚ↪ℝ (num x))
coerce-ℚ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
coerce-ℚ↪ℝ {x#0} (number (x , q)) = {!!}
coerce-ℚ↪ℝ {0≤x} (number (x , q)) = {!!}
coerce-ℚ↪ℝ {0<x} (number (x , q)) = {!!}
coerce-ℚ↪ℝ {x<0} (number (x , q)) = {!!}
coerce-ℚ↪ℝ {x≤0} (number (x , q)) = {!!}

coerce-ℚ↪ℂ : ∀{p} → (x : Number (isRat ,, p)) → Ip isComplex p (ℚ↪ℂ (num x))
coerce-ℚ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
coerce-ℚ↪ℂ {x#0} (number (x , q)) = {!!}
coerce-ℚ↪ℂ {0≤x} (number (x , q)) = {!!}
coerce-ℚ↪ℂ {0<x} (number (x , q)) = {!!}
coerce-ℚ↪ℂ {x<0} (number (x , q)) = {!!}
coerce-ℚ↪ℂ {x≤0} (number (x , q)) = {!!}

coerce-ℝ↪ℂ : ∀{p} → (x : Number (isReal ,, p)) → Ip isComplex p (ℝ↪ℂ (num x))
coerce-ℝ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
coerce-ℝ↪ℂ {x#0} (number (x , q)) = {!!}
coerce-ℝ↪ℂ {0≤x} (number (x , q)) = {!!}
coerce-ℝ↪ℂ {0<x} (number (x , q)) = {!!}
coerce-ℝ↪ℂ {x<0} (number (x , q)) = {!!}
coerce-ℝ↪ℂ {x≤0} (number (x , q)) = {!!}
