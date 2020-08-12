{-# OPTIONS --cubical --no-import-sorts --allow-unsolved-metas #-}

module Number.GenericOperations where

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
open import Function.Base using (_∋_)

-- open import Bundles

open import Number.Postulates
open import Number.Structures
open import Number.Bundles
open import Number.Inclusions
open import Number.Blueprint
open import Number.Coercions

open import Cubical.Data.Fin.Base
-- import Cubical.Data.Fin.Properties
-- open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
-- open import Cubical.Data.Nat.Properties using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_; _≟_ to _≟ₙ_)
-- open import Data.Nat.Base using (ℕ; z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ₙ_; _<_ to _<ₙ_; _+_ to _+ₙ_)
-- open import Agda.Builtin.Bool renaming (true to TT; false to FF)
open import Function.Base using (it; _$_) -- instance search
-- import Cubical.Data.Fin.Properties
-- open import Data.Nat.Properties using (+-mono-<)


+-Types : NumberProp → NumberProp → NumberProp
+-Types (level₀ , pos₀) (level₁ , pos₁) =
  let level  = maxₙₗ level₀ level₁
  in level , +-Positivityʰ level (coerce-PositivityKind level₀ level pos₀) (coerce-PositivityKind level₁ level pos₁)

·-Types : NumberProp → NumberProp → NumberProp
·-Types (level₀ , pos₀) (level₁ , pos₁) =
  let level  = maxₙₗ level₀ level₁
  in level , ·-Positivityʰ level (coerce-PositivityKind level₀ level pos₀) (coerce-PositivityKind level₁ level pos₁)

open ℕⁿ
open ℤᶻ
open ℚᶠ
open ℝʳ
open ℂᶜ

open PatternsType

⁻¹-Types : ∀{l p} → Number (l , p) → Type (ℓ-max (NumberLevel (maxₙₗ l isRat)) (NumberKindProplevel l))
-- numbers that can be zero need an additional apartness proof
⁻¹-Types {isNat    } {X  } (x ,, p) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isInt    } {X  } (x ,, p) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isRat    } {X  } (x ,, p) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isReal   } {X  } (x ,, p) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁺⁻)
⁻¹-Types {isComplex} {X  } (x ,, p) = ∀{{ q : x #ᶜ 0ᶜ }} → Number (isComplex , X⁺⁻)
⁻¹-Types {isNat    } {X₀⁺} (x ,, p) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isRat     , X⁺ )
⁻¹-Types {isInt    } {X₀⁺} (x ,, p) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isRat     , X⁺ )
⁻¹-Types {isRat    } {X₀⁺} (x ,, p) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁺ )
⁻¹-Types {isReal   } {X₀⁺} (x ,, p) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁺ )
⁻¹-Types {isNat    } {X₀⁻} (x ,, p) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isRat     , X⁻ )
⁻¹-Types {isInt    } {X₀⁻} (x ,, p) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isRat     , X⁻ )
⁻¹-Types {isRat    } {X₀⁻} (x ,, p) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁻ )
⁻¹-Types {isReal   } {X₀⁻} (x ,, p) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁻ )
-- positive, negative and nonzero numbers are already apart from zero
⁻¹-Types {isNat    } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isNat    } Unit }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isNat    } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isNat    } Unit }} → Number (isRat     , X⁺ )
⁻¹-Types {isInt    } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isInt    } Unit }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isInt    } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isInt    } Unit }} → Number (isRat     , X⁺ )
⁻¹-Types {isInt    } {X⁻ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isInt    } Unit }} → Number (isRat     , X⁻ )
⁻¹-Types {isRat    } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isRat    } Unit }} → Number (isRat     , X⁺⁻)
⁻¹-Types {isRat    } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isRat    } Unit }} → Number (isRat     , X⁺ )
⁻¹-Types {isRat    } {X⁻ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isRat    } Unit }} → Number (isRat     , X⁻ )
⁻¹-Types {isReal   } {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isReal   } Unit }} → Number (isReal    , X⁺⁻)
⁻¹-Types {isReal   } {X⁺ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isReal   } Unit }} → Number (isReal    , X⁺ )
⁻¹-Types {isReal   } {X⁻ } (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isReal   } Unit }} → Number (isReal    , X⁻ )
⁻¹-Types {isComplex} {X⁺⁻} (x ,, p) = ∀{{ q : Lift {j = NumberKindProplevel isComplex} Unit }} → Number (isComplex , X⁺⁻)

_⁻¹ : ∀{l p} → (x : Number (l , p)) → ⁻¹-Types x

_⁻¹ {isNat    } {X  } (x ,, q) {{h}} = let r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ h in _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isNat    } {X⁺⁻} (x ,, q) {{h}} = let r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ q in _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isNat    } {X₀⁺} (x ,, q) {{h}} = let p = Isℕ↪ℚ.preserves-0< ℕ↪ℚinc _ (ℕ.≤-#-implies-< _ _ q (ℕ.#-sym _ _ h))
                                           r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r 
_⁻¹ {isNat    } {X⁺ } (x ,, q) {{h}} = let p = Isℕ↪ℚ.preserves-0< ℕ↪ℚinc _ q
                                           r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ (ℕ.#-sym _ _ (ℕ.<-implies-# _ _ q))
                                       in  _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r 
_⁻¹ {isNat    } {X₀⁻} (x ,, q) {{h}} = let p = Isℕ↪ℚ.preserves-<0 ℕ↪ℚinc _ (ℕ.≤-#-implies-< _ _ q h)
                                           r = Isℕ↪ℚ.preserves-#0 ℕ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℕ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-<0 _ p r

_⁻¹ {isInt    } {X  } (x ,, q) {{h}} = let r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ h in _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isInt    } {X⁺⁻} (x ,, q) {{h}} = let r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ q in _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-#0 _ r
_⁻¹ {isInt    } {X₀⁺} (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-0< ℤ↪ℚinc _ (ℤ.≤-#-implies-< _ _ q (ℤ.#-sym _ _ h))
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r 
_⁻¹ {isInt    } {X⁺ } (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-0< ℤ↪ℚinc _ q
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ (ℤ.#-sym _ _ (ℤ.<-implies-# _ _ q))
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-0< _ p r
_⁻¹ {isInt    } {X⁻ } (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-<0 ℤ↪ℚinc _ q
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ (ℤ.<-implies-# _ _ q)
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,,  ℚ.⁻¹-preserves-<0 _ p r 
_⁻¹ {isInt    } {X₀⁻} (x ,, q) {{h}} = let p = Isℤ↪ℚ.preserves-<0 ℤ↪ℚinc _ (ℤ.≤-#-implies-< _ _ q h)
                                           r = Isℤ↪ℚ.preserves-#0 ℤ↪ℚinc _ h
                                       in  _⁻¹ᶠ (ℤ↪ℚ x) {{r}} ,, ℚ.⁻¹-preserves-<0 _ p r

_⁻¹ {isRat    } {X  } (x ,, q) {{h}} =  _⁻¹ᶠ x  {{h}} ,, ℚ.⁻¹-preserves-#0 x h
_⁻¹ {isRat    } {X⁺⁻} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{q}} ,, ℚ.⁻¹-preserves-#0 x q
_⁻¹ {isRat    } {X₀⁺} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{h}} ,, ℚ.⁻¹-preserves-0< x (ℚ.≤-#-implies-< _ _ q (ℚ.#-sym _ _ h)) h 
_⁻¹ {isRat    } {X⁺ } (x ,, q) {{h}} = let r = ℚ.#-sym _ _ (ℚ.<-implies-# _ _ q) in _⁻¹ᶠ x  {{r}} ,,  ℚ.⁻¹-preserves-0< _ q r
_⁻¹ {isRat    } {X⁻ } (x ,, q) {{h}} = let r = ℚ.<-implies-# _ _ q in _⁻¹ᶠ x  {{r}} ,, ℚ.⁻¹-preserves-<0 _ q r
_⁻¹ {isRat    } {X₀⁻} (x ,, q) {{h}} =  _⁻¹ᶠ x  {{h}} ,,  ℚ.⁻¹-preserves-<0 x (ℚ.≤-#-implies-< _ _ q h) h

_⁻¹ {isReal   } {X  } (x ,, q) {{h}} =  _⁻¹ʳ x  {{h}} ,, ℝ.⁻¹-preserves-#0 x h
_⁻¹ {isReal   } {X⁺⁻} (x ,, q) {{h}} =  _⁻¹ʳ x  {{q}} ,, ℝ.⁻¹-preserves-#0 x q
_⁻¹ {isReal   } {X₀⁺} (x ,, q) {{h}} =  _⁻¹ʳ x  {{h}} ,, ℝ.⁻¹-preserves-0< x (ℝ.≤-#-implies-< _ _ q (ℝ.#-sym _ _ h)) h 
_⁻¹ {isReal   } {X⁺ } (x ,, q) {{h}} = let r = ℝ.#-sym _ _ (ℝ.<-implies-# _ _ q) in _⁻¹ʳ x {{r}} ,,  ℝ.⁻¹-preserves-0< _ q r
_⁻¹ {isReal   } {X⁻ } (x ,, q) {{h}} = let r = ℝ.<-implies-# _ _ q in _⁻¹ʳ x  {{r}} ,, ℝ.⁻¹-preserves-<0 _ q r
_⁻¹ {isReal   } {X₀⁻} (x ,, q) {{h}} =  _⁻¹ʳ      x  {{h}} ,, ℝ.⁻¹-preserves-<0 x (ℝ.≤-#-implies-< _ _ q h) h

_⁻¹ {isComplex} {X  } (x ,, q) {{h}} =  _⁻¹ᶜ      x  {{h}} ,, ℂ.⁻¹-preserves-#0 x h
_⁻¹ {isComplex} {X⁺⁻} (x ,, q) {{h}} =  _⁻¹ᶜ      x  {{q}} ,, ℂ.⁻¹-preserves-#0 x q

-Types : ∀{l p} → Number (l , p) → Type (NumberLevel (maxₙₗ l isInt))
-Types {isInt    } {X  } (x ,, p) = Number (isInt     , X)
-Types {isRat    } {X  } (x ,, p) = Number (isRat     , X)
-Types {isReal   } {X  } (x ,, p) = Number (isReal    , X)
-Types {isComplex} {X  } (x ,, p) = Number (isComplex , X)
-- the negative of a natural number is a Nonpositive integer
-Types {isNat    } {X  } (x ,, p) = Number (isInt     , X₀⁻)
-- the negative of a nonzero number is a nonzero number
-Types {isNat    } {X⁺⁻} (x ,, p) = Number (isInt     , X⁺⁻)
-Types {isInt    } {X⁺⁻} (x ,, p) = Number (isInt     , X⁺⁻)
-Types {isRat    } {X⁺⁻} (x ,, p) = Number (isRat     , X⁺⁻)
-Types {isReal   } {X⁺⁻} (x ,, p) = Number (isReal    , X⁺⁻)
-Types {isComplex} {X⁺⁻} (x ,, p) = Number (isComplex , X⁺⁻)
-- the negative of a positive number is a negative number
-Types {isNat    } {X₀⁺} (x ,, p) = Number (isInt     , X₀⁻)
-Types {isInt    } {X₀⁺} (x ,, p) = Number (isInt     , X₀⁻)
-Types {isRat    } {X₀⁺} (x ,, p) = Number (isRat     , X₀⁻)
-Types {isReal   } {X₀⁺} (x ,, p) = Number (isReal    , X₀⁻)
-Types {isNat    } {X⁺ } (x ,, p) = Number (isInt     , X⁻ )
-Types {isInt    } {X⁺ } (x ,, p) = Number (isInt     , X⁻ )
-Types {isRat    } {X⁺ } (x ,, p) = Number (isRat     , X⁻ )
-Types {isReal   } {X⁺ } (x ,, p) = Number (isReal    , X⁻ )
-- the negative of a negative number is a positive number
-Types {isNat    } {X₀⁻} (x ,, p) = Number (isInt     , X₀⁺)
-Types {isInt    } {X₀⁻} (x ,, p) = Number (isInt     , X₀⁺)
-Types {isRat    } {X₀⁻} (x ,, p) = Number (isRat     , X₀⁺)
-Types {isReal   } {X₀⁻} (x ,, p) = Number (isReal    , X₀⁺)
-Types {isInt    } {X⁻ } (x ,, p) = Number (isInt     , X⁺ )
-Types {isRat    } {X⁻ } (x ,, p) = Number (isRat     , X⁺ )
-Types {isReal   } {X⁻ } (x ,, p) = Number (isReal    , X⁺ )

-_ : ∀{l p} → (x : Number (l , p)) → -Types x
-_ {isNat    } {X  } (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-0≤ _ $ Isℕ↪ℤ.preserves-0≤ ℕ↪ℤinc _ (ℕ.0≤x x))
-_ {isNat    } {X⁺⁻} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-preserves-#0 _ $ Isℕ↪ℤ.preserves-#0 ℕ↪ℤinc _ p)
-_ {isNat    } {X₀⁺} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-0≤ _ $ Isℕ↪ℤ.preserves-0≤ ℕ↪ℤinc _ p)
-_ {isNat    } {X⁺ } (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-0< _ $ Isℕ↪ℤ.preserves-0< ℕ↪ℤinc _ p)
-_ {isNat    } {X₀⁻} (x ,, p) = (-ᶻ (ℕ↪ℤ x)) ,, (ℤ.-flips-≤0 _ $ Isℕ↪ℤ.preserves-≤0 ℕ↪ℤinc _ p)
-_ {isInt    } {X  } (x ,, p) = (-ᶻ      x ) ,, lift tt
-_ {isInt    } {X⁺⁻} (x ,, p) = (-ᶻ      x ) ,, ℤ.-preserves-#0 _ p
-_ {isInt    } {X₀⁺} (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-0≤ _ p
-_ {isInt    } {X⁺ } (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-0< _ p
-_ {isInt    } {X⁻ } (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-<0 _ p
-_ {isInt    } {X₀⁻} (x ,, p) = (-ᶻ      x ) ,, ℤ.-flips-≤0 _ p
-_ {isRat    } {X  } (x ,, p) = (-ᶠ      x ) ,, lift tt
-_ {isRat    } {X⁺⁻} (x ,, p) = (-ᶠ      x ) ,, ℚ.-preserves-#0 _ p 
-_ {isRat    } {X₀⁺} (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-0≤ _ p
-_ {isRat    } {X⁺ } (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-0< _ p
-_ {isRat    } {X⁻ } (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-<0 _ p
-_ {isRat    } {X₀⁻} (x ,, p) = (-ᶠ      x ) ,, ℚ.-flips-≤0 _ p
-_ {isReal   } {X  } (x ,, p) = (-ʳ      x ) ,, lift tt
-_ {isReal   } {X⁺⁻} (x ,, p) = (-ʳ      x ) ,, ℝ.-preserves-#0 _ p
-_ {isReal   } {X₀⁺} (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-0≤ _ p
-_ {isReal   } {X⁺ } (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-0< _ p
-_ {isReal   } {X⁻ } (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-<0 _ p
-_ {isReal   } {X₀⁻} (x ,, p) = (-ʳ      x ) ,, ℝ.-flips-≤0 _ p
-_ {isComplex} {X  } (x ,, p) = (-ᶜ      x ) ,, lift tt
-_ {isComplex} {X⁺⁻} (x ,, p) = (-ᶜ      x ) ,, ℂ.-preserves-#0 _ p

_+ʰⁿ_ : ∀{p q} → (x : Number (isNat , p)) → (y : Number (isNat , q)) → PositivityKindInterpretation isNat (+-Positivityʰ isNat p q) (num x +ⁿ num y)
_+ʰⁿ_ {X  } {X  } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X  } {X⁺⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X  } {X₀⁺} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X  } {X⁺ } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X  } {X₀⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺⁻} {X  } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺⁻} {X₀⁺} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺⁻} {X⁺ } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺⁻} {X₀⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁺} {X  } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁺} {X⁺⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁺} {X₀⁺} (a ,, pa) (b ,, pb) = ℕ.+-≤-≤-implies-≤ʳ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰⁿ_ {X₀⁺} {X⁺ } (a ,, pa) (b ,, pb) = ℕ.+-≤-<-implies-<ʳ a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰⁿ_ {X₀⁺} {X₀⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺ } {X  } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺ } {X⁺⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X⁺ } {X₀⁺} (a ,, pa) (b ,, pb) = ℕ.+-<-≤-implies-<ʳ a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰⁿ_ {X⁺ } {X⁺ } (a ,, pa) (b ,, pb) = ℕ.+-<-<-implies-<ʳ a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰⁿ_ {X⁺ } {X₀⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁻} {X  } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁻} {X₀⁺} (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁻} {X⁺ } (a ,, pa) (b ,, pb) = tt
_+ʰⁿ_ {X₀⁻} {X₀⁻} (a ,, pa) (b ,, pb) = ℕ.+-≤-≤-implies-≤ˡ a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶻ_ : ∀{p q} → (x : Number (isInt , p)) → (y : Number (isInt , q)) → PositivityKindInterpretation isInt (+-Positivityʰ isInt p q) (num x +ᶻ num y)
_+ʰᶻ_ {X  } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X  } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X  } {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X  } {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X  } {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X  } {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺⁻} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺⁻} {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺⁻} {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺⁻} {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺⁻} {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁺} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁺} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁺} {X₀⁺} (a ,, pa) (b ,, pb) = ℤ.+-≤-≤-implies-≤ʳ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰᶻ_ {X₀⁺} {X⁺ } (a ,, pa) (b ,, pb) = ℤ.+-≤-<-implies-<ʳ a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰᶻ_ {X₀⁺} {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁺} {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺ } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺ } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺ } {X₀⁺} (a ,, pa) (b ,, pb) = ℤ.+-<-≤-implies-<ʳ a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰᶻ_ {X⁺ } {X⁺ } (a ,, pa) (b ,, pb) = ℤ.+-<-<-implies-<ʳ a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰᶻ_ {X⁺ } {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁺ } {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁻ } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁻ } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁻ } {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁻ } {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X⁻ } {X⁻ } (a ,, pa) (b ,, pb) = ℤ.+-<-<-implies-<ˡ a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰᶻ_ {X⁻ } {X₀⁻} (a ,, pa) (b ,, pb) = ℤ.+-<-≤-implies-<ˡ a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰᶻ_ {X₀⁻} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁻} {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁻} {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶻ_ {X₀⁻} {X⁻ } (a ,, pa) (b ,, pb) = ℤ.+-≤-<-implies-<ˡ a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰᶻ_ {X₀⁻} {X₀⁻} (a ,, pa) (b ,, pb) = ℤ.+-≤-≤-implies-≤ˡ a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0    

_+ʰᶠ_ : ∀{p q} → (x : Number (isRat , p)) → (y : Number (isRat , q)) → PositivityKindInterpretation isRat (+-Positivityʰ isRat p q) (num x +ᶠ num y)
_+ʰᶠ_ {X  } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X  } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X  } {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X  } {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X  } {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X  } {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺⁻} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺⁻} {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺⁻} {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺⁻} {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺⁻} {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁺} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁺} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁺} {X₀⁺} (a ,, pa) (b ,, pb) = ℚ.+-≤-≤-implies-≤ʳ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰᶠ_ {X₀⁺} {X⁺ } (a ,, pa) (b ,, pb) = ℚ.+-≤-<-implies-<ʳ a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰᶠ_ {X₀⁺} {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁺} {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺ } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺ } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺ } {X₀⁺} (a ,, pa) (b ,, pb) = ℚ.+-<-≤-implies-<ʳ a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰᶠ_ {X⁺ } {X⁺ } (a ,, pa) (b ,, pb) = ℚ.+-<-<-implies-<ʳ a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰᶠ_ {X⁺ } {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁺ } {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁻ } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁻ } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁻ } {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁻ } {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X⁻ } {X⁻ } (a ,, pa) (b ,, pb) = ℚ.+-<-<-implies-<ˡ a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰᶠ_ {X⁻ } {X₀⁻} (a ,, pa) (b ,, pb) = ℚ.+-<-≤-implies-<ˡ a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰᶠ_ {X₀⁻} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁻} {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁻} {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰᶠ_ {X₀⁻} {X⁻ } (a ,, pa) (b ,, pb) = ℚ.+-≤-<-implies-<ˡ a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰᶠ_ {X₀⁻} {X₀⁻} (a ,, pa) (b ,, pb) = ℚ.+-≤-≤-implies-≤ˡ a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0    

_+ʰʳ_ : ∀{p q} → (x : Number (isReal , p)) → (y : Number (isReal , q)) → PositivityKindInterpretation isReal (+-Positivityʰ isReal p q) (num x +ʳ num y)
_+ʰʳ_ {X  } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X  } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X  } {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X  } {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X  } {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X  } {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺⁻} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺⁻} {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺⁻} {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺⁻} {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺⁻} {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁺} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁺} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁺} {X₀⁺} (a ,, pa) (b ,, pb) = ℝ.+-≤-≤-implies-≤ʳ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰʳ_ {X₀⁺} {X⁺ } (a ,, pa) (b ,, pb) = ℝ.+-≤-<-implies-<ʳ a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰʳ_ {X₀⁺} {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁺} {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺ } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺ } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺ } {X₀⁺} (a ,, pa) (b ,, pb) = ℝ.+-<-≤-implies-<ʳ a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰʳ_ {X⁺ } {X⁺ } (a ,, pa) (b ,, pb) = ℝ.+-<-<-implies-<ʳ a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰʳ_ {X⁺ } {X⁻ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁺ } {X₀⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁻ } {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁻ } {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁻ } {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁻ } {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X⁻ } {X⁻ } (a ,, pa) (b ,, pb) = ℝ.+-<-<-implies-<ˡ a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {X⁻ } {X₀⁻} (a ,, pa) (b ,, pb) = ℝ.+-<-≤-implies-<ˡ a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰʳ_ {X₀⁻} {X  } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁻} {X⁺⁻} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁻} {X₀⁺} (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁻} {X⁺ } (a ,, pa) (b ,, pb) = lift tt
_+ʰʳ_ {X₀⁻} {X⁻ } (a ,, pa) (b ,, pb) = ℝ.+-≤-<-implies-<ˡ a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {X₀⁻} {X₀⁻} (a ,, pa) (b ,, pb) = ℝ.+-≤-≤-implies-≤ˡ a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0    

_+ʰᶜ_ : ∀{p q} → (x : Number (isComplex , p)) → (y : Number (isComplex , q)) → PositivityKindInterpretation isComplex (+-Positivityʰ isComplex p q) (num x +ᶜ num y)
_+ʰᶜ_ x y = lift tt

_+ʰ_ : ∀{l p q} → Number (l , p) → Number (l , q) → Number (l , +-Positivityʰ l p q)
_+ʰ_ {isNat    } x y = (num x +ⁿ num y) ,, (x +ʰⁿ y)
_+ʰ_ {isInt    } x y = (num x +ᶻ num y) ,, (x +ʰᶻ y)
_+ʰ_ {isRat    } x y = (num x +ᶠ num y) ,, (x +ʰᶠ y)
_+ʰ_ {isReal   } x y = (num x +ʳ num y) ,, (x +ʰʳ y)
_+ʰ_ {isComplex} x y = (num x +ᶜ num y) ,, (x +ʰᶜ y)

{- NOTE: this creates a weird Number.L in the Have/Goal display

module _ {Lx Ly Px Py} (x : Number (Lx , Px)) (y : Number (Ly , Py)) where
  private L = maxₙₗ' Lx Ly
  _+_ : Number (L , +-Positivityʰ L (coerce-PositivityKind Lx L Px) (coerce-PositivityKind Ly L Py))
  _+_ =
    let (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂' Lx Ly
    in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y
-}

_+_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py))
    → let L = maxₙₗ Lx Ly
      in Number (L , +-Positivityʰ L (coerce-PositivityKind Lx L Px) (coerce-PositivityKind Ly L Py))
_+_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y

_<ʰ_ : ∀{L} → (x y : NumberKindInterpretation L) → Type (NumberKindProplevel L)
_<ʰ_ {isNat}     x y = x <ⁿ y
_<ʰ_ {isInt}     x y = x <ᶻ y
_<ʰ_ {isRat}     x y = x <ᶠ y
_<ʰ_ {isReal}    x y = x <ʳ y
-- NOTE: this is some realization of a partial function, because `_<_` is defined on all numbers
--       one might already anticipate that this breaks something in the future ...
_<ʰ_ {isComplex} x y = {{p : ⊥}} → Lift ⊥

_<_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberKindProplevel (maxₙₗ Lx Ly))
_<_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) <ʰ num (coerce Ly L Ly≤L y)

_≤ʰ_ : ∀{L} → (x y : NumberKindInterpretation L) → Type (NumberKindProplevel L)
_≤ʰ_ {isNat}     x y = x ≤ⁿ y
_≤ʰ_ {isInt}     x y = x ≤ᶻ y
_≤ʰ_ {isRat}     x y = x ≤ᶠ y
_≤ʰ_ {isReal}    x y = x ≤ʳ y
-- NOTE: this is some realization of a partial function, because `_<_` is defined on all numbers
--       one might already anticipate that this breaks something in the future ...
_≤ʰ_ {isComplex} x y = {{p : ⊥}} → Lift ⊥

_≤_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberKindProplevel (maxₙₗ Lx Ly))
_≤_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) ≤ʰ num (coerce Ly L Ly≤L y)

_#ʰ_ : ∀{L} → (x y : NumberKindInterpretation L) → Type (NumberKindProplevel L)
_#ʰ_ {isNat}     x y = x #ⁿ y
_#ʰ_ {isInt}     x y = x #ᶻ y
_#ʰ_ {isRat}     x y = x #ᶠ y
_#ʰ_ {isReal}    x y = x #ʳ y
_#ʰ_ {isComplex} x y = x #ᶜ y

_#_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberKindProplevel (maxₙₗ Lx Ly))
_#_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) #ʰ num (coerce Ly L Ly≤L y)
