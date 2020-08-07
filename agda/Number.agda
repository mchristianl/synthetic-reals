{-# OPTIONS --cubical --no-import-sorts #-}

module Number where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

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

open import Number.Coercions

ℝ↪ℝ : ℝ.ℝ → ℝ.ℝ
ℝ↪ℝ x = x

{-
ℝ↪ℝinc : IsROrderedFieldInclusion ℝOF ℝOF ℝ↪ℝ
ℝ↪ℝinc = {!!}
-}


open import Cubical.Data.Fin.Base
-- import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Cubical.Data.Nat.Properties using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_; _≟_ to _≟ₙ_)
-- open import Data.Nat.Base using (ℕ; z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ₙ_; _<_ to _<ₙ_; _+_ to _+ₙ_)
open import Agda.Builtin.Bool renaming (true to TT; false to FF)
open import Function.Base using (it; _$_) -- instance search
import Cubical.Data.Fin.Properties
open import Data.Nat.Properties using (+-mono-<)

-- NOTE: well, for 15 allowed coercions, we might just enumerate them
--   unfortunately with overlapping patterns a style as in `Cl` is not possible
--   we need to explicitly write out all the 5×5 combinations
--   or, we implement a min operator which might work even with overlapping patterns

k+x+sy≢x : ∀ k x y → ¬(k +ₙ (x +ₙ suc y) ≡ x)
k+x+sy≢x k x y p = snotz $ sym (+-suc k y) ∙ inj-m+ {x} (+-assoc x k (suc y) ∙ (λ i → (+-comm x k) i +ₙ (suc y)) ∙ sym (+-assoc k x (suc y)) ∙ p ∙ sym (+-zero x))

-- num {isNat     ,, p} (number (x , q)) = x
-- num {isInt     ,, p} (number (x , q)) = x
-- num {isRat     ,, p} (number (x , q)) = x
-- num {isReal    ,, p} (number (x , q)) = x
-- num {isComplex ,, p} (number (x , q)) = x


-- TODO: name this "inject" instead of "coerce"
-- TODO: make the module ℤ and the Carrier ℤ.ℤ
-- TODO: for a binary relation `a # b` it would be nice to have a way to compose ≡-pathes to the left and the right
--       similar to how ∙ can be used for pathes
--       this reasoning might extend to transitive relations
--       `cong₂ _#_ refl x` and `cong₂ _#_ x refl` to this (together with `transport`)
-- NOTE: maybe ℕ↪ℤ should be a postfix operation

-- module _ where
-- module ℕ' = ROrderedCommSemiring ℕ.Bundle
-- module ℤ' = ROrderedCommRing     ℤ.Bundle
-- module ℚ' = ROrderedField        ℚ.Bundle
-- module ℝ' = ROrderedField        ℝ.Bundle
-- module ℂ' = RField               ℂ.Bundle-- 

  

-- coerce-OCSR : ∀{l p} {ll : NumberLevel} {𝕏OCSR 𝕐OCSR : ROrderedCommSemiring {ℝℓ} {ℝℓ'}}
--             → (x : Number (l ,, p))
--             → {f : Il l → Il ll}
--             → IsROrderedCommSemiringInclusion 𝕏OCSR 𝕐OCSR f
--             → Ip ll p (f (num x))
-- coerce-OCSR {l} {ll} {p} {𝕏OCSR} {𝕐OCSR} {f} (number (x , q)) = ?



coerce : (from : NumberLevel)
       → (to   : NumberLevel)
       → from ≤ₙₗ' to
       → ∀{p}
       → Number (from ,, availablePositivity from p)
       → Number (to   ,, availablePositivity to   p)
coerce isNat     isNat     q {p} x = x 
coerce isNat     isInt     q {p} x = number (ℕ↪ℤ (num x) , coerce-ℕ↪ℤ x)
coerce isNat     isRat     q {p} x = {! ℕ↪ℚ !}
coerce isNat     isReal    q {p} x = {! ℕ↪ℝ !}
coerce isNat     isComplex q {p} x = {! ℕ↪ℂ !}
coerce isInt     isInt     q {p} x = x 
coerce isInt     isRat     q {p} x = {! ℤ↪ℚ !}
coerce isInt     isReal    q {p} x = {! ℤ↪ℝ !}
coerce isInt     isComplex q {p} x = {! ℤ↪ℂ !}
coerce isRat     isRat     q {p} x = x 
coerce isRat     isReal    q {p} x = {! ℚ↪ℝ !}
coerce isRat     isComplex q {p} x = {! ℚ↪ℂ !}
coerce isReal    isReal    q {p} x = x 
coerce isReal    isComplex q {p} x = {! ℝ↪ℂ !}
coerce isComplex isComplex q {p} x = x 
--coerce x         y         = nothing
coerce isInt     isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isRat     isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)  
coerce isRat     isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isReal    isRat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isNat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isNat  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isInt  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isInt  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isRat  (k , q) {p} x = ⊥-elim {A = λ _ → Number (isRat  ,, p)} (k+x+sy≢x _ _ _ q)
coerce isComplex isReal (k , q) {p} x = ⊥-elim {A = λ _ → Number (isReal ,, p)} (k+x+sy≢x _ _ _ q)

+-Types : NumberProp → NumberProp → NumberProp
+-Types (level₀ ,, pos₀) (level₁ ,, pos₁) = (Cl level₀ level₁) ,, +-Positivity pos₀ pos₁

·-Types : NumberProp → NumberProp → NumberProp
·-Types (level₀ ,, pos₀) (level₁ ,, pos₁) =  (Cl level₀ level₁) ,, ·-Positivity pos₀ pos₁

private
  instance
    z≤n' : ∀ {n}                 → zero  ≤ₙ n
    z≤n' {n} = z≤n
    s≤s' : ∀ {m n} {{m≤n : m ≤ₙ n}} → suc m ≤ₙ suc n
    s≤s' {m} {n} {{m≤n}} = s≤s m≤n

⁻¹-Levels : (a : NumberLevel) → Σ[ b ∈ NumberLevel ] a ≤ₙₗ b
⁻¹-Levels isNat     = isRat     , it
⁻¹-Levels isInt     = isRat     , it
⁻¹-Levels isRat     = isRat     , it
⁻¹-Levels isReal    = isReal    , it
⁻¹-Levels isComplex = isComplex , it

⁻¹-Levels' : (a : NumberLevel) → NumberLevel
⁻¹-Levels' x = maxₙₗ' x isRat

private
  pattern X   = anyPositivity
  pattern X⁺⁻ = isNonzero
  pattern X₀⁺ = isNonnegative
  pattern X⁺  = isPositive
  pattern X⁻  = isNegative
  pattern X₀⁻ = isNonpositive

⁻¹-Types : NumberProp → Maybe NumberProp
⁻¹-Types (level ,, X  ) = nothing
⁻¹-Types (level ,, X₀⁺) = nothing
⁻¹-Types (level ,, X₀⁻) = nothing
⁻¹-Types (level ,, p  ) = just (fst (⁻¹-Levels level) ,, p)

-Levels : NumberLevel → NumberLevel
-Levels x = minₙₗ' x isInt
-- -Levels isNat = isInt
-- -Levels x     = x

-Types : NumberProp → NumberProp
-Types (level ,, X  ) = -Levels level ,, X
-Types (level ,, X⁺⁻) = -Levels level ,, X⁺⁻
-Types (level ,, X₀⁺) = -Levels level ,, X₀⁻
-Types (level ,, X⁺ ) = -Levels level ,, X⁻
-Types (level ,, X⁻ ) = -Levels level ,, X⁺
-Types (level ,, X₀⁻) = -Levels level ,, X₀⁺

-- coerce : (level-from level-to : NumberLevel) → level-to ≤ₙₗ level-from → Il level-from → Il level-to
-- coerce level-from level-to x = {!!}

--coerce : ∀{p} → (level-from level-to : NumberLevel) → level-from ≤ₙₗ' level-to → Number (level-from ,, p) → Number (level-to ,, p)
--coerce {p} level-from level-to l<l (number (x , q)) = {!!}

_+'_ : ∀{l p q} → Number (l ,, p) → Number (l ,, q) → Number (l ,, +-Positivity p q)
_+'_ a b = {!!}

_+_ : ∀{p q} → Number p → Number q → Number (+-Types p q)
_+_ {xlevel ,, xpos} {ylevel ,, ypos} (number (x , xp)) (number (y , yp)) = number ({!!} , {!!})



