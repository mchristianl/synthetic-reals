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
open import Function.Base using (_∋_)

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
coerce isInt     isInt     q {p} x = x
coerce isRat     isRat     q {p} x = x
coerce isReal    isReal    q {p} x = x
coerce isComplex isComplex q {p} x = x
coerce isNat     isInt     q {p} x = number (ℕ↪ℤ (num x) , coerce-ℕ↪ℤ x)
coerce isNat     isRat     q {p} x = number (ℕ↪ℚ (num x) , coerce-ℕ↪ℚ x)
coerce isNat     isReal    q {p} x = number (ℕ↪ℝ (num x) , coerce-ℕ↪ℝ x)
coerce isNat     isComplex q {p} x = number (ℕ↪ℂ (num x) , coerce-ℕ↪ℂ x)
coerce isInt     isRat     q {p} x = number (ℤ↪ℚ (num x) , coerce-ℤ↪ℚ x)
coerce isInt     isReal    q {p} x = number (ℤ↪ℝ (num x) , coerce-ℤ↪ℝ x)
coerce isInt     isComplex q {p} x = number (ℤ↪ℂ (num x) , coerce-ℤ↪ℂ x)
coerce isRat     isReal    q {p} x = number (ℚ↪ℝ (num x) , coerce-ℚ↪ℝ x)
coerce isRat     isComplex q {p} x = number (ℚ↪ℂ (num x) , coerce-ℚ↪ℂ x)
coerce isReal    isComplex q {p} x = number (ℝ↪ℂ (num x) , coerce-ℝ↪ℂ x)
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
+-Types (level₀ ,, pos₀) (level₁ ,, pos₁) =  (maxₙₗ' level₀ level₁) ,, +-Positivity pos₀ pos₁

·-Types : NumberProp → NumberProp → NumberProp
·-Types (level₀ ,, pos₀) (level₁ ,, pos₁) =  (maxₙₗ' level₀ level₁) ,, ·-Positivity pos₀ pos₁

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

-- ∀{{ q : Unit }} → Number (level ,, X⁺⁻)
-- ∀{{ q : Unit }} → Number (level ,, X⁺ )
-- ∀{{ q : Unit }} → Number (level ,, X⁻ )

open ℕⁿ
open ℤᶻ ℤ.bundle
open ℚᶠ ℚ.bundle
open ℝʳ ℝ.bundle
open ℂᶜ ℂ.bundle


⁻¹-Types' : ∀{l p} → Number (l ,, p) → Type (ℓ-max ℝℓ ℝℓ')
⁻¹-Types' {level    } {X⁺⁻} (number (x , p)) = ∀{{ q : Unit    }} → Number (level     ,, X⁺⁻)
⁻¹-Types' {level    } {X⁺ } (number (x , p)) = ∀{{ q : Unit    }} → Number (level     ,, X⁺ )
⁻¹-Types' {level    } {X⁻ } (number (x , p)) = ∀{{ q : Unit    }} → Number (level     ,, X⁻ )
⁻¹-Types' {isNat    } {X  } (number (x , p)) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isNat     ,, X⁺⁻)
⁻¹-Types' {isInt    } {X  } (number (x , p)) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isInt     ,, X⁺⁻)
⁻¹-Types' {isRat    } {X  } (number (x , p)) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     ,, X⁺⁻)
⁻¹-Types' {isReal   } {X  } (number (x , p)) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    ,, X⁺⁻)
⁻¹-Types' {isComplex} {X  } (number (x , p)) = ∀{{ q : x #ᶜ 0ᶜ }} → Number (isComplex ,, X⁺⁻)
⁻¹-Types' {isNat    } {X₀⁺} (number (x , p)) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isNat     ,, X⁺ )
⁻¹-Types' {isInt    } {X₀⁺} (number (x , p)) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isInt     ,, X⁺ )
⁻¹-Types' {isRat    } {X₀⁺} (number (x , p)) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     ,, X⁺ )
⁻¹-Types' {isReal   } {X₀⁺} (number (x , p)) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    ,, X⁺ )
⁻¹-Types' {isNat    } {X₀⁻} (number (x , p)) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isNat     ,, X⁻ )
⁻¹-Types' {isInt    } {X₀⁻} (number (x , p)) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isInt     ,, X⁻ )
⁻¹-Types' {isRat    } {X₀⁻} (number (x , p)) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     ,, X⁻ )
⁻¹-Types' {isReal   } {X₀⁻} (number (x , p)) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    ,, X⁻ )

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

-- _ = number ( _,_ {B = λ x → Lift {j = ℝℓ'} (Σ ℕⁿ.ℕ₀ (λ z → z +ₙ ℕⁿ.ℕ₀.zero ≡ ℕⁿ.ℕ₀.suc ℕⁿ.ℕ₀.zero))}  (lift {j = ℝℓ} 1) (lift {j = ℝℓ'} ( z≤n {1} )))  

_ = ( _,_ {B = λ x → Lift {j = ℝℓ'} (Σ[ z ∈ ℕ₀ ] z +ₙ 0 ≡ 1)} (lift {j = ℝℓ} 1) (lift {j = ℝℓ'} ( z≤n {1} )))  

_+ʰⁿ_ : ∀{p q} → Number (isNat ,, availablePositivity isNat p) → Number (isNat ,, availablePositivity isNat q) → Number (isNat ,, +-Positivity p q)
_+ʰⁿ_ {X  } {X  } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X  } {X⁺⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X  } {X₀⁺} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X  } {X⁺ } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X  } {X₀⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺⁻} {X  } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺⁻} {X⁺⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺⁻} {X₀⁺} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺⁻} {X⁺ } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺⁻} {X₀⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁺} {X  } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁺} {X⁺⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁺} {X₀⁺} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , {!!}) -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰⁿ_ {X₀⁺} {X⁺ } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , {!!}) -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰⁿ_ {X₀⁺} {X₀⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺ } {X  } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺ } {X⁺⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X⁺ } {X₀⁺} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , {!!}) -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰⁿ_ {X⁺ } {X⁺ } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , {!!}) -- 0 < a → 0 < b → 0 < a + b
_+ʰⁿ_ {X⁺ } {X₀⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁻} {X  } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁻} {X⁺⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁻} {X₀⁺} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁻} {X⁺ } (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , lift tt)
_+ʰⁿ_ {X₀⁻} {X₀⁻} (number (lift a , pa)) (number (lift b , pb)) = number (lift (a +ₙ b) , {!!}) -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶻ_ : ∀{p q} → Number (isInt ,, availablePositivity isInt p) → Number (isInt ,, availablePositivity isInt q) → Number (isInt ,, +-Positivity p q)
_+ʰᶻ_ {p} {q} (number (a , pa)) (number (b , pb)) = {!!}

_+ʰᶠ_ : ∀{p q} → Number (isRat ,, availablePositivity isRat p) → Number (isRat ,, availablePositivity isRat q) → Number (isRat ,, +-Positivity p q)
_+ʰᶠ_ {p} {q} (number (a , pa)) (number (b , pb)) = {!!}

_+ʰʳ_ : ∀{p q} → Number (isReal ,, availablePositivity isReal p) → Number (isReal ,, availablePositivity isReal q) → Number (isReal ,, +-Positivity p q)
_+ʰʳ_ {X  } {X  } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X  } {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X  } {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X  } {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X  } {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X  } {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺⁻} {X  } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺⁻} {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁺} {X  } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁺} {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁺} {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰʳ_ {X₀⁺} {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- 0 < a → 0 < b → 0 < a + b
_+ʰʳ_ {X₀⁺} {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁺} {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺ } {X  } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺ } {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰʳ_ {X⁺ } {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- 0 < a → 0 < b → 0 < a + b
_+ʰʳ_ {X⁺ } {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁺ } {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁻ } {X  } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁻ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁻ } {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁻ } {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X⁻ } {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- a < 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {X⁻ } {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰʳ_ {X₀⁻} {X  } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , lift tt)
_+ʰʳ_ {X₀⁻} {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {X₀⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ʳ b , {!!}) -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶜ_ : ∀{p q} → Number (isComplex ,, availablePositivity isComplex p) → Number (isComplex ,, availablePositivity isComplex q) → Number (isComplex ,, +-Positivity p q)
_+ʰᶜ_ {X  } {X  } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X  } {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X  } {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X  } {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X  } {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X  } {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺⁻} {X  } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt) 
_+ʰᶜ_ {X⁺⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺⁻} {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁺} {X  } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁺} {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁺} {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X₀⁺} {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X₀⁺} {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁺} {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺ } {X  } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺ } {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X⁺ } {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X⁺ } {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁺ } {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁻ } {X  } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁻ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁻ } {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁻ } {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X⁻ } {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X⁻ } {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X₀⁻} {X  } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , lift tt)
_+ʰᶜ_ {X₀⁻} {X⁻ } (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥
_+ʰᶜ_ {X₀⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = number (a +ᶜ b , {!!}) -- ⊥

_+ʰ_ : ∀{l p q} → Number (l ,, availablePositivity l p) → Number (l ,, availablePositivity l q) → Number (l ,, +-Positivity p q)
_+ʰ_ {isNat    } x y = x +ʰⁿ y
_+ʰ_ {isInt    } x y = x +ʰᶻ y
_+ʰ_ {isRat    } x y = x +ʰᶠ y
_+ʰ_ {isReal   } x y = x +ʰʳ y
_+ʰ_ {isComplex} x y = x +ʰᶜ y

_+_ : ∀{Lx Ly Px Py}
    → Number (Lx ,, availablePositivity Lx Px)
    → Number (Ly ,, availablePositivity Ly Py)
    → Number ((maxₙₗ' Lx Ly) ,, +-Positivity Px Py) --  (+-Types p q)
_+_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ' Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂' Lx Ly
  in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y

-- pattern [ℝ₀⁺] = (isReal ,, X₀⁺)
[ℝ₀⁺] = Number (isReal ,, X₀⁺)

{-# DISPLAY Number (isReal ,, X₀⁺) = [ℝ₀⁺] #-}

test101 : Number (isNat ,, isPositive) → Number (isReal ,,  isNonnegative) → {!!}
test101 n r with n + r
... | number (fst₁ , snd₁) =
  let z = [ℝ₀⁺] ∋ r + r
      x = num z
      xp = prp z
  in {! prp z!}
