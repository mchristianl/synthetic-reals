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
open import Number.Structures
open import Number.Bundles
open import Number.Inclusions
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



+-Types : NumberProp → NumberProp → NumberProp
+-Types (level₀ , pos₀) (level₁ , pos₁) =
  let level  = maxₙₗ level₀ level₁
  in level , +-Positivityʰ level (coerce-PositivityLevel level₀ level pos₀) (coerce-PositivityLevel level₁ level pos₁)

·-Types : NumberProp → NumberProp → NumberProp
·-Types (level₀ , pos₀) (level₁ , pos₁) =
  let level  = maxₙₗ level₀ level₁
  in level , ·-Positivityʰ level (coerce-PositivityLevel level₀ level pos₀) (coerce-PositivityLevel level₁ level pos₁)

private
  instance
    z≤n' : ∀ {n}                 → zero  ≤ₙ n
    z≤n' {n} = z≤n
    s≤s' : ∀ {m n} {{m≤n : m ≤ₙ n}} → suc m ≤ₙ suc n
    s≤s' {m} {n} {{m≤n}} = s≤s m≤n

-- TODO: why does `it` not work here?
⁻¹-Levels : (a : NumberLevel) → Σ[ b ∈ NumberLevel ] a ≤ₙₗ b
⁻¹-Levels isNat     = isRat     , z≤n -- it
⁻¹-Levels isInt     = isRat     , s≤s z≤n -- s≤s' {{z≤n'}}
⁻¹-Levels isRat     = isRat     , s≤s (s≤s z≤n) 
⁻¹-Levels isReal    = isReal    , s≤s (s≤s (s≤s z≤n)) -- it 
⁻¹-Levels isComplex = isComplex , s≤s (s≤s (s≤s (s≤s z≤n))) 

⁻¹-Levels' : (a : NumberLevel) → NumberLevel
⁻¹-Levels' x = maxₙₗ x isRat

open PatternsType

{-
private
  pattern X   = anyPositivity
  pattern X⁺⁻ = isNonzero
  pattern X₀⁺ = isNonnegative
  pattern X⁺  = isPositive
  pattern X⁻  = isNegative
  pattern X₀⁻ = isNonpositive
-}

{-
⁻¹-Types : NumberProp → Maybe NumberProp
⁻¹-Types (level ,, X  ) = nothing
⁻¹-Types (level ,, X₀⁺) = nothing
⁻¹-Types (level ,, X₀⁻) = nothing
⁻¹-Types (level ,, p  ) = just (fst (⁻¹-Levels level) ,, p)
-}

-- ∀{{ q : Unit }} → Number (level ,, X⁺⁻)
-- ∀{{ q : Unit }} → Number (level ,, X⁺ )
-- ∀{{ q : Unit }} → Number (level ,, X⁻ )

open ℕⁿ
open ℤᶻ ℤ.bundle
open ℚᶠ ℚ.bundle
open ℝʳ ℝ.bundle
open ℂᶜ ℂ.bundle

open PatternsType

-- ⁻¹-Typesᵒʳ : ∀{P@(l , p) : PositivityLevelOrderedRing} → Number P → Type (NumberLevelLevel l)
-- ⁻¹-Typesᵒʳ {l , p} x = ?

-- ⁻¹-Typesᶠ

⁻¹-Types' : ∀{l p} → Number (l , p) → Type (NumberLevelLevel l)
⁻¹-Types' {l} = {!!}

{-
⁻¹-Types' {level    } {X⁺⁻} (number (x , p)) = ∀{{ q : Unit    }} → Number (level     , X⁺⁻)
⁻¹-Types' {level    } {X⁺ } (number (x , p)) = ∀{{ q : Unit    }} → Number (level     , X⁺ )
⁻¹-Types' {level    } {X⁻ } (number (x , p)) = ∀{{ q : Unit    }} → Number (level     , X⁻ )
⁻¹-Types' {isNat    } {X  } (number (x , p)) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isNat     , X⁺⁻)
⁻¹-Types' {isInt    } {X  } (number (x , p)) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isInt     , X⁺⁻)
⁻¹-Types' {isRat    } {X  } (number (x , p)) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁺⁻)
⁻¹-Types' {isReal   } {X  } (number (x , p)) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁺⁻)
⁻¹-Types' {isComplex} {X  } (number (x , p)) = ∀{{ q : x #ᶜ 0ᶜ }} → Number (isComplex , X⁺⁻)
⁻¹-Types' {isNat    } {X₀⁺} (number (x , p)) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isNat     , X⁺ )
⁻¹-Types' {isInt    } {X₀⁺} (number (x , p)) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isInt     , X⁺ )
⁻¹-Types' {isRat    } {X₀⁺} (number (x , p)) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁺ )
⁻¹-Types' {isReal   } {X₀⁺} (number (x , p)) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁺ )
⁻¹-Types' {isNat    } {X₀⁻} (number (x , p)) = ∀{{ q : x #ⁿ 0ⁿ }} → Number (isNat     , X⁻ )
⁻¹-Types' {isInt    } {X₀⁻} (number (x , p)) = ∀{{ q : x #ᶻ 0ᶻ }} → Number (isInt     , X⁻ )
⁻¹-Types' {isRat    } {X₀⁻} (number (x , p)) = ∀{{ q : x #ᶠ 0ᶠ }} → Number (isRat     , X⁻ )
⁻¹-Types' {isReal   } {X₀⁻} (number (x , p)) = ∀{{ q : x #ʳ 0ʳ }} → Number (isReal    , X⁻ )
-}

-Levels : NumberLevel → NumberLevel
-Levels x = minₙₗ x isInt
-- -Levels isNat = isInt
-- -Levels x     = x

-Types : NumberProp → NumberProp
-Types (l , p) = {!!}

{-
-Types (level , X  ) = -Levels level , X
-Types (level , X⁺⁻) = -Levels level , X⁺⁻
-Types (level , X₀⁺) = -Levels level , X₀⁻
-Types (level , X⁺ ) = -Levels level , X⁻
-Types (level , X⁻ ) = -Levels level , X⁺
-Types (level , X₀⁻) = -Levels level , X₀⁺
-}

-- coerce : (level-from level-to : NumberLevel) → level-to ≤ₙₗ level-from → Il level-from → Il level-to
-- coerce level-from level-to x = {!!}

--coerce : ∀{p} → (level-from level-to : NumberLevel) → level-from ≤ₙₗ' level-to → Number (level-from ,, p) → Number (level-to ,, p)
--coerce {p} level-from level-to l<l (number (x , q)) = {!!}

-- _ = number ( _,_ {B = λ x → Lift {j = ℝℓ'} (Σ ℕⁿ.ℕ₀ (λ z → z +ₙ ℕⁿ.ℕ₀.zero ≡ ℕⁿ.ℕ₀.suc ℕⁿ.ℕ₀.zero))}  (lift {j = ℝℓ} 1) (lift {j = ℝℓ'} ( z≤n {1} )))  

_ = ( _,_ {B = λ x → Lift {j = ℝℓ'} (Σ[ z ∈ ℕ₀ ] z +ₙ 0 ≡ 1)} (lift {j = ℝℓ} 1) (lift {j = ℝℓ'} ( z≤n {1} )))  

coerce : (from : NumberLevel)
       → (to   : NumberLevel)
       → from ≤ₙₗ to
       → ∀{p}
       → Number (from , p)
       → Number (to   , coerce-PositivityLevel from to p)
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

_+ʰⁿ_ : ∀{p q} → (x : Number (isNat , p)) → (y : Number (isNat , q)) → PositivityInterpretation isNat (+-Positivityʰ isNat p q) (num x +ⁿ num y)
_+ʰⁿ_ {X  } {X  } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X  } {X⁺⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X  } {X₀⁺} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X  } {X⁺ } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X  } {X₀⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺⁻} {X  } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁺} {X  } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁺} {X⁺⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁺} {X₀⁺} (number (a , pa)) (number (b , pb)) = ℕ.+-≤-≤-implies-≤ʳ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰⁿ_ {X₀⁺} {X⁺ } (number (a , pa)) (number (b , pb)) = ℕ.+-≤-<-implies-<ʳ a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰⁿ_ {X₀⁺} {X₀⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺ } {X  } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X⁺ } {X₀⁺} (number (a , pa)) (number (b , pb)) = ℕ.+-<-≤-implies-<ʳ a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰⁿ_ {X⁺ } {X⁺ } (number (a , pa)) (number (b , pb)) = ℕ.+-<-<-implies-<ʳ a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰⁿ_ {X⁺ } {X₀⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁻} {X  } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = tt
_+ʰⁿ_ {X₀⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = ℕ.+-≤-≤-implies-≤ˡ a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0

_+ʰᶻ_ : ∀{p q} → (x : Number (isInt , p)) → (y : Number (isInt , q)) → PositivityInterpretation isInt (+-Positivityʰ isInt p q) (num x +ᶻ num y)
_+ʰᶻ_ {p} {q} (number (a , pa)) (number (b , pb)) = {!!}

_+ʰᶠ_ : ∀{p q} → (x : Number (isRat , p)) → (y : Number (isRat , q)) → PositivityInterpretation isRat (+-Positivityʰ isRat p q) (num x +ᶠ num y)
_+ʰᶠ_ {p} {q} (number (a , pa)) (number (b , pb)) = {!!}

_+ʰʳ_ : ∀{p q} → (x : Number (isReal , p)) → (y : Number (isReal , q)) → PositivityInterpretation isReal (+-Positivityʰ isReal p q) (num x +ʳ num y)
_+ʰʳ_ {X  } {X  } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X  } {X⁺⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X  } {X₀⁺} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X  } {X⁺ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X  } {X⁻ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X  } {X₀⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺⁻} {X  } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺⁻} {X⁻ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁺} {X  } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁺} {X⁺⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁺} {X₀⁺} (number (a , pa)) (number (b , pb)) = ℝ.+-≤-≤-implies-≤ʳ a b pa pb -- 0 ≤ a → 0 ≤ b → 0 ≤ a + b
_+ʰʳ_ {X₀⁺} {X⁺ } (number (a , pa)) (number (b , pb)) = ℝ.+-≤-<-implies-<ʳ a b pa pb -- 0 ≤ a → 0 < b → 0 < a + b
_+ʰʳ_ {X₀⁺} {X⁻ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁺} {X₀⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺ } {X  } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺ } {X₀⁺} (number (a , pa)) (number (b , pb)) = ℝ.+-<-≤-implies-<ʳ a b pa pb -- 0 < a → 0 ≤ b → 0 < a + b
_+ʰʳ_ {X⁺ } {X⁺ } (number (a , pa)) (number (b , pb)) = ℝ.+-<-<-implies-<ʳ a b pa pb -- 0 < a → 0 < b → 0 < a + b
_+ʰʳ_ {X⁺ } {X⁻ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁺ } {X₀⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁻ } {X  } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁻ } {X⁺⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁻ } {X₀⁺} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁻ } {X⁺ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X⁻ } {X⁻ } (number (a , pa)) (number (b , pb)) = ℝ.+-<-<-implies-<ˡ a b pa pb -- a < 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {X⁻ } {X₀⁻} (number (a , pa)) (number (b , pb)) = ℝ.+-<-≤-implies-<ˡ a b pa pb -- a < 0 → b ≤ 0 → (a + b) < 0
_+ʰʳ_ {X₀⁻} {X  } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁻} {X⁺⁻} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁻} {X₀⁺} (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁻} {X⁺ } (number (a , pa)) (number (b , pb)) = lift tt
_+ʰʳ_ {X₀⁻} {X⁻ } (number (a , pa)) (number (b , pb)) = ℝ.+-≤-<-implies-<ˡ a b pa pb -- a ≤ 0 → b < 0 → (a + b) < 0
_+ʰʳ_ {X₀⁻} {X₀⁻} (number (a , pa)) (number (b , pb)) = ℝ.+-≤-≤-implies-≤ˡ a b pa pb -- a ≤ 0 → b ≤ 0 → (a + b) ≤ 0    

_+ʰᶜ_ : ∀{p q} → (x : Number (isComplex , p)) → (y : Number (isComplex , q)) → PositivityInterpretation isComplex (+-Positivityʰ isComplex p q) (num x +ᶜ num y)
_+ʰᶜ_ x y = lift tt

_+ʰ_ : ∀{l p q} → Number (l , p) → Number (l , q) → Number (l , +-Positivityʰ l p q)
_+ʰ_ {isNat    } x y = number (num x +ⁿ num y , x +ʰⁿ y)
_+ʰ_ {isInt    } x y = number (num x +ᶻ num y , x +ʰᶻ y)
_+ʰ_ {isRat    } x y = number (num x +ᶠ num y , x +ʰᶠ y)
_+ʰ_ {isReal   } x y = number (num x +ʳ num y , x +ʰʳ y)
_+ʰ_ {isComplex} x y = number (num x +ᶜ num y , x +ʰᶜ y)

{- NOTE: this creates a weird Number.L in the Have/Goal display

module _ {Lx Ly Px Py} (x : Number (Lx , Px)) (y : Number (Ly , Py)) where
  private L = maxₙₗ' Lx Ly
  _+_ : Number (L , +-Positivityʰ L (coerce-PositivityLevel Lx L Px) (coerce-PositivityLevel Ly L Py))
  _+_ =
    let (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂' Lx Ly
    in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y
-}

_+_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py))
    → let L = maxₙₗ Lx Ly
      in Number (L , +-Positivityʰ L (coerce-PositivityLevel Lx L Px) (coerce-PositivityLevel Ly L Py))
_+_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in coerce Lx L Lx≤L x +ʰ coerce Ly L Ly≤L y

_<ʰ_ : ∀{L} → (x y : NumberLevelInterpretation L) → Type (NumberLevelProplevel L)
_<ʰ_ {isNat}     x y = x <ⁿ y
_<ʰ_ {isInt}     x y = x <ᶻ y
_<ʰ_ {isRat}     x y = x <ᶠ y
_<ʰ_ {isReal}    x y = x <ʳ y
-- NOTE: this is some realization of a partial function, because `_<_` is defined on all numbers
--       one might already anticipate that this breaks something in the future ...
_<ʰ_ {isComplex} x y = {{p : ⊥}} → Lift ⊥

_<_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberLevelProplevel (maxₙₗ Lx Ly))
_<_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) <ʰ num (coerce Ly L Ly≤L y)

_≤ʰ_ : ∀{L} → (x y : NumberLevelInterpretation L) → Type (NumberLevelProplevel L)
_≤ʰ_ {isNat}     x y = x ≤ⁿ y
_≤ʰ_ {isInt}     x y = x ≤ᶻ y
_≤ʰ_ {isRat}     x y = x ≤ᶠ y
_≤ʰ_ {isReal}    x y = x ≤ʳ y
-- NOTE: this is some realization of a partial function, because `_<_` is defined on all numbers
--       one might already anticipate that this breaks something in the future ...
_≤ʰ_ {isComplex} x y = {{p : ⊥}} → Lift ⊥

_≤_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberLevelProplevel (maxₙₗ Lx Ly))
_≤_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) ≤ʰ num (coerce Ly L Ly≤L y)

_#ʰ_ : ∀{L} → (x y : NumberLevelInterpretation L) → Type (NumberLevelProplevel L)
_#ʰ_ {isNat}     x y = x #ⁿ y
_#ʰ_ {isInt}     x y = x #ᶻ y
_#ʰ_ {isRat}     x y = x #ᶠ y
_#ʰ_ {isReal}    x y = x #ʳ y
_#ʰ_ {isComplex} x y = x #ᶜ y

_#_ : ∀{Lx Ly Px Py} → (x : Number (Lx , Px)) (y : Number (Ly , Py)) → Type (NumberLevelProplevel (maxₙₗ Lx Ly))
_#_ {Lx} {Ly} {Px} {Py} x y =
  let L = maxₙₗ Lx Ly
      (Lx≤L , Ly≤L) = max-implies-≤ₙₗ₂ Lx Ly
  in num (coerce Lx L Lx≤L x) #ʰ num (coerce Ly L Ly≤L y)


-- pattern [ℝ₀⁺] = (isReal , X₀⁺)
[ℝ₀⁺] = Number (isReal , isNonnegativeᵒʳ)
[ℝ⁺]  = Number (isReal , isPositiveᵒʳ)
[ℕ⁺]  = Number (isNat , isPositiveᵒʳ)
[ℝ]  = Number (isReal , anyPositivityᵒʳ)

-- {-# DISPLAY maxₙₗ' isReal isReal = isReal #-}
{-# DISPLAY Number (isReal , isNonnegative) = [ℝ₀⁺] #-}
{-# DISPLAY Number (isReal , isPositive) = [ℝ⁺] #-}

[1ʳ] : [ℝ⁺]
[1ʳ] = number (1ʳ , ℝ.0<1)

-- NOTE: As-patterns (or @-patterns) go well with resolving things in our approach

-- test101 : Number (isNat , isPositiveᵒʳ) → Number (isReal ,  isNonnegativeᵒʳ) → {!!}
test101 : [ℕ⁺] → [ℝ₀⁺] → [ℝ]
test101 n@(number (nn , np)) r@(number (rn , rp)) with n + r
... | number (fst₁ , snd₁) =
  let z = [ℝ₀⁺] ∋ r + r
      zp = prp z
      x = num z
      xp = prp z
      y =  r + [1ʳ]
      pp : [1ʳ] < (r + [1ʳ])
      pp = {!!}
      pp' : 1ʳ <ʳ num (r + [1ʳ])
      pp' = {!!}
      pp'' : 1ʳ <ʳ (rn +ʳ 1ʳ)
      pp'' = {!!}
      _ : (pp ≡ pp') × (pp ≡ pp'')
      _ = refl , refl
      in {! y   !}

