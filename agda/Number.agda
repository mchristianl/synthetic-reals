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

open import NumberPostulates
open import NumberStructures ℝℓ ℝℓ'
open import NumberBundles    ℝℓ ℝℓ'
open import NumberInclusions ℝℓ ℝℓ'
open import NumberBlueprint  ℝℓ ℝℓ'

ℝ↪ℝ : ℝCarrier → ℝCarrier
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

data Number (p : NumberProp) : Type (ℓ-max ℝℓ ℝℓ') where
  number : In p → Number p

num : ∀{(l ,, p) : NumberProp} → Number (l ,, p) → Il l
num (number p) = fst p
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

module _ where
  module ℕ' = ROrderedCommSemiring ℕOCSR
  module ℤ' = ROrderedCommRing     ℤOCR
  module ℚ' = ROrderedField        ℚOF
  module ℝ' = ROrderedField        ℝOF
  module ℂ' = RField               ℂF

  -- coerce-OCSR : ∀{l p} {ll : NumberLevel} {𝕏OCSR 𝕐OCSR : ROrderedCommSemiring {ℝℓ} {ℝℓ'}}
  --             → (x : Number (l ,, p))
  --             → {f : Il l → Il ll}
  --             → IsROrderedCommSemiringInclusion 𝕏OCSR 𝕐OCSR f
  --             → Ip ll p (f (num x))
  -- coerce-OCSR {l} {ll} {p} {𝕏OCSR} {𝕐OCSR} {f} (number (x , q)) = ?

  module _ where
    open ℤ'
    open IsROrderedCommSemiringInclusion ℕ↪ℤinc
    private f = ℕ↪ℤ
    coerce-ℕ↪ℤ : ∀{p} → (x : Number (isNat ,, p)) → Ip isInt p (ℕ↪ℤ (num x))
    coerce-ℕ↪ℤ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℕ↪ℤ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℤ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℤ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℕ↪ℤ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

  module _ where
    open ℚ'
    open IsROrderedCommSemiringInclusion ℕ↪ℚinc
    private f = ℕ↪ℚ
    coerce-ℕ↪ℚ : ∀{p} → (x : Number (isNat ,, p)) → Ip isRat p (ℕ↪ℚ (num x))
    coerce-ℕ↪ℚ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℕ↪ℚ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q) 
    coerce-ℕ↪ℚ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q) 
    coerce-ℕ↪ℚ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q) 
    coerce-ℕ↪ℚ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

  module _ where
    open ℝ'
    open IsROrderedCommSemiringInclusion ℕ↪ℝinc
    private f = ℕ↪ℝ
    coerce-ℕ↪ℝ : ∀{p} → (x : Number (isNat ,, p)) → Ip isReal p (ℕ↪ℝ (num x))
    coerce-ℕ↪ℝ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℕ↪ℝ {x#0} (number (x , q)) = transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)
    coerce-ℕ↪ℝ {0≤x} (number (x , q)) = transport (λ i → preserves-0 i ≤ f x) (preserves-≤ _ _ q)
    coerce-ℕ↪ℝ {0<x} (number (x , q)) = transport (λ i → preserves-0 i < f x) (preserves-< _ _ q)
    coerce-ℕ↪ℝ {x≤0} (number (x , q)) = transport (λ i → f x ≤ preserves-0 i) (preserves-≤ _ _ q)

  module _ where
    open ℂ'
    -- open IsRFieldInclusion ℕ↪ℝinc
    private f = ℕ↪ℂ
    coerce-ℕ↪ℂ : ∀{p} → (x : Number (isNat ,, p)) → Ip isComplex (availablePositivity isComplex p) (ℕ↪ℂ (num x))
    coerce-ℕ↪ℂ {⁇x⁇} (number (x , q)) = lift tt
    coerce-ℕ↪ℂ {x#0} (number (x , q)) = {!transport (λ i → f x # preserves-0 i) (preserves-# _ _ q)!}
    coerce-ℕ↪ℂ {0≤x} (number (x , q)) = lift tt
    coerce-ℕ↪ℂ {0<x} (number (x , q)) = {!!}
    coerce-ℕ↪ℂ {x≤0} (number (x , q)) = lift tt

  coerce-ℤ↪ℚ : ∀{p} → (x : Number (isInt ,, p)) → Ip isRat p (ℤ↪ℚ (num x))
  coerce-ℤ↪ℚ {⁇x⁇} (number (x , q)) = lift tt
  coerce-ℤ↪ℚ {x#0} (number (x , q)) = {!!}
  coerce-ℤ↪ℚ {0≤x} (number (x , q)) = {!!}
  coerce-ℤ↪ℚ {0<x} (number (x , q)) = {!!}
  coerce-ℤ↪ℚ {x<0} (number (x , q)) = {!!}
  coerce-ℤ↪ℚ {x≤0} (number (x , q)) = {!!}

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

⁻¹-Levels : (a : NumberLevel) → Σ[ b ∈ NumberLevel ] a ≤ₙₗ b
⁻¹-Levels isNat     = isRat     , it
⁻¹-Levels isInt     = isRat     , it
⁻¹-Levels isRat     = isRat     , it
⁻¹-Levels isReal    = isReal    , it
⁻¹-Levels isComplex = isComplex , it

⁻¹-Levels' : (a : NumberLevel) → NumberLevel
⁻¹-Levels' x = maxₙₗ' x isRat

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



