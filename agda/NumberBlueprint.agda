{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module NumberBlueprint where

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

minₙ : ℕ → ℕ → ℕ
minₙ a b with a ≟ₙ b
... | lt a<b = a 
... | eq a≡b = a 
... | gt b<a = b 

maxₙ : ℕ → ℕ → ℕ
maxₙ a b with a ≟ₙ b
... | lt a<b = b
... | eq a≡b = a
... | gt b<a = a

private
  instance
    z≤n' : ∀ {n}                 → zero  ≤ₙ n
    z≤n' {n} = z≤n
    s≤s' : ∀ {m n} {{m≤n : m ≤ₙ n}} → suc m ≤ₙ suc n
    s≤s' {m} {n} {{m≤n}} = s≤s m≤n

¬1<0 : ¬(1 <ₙ 0)
¬1<0 (k , p) = snotz (sym (+-suc k 1) ∙ p) 

suc-preserves-<ₙ : ∀{x y} → x <ₙ y → suc x <ₙ suc y
suc-preserves-<ₙ {x} {y} p = s≤s p
suc-reflects-<ₙ : ∀{x y} → suc x <ₙ suc y → x <ₙ y
suc-reflects-<ₙ {x} {y} (k , p) = k , (injSuc (sym (+-suc k (suc x)) ∙ p))

¬[k+x<k] : ∀ k x → ¬(k +ₙ x <ₙ k)
¬[k+x<k] k x (z , p) = snotz $ sym $ inj-m+ {k} {0} (+-zero k ∙ sym p ∙ +-suc z (k +ₙ x) ∙ (λ i → suc (+-comm z (k +ₙ x) i)) ∙ (λ i → suc (+-assoc k x z (~ i))) ∙ sym (+-suc k (x +ₙ z)))

data NumberLevel : Type where
  isNat     : NumberLevel
  isInt     : NumberLevel
  isRat     : NumberLevel
  isReal    : NumberLevel
  isComplex : NumberLevel  

-- NumberLevelEnumeration
NLE' : NumberLevel → ℕ
NLE' isNat     = 0
NLE' isInt     = 1
NLE' isRat     = 2
NLE' isReal    = 3
NLE' isComplex = 4

NLE⁻¹' : ℕ → NumberLevel
NLE⁻¹' 0 = isNat
NLE⁻¹' 1 = isInt
NLE⁻¹' 2 = isRat
NLE⁻¹' 3 = isReal
NLE⁻¹' 4 = isComplex
NLE⁻¹' x = isComplex
-- NLE⁻¹' (suc⁵ fst₁) = isComplex

NLE : NumberLevel → Fin 5
NLE isNat     = 0 , it
NLE isInt     = 1 , it
NLE isRat     = 2 , it
NLE isReal    = 3 , it
NLE isComplex = 4 , it

_^ᶠ_ : ∀{A : Type ℓ} → (A → A) → ℕ → A → A
_^ᶠ_ f zero x = x
_^ᶠ_ f (suc zero) x = (f x) 
_^ᶠ_ f (suc n) x = (f ^ᶠ n) (f x)

pattern suc⁵ x = suc (suc (suc (suc (suc x))))

NLE⁻¹ : Fin 5 → NumberLevel
NLE⁻¹ (0 , p) = isNat
NLE⁻¹ (1 , p) = isInt
NLE⁻¹ (2 , p) = isRat
NLE⁻¹ (3 , p) = isReal
NLE⁻¹ (4 , p) = isComplex
NLE⁻¹ (suc⁵ fst₁ , p) = ⊥-elim {A =  λ _ → NumberLevel} $ ¬[k+x<k] 5 fst₁ p

NLE-id¹ : ∀ x → fst (NLE (NLE⁻¹ x)) ≡ fst x
NLE-id¹ (0 , p) = refl
NLE-id¹ (1 , p) = refl
NLE-id¹ (2 , p) = refl
NLE-id¹ (3 , p) = refl
NLE-id¹ (4 , p) = refl
NLE-id¹ (suc⁵ fst₁ , p) = ⊥-elim {A =  λ _ → fst (NLE (NLE⁻¹ (suc⁵ fst₁ , p))) ≡ suc⁵ fst₁} $ ¬[k+x<k] 5 fst₁ p

NLE-id² : ∀ x → NLE⁻¹ (NLE x) ≡ x
NLE-id² isNat     = refl 
NLE-id² isInt     = refl
NLE-id² isRat     = refl
NLE-id² isReal    = refl
NLE-id² isComplex = refl

_≤ₙₗ_ : NumberLevel → NumberLevel → Type
a ≤ₙₗ b = fst (NLE a) ≤ₙ fst (NLE b)

_≤ₙₗ'_ : NumberLevel → NumberLevel → Type
a ≤ₙₗ' b = (NLE' a) ≤ₙ (NLE' b)

minₙₗ' : NumberLevel → NumberLevel → NumberLevel
minₙₗ' a b = NLE⁻¹' (minₙ (NLE' a) (NLE' b))

maxₙₗ' : NumberLevel → NumberLevel → NumberLevel
maxₙₗ' a b = NLE⁻¹' (maxₙ (NLE' a) (NLE' b))

data PositivityLevel : Type where
  anyPositivity : PositivityLevel
  isNonzero     : PositivityLevel
  isNonnegative : PositivityLevel
  isPositive    : PositivityLevel
  isNegative    : PositivityLevel
  isNonpositive : PositivityLevel

private
  pattern ⁇x⁇ = anyPositivity
  pattern x#0 = isNonzero
  pattern 0≤x = isNonnegative
  pattern 0<x = isPositive
  pattern x<0 = isNegative
  pattern x≤0 = isNonpositive

record NumberProp : Type where
  constructor _,,_
  field
    level     : NumberLevel
    positivity : PositivityLevel

-- splitting this into a separate function to be able to make use of NumberLevel without inspecting PositivitLevel

open import NumberPostulates
open import NumberBundles ℝℓ ℝℓ'

-- NumberLevel interpretation
Il : NumberLevel → Type ℝℓ
Il isNat     = ℕCarrier
Il isInt     = ℤCarrier
Il isRat     = ℚCarrier
Il isReal    = ℝCarrier
Il isComplex = ℂCarrier

-- PositivityLevel interpretation
Ip : (nl : NumberLevel) → PositivityLevel → (x : Il nl) → Type ℝℓ'
Ip isNat     ⁇x⁇ x =                                        Lift Unit
Ip isNat     x#0 x = let open ROrderedCommSemiring ℕOCSR in ( x # 0f)
Ip isNat     0≤x x = let open ROrderedCommSemiring ℕOCSR in (0f ≤  x)
Ip isNat     0<x x = let open ROrderedCommSemiring ℕOCSR in (0f <  x)
Ip isNat     x≤0 x = let open ROrderedCommSemiring ℕOCSR in ( x ≤ 0f)
Ip isNat     x<0 x =                                        Lift ⊥
Ip isInt     ⁇x⁇ x =                                        Lift Unit
Ip isInt     x#0 x = let open ROrderedCommRing     ℤOCR  in ( x # 0f)
Ip isInt     0≤x x = let open ROrderedCommRing     ℤOCR  in (0f ≤  x)
Ip isInt     0<x x = let open ROrderedCommRing     ℤOCR  in (0f <  x)
Ip isInt     x≤0 x = let open ROrderedCommRing     ℤOCR  in ( x ≤ 0f)
Ip isInt     x<0 x = let open ROrderedCommRing     ℤOCR  in ( x < 0f)
Ip isRat     ⁇x⁇ x =                                        Lift Unit        
Ip isRat     x#0 x = let open ROrderedField        ℚOF   in ( x # 0f)
Ip isRat     0≤x x = let open ROrderedField        ℚOF   in (0f ≤  x)
Ip isRat     0<x x = let open ROrderedField        ℚOF   in (0f <  x)
Ip isRat     x≤0 x = let open ROrderedField        ℚOF   in ( x ≤ 0f)
Ip isRat     x<0 x = let open ROrderedField        ℚOF   in ( x < 0f)
Ip isReal    ⁇x⁇ x =                                        Lift Unit 
Ip isReal    x#0 x = let open ROrderedField        ℝOF   in ( x # 0f)
Ip isReal    0≤x x = let open ROrderedField        ℝOF   in (0f ≤  x)
Ip isReal    0<x x = let open ROrderedField        ℝOF   in (0f <  x)
Ip isReal    x≤0 x = let open ROrderedField        ℝOF   in ( x ≤ 0f)
Ip isReal    x<0 x = let open ROrderedField        ℝOF   in ( x < 0f)
Ip isComplex ⁇x⁇ x =                                        Lift Unit 
Ip isComplex x#0 x = let open RField               ℂF    in ( x # 0f)
Ip isComplex 0≤x x =                                        Lift ⊥
Ip isComplex 0<x x =                                        Lift ⊥
Ip isComplex x≤0 x =                                        Lift ⊥
Ip isComplex x<0 x =                                        Lift ⊥

-- NumberProp interpretation
In : NumberProp → Type (ℓ-max ℝℓ ℝℓ')
In (level ,, positivity) = Σ (Il level) (Ip level positivity)

-- common level
Cl : (a : NumberLevel) → (b : NumberLevel) → NumberLevel -- Σ[ c ∈ NumberLevel ] a ≤ₙₗ c × b ≤ₙₗ c
Cl a b = maxₙₗ' a b
-- Cl _         isComplex = isComplex
-- Cl isComplex _         = isComplex
-- Cl _         isReal    = isReal
-- Cl isReal    _         = isReal
-- Cl _         isRat     = isRat
-- Cl isRat     _         = isRat
-- Cl _         isInt     = isInt
-- Cl isInt     _         = isInt
-- Cl isNat     isNat     = isNat

private
  pattern X   = anyPositivity
  pattern X⁺⁻ = isNonzero
  pattern X₀⁺ = isNonnegative
  pattern X⁺  = isPositive
  pattern X⁻  = isNegative
  pattern X₀⁻ = isNonpositive

-- workflow:
-- 1. split on the both positivities at once
-- 2. add a general clause on top
-- 3. check file
-- 4. remove all unreachable clauses and goto 2.
-- feel free to remove too many clauses and let agda display the missing ones
+-Positivity : PositivityLevel → PositivityLevel → PositivityLevel
+-Positivity _   X   = X  
+-Positivity X   _   = X  
+-Positivity _   X⁺⁻ = X  
+-Positivity X⁺⁻ _   = X
-- clauses with same sign
+-Positivity X₀⁺ X₀⁺ = X₀⁺ 
+-Positivity X₀⁻ X₀⁻ = X₀⁻ 
+-Positivity X₀⁺ X⁺  = X⁺  
+-Positivity X⁺  X₀⁺ = X⁺  
+-Positivity X⁺  X⁺  = X⁺  
+-Positivity X₀⁻ X⁻  = X⁻ 
+-Positivity X⁻  X⁻  = X⁻
+-Positivity X⁻  X₀⁻ = X⁻
-- remaining clauses with alternating sign
+-Positivity X₀⁻ X₀⁺ = X  
+-Positivity X₀⁺ X₀⁻ = X  
+-Positivity X⁻  X₀⁺ = X  
+-Positivity X₀⁺ X⁻  = X  
+-Positivity X⁻  X⁺  = X  
+-Positivity X⁺  X⁻  = X  
+-Positivity X₀⁻ X⁺  = X  
+-Positivity X⁺  X₀⁻ = X  

·-Positivity : PositivityLevel → PositivityLevel → PositivityLevel
·-Positivity _   X   = X  
·-Positivity X   _   = X  
·-Positivity X₀⁺ X⁺⁻ = X  
·-Positivity X⁺⁻ X₀⁺ = X
·-Positivity X₀⁻ X⁺⁻ = X 
·-Positivity X⁺⁻ X₀⁻ = X
-- multiplying nonzero numbers gives a nonzero number
·-Positivity X⁺⁻ X⁺⁻ = X⁺⁻ 
·-Positivity X⁺  X⁺⁻ = X⁺⁻ 
·-Positivity X⁺⁻ X⁺  = X⁺⁻
·-Positivity X⁻  X⁺⁻ = X⁺⁻
·-Positivity X⁺⁻ X⁻  = X⁺⁻
-- multiplying positive numbers gives a positive number
·-Positivity X₀⁺ X₀⁺ = X₀⁺ 
·-Positivity X₀⁺ X⁺  = X₀⁺ 
·-Positivity X⁺  X₀⁺ = X₀⁺ 
·-Positivity X⁺  X⁺  = X⁺
-- multiplying negative numbers gives a negative number
·-Positivity X₀⁻ X⁻  = X₀⁺
·-Positivity X⁻  X₀⁻ = X₀⁺
·-Positivity X₀⁻ X₀⁻ = X₀⁺  
·-Positivity X⁻  X⁻  = X⁺ 
-- multiplying a positive and a negative number gives a negative number
·-Positivity X⁻  X₀⁺ = X₀⁻
·-Positivity X₀⁺ X⁻  = X₀⁻
·-Positivity X₀⁻ X⁺  = X₀⁻
·-Positivity X⁺  X₀⁻ = X₀⁻
·-Positivity X₀⁻ X₀⁺ = X₀⁻
·-Positivity X₀⁺ X₀⁻ = X₀⁻
·-Positivity X⁻  X⁺  = X⁻ 
·-Positivity X⁺  X⁻  = X⁻

-- this narrows the to-be-preserved properties down to the properties that are available
-- it only affects ℂ where we do not have < and ≤
availablePositivity : NumberLevel → PositivityLevel → PositivityLevel
availablePositivity isNat      p  =  p
availablePositivity isInt      p  =  p
availablePositivity isRat      p  =  p
availablePositivity isReal     p  =  p
availablePositivity isComplex ⁇x⁇ = ⁇x⁇
availablePositivity isComplex x#0 = x#0
availablePositivity isComplex 0≤x = ⁇x⁇
availablePositivity isComplex 0<x = x#0
availablePositivity isComplex x<0 = x#0
availablePositivity isComplex x≤0 = ⁇x⁇


