{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module Number.Blueprint where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
open import Cubical.Data.Nat using (zero; suc) renaming (ℕ to ℕ₀; _+_ to _+ₙ_)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

open import Cubical.Data.Unit.Base -- Unit
open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Data.Maybe.Base


open import Cubical.Data.Fin.Base
-- import Cubical.Data.Fin.Properties
-- open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
open import Cubical.Data.Nat.Properties -- using (+-suc; injSuc; snotz; +-comm; +-assoc; +-zero; inj-m+)
open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_; _≟_ to _≟ₙ_)
-- open import Data.Nat.Base using (ℕ; z≤n; s≤s; zero; suc) renaming (_≤_ to _≤ₙ_; _<_ to _<ₙ_; _+_ to _+ₙ_)
open import Agda.Builtin.Bool renaming (true to TT; false to FF)
open import Function.Base using (it; _$_) -- instance search
import Cubical.Data.Fin.Properties
open import Data.Nat.Properties using (+-mono-<)

minₙ : ℕ₀ → ℕ₀ → ℕ₀
minₙ a b with a ≟ₙ b
... | lt a<b = a 
... | eq a≡b = a 
... | gt b<a = b 

maxₙ : ℕ₀ → ℕ₀ → ℕ₀
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

import MoreLogic
open MoreLogic.Reasoning

<-asymₙ : ∀ a b → a <ₙ b → ¬(b <ₙ a)
<-asymₙ a b (k , p) (l , q) = snotz $ inj-m+ {a} ((sym γ ∙ transport (λ i → l +ₙ suc (p (~ i)) ≡ a) q) ∙ sym (+-zero a))
  where
    γ = (
      l +ₙ suc (k +ₙ suc a)   ≡⟨ ( λ i → l +ₙ suc (+-suc k a i)) ⟩
      l +ₙ suc (suc (k +ₙ a)) ≡⟨ ( λ i → l +ₙ suc (suc (+-comm k a i)) ) ⟩
      l +ₙ suc (suc (a +ₙ k)) ≡⟨ ( λ i → l +ₙ suc (+-suc a k (~ i))) ⟩
      l +ₙ suc (a +ₙ suc k)   ≡⟨ ( λ i → l +ₙ (+-suc a (suc k) (~ i))) ⟩
      l +ₙ (a +ₙ suc (suc k)) ≡⟨ +-assoc l a (suc (suc k)) ⟩
      (l +ₙ a) +ₙ suc (suc k) ≡⟨ (λ i → +-comm l a i +ₙ suc (suc k) ) ⟩
      (a +ₙ l) +ₙ suc (suc k) ≡⟨ sym $ +-assoc a l (suc (suc k)) ⟩
      a +ₙ (l +ₙ suc (suc k)) ≡⟨ (λ i → a +ₙ +-suc l (suc k) i) ⟩
      a +ₙ suc (l +ₙ suc k)   ∎)

<>-implies-≡ₙ : ∀ a b → a ≤ₙ b → b ≤ₙ a → a ≡ b
<>-implies-≡ₙ a b (n , p) (m , q) with m+n≡0→m≡0×n≡0 {m} {n} (m+n≡n→m≡0 γ)
  where γ = sym (+-assoc m n a) ∙ (λ i → m +ₙ p i) ∙ q
... | m≡0 , n≡0 = (λ i → n≡0 (~ i) +ₙ a) ∙ p

-- with a ≟ₙ b
-- ... | lt x = {! <-asymₙ !}
-- ... | eq x = x
-- ... | gt x = {!!}

data NumberLevel : Type where
  isNat     : NumberLevel
  isInt     : NumberLevel
  isRat     : NumberLevel
  isReal    : NumberLevel
  isComplex : NumberLevel  

-- NumberLevelEnumeration
NLE' : NumberLevel → ℕ₀
NLE' isNat     = 0
NLE' isInt     = 1
NLE' isRat     = 2
NLE' isReal    = 3
NLE' isComplex = 4

NLE⁻¹' : ℕ₀ → NumberLevel
NLE⁻¹' 0 = isNat
NLE⁻¹' 1 = isInt
NLE⁻¹' 2 = isRat
NLE⁻¹' 3 = isReal
NLE⁻¹' 4 = isComplex
NLE⁻¹' x = isComplex
-- NLE⁻¹' (suc⁵ fst₁) = isComplex

NLE-id²' : ∀ x → NLE⁻¹' (NLE' x) ≡ x
NLE-id²' isNat     = refl 
NLE-id²' isInt     = refl
NLE-id²' isRat     = refl
NLE-id²' isReal    = refl
NLE-id²' isComplex = refl

NLE : NumberLevel → Fin 5
NLE isNat     = 0 , it
NLE isInt     = 1 , it
NLE isRat     = 2 , it
NLE isReal    = 3 , it
NLE isComplex = 4 , it

_^ᶠ_ : ∀{A : Type ℓ} → (A → A) → ℕ₀ → A → A
_^ᶠ_ f zero x = x
_^ᶠ_ f (suc zero) x = (f x) 
_^ᶠ_ f (suc n) x = (f ^ᶠ n) (f x)

private
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

≟ₙ-sym : ∀ a b → Trichotomy (NLE' a) (NLE' b) → Trichotomy (NLE' b) (NLE' a)
≟ₙ-sym a b (lt x) = gt x
≟ₙ-sym a b (eq x) = eq (sym x)
≟ₙ-sym a b (gt x) = lt x

max-symₙₗ : ∀ a b → maxₙₗ' a b ≡ maxₙₗ' b a
max-symₙₗ a b with NLE' a ≟ₙ NLE' b | NLE' b ≟ₙ NLE' a
... | lt x | lt y = ⊥-elim {A = λ _ → NLE⁻¹' (NLE' b) ≡ NLE⁻¹' (NLE' a)} $  <-asymₙ _ _ x y 
... | lt x | eq y = refl
... | lt x | gt y = refl
... | eq x | lt y = refl
... | eq x | eq y = cong NLE⁻¹' x
... | eq x | gt y = cong NLE⁻¹' x
... | gt x | lt y = refl
... | gt x | eq y = sym (cong NLE⁻¹' y)
... | gt x | gt y = ⊥-elim {A = λ _ → NLE⁻¹' (NLE' a) ≡ NLE⁻¹' (NLE' b)} $  <-asymₙ _ _ x y 

max-implies-≤ₙₗ' : (a : NumberLevel) → (b : NumberLevel) → a ≤ₙₗ' maxₙₗ' a b
max-implies-≤ₙₗ' a b with (NLE' a) ≟ (NLE' b)
... | lt (x , p) =  suc x ,  sym (+-suc _ _)  ∙ p ∙ cong NLE' (sym (NLE-id²' b))
... | eq x = 0 , sym (cong NLE' (NLE-id²' a) ∙ refl {x = NLE' a})
... | gt x = 0 , sym (cong NLE' (NLE-id²' a) ∙ refl {x = NLE' a})

max-implies-≤ₙₗ₂' : (a : NumberLevel) → (b : NumberLevel) → (a ≤ₙₗ' maxₙₗ' a b) × (b ≤ₙₗ' maxₙₗ' a b)
max-implies-≤ₙₗ₂' a b = max-implies-≤ₙₗ' a b , transport (λ i → b ≤ₙₗ' max-symₙₗ b a i) (max-implies-≤ₙₗ' b a)


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

open import Number.Postulates
open import Number.Bundles ℝℓ ℝℓ'

-- NumberLevel interpretation
Il : NumberLevel → Type ℝℓ
Il isNat     = let open ℕ* in ℕ -- NOTE: this occurs in the Have/Goal
Il isInt     = let open ℤ in ℤ --       so somehow the "amount of normalization" at the call site is inherited from the function (clause)
Il isRat     = let open ℚ in ℚ --       the finding is, that to produce "nice" Goals,
Il isReal    = let open ℝ in ℝ --         we need to create the same symbol-import-path in the definition clause
Il isComplex = let open ℂ in ℂ --         that will also be present at the call site

-- PositivityLevel interpretation
Ip : (nl : NumberLevel) → PositivityLevel → (x : Il nl) → Type ℝℓ'
Ip isNat     ⁇x⁇ x =                                        Lift Unit
Ip isNat     x#0 x = let open ℕ                             in ( x # 0f)
Ip isNat     0≤x x = let open ℕ                             in (0f ≤  x)
Ip isNat     0<x x = let open ℕ                             in (ℕ.0f < x) 
Ip isNat     x≤0 x = let open ℕ                             in ( x ≤ 0f) 
Ip isNat     x<0 x =                                        Lift ⊥
Ip isInt     ⁇x⁇ x =                                        Lift Unit
Ip isInt     x#0 x = let open ℤ.Bundle             ℤ.bundle in ( x # 0f)
Ip isInt     0≤x x = let open ℤ.Bundle             ℤ.bundle in (0f ≤  x)
Ip isInt     0<x x = let open ℤ.Bundle             ℤ.bundle in (0f <  x)
Ip isInt     x≤0 x = let open ℤ.Bundle             ℤ.bundle in ( x ≤ 0f)
Ip isInt     x<0 x = let open ℤ.Bundle             ℤ.bundle in ( x < 0f)
Ip isRat     ⁇x⁇ x =                                        Lift Unit        
Ip isRat     x#0 x = let open ℚ.Bundle             ℚ.bundle in ( x # 0f)
Ip isRat     0≤x x = let open ℚ.Bundle             ℚ.bundle in (0f ≤  x)
Ip isRat     0<x x = let open ℚ.Bundle             ℚ.bundle in (0f <  x)
Ip isRat     x≤0 x = let open ℚ.Bundle             ℚ.bundle in ( x ≤ 0f)
Ip isRat     x<0 x = let open ℚ.Bundle             ℚ.bundle in ( x < 0f)
Ip isReal    ⁇x⁇ x =                                        Lift Unit 
Ip isReal    x#0 x = let open ℝ.Bundle             ℝ.bundle in ( x # 0f)
Ip isReal    0≤x x = let open ℝ.Bundle             ℝ.bundle in (0f ≤  x)
Ip isReal    0<x x = let open ℝ.Bundle             ℝ.bundle in (0f <  x)
Ip isReal    x≤0 x = let open ℝ.Bundle             ℝ.bundle in ( x ≤ 0f)
Ip isReal    x<0 x = let open ℝ.Bundle             ℝ.bundle in ( x < 0f)
Ip isComplex ⁇x⁇ x =                                        Lift Unit 
Ip isComplex x#0 x = let open ℂ.Bundle             ℂ.bundle in ( x # 0f)
Ip isComplex 0≤x x =                                        Lift ⊥
Ip isComplex 0<x x =                                        Lift ⊥
Ip isComplex x≤0 x =                                        Lift ⊥
Ip isComplex x<0 x =                                        Lift ⊥

-- NumberProp interpretation
In : NumberProp → Type (ℓ-max ℝℓ ℝℓ')
In (level ,, positivity) = Σ (Il level) (Ip level positivity)

data Number (p : NumberProp) : Type (ℓ-max ℝℓ ℝℓ') where
  number : In p → Number p

num : ∀{(l ,, p) : NumberProp} → Number (l ,, p) → Il l
num (number p) = fst p

prp : ∀{(l ,, p) : NumberProp} → (x : Number (l ,, p)) → Ip l p (num x)
prp (number p) = snd p

pop : ∀{p : NumberProp} → Number p → In p
pop (number (x , p)) = x , p

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
-- multiplying negative numbers gives a positive number
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


