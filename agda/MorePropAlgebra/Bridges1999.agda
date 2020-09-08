{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_)
open import Cubical.Foundations.Logic renaming
  ( inl to inlᵖ
  ; inr to inrᵖ
  ; _⇒_ to infixr 0 _⇒_                  -- shifting by -6
  ; _⇔_ to infixr -2 _⇔_                 --
  ; ∃[]-syntax to infix  -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix  -4 ∃[∶]-syntax --
  ; ∀[∶]-syntax to infix  -4 ∀[∶]-syntax --
  ; ∀[]-syntax to infix  -4 ∀[]-syntax   --
  )
open import Cubical.Data.Unit.Base using (Unit)

import Data.Sum
import Cubical.Data.Sigma

import Cubical.Structures.CommRing

import Cubical.Core.Primitives
import Agda.Builtin.Cubical.Glue
import Cubical.Foundations.Id

open import MoreLogic.Reasoning
open import MoreLogic.Definitions renaming (_ᵗ⇒_ to infixr 0 _ᵗ⇒_)
open import MoreLogic.Properties

open import Utils

open import MorePropAlgebra.Bundles
open import MorePropAlgebra.Definitions as Defs hiding (_≤''_)
open import MorePropAlgebra.Consequences

module MorePropAlgebra.Bridges1999 {ℓ ℓ'} (assumptions : OrderedField {ℓ} {ℓ'}) where

import MorePropAlgebra.Properties.AlmostOrderedField
-- module AlmostOrderedField'Properties  = MorePropAlgebra.Properties.AlmostOrderedField   record { OrderedField assumptions }
-- module AlmostOrderedField'            =                            AlmostOrderedField   record { OrderedField assumptions }
-- (      AlmostOrderedField')           =                            AlmostOrderedField ∋ record { OrderedField assumptions }

-- module This = OrderedField assumptions renaming (Carrier to F; _-_ to _-_)

-- import MorePropAlgebra.Booij2020
-- -- open MorePropAlgebra.Booij2020.Chapter4 AlmostOrderedField' public
-- open MorePropAlgebra.Booij2020.Chapter4 (record { OrderedField assumptions }) public
-- open +-<-ext+·-preserves-<⇒ (OrderedField.+-<-ext assumptions) (OrderedField.·-preserves-< assumptions) public
-- -- open AlmostOrderedField'Properties -- using (_⁻¹; _≤''_)
-- -- open MorePropAlgebra.Properties.AlmostOrderedField (record { OrderedField assumptions }) public

-- remember opening this as the last one to omit prefixes
-- open import MorePropAlgebra.Properties.OrderedField assumptions
-- open OrderedField assumptions renaming (Carrier to F; _-_ to _-_)

import MorePropAlgebra.Booij2020
open MorePropAlgebra.Booij2020.Chapter4 (record { OrderedField assumptions })
open +-<-ext+·-preserves-<⇒ (OrderedField.+-<-ext assumptions) (OrderedField.·-preserves-< assumptions)
-- open MorePropAlgebra.Properties.AlmostOrderedField (record { OrderedField assumptions }) hiding (_⁻¹)
open import MorePropAlgebra.Properties.OrderedField assumptions
open OrderedField assumptions renaming (Carrier to F; _-_ to _-_) hiding (_#_; _≤_)
open AlmostOrderedField' using (_#_; _≤_)
open AlmostOrderedField'Properties -- using (_⁻¹)

-- NOTE: we are proving Bridges' properties with Booij's definition of _≤_
--         which is some form of cheating
--       because we are interested in the properties, mostly
--         or rather to check our definitions for "completeness" against these properties
--       therefore our proofs differ from Brigdes' proofs
--         and this approach does not show that from R1-* and R2-* follows R3-* as in the paper

-- record hProp! (ℓ : _) : Type (ℓ-suc ℓ) where
--   constructor [!]_
--   field out : hProp ℓ
--
-- [_]! : ∀{ℓ} → hProp! ℓ → Type ℓ
-- [ P ]! = [ hProp!.out P ]

-- [!]_ : ∀{ℓ} → hProp ℓ → hProp ℓ × Unit
-- [!]_ P .fst = P
-- [!]_ P .snd = Cubical.Data.Unit.Base.tt
--
-- [_]! : ∀{ℓ} → hProp ℓ × Unit → Type ℓ
-- [ (P , _) ]! = [ P ]

-- [!]_ : ∀{ℓ} → hProp ℓ → hProp ℓ
-- [!] P = ∀[ x ∶ Unit ] P
--
-- [!!] = Cubical.Data.Unit.Base.tt
--
-- infixr -4 [!]_

-- NOTE: Brigdes writes `x ≠ y`  where we write   `x # y`
--                and `¬(x = y)` where we write `¬(x ≡ y)`

-- Heyting field axioms
R1-1 = ∀[ x ] ∀[ y ]              [ is-set ]            x + y ≡ˢ y + x
R1-2 = ∀[ x ] ∀[ y ] ∀[ z ]       [ is-set ]      (x + y) + z ≡ˢ x + (y + z)
R1-3 = ∀[ x ]                     [ is-set ]           0f + x ≡ˢ x
R1-4 = ∀[ x ]                     [ is-set ]        x + (- x) ≡ˢ 0f
R1-5 = ∀[ x ] ∀[ y ]              [ is-set ]            x · y ≡ˢ y · x
R1-6 = ∀[ x ] ∀[ y ] ∀[ z ]       [ is-set ]      (x · y) · z ≡ˢ x · (y · z)
R1-7 = ∀[ x ]                     [ is-set ]           1f · x ≡ˢ x
R1-8 = ∀[ x ] ∀[ p ∶ [ x # 0f ] ] [ is-set ] x · (x ⁻¹) {{p}} ≡ˢ 1f
R1-9 = ∀[ x ] ∀[ y ] ∀[ z ]       [ is-set ]      x · (y + z) ≡ˢ x · y + x · z

-- _<_ axioms
R2-1 = ∀[ x ] ∀[ y ]                                  ¬((x < y) ⊓ (y < x))
R2-2 = ∀[ x ] ∀[ y ]   ( x < y)            ⇒ (∀[ z ]    (z < y) ⊔ (x < z))
R2-3 = ∀[ x ] ∀[ y ]  ¬( x # y)            ⇒ [ is-set ]       x ≡ˢ y
R2-4 = ∀[ x ] ∀[ y ]   ( x < y)            ⇒ (∀[ z ]    (x + z) < (y + z))
R2-5 = ∀[ x ] ∀[ y ]   (0f < x) ⇒ (0f < y) ⇒                 0f < x · y

-- derivable properties
R3-1  = ∀[ x ]                                                            ¬(x < x)
R3-2  = ∀[ x ]                                                              x ≤ x
R3-3  = ∀[ x ] ∀[ y ] ∀[ z ] (    x < y    ) ⇒ (y < z ) ⇒                   x < z
R3-4  = ∀[ x ] ∀[ y ]                                               ¬((x < y) ⊓ (y ≤ x))
R3-5  = ∀[ x ] ∀[ y ] ∀[ z ] (    x ≤ y    ) ⇒ (y < z ) ⇒                   x < z
R3-6  = ∀[ x ] ∀[ y ] ∀[ z ] (    x < y    ) ⇒ (y ≤ z ) ⇒                   x < z
R3-7  = ∀[ x ] ∀[ y ]                                               (¬(x < y) ⇔    (y ≤ x))
R3-8  = ∀[ x ] ∀[ y ]                                               (¬(x ≤ y) ⇔ ¬ ¬(y < x))
R3-9  = ∀[ x ] ∀[ y ] ∀[ z ] (    y ≤ z    )            ⇒           ( (x ≤ y) ⇔    (x ≤ z))
R3-10 = ∀[ x ] ∀[ y ]        (    x ≤ y    ) ⇒ (y ≤ x ) ⇒                        [ is-set ] x ≡ˢ y
R3-11 = ∀[ x ] ∀[ y ]                                               ¬((x < y) ⊓ ([ is-set ] x ≡ˢ y))
R3-12 = ∀[ x ]               (   0f ≤ x    )            ⇒ ([ is-set ] x ≡ˢ 0f ⇔ (∀[ ε ] (0f < ε) ⇒ (x < ε)))
R3-13 = ∀[ x ] ∀[ y ]        (   0f < x + y)            ⇒            (0f < x) ⊔ (0f < y)
R3-14 = ∀[ x ]               (   0f < x    )            ⇒                 - x < 0f
R3-15 = ∀[ x ] ∀[ y ] ∀[ z ] (    x < y    ) ⇒ (z < 0f) ⇒               y · z < x · z
R3-16 = ∀[ x ]               (    x # 0f   )            ⇒                  0f < x · x
R3-17 =                                                                    0f < 1f
R3-18 = ∀[ x ]                                                             0f ≤ x · x
R3-19 = ∀[ x ]               (   0f < x    ) ⇒ (x < 1f) ⇒               x · x < x
R3-20 = ∀[ x ]               ( - 1f < x    ) ⇒ (x < 1f) ⇒       ¬((x < x · x) ⊓ (- x < x · x))
R3-21 = ∀[ x ]               (   0f < x · x)            ⇒                   x # 0f
R3-22 = ∀[ x ]               (   0f < x    )            ⇒ Σᵖ[ p ∶ x # 0f ] (0f ≤ (x ⁻¹) {{p}})

r1-1 : ∀ x y                      →            x + y ≡ y + x        ; _ : [ R1-1 ]; _ = r1-1
r1-2 : ∀ x y z                    →      (x + y) + z ≡ x + (y + z)  ; _ : [ R1-2 ]; _ = r1-2
r1-3 : ∀ x                        →           0f + x ≡ x            ; _ : [ R1-3 ]; _ = r1-3
r1-4 : ∀ x                        →        x + (- x) ≡ 0f           ; _ : [ R1-4 ]; _ = r1-4
r1-5 : ∀ x y                      →            x · y ≡ y · x        ; _ : [ R1-5 ]; _ = r1-5
r1-6 : ∀ x y z                    →      (x · y) · z ≡ x · (y · z)  ; _ : [ R1-6 ]; _ = r1-6
r1-7 : ∀ x                        →           1f · x ≡ x            ; _ : [ R1-7 ]; _ = r1-7
r1-8 : ∀ x     → (p : [ x # 0f ]) → x · (x ⁻¹) {{p}} ≡ 1f           ; _ : [ R1-8 ]; _ = r1-8
r1-9 : ∀ x y z                    →      x · (y + z) ≡ x · y + x · z; _ : [ R1-9 ]; _ = r1-9

r1-1       =       +-comm
r1-2 x y z = sym $ +-assoc    x y z
r1-3 x     =       +-identity x .snd
r1-4 x     =       +-inv      x .fst
r1-5       =       ·-comm
r1-6 x y z = sym $ ·-assoc    x y z
r1-7 x     =       ·-identity x .snd
r1-8       =       ·-rinv
r1-9 x y z =       is-dist    x y z .fst

r2-3 : ∀ x y → [ ¬( x # y) ] → x ≡ y; _ : [ R2-3 ]; _ = r2-3
r2-3 = #-tight

-- R3-23 `∀ m m' n n' → 0 < n → 0 < n' → (m / n > m' / n') ⇔ (m · n' > m' · n)`
-- R3-24 `∀(n ∈ ℕ⁺) → (n ⁻¹ > 0)`
-- R3-25 `x > 0 → y ≥ 0 → ∃[ n ∈ ℤ ] n · x > y`
-- R3-26 `(x > 0) ⇒ (x ⁻¹ > 0)`
-- R3-27 `(x · y > 0) ⇒ (x ≠ 0) ⊓ (y ≠ 0)`
-- R3-28 `∀(x > 0) → ∃[ n ∈ ℕ⁺ ] x < n < x + 2`
-- R3-29 `∀ a b → a < b → ∃[ q ∈ ℚ ] a < r < b`

r3-1 : [ R3-1 ]
r3-1 = <-irrefl

r3-2 : [ R3-2 ]
r3-2 = ≤-refl

r3-3 : [ R3-3 ]
r3-3 = <-trans

r3-4 : [ R3-4 ]
r3-4 x y (x<y , y≤x) = y≤x x<y

r3-5 : [ R3-5 ]
r3-5 = ≤-<-trans

private
  ≤⇒≤'' : ∀ x y → [ x ≤ y ] → [ x ≤'' y ]
  ≤⇒≤'' x y = ≤-⇔-≤'' x y .fst

  ≤''⇒≤ : ∀ x y → [ x ≤'' y ] → [ x ≤ y ]
  ≤''⇒≤ x y = ≤-⇔-≤'' x y .snd

  ≤-≡-≤'' : ∀ x y → (Liftᵖ {ℓ'} {ℓ} (x ≤ y)) ≡ (x ≤'' y)
  ≤-≡-≤'' x y = ⇔toPath ((≤⇒≤'' x y) ∘ (unliftᵖ (x ≤ y))) ((liftᵖ (x ≤ y)) ∘ (≤''⇒≤ x y))

r3-6 : [ R3-6 ]
r3-6 = <-≤-trans

r3-7 : [ R3-7 ]
r3-7 x y .fst = λ x → x -- holds definitionally for Booij's _≤_
r3-7 x y .snd = λ x → x

r3-12 : [ R3-12 ]
fst (r3-12 x 0≤x) x≡0 y 0<y  = transport (λ i → [ x≡0 (~ i) < y ]) 0<y
-- suppose that x < ε for all ε > 0. If x > 0, then x < x, a contradiction; so 0 ≥ x. Thus x ≥ 0 and 0 ≥ x, and therefore x = 0.
-- this is just antisymmetry for different ≤s : ∀ x y → [ x ≤ y ] → [ y ≤'' x ] → x ≡ y
snd (r3-12 x 0≤x) [∀ε>0∶x<ε] = let x≤0 : [ x ≤ 0f ]
                                   x≤0 0<x = <-irrefl x ([∀ε>0∶x<ε] x 0<x)
                               in ≤-antisym x 0f x≤0 0≤x

r3-14 : ∀ x → [ 0f < x ⇒ - x < 0f ]; _ : [ R3-14 ]; _ = r3-14
-- -x = 0 + (-x) < x + (-x) = 0
r3-14 x =
  [ 0f         < x         ] ⇒⟨ +-preserves-< 0f x (- x) ⟩
  [ 0f + (- x) < x + (- x) ] ⇒⟨ subst (λ p → [ 0f - x < p ]) (+-rinv x) ⟩
  [ 0f + (- x) < 0f        ] ⇒⟨ subst (λ p → [ p < 0f ]) (+-identity (- x) .snd) ⟩
  [       - x  < 0f        ] ◼


r3-14' : ∀ x → [ x < 0f ⇒ 0f < - x ]
-- -x = 0 + (-x) < x + (-x) = 0
r3-14' x =
  [ x         < 0f         ] ⇒⟨ +-preserves-< x 0f (- x) ⟩
  [ x + (- x) < 0f + (- x) ] ⇒⟨ subst (λ p → [ x - x < p ]) (+-identity (- x) .snd) ⟩
  [ x + (- x) < (- x)      ] ⇒⟨ subst (λ p → [ p < - x ]) (+-rinv x) ⟩
  [       0f  < (- x)      ] ◼

-swaps-<ˡ : ∀ x y → [ (- x) < (- y) ⇒ y < x ]
-swaps-<ˡ x y =
  [ - x     < - y             ] ⇒⟨ +-preserves-< _ _ _ ⟩
  [ - x + x < - y + x         ] ⇒⟨ subst (λ p → [ p < - y + x ]) (+-linv x) ⟩
  [  0f     < - y + x         ] ⇒⟨ subst (λ p → [ 0f < p ]) (+-comm (- y) x) ⟩
  [  0f     <   x - y         ] ⇒⟨ +-preserves-< _ _ _ ⟩
  [  0f + y <  (x - y) + y    ] ⇒⟨ subst (λ p → [ p < (x - y) + y ]) (+-identity y .snd) ⟩
  [       y <  (x - y) + y    ] ⇒⟨ subst (λ p → [ y < p ]) (sym $ +-assoc x (- y) y) ⟩
  [       y <   x + (- y + y) ] ⇒⟨ subst (λ p → [ y < x + p ]) (+-linv y) ⟩
  [       y <   x + 0f        ] ⇒⟨ subst (λ p → [ y < p ]) (+-identity x .fst) ⟩
  [       y <   x             ] ◼

-- invInvo
-swaps-<ʳ : ∀ x y → [ x < y ⇒ (- y) < (- x) ]
-swaps-<ʳ x y =
  [     x <     y ] ⇒⟨ subst (λ p → [ p < y ]) (sym $ GroupLemmas'.invInvo x) ⟩
  [ - - x <     y ] ⇒⟨ subst (λ p → [ - - x < p ]) (sym $ GroupLemmas'.invInvo y) ⟩
  [ - - x < - - y ] ⇒⟨ -swaps-<ˡ (- x) (- y) ⟩
  [   - y <   - x ] ◼

-swaps-< : ∀ x y → [ x < y ⇔ (- y) < (- x) ]
-swaps-< x y .fst = -swaps-<ʳ x y
-swaps-< x y .snd = -swaps-<ˡ y x

r3-15 : ∀ x y z → [ (    x < y    ) ⇒ (z < 0f) ⇒               y · z < x · z ]; _ : [ R3-15 ]; _ = r3-15
-- since -z > 0 we have
-- -xz = x(-z) > y(-z) = -yz
-- so -xz + yz + xz > -yz + yz + xz
r3-15 x y z x<y z<0 = (
  [    x         <    y         ] ⇒⟨ ·-preserves-< x y (- z) (r3-14' z z<0) ⟩
  [    x · (- z) <    y · (- z) ] ⇒⟨ subst (λ p → [ p < y · (- z) ]) (RingTheory'.-commutesWithRight-· x z) ⟩
  [ - (x ·    z) <    y · (- z) ] ⇒⟨ subst (λ p → [ -(x · z) < p ]) (RingTheory'.-commutesWithRight-· y z) ⟩
  [ - (x ·    z) < - (y ·    z) ] ⇒⟨ -swaps-< (y · z) (x · z) .snd ⟩
  [    y ·    z  <    x ·    z  ] ◼) x<y

r3-16 : ∀ x → [               (    x # 0f   )            ⇒                  0f < x · x ]; _ : [ R3-16 ]; _ = r3-16
r3-16 x (inl x<0) = (
  [         x  < 0f            ] ⇒⟨ r3-14' x ⟩
  [ 0f         <  - x          ] ⇒⟨ ·-preserves-< 0f (- x) (- x) (r3-14' x x<0) ⟩
  [ 0f · (- x) < (- x) · (- x) ] ⇒⟨ subst (λ p → [ p < (- x) · (- x) ]) (RingTheory'.0-leftNullifies (- x)) ⟩
  [ 0f         < (- x) · (- x) ] ⇒⟨ subst (λ p → [ 0f < p ]) (RingTheory'.-commutesWithRight-· (- x) x) ⟩
  [ 0f         < - ((- x) · x) ] ⇒⟨ subst (λ p → [ 0f < - p ]) (RingTheory'.-commutesWithLeft-· x x) ⟩
  [ 0f         < - - (x · x)   ] ⇒⟨ subst (λ p → [ 0f < p ]) (GroupLemmas'.invInvo (x · x)) ⟩
  [ 0f         < x · x         ] ◼) x<0
r3-16 x (inr 0<x) = (
  [ 0f     < x     ] ⇒⟨ ·-preserves-< 0f x x 0<x ⟩
  [ 0f · x < x · x ] ⇒⟨ subst (λ p → [ p < x · x ]) (RingTheory'.0-leftNullifies x) ⟩
  [ 0f     < x · x ] ◼) 0<x

r3-18 : ∀ x → [ 0f ≤ x · x ]; _ : [ R3-18 ]; _ = r3-18
-- suppose x² < 0. Then ¬(x ≠ 0) by 16; so x = 0 and therefore x² = 0, a contradiction. Hence ¬(x² < 0) and therefore x² ≥ 0.
r3-18 x x²<0 = let ¬x#0 = contraposition (x # 0f) (0f < x · x) (r3-16 x) (<-asym (x · x) 0f x²<0)
                   x≡0  = r2-3 _ _ ¬x#0
                   x²≡0 = (λ i → x≡0 i · x≡0 i) ∙ RingTheory'.0-leftNullifies 0f
               in transport (λ i → [ ¬ (x²≡0 (~ i) < 0f) ] ) (<-irrefl 0f) x²<0
