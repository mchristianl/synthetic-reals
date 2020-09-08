{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_; it)
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

private
  ≤⇒≤'' : ∀ x y → [ x ≤ y ] → [ x ≤'' y ]
  ≤⇒≤'' x y = ≤-⇔-≤'' x y .fst

  ≤''⇒≤ : ∀ x y → [ x ≤'' y ] → [ x ≤ y ]
  ≤''⇒≤ x y = ≤-⇔-≤'' x y .snd

  ≤-≡-≤'' : ∀ x y → (Liftᵖ {ℓ'} {ℓ} (x ≤ y)) ≡ (x ≤'' y)
  ≤-≡-≤'' x y = ⇔toPath ((≤⇒≤'' x y) ∘ (unliftᵖ (x ≤ y))) ((liftᵖ (x ≤ y)) ∘ (≤''⇒≤ x y))

is-0≡-0 : 0f ≡ - 0f
is-0≡-0 = sym (+-inv 0f .snd) ∙ (+-identity (- 0f) .fst)

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

·-reflects-<0 : ∀ x y → [ 0f < y ] → [ x · y < 0f ] → [ x < 0f ]
·-reflects-<0 x y 0<y x·y<0 = ·-reflects-< x 0f y 0<y  (subst (λ p → [ x · y < p ]) (sym $ RingTheory'.0-leftNullifies y) x·y<0)

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
R3-9  = ∀[ x ] ∀[ y ] ∀[ z ] (    y ≤ z    ) ⇒ (x ≤ y ) ⇒                  (x ≤ z)
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
-- R3-23 `∀ m m' n n' → 0 < n → 0 < n' → (m / n > m' / n') ⇔ (m · n' > m' · n)`
-- R3-24 `∀(n ∈ ℕ⁺) → (n ⁻¹ > 0)`
-- R3-25 `x > 0 → y ≥ 0 → ∃[ n ∈ ℤ ] n · x > y`
-- R3-26 `(x > 0) ⇒ (x ⁻¹ > 0)`
-- R3-27 `(x · y > 0) ⇒ (x ≠ 0) ⊓ (y ≠ 0)`
-- R3-28 `∀(x > 0) → ∃[ n ∈ ℕ⁺ ] x < n < x + 2`
-- R3-29 `∀ a b → a < b → ∃[ q ∈ ℚ ] a < r < b`

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

r2-1 : ∀ x y →                                    [ ¬((x < y) ⊓ (y < x)) ]; _ : [ R2-1 ]; _ = r2-1
r2-2 : ∀ x y → [    x < y  ]              → ∀ z → [   (z < y) ⊔ (x < z)  ]; _ : [ R2-2 ]; _ = r2-2
r2-3 : ∀ x y → [ ¬( x # y) ]              →                 x ≡ y         ; _ : [ R2-3 ]; _ = r2-3
r2-4 : ∀ x y → [    x < y  ]              → ∀ z → [ (x + z) < (y + z)    ]; _ : [ R2-4 ]; _ = r2-4
r2-5 : ∀ x y → [   0f < x  ] → [ 0f < y ] →       [      0f < x · y      ]; _ : [ R2-5 ]; _ = r2-5

r2-1 x y (x<y , y<x) = <-asym x y x<y y<x
r2-2 x y x<y z = pathTo⇒ (⊔-comm (x < z) (z < y)) (<-cotrans x y x<y z)
r2-3 = #-tight
r2-4 x y x<y z = +-preserves-< x y z x<y
r2-5 x y 0<x 0<y = subst (λ p → [ p < x · y ]) (RingTheory'.0-leftNullifies y) (·-preserves-< 0f x y 0<y 0<x)

r3-1   : ∀ x                             → [       ¬(x < x)         ]; _ : [ R3-1  ]; _ = r3-1
r3-2   : ∀ x                             → [         x ≤ x          ]; _ : [ R3-2  ]; _ = r3-2
r3-3   : ∀ x y z → [ x < y ] → [ y < z ] → [         x < z          ]; _ : [ R3-3  ]; _ = r3-3
r3-4   : ∀ x y                           → [ ¬((x < y) ⊓ (y ≤ x))   ]; _ : [ R3-4  ]; _ = r3-4
r3-5   : ∀ x y z → [ x ≤ y ] → [ y < z ] → [         x < z          ]; _ : [ R3-5  ]; _ = r3-5
r3-6   : ∀ x y z → [ x < y ] → [ y ≤ z ] → [         x < z          ]; _ : [ R3-6  ]; _ = r3-6
r3-7   : ∀ x y                           → [ (¬(x < y) ⇔    (y ≤ x))]; _ : [ R3-7  ]; _ = r3-7
r3-8   : ∀ x y                           → [  ¬(x ≤ y) ⇔ ¬ ¬(y < x) ]; _ : [ R3-8  ]; _ = r3-8
r3-9   : ∀ x y z → [ y ≤ z ] → [ x ≤ y ] → [         x ≤ z          ]; _ : [ R3-9  ]; _ = r3-9
r3-10  : ∀ x y   → [ x ≤ y ] → [ y ≤ x ] →                   x ≡ y   ; _ : [ R3-10 ]; _ = r3-10
r3-11  : ∀ x y                           → ¬ᵗ ([ x < y ] ×  (x ≡ y)) ; _ : [ R3-11 ]; _ = r3-11

r3-12  : ∀ x     → [   0f ≤ x     ]              → [ [ is-set ] x ≡ˢ 0f ⇔ (∀[ ε ] (0f < ε) ⇒ (x < ε)) ]; _ : [ R3-12 ]; _ = r3-12
r3-13  : ∀ x y   → [   0f < x + y ]              → [           (0f < x) ⊔ (0f < y)         ]; _ : [ R3-13 ]; _ = r3-13
r3-14  : ∀ x     → [   0f < x     ]              → [                - x < 0f               ]; _ : [ R3-14 ]; _ = r3-14
r3-14' : ∀ x     → [    x < 0f    ]              → [                 0f < - x              ]
r3-15  : ∀ x y z → [    x < y     ] → [ z < 0f ] → [              y · z < x · z            ]; _ : [ R3-15 ]; _ = r3-15
r3-16  : ∀ x     → [    x # 0f    ]              → [                 0f < x · x            ]; _ : [ R3-16 ]; _ = r3-16
r3-17  :                                           [                 0f < 1f               ]; _ : [ R3-17 ]; _ = r3-17
r3-18  : ∀ x                                     → [                 0f ≤ x · x            ]; _ : [ R3-18 ]; _ = r3-18
r3-19  : ∀ x     → [   0f < x     ] → [ x < 1f ] → [              x · x < x                ]; _ : [ R3-19 ]; _ = r3-19
r3-20  : ∀ x     → [ - 1f < x     ] → [ x < 1f ] → [      ¬((x < x · x) ⊓ (- x < x · x))   ]; _ : [ R3-20 ]; _ = r3-20
r3-21  : ∀ x     → [   0f < x · x ]              → [                  x # 0f               ]; _ : [ R3-21 ]; _ = r3-21
r3-22  : ∀ x     → [   0f < x     ]              → Σ[ p ∈ [ x # 0f ] ] [ 0f ≤ (x ⁻¹) {{p}} ]; _ : [ R3-22 ]; _ = r3-22
r3-22' : ∀ x     → [   0f < x     ]              → Σ[ p ∈ [ x # 0f ] ] [ 0f < (x ⁻¹) {{p}} ]

r3-1 = <-irrefl
r3-2 = ≤-refl
r3-3 = <-trans
r3-4 x y (x<y , y≤x) = y≤x x<y
r3-5 = ≤-<-trans
r3-6 = <-≤-trans
r3-7 x y .fst = λ x → x -- holds definitionally for Booij's _≤_
r3-7 x y .snd = λ x → x
r3-8  x y .fst = λ x → x -- holds definitionally for Booij's _≤_
r3-8  x y .snd = λ x → x -- holds definitionally for Booij's _≤_
r3-9  x y z y≤z x≤y = ≤-trans x y z x≤y y≤z
r3-10 = ≤-antisym
r3-11 x y (x<y , x≡y) = <-irrefl _ (pathTo⇒ (λ i → x≡y i < y) x<y)

fst (r3-12 x 0≤x) x≡0 y 0<y  = transport (λ i → [ x≡0 (~ i) < y ]) 0<y
-- suppose that x < ε for all ε > 0. If x > 0, then x < x, a contradiction; so 0 ≥ x. Thus x ≥ 0 and 0 ≥ x, and therefore x = 0.
-- this is just antisymmetry for different ≤s : ∀ x y → [ x ≤ y ] → [ y ≤'' x ] → x ≡ y
snd (r3-12 x 0≤x) [∀ε>0∶x<ε] = let x≤0 : [ x ≤ 0f ]
                                   x≤0 0<x = <-irrefl x ([∀ε>0∶x<ε] x 0<x)
                               in ≤-antisym x 0f x≤0 0≤x

r3-13 x y 0<x+y = +-<-ext 0f 0f x y (subst (λ p → [ p < x + y ]) (sym (+-identity 0f .snd)) 0<x+y)

-- -x = 0 + (-x) < x + (-x) = 0
r3-14 x =
  [ 0f         < x         ] ⇒⟨ +-preserves-< 0f x (- x) ⟩
  [ 0f + (- x) < x + (- x) ] ⇒⟨ subst (λ p → [ 0f - x < p ]) (+-rinv x) ⟩
  [ 0f + (- x) < 0f        ] ⇒⟨ subst (λ p → [ p < 0f ]) (+-identity (- x) .snd) ⟩
  [       - x  < 0f        ] ◼

-- -x = 0 + (-x) < x + (-x) = 0
r3-14' x =
  [ x         < 0f         ] ⇒⟨ +-preserves-< x 0f (- x) ⟩
  [ x + (- x) < 0f + (- x) ] ⇒⟨ subst (λ p → [ x - x < p ]) (+-identity (- x) .snd) ⟩
  [ x + (- x) < (- x)      ] ⇒⟨ subst (λ p → [ p < - x ]) (+-rinv x) ⟩
  [       0f  < (- x)      ] ◼

-- since -z > 0 we have
-- -xz = x(-z) > y(-z) = -yz
-- so -xz + yz + xz > -yz + yz + xz
r3-15 x y z x<y z<0 = (
  [    x         <    y         ] ⇒⟨ ·-preserves-< x y (- z) (r3-14' z z<0) ⟩
  [    x · (- z) <    y · (- z) ] ⇒⟨ subst (λ p → [ p < y · (- z) ]) (RingTheory'.-commutesWithRight-· x z) ⟩
  [ - (x ·    z) <    y · (- z) ] ⇒⟨ subst (λ p → [ -(x · z) < p ]) (RingTheory'.-commutesWithRight-· y z) ⟩
  [ - (x ·    z) < - (y ·    z) ] ⇒⟨ -swaps-< (y · z) (x · z) .snd ⟩
  [    y ·    z  <    x ·    z  ] ◼) x<y

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

r3-17 = is-0<1

-- suppose x² < 0. Then ¬(x ≠ 0) by 16; so x = 0 and therefore x² = 0, a contradiction. Hence ¬(x² < 0) and therefore x² ≥ 0.
r3-18 x x²<0 = let ¬x#0 = contraposition (x # 0f) (0f < x · x) (r3-16 x) (<-asym (x · x) 0f x²<0)
                   x≡0  = r2-3 _ _ ¬x#0
                   x²≡0 = (λ i → x≡0 i · x≡0 i) ∙ RingTheory'.0-leftNullifies 0f
               in transport (λ i → [ ¬ (x²≡0 (~ i) < 0f) ] ) (<-irrefl 0f) x²<0
r3-19 x  0<x x<1 = subst (λ p → [ x · x < p ]) (·-lid x) (·-preserves-< x 1f x 0<x x<1)

r3-20 x -1<x x<1 (x<x² , -x<x²) =
  -- Suppose that - 1 < x < 1 and that (x² > x ∧ x² > -x).
  let -- If x > 0, then x = x (-1) < x² < x(1) = x which contradicts our second assumption. Hence ¬(x > 0) and therefore x ≤ 0.
      argument1 : [ 0f < x ⇒ x · x < x ]
      argument1 0<x = subst (λ p → [ x · x < p ]) (·-identity x .snd) (·-preserves-< x 1f x 0<x x<1)
      x≤0 : [ x ≤ 0f ]
      x≤0 = contraposition (0f < x) (x · x < x) argument1 (<-asym _ _  x<x²)
      -- A similar argument shows that x ≥ 0.
      argument2 : [ x < 0f ⇒ x · x < - x ]
      argument2 x<0 = let 0<-x = subst (λ p → [ p < - x ]) (sym is-0≡-0) (-swaps-< x 0f .fst x<0)
                      in (
                        [  (- 1f) · (- x)  < x · (- x) ] ⇒⟨ subst (λ p → [ p < x · (- x) ]) (RingTheory'.-commutesWithLeft-· 1f (- x)) ⟩
                        [ -(  1f  · (- x)) < x · (- x) ] ⇒⟨ subst (λ p → [ - p < x · (- x) ]) (·-identity (- x) .snd) ⟩
                        [ -(         - x)  < x · (- x) ] ⇒⟨ subst (λ p → [ - - x < p ]) (RingTheory'.-commutesWithRight-· x x) ⟩
                        [ -(         - x)  < -(x · x)  ] ⇒⟨ -swaps-< (x · x) (- x) .snd ⟩
                        [            x · x < - x       ] ◼) (·-preserves-< (- 1f) x (- x) 0<-x -1<x)
      0≤x  : [ 0f ≤ x ]
      0≤x  = contraposition (x < 0f) (x · x < - x) argument2 (<-asym _ _ -x<x²)
      -- whence x = 0.
      x≡0  = ≤-antisym x 0f x≤0 0≤x
      -- But in that case we have -x = x² = x, again a contradiction.
      x<0  = subst (λ p → [   x < p ]) (RingTheory'.0-leftNullifies 0f) (subst (λ p → [   x < p · p ]) x≡0  x<x²)
      -x<0 = subst (λ p → [ - x < p ]) (RingTheory'.0-leftNullifies 0f) (subst (λ p → [ - x < p · p ]) x≡0 -x<x²)
      0<x  = -swaps-< 0f x .snd (subst (λ p → [ - x < p ]) is-0≡-0 -x<0)
  in <-asym _ _ 0<x x<0

-- Either x > 0 or x² > x.
r3-21 x  0<x² = case <-cotrans 0f (x · x) 0<x² x as (0f < x) ⊔ (x < x · x) ⇒ x # 0f of λ
  { (inl 0<x ) → inr 0<x
  -- In the latter case, either x² > -x or -x > x.
  ; (inr x<x²) → case <-cotrans x (x · x) x<x² (- x) as (x < - x) ⊔ (- x < x · x) ⇒ x # 0f of λ
    -- Suppose -x > x. Then x - x > x + x = 2x, so 0 > x.
    { (inl  x<-x) → let x<0 : [ x < 0f ]
                        x<0 = (
                          [ x     < - x          ] ⇒⟨ +-preserves-< x (- x) x ⟩
                          [ x + x < - x + x      ] ⇒⟨ subst (λ p → [ x + x < p ]) (+-inv x .snd) ⟩
                          [ x + x < 0f           ] ⇒⟨ subst (λ p → [ p + p < 0f ]) (sym $ ·-identity x .fst) ⟩
                          [ x · 1f + x · 1f < 0f ] ⇒⟨ subst (λ p → [ p < 0f ]) (sym $ is-dist x 1f 1f .fst) ⟩
                          [ x · (1f + 1f) < 0f   ] ⇒⟨ ·-reflects-<0 x (1f + 1f) (<-trans 0f 1f (1f + 1f) is-0<1 (subst (λ p → [ p < 1f + 1f ]) (+-identity 1f .snd) (+-preserves-< 0f 1f 1f is-0<1))) ⟩
                          [ x < 0f               ] ◼) x<-x
                    in inl x<0
    -- Thus we may assume that x² > x and x² < -x.
    ; (inr -x<x²) → case <-cotrans 0f 1f is-0<1 x as (0f < x) ⊔ (x < 1f) ⇒ x # 0f of λ
      -- then either x > 0 or 1 > x.
      { (inl 0<x) → inr 0<x
      -- In the latter case, if x > -1, then we cotradict 20; so 0 > -1 ≥ x
      ; (inr x<1) → let x≤-1 : [ x ≤ - 1f ]
                        x≤-1 -1<x = r3-20 x -1<x x<1 (x<x² , -x<x²)
                        -1<0 : [ - 1f < 0f ]
                        -1<0 = subst (λ p → [ - 1f < p ]) (sym is-0≡-0) (-swaps-< 0f 1f .fst is-0<1)
                    -- and therefore 0 > x.
                    in inl $ ≤-<-trans _ _ _ x≤-1 -1<0
      }
    }
  }

r3-22 x  0<x     = let instance _ = inr 0<x in it , <-asym _ _ (⁻¹-preserves-sign _ _ 0<x (·-rinv x it))
r3-22' x 0<x     = let instance _ = inr 0<x in it , ⁻¹-preserves-sign _ _ 0<x (·-rinv x it)
