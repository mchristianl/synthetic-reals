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

open import Utils -- deMorgan₂'

open import MorePropAlgebra.Definitions as Defs hiding (_≤''_)

module MorePropAlgebra.Bridges1999 where

-- NOTE: this record is an alternative to a very big module-telescope for this module
--       the idea here is to make as many assumptions to fields as possible even though some assumptions can be derived from each other
--       such deriving happens at the "call site" where these definitions should be inlined
--       also this way we get fixity
record BridgesAssumptions {ℓ ℓ'} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier   : Type ℓ
    0f        : Carrier
    1f        : Carrier
    _<_       : hPropRel Carrier Carrier ℓ'
    min       : Carrier → Carrier → Carrier
    max       : Carrier → Carrier → Carrier
    _+_       : Carrier → Carrier → Carrier
    _·_       : Carrier → Carrier → Carrier
    -_        : Carrier → Carrier
    <-asym    : [ isAsym     _<_ ]
    <-irrefl  : [ isIrrefl   _<_ ]
    <-trans   : [ isTrans    _<_ ]
    <-cotrans : [ isCotrans  _<_ ]
    is-set    : isSet Carrier

  _-_ : Carrier → Carrier → Carrier
  a - b = a + (- b)

  _#_   : hPropRel Carrier Carrier ℓ'
  x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x) -- Booij's and Bridges' definition of _#_

  _≤_   : hPropRel Carrier Carrier ℓ'
  x ≤ y = ¬(y < x)                          -- Booij's  definition of _≤_

  _≤''_ : hPropRel Carrier Carrier (ℓ-max ℓ ℓ')
  x ≤'' y = ∀[ ε ] (y < ε) ⇒ (x < ε)        -- Bridges' definition of _≤_

  -- _>_ = flip _<_
  -- _≥_ = flip _≤_

  field
    _⁻¹       : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier
    ≤-refl    : [ isRefl _≤_ ]
    ≤-antisym : [ isAntisymˢ _≤_ is-set ]

  _/_ : (x y : Carrier) → {{p : [ y # 0f ]}} → Carrier
  (x / y) {{p}} = x · (y ⁻¹) {{p}}

  infix  9 _⁻¹
  infixl 7 _·_
  infixl 7 _/_
  infix  6 -_
  infix  5 _-_
  infixl 5 _+_
  infixl 4 _#_
  infixl 4 _≤_
  infixl 4 _<_
  -- infixl 4 _≥_
  -- infixl 4 _>_

module Results {ℓ ℓ'} (assumptions : BridgesAssumptions {ℓ} {ℓ'}) where
  open BridgesAssumptions assumptions -- atlernative to module telescope

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
  R2-2 = ∀[ x ] ∀[ y ]   ( y < x)            ⇒ (∀[ z ]    (z < x) ⊔ (y < z))
  R2-3 = ∀[ x ] ∀[ y ]  ¬( x # y)            ⇒ [ is-set ]       x ≡ˢ y
  R2-4 = ∀[ x ] ∀[ y ]   ( y < x)            ⇒ (∀[ z ]    (y + z) < (x + z))
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
  -- Either x < z or y < x. The latter is ruled out by 4.
  r3-5 x y z x≤y y<z = ⊔-elim (y < x) (x < z) (λ _ → x < z) (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z) (<-cotrans y z y<z x)

  r3-6 : [ R3-6 ]
  r3-6 x y z x<y y≤z = ⊔-elim (x < z) (z < y) (λ _ → x < z) (λ x<z → x<z) (λ z<y → ⊥-elim (y≤z z<y)) (<-cotrans _ _ x<y z)

  r3-7 : [ R3-7 ]
  r3-7 x y .fst = λ x → x -- holds definitionally for Booij's _≤_
  r3-7 x y .snd = λ x → x

  r3-12 : [ R3-12 ]
  fst (r3-12 x 0≤x) x≡0 y 0<y  = transport (λ i → [ x≡0 (~ i) < y ]) 0<y
  snd (r3-12 x 0≤x) [∀ε>0∶x<ε] = let x≤0 : [ x ≤ 0f ]
                                     x≤0 0<x = <-irrefl x ([∀ε>0∶x<ε] x 0<x)
                                 in ≤-antisym x 0f x≤0 0≤x

  -- suppose that x < ε for all ε > 0. If x > 0, then x < x, a contradiction; so 0 ≥ x. Thus x ≥ 0 and 0 ≥ x, and therefore x = 0.
  bridges-R3-12 : ∀ x → [ 0f ≤ x ] → (∀ ε → [ 0f < ε ] → [ x < ε ]) → x ≡ 0f
  bridges-R3-12 x 0≤x [∀ε>0∶x<ε] =
    let x≤0 : [ x ≤ 0f ]
        x≤0 0<x = <-irrefl x ([∀ε>0∶x<ε] x 0<x)
    in ≤-antisym x 0f x≤0 0≤x

  ≤''⇒≤ : ∀ x y → [ x ≤'' y ] → [ x ≤ y ]
  ≤''⇒≤ x y x≤''y y<x = <-irrefl x (x≤''y x y<x)

  ≤⇒≤'' : ∀ x y → [ x ≤ y ] → [ x ≤'' y ]
  ≤⇒≤'' x y x≤y ε y<ε = r3-5 x y ε x≤y y<ε

  -- NOTE: it seems that `_⇔_` might be the "preferred" / "most performant" / "least cluttered" way to "store" a path when hProps are available
  ≤-⇔-≤'' : ∀ x y → [ (x ≤ y) ⇔ (x ≤'' y) ]
  ≤-⇔-≤'' x y = (≤⇒≤'' x y) , (≤''⇒≤ x y)

  ≤-≡-≤'' : ∀ x y → (Liftᵖ {ℓ'} {ℓ} (x ≤ y)) ≡ (x ≤'' y)
  ≤-≡-≤'' x y = ⇔toPath
              ((≤⇒≤'' x y) ∘ (unliftᵖ (x ≤ y))) -- (λ{ (lift p) → ≤⇒≤'' x y p})
              ((liftᵖ (x ≤ y)) ∘ (≤''⇒≤ x y))

  -- ≤+preserves-<⇒≡ ... this is just antisymmetry for different ≤s : ∀ x y → [ x ≤ y ] → [ y ≤'' x ] → x ≡ y
  bridges-R3-12' : ∀ x y → [ x ≤ y ] → (∀ ε → [ x < ε ] → [ y < ε ]) → x ≡ y
  bridges-R3-12' x y x≤y [∀x<ε→y<ε] =
    let y≤x : [ y ≤ x ]
        y≤x x<y = <-irrefl y ([∀x<ε→y<ε] y x<y)
    in ≤-antisym x y x≤y y≤x
