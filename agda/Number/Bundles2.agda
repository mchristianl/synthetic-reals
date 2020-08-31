{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Bundles2 where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
-- open import Cubical.Foundations.Logic
-- open import Cubical.Structures.Ring
-- open import Cubical.Structures.Group
-- open import Cubical.Structures.AbGroup

open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_)

open import Cubical.HITs.PropositionalTruncation --.Properties


open import Utils using (!_; !!_)
import MoreLogic
open MoreLogic.Definitions
open MoreLogic.Properties
import MorePropAlgebra
open MorePropAlgebra.Definitions
open MorePropAlgebra.Consequences
open import Number.Structures2


open MoreLogic.Reasoning

{-
| name | struct              | apart | abs | order | cauchy | sqrt₀⁺  | exp | final name                                                             |
|------|---------------------|-------|-----|-------|--------|---------|-----|------------------------------------------------------------------------|
| ℕ    | Semiring            |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedSemiring                                                |
| ℤ    | Ring                |  (✓)  | (✓) | lin.  |        | (on x²) |     | LinearlyOrderedRing                                                    |
| ℚ    | Field               |  (✓)  | (✓) | lin.  |        | (on x²) | (✓) | LinearlyOrderedField                                                   |
| ℝ    | Field               |  (✓)  | (✓) | part. |   ✓    |    ✓    | (✓) | CompletePartiallyOrderedFieldWithSqrt                                  |
| ℂ    | euclidean 2-Product |  (✓)  | (✓) |       |  (✓)   |         |  ?  | EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt             |
| R    | Ring                |   ✓   |  ✓  |       |        |         |  ?  | ApartnessRingWithAbsIntoCompletePartiallyOrderedFieldWithSqrt          |
| G    | Group               |   ✓   |  ✓  |       |        |         |  ?  | ApartnessGroupWithAbsIntoCompletePartiallyOrderedFieldWithSqrt         |
| K    | Field               |   ✓   |  ✓  |       |   ✓    |         |  ?  | CompleteApartnessFieldWithAbsIntoCompletePartiallyOrderedFieldWithSqrt |
-}


-- NOTE: this smells like "CPO" https://en.wikipedia.org/wiki/Complete_partial_order
record CompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _<_     : hPropRel Carrier Carrier ℓ'
    min     : Carrier → Carrier → Carrier
    max     : Carrier → Carrier → Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    <-irrefl  : [ isIrreflᵖ _<_ ]
    <-trans   : [ isTransᵖ _<_ ]
    <-cotrans : [ isCotransᵖ _<_ ]
    isset   : isSet Carrier

  -- NOTE: these intermediate definitions are restricted and behave like let-definitions
  --       e.g. they show up in goal contexts and they do not allow for `where` blocks

  <-asym : [ isAsymᵖ _<_ ]
  <-asym = irrefl+trans→asym _<_ <-irrefl <-trans

  _-_ : Carrier → Carrier → Carrier
  a - b = a + (- b)

  _#_ : hPropRel Carrier Carrier ℓ'
  x # y = ([ x < y ] ⊎ [ y < x ]) , isProp-P⊎Q (x < y) (y < x) (inl (<-asym x y))

  _≤_ : hPropRel Carrier Carrier ℓ'
  x ≤ y = ¬ᵖ(y < x)

  ≤-refl : [ isReflᵖ _≤_ ]
  ≤-refl = <-irrefl

  ≤-trans : [ isTransᵖ _≤_ ]
  ≤-trans a b c ¬b<a ¬c<b c<a =
    ⊔-elim (c < b) (b < a) (λ _ → ⊥)
    (λ c<b → ¬c<b c<b)
    (λ b<a → ¬b<a b<a)
    (<-cotrans _ _ c<a b)

  -- ≤-cotrans : [ isCotransᵖ _≤_ ]
  -- ≤-cotrans a b a≤b x =
  --   let γ : [ (b < x) ⊓ (x < a) ] → [ b < a ]
  --       γ p = <-trans b x a (fst p) (snd p)
  --       -- γ p = ⊔-elim (b < x) (x < a) (λ _ → a < b)
  --       --       (λ b<x → {! <-cotrans b x b<x a  !})
  --       --       (λ x<a → {! <-cotrans x a x<a b  !}) p
  --   in  {! contraposition ((b < x) ⊓ (x < a)) (b < a) γ a≤b  !} -- need deMorgan₁
  -- Q → P
  -- ¬ P → ¬ Q

  -- <-asym¹ = λ(a b : Carrier) → λ x y → {!  (<-asym a b)   !}

  -- if x > y then x > y ≥ x, wich contradicts 4. Hence ¬(x > y). Similarly, ¬(y > x), so ¬(x ≠ y) and therefore by axiom R2(3), x = y.
  -- NOTE: this makes use of #-tight to proof ≤-antisym
  --       but we are alrady using ≤-antisym to proof #-tight
  --       so I guess that we have to assume one of them?
  --       Bridges lists tightness a property of _<_, so he seems to assume #-tight
  --       Booij assumes `≤-isLattice : IsLattice _≤_ min max` which gives ≤-refl, ≤-antisym and ≤-trans and proofs #-tight from it
  -- ≤-antisym : (∀ x y → [ ¬ᵖ (x # y) ] → x ≡ y) → [ isAntisymˢ isset _≤_ ]
  ≤-antisym : [ isTightˢ'' isset _<_ ] → [ isAntisymˢ isset _≤_ ]
  ≤-antisym #-tight x y y≤x x≤y =
    let ¬[x#y] : [ ¬ᵖ (x # y) ]
        ¬[x#y] p = (deMorgan₂-back (x < y) (y < x) (x≤y , y≤x)) (⊎-implies-⊔ (x < y) (y < x) p)
    in #-tight x y ¬[x#y]

  -- R-antisym : [    R a b ] → [    R b a ] → a ≡ b
  -- R-tight   : [ ¬ᵖ R a b ] → [ ¬ᵖ R b a ] → a ≡ b

  -- a ≤ b = ¬ᵖ (b < a)
  -- a # b = ¬ᵖ ([ a < b ] ⊎ [ b < a ])
  -- ≤-antisym : [ ¬ᵖ (b < a) ] → [ ¬ᵖ (a < b) ] → a ≡ b
  -- ≤-antisym : [ ¬ᵖ (b < a) ] × [ ¬ᵖ (a < b) ] → a ≡ b -- by curry/uncurry
  -- ≤-antisym : ¬ ( [ b < a ]  ⊎     [ a < b ]) → a ≡ b -- by <-irrefl
  -- #-tight   : [ ¬ᵖ (a < b)   ⊔   ¬ᵖ (b < a) ] → a ≡ b
  -- #-tight   : [ ¬ᵖ (a < b) ] × [ ¬ᵖ (b < a) ] → a ≡ b -- by curry/uncurry
  -- #-tight   : ¬ ( [ a < b ]  ⊎     [ b < a ]) → a ≡ b -- by <-irrefl

  -- #-tight : [ isAntisymˢ isset _≤_ ] → ∀ x y → [ ¬ᵖ (x # y) ] → x ≡ y
  #-tight : [ isAntisymˢ isset _≤_ ] → [ isTightˢ'' isset _<_ ]
  #-tight ≤-antisym x y ¬[[x<y]⊎[y<x]] = let (¬[x<y] , ¬[y<x]) = Utils.deMorgan₂' ¬[[x<y]⊎[y<x]]
                                         in ≤-antisym _ _ ¬[y<x] ¬[x<y]
                                         
  #-tight≡≤-antisym : isTightˢ'' isset _<_ ≡ isAntisymˢ isset _≤_
  #-tight≡≤-antisym =
    ⇒∶ (λ #-tight x y y≤x x≤y →
          let ¬[x#y] : [ ¬ᵖ (x # y) ]
              ¬[x#y] p = (deMorgan₂-back (x < y) (y < x) (x≤y , y≤x)) (⊎-implies-⊔ (x < y) (y < x) p)
            in #-tight x y ¬[x#y])
    ⇐∶ (λ ≤-antisym x y ¬[[x<y]⊎[y<x]] →
          let (¬[x<y] , ¬[y<x]) = Utils.deMorgan₂' ¬[[x<y]⊎[y<x]]
          in ≤-antisym _ _ ¬[y<x] ¬[x<y])

  abs : Carrier → Carrier
  abs x = max x (- x)

  -- suppose that x < ε for all ε > 0. If x > 0, then x < x, a contradiction; so 0 ≥ x. Thus x ≥ 0 and 0 ≥ x, and therefore x = 0.
  bridges-R3-12 : ∀ x → [ 0f ≤ x ] → (∀ ε → [ 0f < ε ] → [ x < ε ]) → x ≡ 0f
  bridges-R3-12 x 0≤x f = let γ : [ x ≤ 0f ]
                              γ = {!   !}
                           in {!   !}
  field
    -- `R3.12` in [Bridges 1999]
    -- bridges-R2-2  : ∀ x y → [ y < x ] → ∀ z → [ (z < x) ⊔ (y < z) ]
    sqrt : (x : Carrier) → {{ ! [ 0f ≤ x ] }} → Carrier
    0≤sqrt : ∀ x → {{ p : ! [ 0f ≤ x ] }} → [ 0f ≤ sqrt x {{p}} ]
    0≤x² : ∀ x → [ 0f ≤ (x · x) ]

  ≤-split : ∀ x → [ 0f ≤ x ] → ( x ≡ 0f ) ⊎ [ 0f < x ]
  ≤-split x p = {!   !}

  instance _ = λ {x} → !! 0≤x² x

  field
    -- NOTE: all "interface" instance arguments (i.e. those that appear in the goal) need to be passed in as arguments
    -- sqrt-of-²  : ∀ x → {{ p₁ : ! [ 0f ≤ x ] }} → {{ p₂ : ! [ 0f ≤ x · x ] }} → sqrt (x · x) {{p₂}} ≡ x
    -- sqrt-unique-existence : ∀ x → {{ p : ! [ 0f ≤ x ] }} → Σ[ y ∈ Carrier ] y · y ≡ x
    -- sqrt-uniqueness : ∀ x y z → {{ p : ! [ 0f ≤ x ] }} → y · y ≡ x → z · z ≡ x → y ≡ z



    ·-uniqueness : ∀ x y → {{ p₁ : ! [ 0f ≤ x ] }} → {{ p₂ : ! [ 0f ≤ y ] }} → x · x ≡ y · y → x ≡ y

    sqrt-existence   : ∀ x   → {{ p  : ! [ 0f ≤ x ] }} → sqrt x {{p}} · sqrt x {{p}} ≡ x
    sqrt-preserves-· : ∀ x y → {{ p₁ : ! [ 0f ≤ x ] }} → {{ p₁ : ! [ 0f ≤ y ] }} → {{ p₁ : ! [ 0f ≤ x · y ] }} → sqrt (x · y) ≡ sqrt x · sqrt y
    sqrt0≡0 : {{ p : ! [ 0f ≤ 0f ] }} → sqrt 0f {{p}} ≡ 0f
    sqrt1≡1 : {{ p : ! [ 0f ≤ 1f ] }} → sqrt 1f {{p}} ≡ 1f
    -- √x √x = x ⇒ √xx = x
    -- √x √x √x √x = x x
    -- √(√x √x √x √x) = √(x x)

  -- ²-of-sqrt' : ∀ x → {{ p : ! [ 0f ≤ x ] }} → sqrt x {{p}} · sqrt x {{p}} ≡ x
  -- ²-of-sqrt' x {{p}} = let y = sqrt x; instance q = !! 0≤sqrt x in transport (
  --   sqrt (y · y) ≡ y ≡⟨ {!   !} ⟩
  --   sqrt (y · y) · sqrt (y · y) ≡ y · sqrt (y · y) ≡⟨ {!   !} ⟩
  --   sqrt (y · y) · sqrt (y · y) ≡ y · y ≡⟨ {! λ x → x  !} ⟩
  --   sqrt x · sqrt x ≡ x ∎) (sqrt-of-² y)
--    {!   !} ⇒⟨ {!   !} ⟩
--    {!   !} ◼) {! (sqrt-of-² y ) !}
  -- sqrt (x · x) ≡ x
  -- sqrt (x · x) · sqrt (x · x) ≡ x · sqrt (x · x)
  -- sqrt (x · x) · sqrt (x · x) ≡ x · x
  -- x = sqrt y
  -- sqrt y · sqrt y ≡ y

  sqrt-test : (x y z : Carrier) → [ 0f ≤ x ] → [ 0f ≤ y ] → Carrier
  sqrt-test x y z 0≤x 0≤y = let instance _ = !! 0≤x
                                instance _ = !! 0≤y
                            in (sqrt x) + (sqrt y) + (sqrt (z · z))

  field
    _⁻¹ : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier

  infix  9 _⁻¹
  infixl 7 _·_
  infix  6 -_
  infix  5 _-_
  infixl 5 _+_
  infixl 4 _#_
  infixl 4 _≤_
  infixl 4 _<_

-----------8<--------------------------------------------8<------------------------------------------8<------------------

{- currently, we have that IsAbs works on "rigs" (rings where `-_` is not necessary)
   but in our applications, we do want to take the square root immediately on modules
   therefore, `abs` is defined here as always mapping into `CompletePartiallyOrderedFieldWithSqrt` although more general `abs`es would be possible
-}

module _ -- mathematical structures with `abs` into the real numbers
  {ℝℓ ℝℓ' : Level}
  (ℝbundle : CompletePartiallyOrderedFieldWithSqrt {ℝℓ} {ℝℓ'})
  where
  module ℝ = CompletePartiallyOrderedFieldWithSqrt ℝbundle
  open ℝ using () renaming (Carrier to ℝ; isset to issetʳ; _≤_ to _≤ʳ_; 0f to 0ʳ; 1f to 1ʳ; _+_ to _+ʳ_; _·_ to _·ʳ_; -_ to -ʳ_; _-_ to _-ʳ_)

  -- this makes the complex numbers ℂ
  module EuclideanTwoProductOfCompletePartiallyOrderedFieldWithSqrt where
    Carrier : Type ℝℓ
    Carrier = ℝ × ℝ

    re im : Carrier → ℝ
    re = fst
    im = snd

    0f : Carrier
    0f = 0ʳ , 0ʳ

    1f : Carrier
    1f = 1ʳ , 0ʳ

    _+_ : Carrier → Carrier → Carrier
    (ar , ai) + (br , bi) = (ar +ʳ br) , (ai +ʳ bi)

    _·_ : Carrier → Carrier → Carrier
    (ar , ai) · (br , bi) = (ar ·ʳ br -ʳ ai ·ʳ bi) , (ar ·ʳ bi +ʳ br ·ʳ ai)

    -_ : Carrier → Carrier
    - (ar , ai) = (-ʳ ar , -ʳ ai)

    isset : isSet Carrier
    isset = isSetΣ ℝ.isset (λ _ → ℝ.isset)



  -- this makes the `R` in `RModule`
  record ApartnessRingWithAbsIntoCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
    field
      Carrier : Type ℓ
      0f      : Carrier
      1f      : Carrier
      _+_     : Carrier → Carrier → Carrier
      _·_     : Carrier → Carrier → Carrier
      -_      : Carrier → Carrier
      _#_     : hPropRel Carrier Carrier ℓ'
      abs     : Carrier → ℝ

  -- this makes the `G` in `GModule`
  record ApartnessGroupWithAbsIntoCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
    field
      Carrier : Type ℓ
      1f      : Carrier
      _·_     : Carrier → Carrier → Carrier
      _⁻¹     : Carrier → Carrier
      _#_     : hPropRel Carrier Carrier ℓ'
      abs     : Carrier → ℝ

  -- this makes the `K` in `KModule`
  record CompleteApartnessFieldWithAbsIntoCompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℝℓ ℝℓ'))) where
    field
      Carrier : Type ℓ
      0f      : Carrier
      1f      : Carrier
      _+_     : Carrier → Carrier → Carrier
      _·_     : Carrier → Carrier → Carrier
      -_      : Carrier → Carrier
      _#_     : hPropRel Carrier Carrier ℓ'
      _⁻¹     : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier
      abs     : Carrier → ℝ
      isset   : isSet Carrier
      isAbs   : [ isAbsᵖ isset 0f _+_ _·_ _#_ abs issetʳ 0ʳ _+ʳ_ _·ʳ_ _≤ʳ_ ]

    -- TODO: complete this
