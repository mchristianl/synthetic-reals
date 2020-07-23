{-# OPTIONS --cubical --no-import-sorts #-}

module Booij where

{- NOTE: for some properties where it is applicable
         we should supply both variants: the tuple variant and the l/r-variant
         and we might choose that the tuple variant is the field and the l/r-variant is the projection
         TODO: check whether this is the way its done in the standard library

an example

   ·-inv      : (x : F) → (p : x # 0f) → (x · (_⁻¹ᶠ x {{p}}) ≡ 1f) × ((_⁻¹ᶠ x {{p}}) · x ≡ 1f)
   ·-rinv     : (x : F) → (p : x # 0f) →  x · (_⁻¹ᶠ x {{p}}) ≡ 1f
   ·-linv     : (x : F) → (p : x # 0f) →                              (_⁻¹ᶠ x {{p}}) · x ≡ 1f

and then we have also

   ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Structures.CommRing
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- open import Cubical.Structures.Poset
open import Cubical.Foundations.Function

open import Function.Base using (_∋_)
open import Function.Base using (it) -- instance search

-- open import Function.Reasoning using (∋-syntax)

-- TODO: merge the notes with Hit.agda
-- NOTE: there seems to be a convention that
--   "We will adopt the convention of denoting the level of the carrier set by ℓ₀ and the level of the relation result by ℓ₁."

-- https://www.cs.bham.ac.uk/~abb538/thesis.pdf
-- Booij 2020 - Analysis in Univalent Type Theory

-- 4.1  Algebraic structure of numbers
--
-- Fields have the property that nonzero numbers have a multiplicative inverse, or more precisely, that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.
--
-- Remark 4.1.1.
-- If we require the collection of numbers to form a set in the sense of Definition 2.5.4, and satisfy the ring axioms, then multiplicative inverses are unique, so that the above is equivalent to the proposition
--   (Π x : F) x ≠ 0 ⇒ (Σ y : F) x · y = 1.
--
-- Definition 4.1.2.
-- A classical field is a set F with points 0, 1 : F, operations +, · : F → F → F, which is a commutative ring with unit, such that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

private
  variable
    ℓ ℓ' ℓ'' : Level

module _ where
  open import Cubical.Structures.Group
  import Cubical.Structures.Group.Properties
  module GroupLemmas' (G : Group {ℓ}) where
    open Group G public
    simplR = GroupLemmas.simplR G
    invUniqueL : {g h : Carrier} → g + h ≡ 0g → g ≡ - h
    invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h)) 



module ClassicalFieldModule where -- NOTE: one might want to put this into another file to omit the name-clashing
  record IsClassicalField {F : Type ℓ}
                          (0f : F) (1f : F) (_+_ : F → F → F) (_·_ : F → F → F) (-_ : F → F) (_⁻¹ᶠ : (x : F) → {{¬(x ≡ 0f)}} → F) : Type ℓ where
    constructor isclassicalfield

    field
      isCommRing : IsCommRing 0f 1f _+_ _·_ -_
      ·-rinv : (x : F) → (p : ¬(x ≡ 0f)) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
      ·-linv : (x : F) → (p : ¬(x ≡ 0f)) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f

    open IsCommRing {0r = 0f} {1r = 1f} isCommRing public

  record ClassicalField : Type (ℓ-suc ℓ) where
    field
      Carrier : Type ℓ
      0f   : Carrier
      1f   : Carrier
      _+_  : Carrier → Carrier → Carrier
      _·_  : Carrier → Carrier → Carrier
      -_   : Carrier → Carrier
      _⁻¹ᶠ : (x : Carrier) → {{¬(x ≡ 0f)}} → Carrier
      isClassicalField : IsClassicalField 0f 1f _+_ _·_ -_ _⁻¹ᶠ

    infix  9 _⁻¹ᶠ
    infix  8 -_
    infixl 7 _·_
    infixl 6 _+_

    open IsClassicalField isClassicalField public

-- Remark 4.1.3.
-- As in the classical case, by proving that additive and multiplicative inverses are unique, we also obtain the negation and division operations.
--
-- For the reals, the assumption x ≠ 0 does not give us any information allowing us to bound x away from 0, which we would like in order to compute multiplicative inverses.
-- Hence, we give a variation on the denition of fields in which the underlying set comes equipped with an apartness relation #, which satises x # y ⇒ x ≠ y, although the converse implication may not hold.
-- This apartness relation allows us to make appropriate error bounds and compute multiplicative inverses based on the assumption x # 0.
--
-- Definition 4.1.4.
-- - An apartness relation, denoted by #, is an irreflexive symmetric cotransitive relation.
-- - A strict partial order, denoted by <, is an irreflexive transitive cotransitive relation.

-- NOTE: there is also PropRel in Cubical.Relation.Binary.Base which uses
-- NOTE: one needs these "all-lowercase constructors" to make use copatterns
-- NOTE: see also Relation.Binary.Indexed.Homogeneous.Definitions.html
-- NOTE: see also Algebra.Definitions.html

IsIrrefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsIrrefl {A = A} R = (a : A) → ¬(R a a)

IsCotrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsCotrans {A = A} R = (a b : A) → R a b → (∀(x : A) → (R a x) ⊎ (R x b))

-- IsApartnessRel : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
-- IsApartnessRel R = IsIrrefl R × BinaryRelation.isSym R × IsCotrans R

record IsApartnessRel {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isIrrefl  : IsIrrefl R
    isSym     : BinaryRelation.isSym R
    isCotrans : IsCotrans R

-- IsStrictPartialOrder : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
-- IsStrictPartialOrder R = IsIrrefl R × BinaryRelation.isTrans R × IsCotrans R

record IsStrictPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isstrictpartialorder
  field
    isIrrefl  : IsIrrefl R
    isTrans   : BinaryRelation.isTrans R
    isCotrans : IsCotrans R

-- NOTE: because it fits here we just also do

record IsPreorder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ispreorder
  field
    isRefl    : BinaryRelation.isRefl R
    isTrans   : BinaryRelation.isTrans R

-- NOTE: there is already
--         isAntisym : {A : Type ℓ₀} → isSet A → Order ℓ₁ A → hProp (ℓ-max ℓ₀ ℓ₁)
--       in Cubical.Structures.Poset. Can we use this?

IsAntisym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsAntisym {A = A} R = ∀ a b → R a b → R b a → a ≡ b

record IsPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor ispartialorder
  field
    isRefl    : BinaryRelation.isRefl R
    isAntisym : IsAntisym R
    isTrans   : BinaryRelation.isTrans R

-- NOTE: not necessary anymore
{-
IsConnexive : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnexive {A = A} R = ∀ a b → (R a b) ⊎ (R b a)

record IsTotalOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor istotalorder
  field
    isAntisym   : IsAntisym R
    isTrans     : BinaryRelation.isTrans R
    isConnexive : IsConnexive R

IsAsym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsAsym {A = A} R = ∀ a b → R a b → ¬ R b a

IsTrichotomous : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTrichotomous {A = A} R = ∀ a b → ((R a b) ⊎ (R b a)) ⊎ (a ≡ b)

record IsStrictTotalOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isstricttotalorder
  field
    isTrans        : BinaryRelation.isTrans R
    isTrichotomous : IsTrichotomous R
    isIrrefl       : IsIrrefl R
    isAsym         : IsAsym R
-}

-- Definition 4.1.5.
-- A constructive field is a set F with points 0, 1 : F, binary operations +, · : F → F → F, and a binary relation # such that
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. x : F has a multiplicative inverse iff x # 0;
-- 3. + is #-extensional, that is, for all w, x, y, z : F
--    w + x # y + z ⇒ w # y ∨ x # z.

record IsConstructiveField {F : Type ℓ}
                           (0f : F) (1f : F) (_+_ : F → F → F) (_·_ : F → F → F) (-_ : F → F) (_#_ : Rel F F ℓ') (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) : Type (ℓ-max ℓ ℓ') where
  constructor isconstructivefield

  field
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    ·-rinv     : ∀ x → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : ∀ x → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    ·-inv-back : ∀ x y → (x · y ≡ 1f) → x # 0f × y # 0f
    #-tight    : ∀ x y → ¬(x # y) → x ≡ y
    -- NOTE: the following ⊎ caused trouble two times with resolving ℓ or ℓ'
    +-#-extensional : ∀ w x y z → (w + x) # (y + z) → (w # y) ⊎ (x # z)
    isApartnessRel  : IsApartnessRel _#_

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsApartnessRel isApartnessRel public
    renaming
      ( isIrrefl  to #-irrefl
      ; isSym     to #-sym
      ; isCotrans to #-cotrans )

record ConstructiveField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor constructivefield
  field
    Carrier : Type ℓ
    0f   : Carrier
    1f   : Carrier
    _+_  : Carrier → Carrier → Carrier
    _·_  : Carrier → Carrier → Carrier
    -_   : Carrier → Carrier
    _#_  : Rel Carrier Carrier ℓ'
    _⁻¹ᶠ : (x : Carrier) → {{x # 0f}} → Carrier
    isConstructiveField : IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ

  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_

  open IsConstructiveField isConstructiveField public


-- NOTE: some syntax for "implicational" reasoning
infix  3 _◼ -- for a list of unicode symbols in agda, see https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html
infixr 2 _⇒⟨_⟩_

_⇒⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : Type ℓ'} {R : Type ℓ''} → (P : Type ℓ) → (P → Q) → (Q → R) → (P → R)
_ ⇒⟨ pq ⟩ qr = qr ∘ pq

_◼ : ∀{ℓ} (A : Type ℓ) → A → A
_ ◼ = λ x → x

-- Lemma 4.1.6.
-- For a constructive field (F, 0, 1, +, ·, #), the following hold.
-- 1. 1 # 0.
-- 2. Addition + is #-compatible in the sense that for all x, y, z : F
--    x # y ⇔ x + z # y + z.
-- 3. Multiplication · is #-extensional in the sense that for all w, x, y, z : F
--    w · x # y · z ⇒ w # y ∨ x # z.
module Lemmas-4-6-1 (F : ConstructiveField {ℓ} {ℓ'}) where

  open ConstructiveField F

  open import Cubical.Structures.Ring
  -- NOTE: this also creates additional `Ring.Carrier (makeRing ...)` in the "Goal/Have-previews", except when using C-u C-u C-... then these get normalized fine
  -- using this `R` makes it a little better
  R = (makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)
  open Cubical.Structures.Ring.Theory R

  -- Lemma 4.1.6.1
  1f#0f : 1f # 0f
  1f#0f with ·-identity 1f
  1f#0f | 1·1≡1 , _ = fst (·-inv-back _ _ 1·1≡1)

  -- NOTE: a few facts about rings that might be collected from elsewhere
  a+b-b≡a : ∀ a b → a ≡ (a + b) - b
  a+b-b≡a a b = let P = sym (fst (+-inv b))
                    Q = sym (fst (+-identity a))
                    R = transport (λ i → a ≡ a + P i) Q
                    S = transport (λ i → a ≡ (+-assoc a b (- b)) i ) R
                in S

  -- NOTE: this is called `simplL` and `simplL` in `Cubical.Structures.Group.Properties.GroupLemmas`
  +-preserves-≡ : ∀{a b} → ∀ c → a ≡ b → a + c ≡ b + c
  +-preserves-≡ c a≡b i = a≡b i + c

  +-preserves-≡-l : ∀{a b} → ∀ c → a ≡ b → c + a ≡ c + b
  +-preserves-≡-l c a≡b i = c + a≡b i

  a+b≡0→a≡-b : ∀{a b} → a + b ≡ 0f → a ≡ - b
  a+b≡0→a≡-b {a} {b} a+b≡0 = transport
    (λ i →
      let RHS = snd (+-identity (- b))
          LHS₁ : a + (b + - b) ≡ a + 0f
          LHS₁ = +-preserves-≡-l a (fst (+-inv b))
          LHS₂ : (a + b) - b ≡ a
          LHS₂ = transport (λ j →  (+-assoc a b (- b)) j ≡ fst (+-identity a) j) LHS₁
          in  LHS₂ i ≡ RHS i
    ) (+-preserves-≡ (- b) a+b≡0)

  -- NOTE: there is already
  -- -commutesWithRight-· : (x y : R) →  x · (- y) ≡ - (x · y)

  a·-b≡-a·b : ∀ a b → a · (- b) ≡ - a · b
  a·-b≡-a·b a b =
    let P : a · 0f ≡ 0f
        P = 0-rightNullifies a
        Q : a · (- b + b) ≡ 0f
        Q = transport (λ i →  a · snd (+-inv b) (~ i) ≡ 0f) P
        R : a · (- b) + a · b ≡ 0f
        R = transport (λ i → ·-rdist-+ a (- b) b i ≡ 0f) Q
    in a+b≡0→a≡-b R

  a·b-a·c≡a·[b-c] : ∀ a b c → a · b - a · c ≡ a · (b - c)
  a·b-a·c≡a·[b-c] a b c =
    let P : a · b + a · (- c) ≡ a · (b + - c)
        P = sym (·-rdist-+ a b (- c))
        Q : a · b - a · c ≡ a · (b + - c)
        Q = transport (λ i →  a · b + a·-b≡-a·b a c i ≡ a · (b + - c) ) P
    in  Q

  -- Lemma 4.1.6.2
  --   For #-compatibility of +, suppose x # y, that is, (x +z) −z # (y +z) −z.
  --   Then #-extensionality gives (x + z # y + z) ∨ (−z # −z), where the latter case is excluded by irreflexivity of #.
  +-#-compatible : ∀(x y z : Carrier) → x # y → x + z # y + z
  +-#-compatible x y z x#y with
    let P = transport (λ i →  a+b-b≡a x z i # a+b-b≡a y z i ) x#y
    in  +-#-extensional _ _ _ _ P
  ... | inl x+z#y+z = x+z#y+z
  ... | inr  -z#-z  = ⊥-elim (#-irrefl _ -z#-z)

  -- The other direction is similar.
  +-#-compatible-inv : ∀(x y z : Carrier) → x + z # y + z → x # y
  +-#-compatible-inv _ _ _ x+z#y+z with +-#-extensional _ _ _ _ x+z#y+z
  ... | inl x#y = x#y
  ... | inr z#z = ⊥-elim (#-irrefl _ z#z)

  -- Lemma 4.1.6.3
  ·-#-extensional-case1 : ∀(w x y z : Carrier) → w · x # y · z → w · x # w · z → x # z
  ·-#-extensional-case1 w x y z w·x#y·z w·x#w·z =
    let
      instance -- this allows to use ⁻¹ᶠ without an instance argument
        w·[z-x]#0f =
          ( w · x         # w ·  z         ⇒⟨ +-#-compatible _ _ (- (w · x)) ⟩
            w · x - w · x # w ·  z - w · x ⇒⟨ transport (λ i →  (fst (+-inv (w · x)) i) # a·b-a·c≡a·[b-c] w z x i) ⟩
                       0f # w · (z - x)    ⇒⟨ #-sym _ _ ⟩
            w ·   (z - x) # 0f             ◼) w·x#w·z
    in (     w  · (z - x) # 0f                      ⇒⟨ (λ _ → ·-rinv (w · (z - x)) it ) ⟩  -- NOTE: "plugging in" the instance did not work, ∴ `it`
             w  · (z - x) · (w · (z - x)) ⁻¹ᶠ  ≡ 1f ⇒⟨ transport (λ i → ·-comm w (z - x) i · (w · (z - x)) ⁻¹ᶠ ≡ 1f) ⟩
        (z - x) ·  w      · (w · (z - x)) ⁻¹ᶠ  ≡ 1f ⇒⟨ transport (λ i → ·-assoc (z - x) w ((w · (z - x)) ⁻¹ᶠ) (~ i) ≡ 1f) ⟩
        (z - x) · (w      · (w · (z - x)) ⁻¹ᶠ) ≡ 1f ⇒⟨ fst ∘ (·-inv-back _ _)  ⟩
           z    - x       # 0f                      ⇒⟨ +-#-compatible _ _ x ⟩
          (z    - x) + x  # 0f + x                  ⇒⟨ transport (λ i → +-assoc z (- x) x (~ i) # snd (+-identity x) i) ⟩
           z + (- x  + x) #      x                  ⇒⟨ transport (λ i → z + snd (+-inv x) i # x) ⟩
           z +      0f    # x                       ⇒⟨ transport (λ i → fst (+-identity z) i # x) ⟩
           z              # x                       ⇒⟨ #-sym _ _ ⟩
           x              # z                       ◼) it -- conceptually we would plug `w·[z-x]#0f` in, but this breaks the very first step

  ·-#-extensional : ∀(w x y z : Carrier) → w · x # y · z → (w # y) ⊎ (x # z)
  ·-#-extensional w x y z w·x#y·z with #-cotrans _ _ w·x#y·z (w · z)
  ... | inl w·x#w·z =    inr (·-#-extensional-case1 w x y z w·x#y·z w·x#w·z) -- first case
  ... | inr w·z#y·z = let z·w≡z·y = (transport (λ i → ·-comm w z i # ·-comm y z i) w·z#y·z)
                      in inl (·-#-extensional-case1 _ _ _ _ z·w≡z·y z·w≡z·y) -- second case reduced to first case

-- Lemma 4.1.7.
-- Given a strict partial order < on a set X:
-- 1. we have an apartness relation defined by
--    x # y := (x < y) ∨ (y < x), and
--
_#'_ : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → Rel X X ℓ'
_#'_ {_<_ = _<_} x y = (x < y) ⊎ (y < x)

swap : ∀{x : Type ℓ} {y : Type ℓ'} → x ⊎ y → y ⊎ x
swap (inl x) = inr x
swap (inr x) = inl x

#'-isApartnessRel : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → (isSPO : IsStrictPartialOrder _<_) → IsApartnessRel (_#'_ {_<_ = _<_})
#'-isApartnessRel {X = X} {_<_ = _<_} isSPO =
  -- decompose record: see https://agda.readthedocs.io/en/v2.6.1/language/let-and-where.html#let-record-pattern
  let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
  in λ where -- anonymous copattern-matching lambda: see https://agda.readthedocs.io/en/v2.6.1/language/record-types.html
    -- clauses work here and case-split does also work!
    -- but I get a "Not implemented: The Agda synthesizer (Agsy) does not support copatterns yet" on proof search
    .IsApartnessRel.isIrrefl a (inl a<a) → <-irrefl _ a<a
    .IsApartnessRel.isIrrefl a (inr a<a) → <-irrefl _ a<a
    .IsApartnessRel.isSym    a b p → swap p
    .IsApartnessRel.isCotrans a b (inl a<b) x → case (<-cotrans _ _ a<b x) of λ where -- case x of f = f x
      -- NOTE: here we have proof search again
      (inl a<x) → inl (inl a<x)
      (inr x<b) → inr (inl x<b)
    .IsApartnessRel.isCotrans a b (inr b<a) x → case (<-cotrans _ _ b<a x) of λ where
      (inl b<x) → inr (inr b<x)
      (inr x<a) → inl (inr x<a)

-- variant without copatterns: "just" move the `λ where` "into" the record
#'-isApartnessRel' : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → {IsStrictPartialOrder _<_} → IsApartnessRel (_#'_ {_<_ = _<_})
#'-isApartnessRel' {X = X} {_<_ = _<_} {isSPO} =
  let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
  in record
    { isIrrefl  = λ where a (inl a<a) → <-irrefl _ a<a
                          a (inr a<a) → <-irrefl _ a<a
    ; isSym     = λ where a b p → swap p
    ; isCotrans = λ where
      a b (inl a<b) x → case (<-cotrans _ _ a<b x) of λ where
        (inl a<x) → inl (inl a<x)
        (inr x<b) → inr (inl x<b)
      a b (inr b<a) x → case (<-cotrans _ _ b<a x) of λ where
        (inl b<x) → inr (inr b<x)
        (inr x<a) → inl (inr x<a)
    }

-- 2. we have a preorder defined by
--    x ≤ y := ¬(y < x).

_≤'_ : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → Rel X X ℓ'
_≤'_ {_<_ = _<_} x y = ¬ (y < x)

≤-isPreorder' : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → {IsStrictPartialOrder _<_} → IsPreorder (_≤'_ {_<_ = _<_})
≤-isPreorder' {X = X} {_<_ = _<_} {isSPO} =
  let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
  in λ where
   .IsPreorder.isRefl → <-irrefl
   .IsPreorder.isTrans a b c ¬b<a ¬c<b c<a → case (<-cotrans _ _ c<a b) of λ where
     (inl c<b) → ¬c<b c<b
     (inr b<a) → ¬b<a b<a

-- Definition 4.1.8.
-- Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
--   z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
-- and max computes least upper bounds in the sense that for every x, y, z : A, we have
--   max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.

record IsLattice {A : Type ℓ}
                 (_≤_ : Rel A A ℓ') (min max : A → A → A) : Type (ℓ-max ℓ ℓ') where
  constructor islattice
  field
    isPartialOrder : IsPartialOrder _≤_
    glb      : ∀ x y z → z ≤ min x y → z ≤ x × z ≤ y
    glb-back : ∀ x y z → z ≤ x × z ≤ y → z ≤ min x y
    lub      : ∀ x y z → max x y ≤ z → x ≤ z × y ≤ z
    lub-back : ∀ x y z → x ≤ z × y ≤ z → max x y ≤ z

  open IsPartialOrder isPartialOrder public
    renaming
      ( isRefl    to ≤-refl
      ; isAntisym to ≤-antisym
      ; isTrans   to ≤-trans )

record Lattice : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor lattice
  field
    Carrier : Type ℓ
    _≤_ : Rel Carrier Carrier ℓ'
    min max : Carrier → Carrier → Carrier
    isLattice : IsLattice _≤_ min max

  infixl 4 _≤_

  open IsLattice isLattice public

-- Remark 4.1.9.2
-- 1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that for every x and y, min(x,y) = x ∨ min(x,y) = y. However, we can characterize min as
--   z < min(x,y) ⇔ z < x ∨ z < y
--   and similarly for max, see Lemma 6.7.1.
-- 2. In a partial order, for two fixed elements a and b, all joins and meets of a, b are equal, so that Lemma 2.6.20 the type of joins and the type of meets are propositions. Hence, providing the maps min and max as in the above definition is equivalent to the showing the existenceof all binary joins and meets.
--
-- The following definition is modified from on The Univalent Foundations Program [89, Definition 11.2.7].
--
-- Definition 4.1.10.
-- An ordered field is a set F together with constants 0, 1, operations +, ·, min, max, and a binary relation < such that:
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. < is a strict [partial] order;
-- 3. x : F has a multiplicative inverse iff x # 0, recalling that # is defined as in Lemma 4.1.7;
-- 4. ≤, as in Lemma 4.1.7, is antisymmetric, so that (F, ≤) is a partial order;
-- 5. (F, ≤, min, max) is a lattice.
-- 6. for all x, y, z, w : F:
--    x + y < z + w ⇒ x < z ∨ y < w, (†)
--    0 < z ∧ x < y ⇒ x z < y z.     (∗)
-- Our notion of ordered fields coincides with The Univalent Foundations Program [89, Definition 11.2.7].

-- NOTE: well, the HOTT book definition organizes things slightly different. Why prefer one approach over the other?
record IsOrderedField {F : Type ℓ}
                 (0f 1f : F) (_+_ : F → F → F) (-_ : F → F) (_·_ min max : F → F → F) (_<_ _#_ _≤_ : Rel F F ℓ') (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) : Type (ℓ-max ℓ ℓ') where
  constructor isorderedfield
  field
    -- 1.
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    -- 2.
    <-isStrictPartialOrder : IsStrictPartialOrder _<_
    -- 3.
    ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    -- NOTE: this "creates" new properties `x # 0f` and `y # 0f` that are different (!) from possibly existing "previous" ones
    --       meaning, that this conflicts a usage where we might recreate these properties somewhere (inside of a module or a function)
    --       and having the result-type depending on them
    --       we can't use the result "outside" then, because it' differs in this `x # 0f` and `y # 0f` entity
    --       although we might not see it (because instance arguments are hidden)
    --       there is another NOTE of this further down
    ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    -- 4. NOTE: we already have ≤-isPartialOrder in <-isLattice
    -- ≤-isPartialOrder : IsPartialOrder _≤_
    -- 5.
    <-isLattice : IsLattice _≤_ min max
    -- 6. (†)
    -- NOTE: this is 'shifted' from the pevious definition of #-extensionality for + .. does the name still fit?
    +-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)
    -- 6. (∗)
    ·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z)

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsStrictPartialOrder <-isStrictPartialOrder public
    renaming
      ( isIrrefl  to <-irrefl
      ; isTrans   to <-trans
      ; isCotrans to <-cotrans )
  -- open IsPartialOrder ≤-isPartialOrder public
  --   renaming
  --     ( isRefl    to ≤-refl
  --     ; isAntisym to ≤-antisym
  --     ; isTrans   to ≤-trans )
  open IsLattice <-isLattice public

record OrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedfield
  field
    Carrier : Type ℓ
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : Rel Carrier Carrier ℓ'

  _#_ = _#'_ {_<_ = _<_}
  _≤_ = _≤'_ {_<_ = _<_}

  field
    -- NOTE: we might want to add some general instances to convert `0f # x` or `x < 0f` or `0f < x` into `x # 0f`
    --       because there is always some fiddling necessary when using _⁻¹ᶠ
    --       e.g. see poof of `item-8` below where we also had to turn `0f ≤ z` and `z # 0` into `0f < z` because
    --         ·-preserves-< was defined in terms of `0f < z`
    _⁻¹ᶠ    : (x : Carrier) → {{x # 0f}} → Carrier
    isOrderedField : IsOrderedField 0f 1f _+_ -_ _·_ min max _<_ _#_ _≤_ _⁻¹ᶠ

  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_
  infixl 4 _≤_
  infixl 4 _<_

  open IsOrderedField isOrderedField public

  abstract
    -- NOTE: there might be some reason not to "do" (or "open") all the theory of a record within that record
    +-preserves-< : ∀ a b x → a < b → a + x < b + x
    +-preserves-< a b x a<b = (
       a            <  b            ⇒⟨ transport (λ i → sym (fst (+-identity a)) i < sym (fst (+-identity b)) i) ⟩
       a +    0f    <  b +    0f    ⇒⟨ transport (λ i → a + sym (+-rinv x) i < b + sym (+-rinv x) i) ⟩
       a + (x  - x) <  b + (x  - x) ⇒⟨ transport (λ i → +-assoc a x (- x) i < +-assoc b x (- x) i) ⟩
      (a +  x) - x  < (b +  x) - x  ⇒⟨ +-<-extensional (- x) (a + x) (- x) (b + x) ⟩
      (a + x < b + x) ⊎ (- x < - x) ⇒⟨ (λ{ (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                         ; (inr  -x<-x ) → ⊥-elim {A = λ _ → (a + x < b + x)} (<-irrefl (- x) -x<-x) }) ⟩
       a + x < b + x ◼) a<b

    {- NOTE: this was "each strict total order is a strict parial order .. when having +-<-extensionality and +-preserves-< and ..." or so
             but we do not have a strict total order in IsOrderedField
    <-isStrictPartialOrder : IsStrictPartialOrder _<_
    <-isStrictPartialOrder = record
     { isIrrefl  = <-irrefl
     ; isTrans   = <-trans
     ; isCotrans = λ where
       a b a<b x →
         ( a      <  b      ⇒⟨ +-preserves-< _ _ _ ⟩
           a + x  <  b + x  ⇒⟨ transport (λ i → a + x < (+-comm b x) i) ⟩
           a + x  <  x + b  ⇒⟨ +-<-extensional b a x x ⟩
          (a < x) ⊎ (x < b) ◼) a<b
     }
     -}

    ≤-isPreorder : IsPreorder _≤_
    ≤-isPreorder = ≤-isPreorder' {_<_ = _<_} {<-isStrictPartialOrder}

import Cubical.Structures.Group
module GroupTheory1 (G : Cubical.Structures.Group.Group {ℓ}) where
  open Cubical.Structures.Group
  open Group G

  -- ported from
  -- import Algebra.Properties.Group

  right-helper : ∀ x y → y ≡ - x + (x + y)
  right-helper x y = (
    y               ≡⟨ sym (snd (identity y)) ⟩
    0g          + y ≡⟨ cong₂ _+_ (sym (snd (inverse x))) refl  ⟩
    ((- x) + x) + y ≡⟨ sym (assoc (- x) x y) ⟩
    (- x) + (x + y) ∎)

  -- alternative:
  --   follows from uniqueness of -
  --     (a + -a) ≡ 0
  --     ∃! b . a + b = 0
  --   show that a is an additive inverse of - a then it must be THE additive inverse of - a and has to be called - - a which is a by uniqueness
  -involutive : ∀ x → - - x ≡ x
  -involutive x = (
    (- (- x))             ≡⟨ sym (fst (identity _)) ⟩
    (- (- x)) + 0g        ≡⟨ cong₂ _+_ refl (sym (snd (inverse _))) ⟩
    (- (- x)) + (- x + x) ≡⟨ sym (right-helper (- x) x) ⟩
    x                    ∎)

contraposition : {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ¬ Q → ¬ P
contraposition f ¬q p = ⊥-elim (¬q (f p))

-- deMorgan₁ : {P : Type ℓ} {Q : Type ℓ'} → ¬(P × Q) → (¬ P) ⊎ (¬ Q)
-- deMorgan₁ {P = P} {Q = Q} = {!!}

-- deMorgan₁-back : {P : Type ℓ} {Q : Type ℓ'} → (¬ P) ⊎ (¬ Q) → ¬(P × Q)
-- deMorgan₁-back {P = P} {Q = Q} = {!!}

deMorgan₂ : {P : Type ℓ} {Q : Type ℓ'} → ¬(P ⊎ Q) → (¬ P) × (¬ Q)
deMorgan₂ {P = P} {Q = Q} = {!!}


-- deMorgan₁ : ∀ x y → ¬ (x × y) ≡ (¬ x) ⊎ (¬ y)
-- deMorgan₁ x y = lemma (x × y) (¬ x ⊎ ¬ y) lem₁ lem₂
--   where
--   lem₁ = (
--     (x × y) × (¬ x ⊎ ¬ y)          ≡⟨ {! ×-⊎-distribˡ _ _ _ !} ⟩
--     (x × y) × ¬ x ⊎ (x × y) × ¬ y  ≡⟨ {! ⊎-congʳ $ ×-congʳ $ ×-comm _ _ !} ⟩
--     (y × x) × ¬ x ⊎ (x × y) × ¬ y  ≡⟨ {! ×-assoc _ _ _ ⟨ ⊎-cong ⟩ ⟩ ×-assoc _ _ _ !} ⟩
--     y × (x × ¬ x) ⊎ x × (y × ¬ y)  ≡⟨ {! (×-congˡ $ ×-complementʳ _) ⟨ ⊎-cong ⟩
--                                       (×-congˡ $ ×-complementʳ _) !} ⟩
--     (y × ⊥) ⊎ (x × ⊥)              ≡⟨ {! ×-zeroʳ _ ⟨ ⊎-cong ⟩ ⟩ ×-zeroʳ _ !} ⟩
--     ⊥ ⊎ ⊥                          ≡⟨ {! ⊎-identityʳ _ !} ⟩
--     ⊥                              ∎)
-- 
--   lem₃ = (
--     (x × y) ⊎ ¬ x          ≡⟨ {! ⊎-×-distribʳ _ _ _ !} ⟩
--     (x ⊎ ¬ x) × (y ⊎ ¬ x)  ≡⟨ {! ×-congʳ $ ⊎-complementʳ _ !} ⟩
--     ⊤ × (y ⊎ ¬ x)          ≡⟨ {! ×-identityˡ _ !} ⟩
--     y ⊎ ¬ x                ≡⟨ {! ⊎-comm _ _ !} ⟩
--     ¬ x ⊎ y                ∎)
-- 
--   lem₂ = (
--     (x × y) ⊎ (¬ x ⊎ ¬ y)  ≡⟨ {! ⊎-assoc _ _ _ !} ⟩
--     ((x × y) ⊎ ¬ x) ⊎ ¬ y  ≡⟨ {! ⊎-congʳ lem₃ !} ⟩
--     (¬ x ⊎ y) ⊎ ¬ y        ≡⟨ {! ⊎-assoc _ _ _ !} ⟩
--     ¬ x ⊎ (y ⊎ ¬ y)        ≡⟨ {! ⊎-congˡ $ ⊎-complementʳ _ !} ⟩
--     ¬ x ⊎ ⊤                ≡⟨ {! ⊎-zeroʳ _ !} ⟩
--     ⊤                      )



-- Lemma 4.1.11.
-- In the presence of the first five axioms of Definition 4.1.10, conditions (†) and (∗) are together equivalent to the condition that for all x, y, z : F,
--  1. x ≤ y ⇔ ¬(y < x),
--  2. x # y ⇔ (x < y) ∨ (y < x)
--  3. x ≤ y ⇔ x + z ≤ y + z,
--  4. x < y ⇔ x + z < y + z,
--  5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
--  6. x < y ≤ z ⇒ x < z,
--  7. x ≤ y < z ⇒ x < z,
--  8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
--  9. 0 < z ⇒ (x < y ⇔ x z < y z),
-- 10. 0 < 1.
-- NOTE: this looks useful, so we might want to have it separately
--       therefore I'll just copy the `OrderedField` record's nested structure (Definition 4.1.10)
--       although this "header" of it looks very ugly
-- NOTE: well, there is some syntax for this: https://lists.chalmers.se/pipermail/agda/2018/010217.html
--       also see https://github.com/agda/agda/issues/1235
--       BUT: it adds a ₁ to every symbol in the goal preview, even when normalizing
module Lemma-4-1-11
  --------------------------------------- structures
  (F       : Type ℓ)
  (0f 1f   : F)
  (_+_     : F → F → F)
  (-_      : F → F)
  (_·_     : F → F → F)
  (min max : F → F → F)
  (_<_     : Rel F F ℓ')
  --------------------------------------- definitions (fixites)
  -- https://lists.chalmers.se/pipermail/agda/2018/010217.html
  --   Those lets are not parameters of the module
  (let _·_  = _·_ ; infixl 7 _·_ )
  (let -_   = -_  ; infix  6 -_ )
  (let _+_  = _+_ ; infixl 5 _+_ )
  (let _<_  = _<_ ; infixl 4 _<_ )
  --------------------------------------- properties
  -- 1.
  (isCommRing : IsCommRing 0f 1f _+_ _·_ -_)
  -- 2.
  (<-isStrictTotalOrder : IsStrictPartialOrder _<_)
  --------------------------------------- definitions
  (let _#_ = _#'_ {_<_ = _<_}; infixl 4 _#_)
  (let _≤_ = _≤'_ {_<_ = _<_}; infixl 4 _≤_)
  --------------------------------------- structures
  (_⁻¹ᶠ    : (x : F) → {{x # 0f}} → F)
  (let _⁻¹ᶠ = _⁻¹ᶠ; infix  9 _⁻¹ᶠ)
  --------------------------------------- properties
  -- 3.
  (·-rinv     : ∀ x → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f)
  (·-linv     : ∀ x → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f)
  (·-inv-back : ∀(x y : F) → (x · y ≡ 1f) → (x # 0f) × (y # 0f) )
  -- 4.
  (≤-isPartialOrder : IsPartialOrder _≤_)
  -- 5.
  (<-isLattice : IsLattice _≤_ min max)
  --------------------------------------- definitions (fixites)
  -- https://lists.chalmers.se/pipermail/agda/2018/010217.html
  --   Those lets are not parameters of the module
  -- this one is tricky: its usually from `Group` and we get it by opening `IsCommRing`
  -- (let _-_  = λ(x y : F) → x + (- y) ; infixl 6 _-_)
  where
  --------------------------------------- populating the scope
  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsStrictPartialOrder <-isStrictTotalOrder public
    renaming
      ( isIrrefl  to <-irrefl
      ; isTrans   to <-trans
      ; isCotrans to <-cotrans )
  open IsPartialOrder ≤-isPartialOrder public
    renaming
      ( isRefl    to ≤-refl
      ; isAntisym to ≤-antisym
      ; isTrans   to ≤-trans )
  open IsLattice <-isLattice public

----8<---------------------------8<--------------------------8<----

  -- NOTE: when using "implicational" reasoning `_⇒⟨_⟩` agda is pretty good in determining the arguments within `⟨_⟩`
  --       but all arguments become necessary when being inside of a path, e.g. for using `transport`
  --       so it might be a good strategy to have all the "tactics" (well, not really tactics, but
  --         the most used "proof machinery" at least) available as explicit functions, such that only a single function
  --         needs to be applied in each step
  --       often, just using `cong₂` instead of a path as the argument of `transport` already helps
  --         well, no. see [XX]
  --       this is observable in the standard library to some degree `grep -RHni ≡⟨ ~/agda/cubical/`
  -- NOTE: there is also a `≡⟨⟩` just for the identity which is useful for folding/unfolding definition
  --         i.e. steps that hold definitionally
  --         _≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y
  --         _ ≡⟨⟩ x≡y = x≡y
  --         infixr 2 _≡⟨⟩_
  --       this just avoids the use of `≡⟨ λ x → x ⟩`

  -- NOTE: I am doing this for the n'th time now ...
  --       these four cases can surely be omitted by using correct equivalences (TODO)
  -- NOTE: I think I am very close. Sometimes it amounts just to dropping `transport` to have the equivalence
  --       so there is still some exercise for getting used to this
  -- NOTE: there is Tactic.MonoidSolver in the old standard library
  --       and https://github.com/UlfNorell/agda-prelude/blob/master/src/Tactic/Monoid.agda
  --           https://github.com/UlfNorell/agda-prelude/blob/master/test/MonoidTactic.agda
  --       and https://github.com/agda/agda-stdlib/blob/experimental/README/Solvers/ReflectiveMonoid.agda 
  --       and maybe a few more ...

  -- +-preserves-≡ʳ : ∀ x y z → x ≡ y → x + z ≡ y + z
  -- +-preserves-≡ʳ x y z x≡y = transport (λ i → x + z ≡ x≡y i + z) refl

  -- +-preserves-≡ˡ : ∀ x y z → x ≡ y → z + x ≡ z + y
  -- +-preserves-≡ˡ x y z x≡y = transport (λ i → z + x ≡ z + x≡y i) refl

  open import Cubical.Structures.Ring
  R = (makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)

  -- implicitInverse : (x y : F) → x + y ≡ 0f → y ≡ - x
  -- implicitInverse = Theory.implicitInverse R

  -isDistributive : (x y : F) → (- x) + (- y) ≡ - (x + y)
  -isDistributive = Theory.-isDistributive R

  -- translatedDifference : (x a b : F) → a - b ≡ (x + a) - (x + b)
  -- translatedDifference = Theory.translatedDifference R

  -commutesWithRight-· : (x y : F) →  x · (- y) ≡ - (x · y)
  -commutesWithRight-· = Theory.-commutesWithRight-· R

  -commutesWithLeft-· : (x y : F) →  (- x) · y ≡ - (x · y)
  -commutesWithLeft-· = Theory.-commutesWithLeft-· R

  0-leftNullifies : (x : F) → 0f · x ≡ 0f
  0-leftNullifies = Theory.0-leftNullifies R

  G = (Cubical.Structures.Group.makeGroup 0f _+_ -_ is-set +-assoc +-rid +-lid +-rinv +-linv)
  open GroupTheory1 G

  module forward
    -- 6. (†)
    (+-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w))
    -- 6. (∗)
    (·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z))
    where
    abstract -- does this really improve performance?

      -- NOTE: the equivalences might be proven together
      -- TODO: name these

      --  1. x ≤ y ⇔ ¬(y < x),
      item-1 : ∀ x y → x ≤ y → ¬(y < x)
      item-1 = λ _ _ x≤y → x≤y -- holds definitionally

      item-1-back : ∀ x y → ¬(y < x) → x ≤ y
      item-1-back = λ _ _ ¬[y<x] → ¬[y<x]

      --  2. x # y ⇔ (x < y) ∨ (y < x)
      item-2 : ∀ x y → x # y → (x < y) ⊎ (y < x)
      item-2 = λ _ _ x#y → x#y -- holds definitionally

      item-2-back : ∀ x y → (x < y) ⊎ (y < x) → x # y
      item-2-back = λ _ _ [x<y]⊎[y<x] → [x<y]⊎[y<x] -- holds definitionally

      -- NOTE: just a plain copy of the previous proof
      +-preserves-< : ∀ a b x → a < b → a + x < b + x
      +-preserves-< a b x a<b = (
         a            <  b            ⇒⟨ transport (λ i → sym (fst (+-identity a)) i < sym (fst (+-identity b)) i) ⟩
         a +    0f    <  b +    0f    ⇒⟨ transport (λ i → a + sym (+-rinv x) i < b + sym (+-rinv x) i) ⟩
         a + (x  - x) <  b + (x  - x) ⇒⟨ transport (λ i → +-assoc a x (- x) i < +-assoc b x (- x) i) ⟩
        (a +  x) - x  < (b +  x) - x  ⇒⟨ +-<-extensional (- x) (a + x) (- x) (b + x) ⟩
        (a + x < b + x) ⊎ (- x < - x) ⇒⟨ (λ{ (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                           ; (inr  -x<-x ) → ⊥-elim {A = λ _ → (a + x < b + x)} (<-irrefl (- x) -x<-x) }) ⟩
         a + x < b + x ◼) a<b

      +-preserves-<-back : ∀ x y z → x + z < y + z → x < y
      +-preserves-<-back x y z =
        ( x + z < y + z              ⇒⟨ +-preserves-< _ _ (- z) ⟩
          (x + z) - z  < (y + z) - z ⇒⟨ transport (λ i → +-assoc x z (- z) (~ i) < +-assoc y z (- z) (~ i)) ⟩
          x + (z - z) < y + (z - z)  ⇒⟨ transport (λ i → x + +-rinv z i < y + +-rinv z i) ⟩
          x + 0f < y + 0f            ⇒⟨ transport (λ i → fst (+-identity x) i < fst (+-identity y) i) ⟩
          x < y ◼)

      --  3. x ≤ y ⇔ x + z ≤ y + z,
      item-3 : ∀ x y z → x ≤ y → x + z ≤ y + z
      item-3 x y z = (
         x     ≤ y          ⇒⟨ (λ z → z) ⟩ -- unfold the definition
        (y     < x     → ⊥) ⇒⟨ (λ f → f ∘ (+-preserves-<-back y x z) ) ⟩
        (y + z < x + z → ⊥) ⇒⟨ (λ z → z) ⟩ -- refold the definition
         x + z ≤ y + z ◼)

      item-3-back : ∀ x y z → x + z ≤ y + z → x ≤ y
      item-3-back x y z = (
         x + z ≤ y + z      ⇒⟨ (λ z → z) ⟩ -- unfold the definition
        (y + z < x + z → ⊥) ⇒⟨ (λ f p → f (+-preserves-< y x z p)) ⟩ -- just a variant of the above
        (y     < x     → ⊥) ⇒⟨ (λ z → z) ⟩ -- refold the definition
         x     ≤ y ◼)

      --  4. x < y ⇔ x + z < y + z,
      item-4 : ∀ x y z → x < y → x + z < y + z
      item-4 = +-preserves-<

      item-4-back : ∀ x y z → x + z < y + z → x < y
      item-4-back = +-preserves-<-back

      --  5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
      item-5 : ∀ x y → 0f < x + y → (0f < x) ⊎ (0f < y)
      item-5 x y = (
        (0f      < x + y) ⇒⟨ transport (λ i → fst (+-identity 0f) (~ i) < x + y) ⟩
        (0f + 0f < x + y) ⇒⟨ +-<-extensional y 0f 0f x ⟩
        (0f < x) ⊎ (0f < y) ◼)

      --  6. x < y ≤ z ⇒ x < z,
      item-6 : ∀ x y z → x < y → y ≤ z → x < z
      item-6 x y z x<y y≤z = (
         x      <  y      ⇒⟨ +-preserves-< _ _ _ ⟩
         x + z  <  y + z  ⇒⟨ transport (λ i → x + z < +-comm y z i) ⟩
         x + z  <  z + y  ⇒⟨ +-<-extensional y x z z  ⟩
        (x < z) ⊎ (z < y) ⇒⟨ (λ{ (inl x<z) → x<z
                               ; (inr z<y) → ⊥-elim (y≤z z<y) }) ⟩
         x < z  ◼) x<y

      --  7. x ≤ y < z ⇒ x < z,
      item-7 : ∀ x y z → x ≤ y → y < z → x < z
      item-7 x y z x≤y = ( -- very similar to the previous one
         y      <  z      ⇒⟨ +-preserves-< y z x ⟩
         y + x  <  z + x  ⇒⟨ transport (λ i → +-comm y x i < z + x) ⟩
         x + y  <  z + x  ⇒⟨ +-<-extensional x x y z ⟩
        (x < z) ⊎ (y < x) ⇒⟨ (λ{ (inl x<z) → x<z
                               ; (inr y<x) → ⊥-elim (x≤y y<x)}) ⟩
         x < z  ◼)

      item-10 : 0f < 1f

      --  8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
      item-8 : ∀ x y z → x ≤ y → 0f ≤ z → x · z ≤ y · z
      -- For item 8, suppose x ≤ y and 0 ≤ z and yz < xz.
      item-8 x y z x≤y 0≤z y·z<x·z = let
        -- Then 0 < z (x − y) by (†),
        i   = (  y · z            <  x · z                ⇒⟨ transport (λ i → ·-comm y z i < ·-comm x z i) ⟩
                 z · y            <  z · x                ⇒⟨ +-preserves-< _ _ _ ⟩
                (z · y) - (z · y) < (z · x) - (z ·    y ) ⇒⟨ transport (cong₂ _<_ (+-rinv (z · y))
                                                               ( λ i → (z · x) + sym (-commutesWithRight-· z y) i )) ⟩
                               0f < (z · x) + (z · (- y)) ⇒⟨ transport (cong₂ _<_ refl (sym (fst (dist z x (- y))))) ⟩ -- [XX]
                               0f <  z · (x - y) ◼) y·z<x·z
        instance _ = z · (x - y) # 0f ∋ inr i
        -- and so, being apart from 0, z (x − y) has a multiplicative inverse w.
        w   = (z · (x - y)) ⁻¹ᶠ
        ii  : 1f ≡ (z · (x - y)) · w
        ii  = sym (·-rinv _ _)
        -- Hence z itself has a multiplicative inverse w (x − y),
        iii : 1f ≡ z · ((x - y) · w)
        iii = transport (λ i → 1f ≡ ·-assoc z (x - y) w (~ i)) ii
        instance z#0f = z # 0f ∋ fst (·-inv-back _ _ (sym iii))
        -- and so 0 < z ∨ z < 0, where the latter case contradicts the assumption 0 ≤ z, so that we have 0 < z.
        instance _    = 0f < z ∋ case z#0f of λ where
                        (inl z<0) → ⊥-elim (0≤z z<0)
                        (inr 0<z) → 0<z
        -- Now w (x − y) has multiplicative inverse z, so it is apart from 0,
        iv  :  (x - y) · w # 0f
        iv  = snd (·-inv-back _ _ (sym iii))
        -- that is (0 < w (x − y)) ∨ (w (x − y) < 0).  
        in case iv of λ where
          -- By (∗), from 0 < w (x − y) and yz < xz we get yzw (x − y) < xzw (x − y), so y < x, contradicting our assumption that x ≤ y.
          (inr 0<[x-y]·w) → (
             y ·  z                   <  x ·  z                    ⇒⟨ ·-preserves-< _ _ _ 0<[x-y]·w ⟩
            (y ·  z) · ((x - y) · w)  < (x ·  z) · ((x - y) · w)   ⇒⟨ transport (λ i →
                                                                          (·-assoc y z ((x - y) · w)) (~ i)
                                                                        < (·-assoc x z ((x - y) · w)) (~ i)) ⟩
             y · (z  · ((x - y) · w)) <  x · (z  · ((x - y) · w))  ⇒⟨ transport (λ i →
                                                                         y · (iii (~ i)) < x · (iii (~ i))) ⟩
             y · 1f                   <  x · 1f                    ⇒⟨ transport (cong₂ _<_
                                                                        (fst (·-identity y)) (fst (·-identity x))) ⟩
             y                        <  x                         ⇒⟨ x≤y ⟩
            ⊥ ◼) y·z<x·z
          -- In the latter case, from (∗) we get zw (x − y) < 0, i.e.
          -- 1 < 0 which contradicts item 10, so that we have 0 < w (x − y).
          (inl p) → (
                 (x - y) · w      < 0f     ⇒⟨ ·-preserves-< _ _ _ it ⟩
                ((x - y) · w) · z < 0f · z ⇒⟨ transport (cong₂ _<_ (·-comm _ _) (0-leftNullifies z)) ⟩
            z · ((x - y) · w)     < 0f     ⇒⟨ ( transport λ i → iii (~ i) < 0f) ⟩
                               1f < 0f     ⇒⟨ <-trans _ _ _  item-10 ⟩
                               0f < 0f     ⇒⟨ <-irrefl _ ⟩
            ⊥ ◼) p

      --  9. 0 < z ⇒ (x < y ⇔ x z < y z),
      item-9 : ∀ x y z → 0f < z → (x < y → x · z < y · z)
      item-9 = ·-preserves-<

      -- ·-inv-same-sign : ∀ x → (p : 0f < x) → (0f < _⁻¹ᶠ x {{inr p}})
      -- ·-inv-same-sign x p = {!!}

      -- ·-inv-unique : ∀ x y z → x · y ≡ 1f → x · z ≡ 1f → y ≡ z
      -- ·-inv-unique = {!!}

      {-
      ·-inv-same-sign : ∀ x y → 0f < x → 1f ≡ x · y → 0f < y
      ·-inv-same-sign x y 0<x 1=x·y = let
        instance _ = 0<x -- this is to multiply with 
        instance _ = x # 0f ∋ inr 0<x -- this is to make use of ⁻¹
        in (0f < 1f    ⇒⟨ {!!} ⟩
            0f < x · y ⇒⟨ {!!} ⟩
            (x ⁻¹ᶠ) · 0f < x ⁻¹ᶠ · (x · y) ⇒⟨ {!!} ⟩
            0f < (x ⁻¹ᶠ · x) · y ⇒⟨ {!!} ⟩
            0f < y ◼) item-10

            0 < x · y
      -}

      -- NOTE: ∙ reads from left to right, e.g. "step1 ∙ step2 ∙ step3"
      -- NOTE: ported from Cubical.Structures.Group.GroupLemmas
      simplR : {a b : F} (c : F) {{_ : c # 0f}} → a · c ≡ b · c → a ≡ b
      simplR {a} {b} c {{_}} a·c≡b·c =
         a                ≡⟨ sym (fst (·-identity a)) ∙ cong (a ·_) (sym (·-rinv c it)) ∙ ·-assoc _ _ _ ⟩
        (a · c) · (c ⁻¹ᶠ) ≡⟨ cong (_· c ⁻¹ᶠ) a·c≡b·c ⟩
        (b · c) · (c ⁻¹ᶠ) ≡⟨ sym (·-assoc _ _ _) ∙ cong (b ·_) (·-rinv c it) ∙ fst (·-identity b)  ⟩
         b ∎

      ·-preserves-≡ʳ : {a b : F} (c : F) {{_ : c # 0f}} → a · c ≡ b · c → a ≡ b
      ·-preserves-≡ʳ = simplR

      -- NOTE: while this might make it "easier" to read at some point, we broke the signature into two parts
      -- ·-linv-unique : (x y : F) (x·y≡1 : (x ·₁ y) ≡ 1f) → x ≡ (y ⁻¹ᶠ₁)
      module _ (x y : F) (x·y≡1 : x · y ≡ 1f) where
        -- NOTE: (IMPORTANT)
        --       the following line "creates" a "new" `y#0`
        --       now, this is apriory not equal to previous `y#0`s because `·-inv-back` does not give us a prop
        --       therefore I am observing a situation where I have exactly the goal
        --         Goal: (z ⁻¹ᶠ₁) ≡ ((((y ·₁ z) - (x ·₁ z)) ⁻¹ᶠ₁) ·₁ (y - x))
        --         Have: (z ⁻¹ᶠ₁) ≡ ((((y ·₁ z) - (x ·₁ z)) ⁻¹ᶠ₁) ·₁ (y - x))
        --       but Agda refuses to take what I have with the following message
        --         ERROR
        --           [almost what I was giving agda, but expanded] != inr 0<z of type (z <₁ 0f) ⊎ (0f <₁ z)
        --         when checking that the expression
        --           [what I was giving agda] has type [the goal type]
        --       so this might be mitigated by using Prop instead
        --       although some more thinking should go into this kind of instance usage
        y#0 = snd (·-inv-back _ _ x·y≡1)
        instance _ = y#0
        import Cubical.Structures.Group

        -- NOTE: ported from Cubical.Structures.Group.GroupLemmas
        abstract
          ·-linv-unique' : Σ[ p ∈ y # 0f ] (x ≡ _⁻¹ᶠ y {{p}})
          ·-linv-unique' = it , (
            x · y ≡ 1f        ⇒⟨ transport (λ i → x · y ≡ ·-linv y it (~ i)) ⟩
            x · y ≡ y ⁻¹ᶠ · y ⇒⟨ simplR _  ⟩
            x     ≡ y ⁻¹ᶠ     ◼) x·y≡1

      ·-linv-unique : (x y : F) → ((x · y) ≡ 1f) → Σ[ p ∈ y # 0f ] x ≡ (_⁻¹ᶠ y {{p}})
      ·-linv-unique = ·-linv-unique'

      -- NOTE: a variant for not having to state the `let instance` twice (but this needs an indentation)
      -- ⁻¹ᶠ-involutive : (x : F) (z#0 : x #' 0f) → ((x ⁻¹ᶠ₁) ⁻¹ᶠ₁) ≡ x
      module _ (z : F) (z#0 : z # 0f) where
        private
          instance _ = z#0
          z⁻¹ = z ⁻¹ᶠ -- NOTE: interestingly, the instance argument is not applied and y remains normalized in terms of z
                    --       so we get `y : {{ _ : z #' 0f }} → F` here
          z⁻¹#0 = snd (·-inv-back z z⁻¹ (·-rinv z it))
          -- NOTE: for some reason I get "There are instances whose type is still unsolved when checking that the expression it has type z #' 0f"
          --       typing `y : F` did not help much. therefore this goes in two lines
          instance _ = z⁻¹#0
          z⁻¹⁻¹ = z⁻¹ ⁻¹ᶠ

        -- NOTE: this should be similar to `right-helper` + `-involutive`
        ⁻¹ᶠ-involutive : (z ⁻¹ᶠ) ⁻¹ᶠ ≡ z
        ⁻¹ᶠ-involutive = (
           z⁻¹⁻¹              ≡⟨ sym (fst (·-identity _)) ⟩
           z⁻¹⁻¹ ·      1f    ≡⟨ (λ i →  z⁻¹⁻¹ · ·-linv _ it (~ i)) ⟩
           z⁻¹⁻¹ · (z⁻¹  · z) ≡⟨ ·-assoc _ _ _ ⟩
          (z⁻¹⁻¹ ·  z⁻¹) · z  ≡⟨ (λ i → ·-linv z⁻¹ it i · z) ⟩
                1f       · z  ≡⟨  snd (·-identity _)  ⟩
                           z  ∎)

      -- ⁻¹ᶠ-preserves-sign : (x : F) (0<z : 0f <₁ x) → 0f <₁ (x ⁻¹ᶠ₁)
      module _ (z : F) (0<z : 0f < z) where
        private
          instance _ = z # 0f ∋ inr 0<z
          z⁻¹ = z ⁻¹ᶠ
          z⁻¹#0 = snd (·-inv-back z z⁻¹ (·-rinv z it))
        abstract
          ⁻¹ᶠ-preserves-sign : 0f < z ⁻¹ᶠ
          ⁻¹ᶠ-preserves-sign with z⁻¹#0
          ... | inl z⁻¹<0 = (
            z⁻¹     < 0f     ⇒⟨ ·-preserves-< _ _ z 0<z ⟩
            z⁻¹ · z < 0f · z ⇒⟨ transport (λ i → ·-linv z it i <  0-leftNullifies z i) ⟩
            1f      < 0f     ⇒⟨ <-trans _ _ _ item-10 ⟩
            0f      < 0f     ⇒⟨ <-irrefl _ ⟩
                    ⊥        ⇒⟨ ⊥-elim ⟩ _ ◼) z⁻¹<0
          ... | inr 0<z⁻¹ = 0<z⁻¹


      item-9-back : ∀ x y z → 0f < z → (x · z < y · z → x < y)
      -- For the other direction of item 9, assume 0 < z and xz < yz,
      item-9-back x y z 0<z x·z<y·z = let
        instance _ = (          x · z  <  y · z            ⇒⟨ +-preserves-< _ _ _ ⟩
                     (x · z) - (x · z) < (y · z) - (x · z) ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                    0f < (y · z) - (x · z) ◼) x·z<y·z
                 _ = (y · z) - (x · z) # 0f ∋ inr it
        -- so that yz − xz has a multiplicative inverse w,
        w = ((y · z) - (x · z)) ⁻¹ᶠ
        o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (-commutesWithLeft-· x z) (~ i)) ⟩
              (y · z) + ((- x) · z) ≡⟨ sym (snd (dist y (- x) z)) ⟩
              (y - x) · z ∎)
        instance _ = (y - x) · z # 0f ∋  transport (λ i → o i # 0f) it
        -- and so z itself has multiplicative inverse w (y − x).
        1≡z·[w·[y-x]] = γ
        iii = 1≡z·[w·[y-x]]
        1≡[w·[y-x]]·z : 1f ≡ (w · (y - x)) · z
        1≡[w·[y-x]]·z = transport (λ i → 1f ≡ ·-comm z (w · (y - x)) i) 1≡z·[w·[y-x]]
        -- Then since 0 < z and xz < yz, by (∗), we get xzw (y − x) < yzw (y − x), and hence x < y.
        instance _ = z # 0f ∋ inr 0<z
        z⁻¹ = w · (y - x)
        z⁻¹≡w·[y-x] : z ⁻¹ᶠ ≡ (w · (y - x))
        z⁻¹≡w·[y-x] = {! sym (snd (·-linv-unique (w · (y - x)) z (sym 1≡[w·[y-x]]·z))) !}
        instance _ = 0f < w · (y - x) ∋ {! 1≡z·[w·[y-x]]!}
        -- instance _ = 0f < z⁻¹ ∋ ?
        in (  x ·  z         <  y ·  z         ⇒⟨ ·-preserves-< _ _ z⁻¹ it ⟩
             (x ·  z) · z⁻¹  < (y ·  z) · z⁻¹  ⇒⟨ transport (λ i → ·-assoc x z z⁻¹ (~ i) < ·-assoc y z z⁻¹ (~ i)) ⟩
              x · (z  · z⁻¹) <  y · (z  · z⁻¹) ⇒⟨ transport (λ i → x · iii (~ i) < y · iii (~ i)) ⟩
              x · 1f         <  y · 1f         ⇒⟨ transport (cong₂ _<_ (fst (·-identity x)) (fst (·-identity y))) ⟩
              x              <  y              ◼) x·z<y·z
        where
          abstract
            γ =
              let -- NOTE: for some reason the instance resolution does only work in let-blocks
              -- I get a "Terms marked as eligible for instance search should end with a name, so `instance' is ignored here. when checking the definition of my-instance"
              instance my-instance = (          x · z  <  y · z            ⇒⟨ +-preserves-< _ _ _ ⟩
                           (x · z) - (x · z) < (y · z) - (x · z) ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                          0f < (y · z) - (x · z) ◼) x·z<y·z
                       _ = (y · z) - (x · z) # 0f ∋ inr it
              -- so that yz − xz has a multiplicative inverse w,
              w = ((y · z) - (x · z)) ⁻¹ᶠ
              o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (-commutesWithLeft-· x z) (~ i)) ⟩
                    (y · z) + ((- x) · z) ≡⟨ sym (snd (dist y (- x) z)) ⟩
                    (y - x) · z ∎)
              instance _ = (y - x) · z # 0f ∋  transport (λ i → o i # 0f) it
              in (
                1f                      ≡⟨ (λ i → ·-linv ((y · z) - (x · z)) it (~ i)) ⟩
                w · ((y · z) - (x · z)) ≡⟨ (λ i → w · o i) ⟩
                w · ((y - x) · z)       ≡⟨ (λ i → w · ·-comm (y - x) z i ) ⟩
                w · (z · (y - x))       ≡⟨ (λ i → ·-assoc w z (y - x) i) ⟩
                (w · z) · (y - x)       ≡⟨ (λ i → ·-comm w z i · (y - x)) ⟩
                (z · w) · (y - x)       ≡⟨ (λ i → ·-assoc z w (y - x) (~ i)) ⟩
                z · (w · (y - x))       ∎)

      {-
      module _ (x y z : F) (0<z : 0f < z) (x·z<y·z : x · z < y · z) where
        -- For the other direction of item 9, assume 0 < z and xz < yz,
        instance _ = (          x · z  <  y · z            ⇒⟨ +-preserves-< _ _ _ ⟩
                     (x · z) - (x · z) < (y · z) - (x · z) ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                    0f < (y · z) - (x · z) ◼) x·z<y·z
        instance _ = (y · z) - (x · z) # 0f ∋ inr it
        -- so that yz − xz has a multiplicative inverse w,
        w = ((y · z) - (x · z)) ⁻¹ᶠ
        o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (-commutesWithLeft-· x z) (~ i)) ⟩
              (y · z) + ((- x) · z) ≡⟨ sym (snd (dist y (- x) z)) ⟩
              (y - x) · z ∎)
        instance _ = (y - x) · z # 0f ∋  transport (λ i → o i # 0f) it
        -- and so z itself has multiplicative inverse w (y − x).
        1≡z·[w·[y-x]] : 1f ≡ z · (w · (y - x))
        1≡z·[w·[y-x]] = γ where
          abstract
            γ = (
             1f                      ≡⟨ (λ i → ·-linv ((y · z) - (x · z)) it (~ i)) ⟩
             w · ((y · z) - (x · z)) ≡⟨ (λ i → w · o i) ⟩
             w · ((y - x) · z)       ≡⟨ (λ i → w · ·-comm (y - x) z i ) ⟩
             w · (z · (y - x))       ≡⟨ (λ i → ·-assoc w z (y - x) i) ⟩
             (w · z) · (y - x)       ≡⟨ (λ i → ·-comm w z i · (y - x)) ⟩
             (z · w) · (y - x)       ≡⟨ (λ i → ·-assoc z w (y - x) (~ i)) ⟩
             z · (w · (y - x))       ∎)
        1≡[w·[y-x]]·z : 1f ≡ (w · (y - x)) · z
        1≡[w·[y-x]]·z = transport (λ i → 1f ≡ ·-comm z (w · (y - x)) i) 1≡z·[w·[y-x]]
        -- Then since 0 < z and xz < yz, by (∗), we get xzw (y − x) < yzw (y − x), and hence x < y.
        instance _ = z # 0f ∋ inr 0<z
        z⁻¹ = w · (y - x)
        --  ·-linv-unique _ _ (sym iii)
        z⁻¹≡w·[y-x] : z ⁻¹ᶠ ≡ (w · (y - x))
        z⁻¹≡w·[y-x] = {! sym (·-linv-unique _ _ (sym 1≡[w·[y-x]]·z)) !}
        --   (⁻¹ᶠ-preserves-sign z 0<z)
        -- transport (λ i → z⁻¹≡w·[y-x] i)        
        iv : 0f < (z ⁻¹ᶠ) → 0f < ((((y · z) + (- (x · z))) ⁻¹ᶠ) · (y + (- x)))
        iv = {! transport (λ i → 0f < z⁻¹≡w·[y-x] i) !}
        -- (⁻¹ᶠ-preserves-sign z 0<z)
        instance _ = 0f < w · (y - x) ∋ {!    !}
        item-9-back : x < y
        item-9-back =
           (  x ·  z         <  y ·  z         ⇒⟨ ·-preserves-< _ _ z⁻¹ it ⟩
             (x ·  z) · z⁻¹  < (y ·  z) · z⁻¹  ⇒⟨ transport (λ i → ·-assoc x z z⁻¹ (~ i) < ·-assoc y z z⁻¹ (~ i)) ⟩
              x · (z  · z⁻¹) <  y · (z  · z⁻¹) ⇒⟨ transport (λ i → x · 1≡z·[w·[y-x]] (~ i) < y · 1≡z·[w·[y-x]] (~ i)) ⟩
              x · 1f         <  y · 1f         ⇒⟨ transport (cong₂ _<_ (fst (·-identity x)) (fst (·-identity y))) ⟩
              x              <  y              ◼) x·z<y·z
      -}
      {-
        let
          instance _ = z # 0f ∋ inr 0<z -- make the instance available
          z⁻¹ = z ⁻¹ᶠ
          #-sym : ∀{a b} → a # b → b # a
          #-sym {a} {b} = swap
          0#z⁻¹ =  #-sym (snd (·-inv-back z z⁻¹ (·-rinv z (inr 0<z))))
          0<z⁻¹ : 0f < z ⁻¹ᶠ
          0<z⁻¹ = {! ·-preserves-< 0f 1f  !}
          -- 0 < 1
          -- 0 < z · z⁻¹
        in (
        (x · z) < (y · z) ⇒⟨ {! ·-preserves-< (x · z) (y · z) z⁻¹!} ⟩
        (x · z) · z⁻¹ < (y · z) · z⁻¹ ⇒⟨ {!!} ⟩
        x · (z · z⁻¹) < y · (z · z⁻¹) ⇒⟨ {!!} ⟩
        x · 1f < y · 1f ⇒⟨ {!!} ⟩
        x < y ◼)
      -}

      -- 10. 0 < 1.
      item-10 with snd (·-inv-back _ _ (fst (·-identity 1f)))
      -- For item 10, since 1 has multiplicative inverse 1, it is apart from 0, hence 0 < 1 ∨ 1 < 0.
      ... | inl 1<0 =
        -- If 1 < 0 then by item 4 we have 0 < −1 and so by (∗) we get 0 < (−1) · (−1), that is, 0 < 1, so by transitivity 1 < 1, contradicting irreflexivity of <.
         (1f          < 0f                ⇒⟨ +-preserves-< 1f 0f (- 1f) ⟩
          1f    - 1f  < 0f - 1f           ⇒⟨ transport (λ i → +-rinv 1f i < snd (+-identity (- 1f)) i) ⟩
          0f          <    - 1f           ⇒⟨ ( λ 0<-1 → ·-preserves-< 0f (- 1f) (- 1f) 0<-1 0<-1) ⟩
          0f · (- 1f) <   (- 1f) · (- 1f) ⇒⟨ transport (cong₂ _<_ (0-leftNullifies (- 1f)) refl) ⟩
          0f          <   (- 1f) · (- 1f) ⇒⟨ transport (λ i → 0f < -commutesWithRight-· (- 1f) (1f)   i ) ⟩
          0f          < -((- 1f) ·    1f )⇒⟨ transport (λ i → 0f < -commutesWithLeft-·  (- 1f)  1f (~ i)) ⟩
          0f          < (-(- 1f))·    1f  ⇒⟨ transport (λ i → 0f < -involutive 1f i · 1f) ⟩
          0f          <      1f  ·    1f  ⇒⟨ transport (λ i → 0f < fst (·-identity 1f) i) ⟩
          0f          <      1f           ⇒⟨ <-trans _ _ _ 1<0 ⟩
          1f          <      1f           ⇒⟨ <-irrefl 1f ⟩
                      ⊥                   ⇒⟨ ⊥-elim ⟩ _ ◼) 1<0
      ... | inr 0<1 = 0<1

  -- Conversely, assume the 10 listed items—in particular, items 4, 5 and 9.
  module back
    -- (item-1      : ∀ x y → x ≤ y → ¬(y < x))
    -- (item-1-back : ∀ x y → ¬(y < x) → x ≤ y)
    -- (item-2      : ∀ x y → x # y → (x < y) ⊎ (y < x))
    -- (item-2-back : ∀ x y → (x < y) ⊎ (y < x) → x # y)
    -- (item-3      : ∀ x y z → x ≤ y → x + z ≤ y + z)
    -- (item-3-back : ∀ x y z → x + z ≤ y + z → x ≤ y)
       (item-4      : ∀ x y z → x < y → x + z < y + z)
    -- (item-4-back : ∀ x y z → x + z < y + z → x < y)
       (item-5      : ∀ x y → 0f < x + y → (0f < x) ⊎ (0f < y))
    -- (item-6      : ∀ x y z → x < y → y ≤ z → x < z)
    -- (item-7      : ∀ x y z → x ≤ y → y < z → x < z)
    -- (item-8      : ∀ x y z → x ≤ y → 0f ≤ z → x · z ≤ y · z)
       (item-9      : ∀ x y z → 0f < z → (x < y → x · z < y · z))
    -- (item-9-back : ∀ x y z → 0f < z → (x · z < y · z → x < y))
    -- (item-10     : 0f < 1f)
    where

    item-4' : ∀ x y → 0f < x - y → y < x
    item-4' x y = (
      0f     <  x - y         ⇒⟨ item-4 0f (x + (- y)) y ⟩
      0f + y < (x - y) + y    ⇒⟨ transport (λ i → snd (+-identity y) i < sym (+-assoc x (- y) y) i) ⟩
           y <  x + (- y + y) ⇒⟨ transport (λ i → y < x + snd (+-inv y) i) ⟩
           y <  x + 0f        ⇒⟨ transport (λ i → y < fst (+-identity x) i)  ⟩
           y <  x ◼)

    lemma : ∀ x y z w → (z +   w) + ((- x)  + (- y)) ≡ (z - x) + (w - y)
    lemma x y z w = (
      -- NOTE: there has to be a shorter way to to this kind of calculations ...
      --       also I got not much introspection while creating the paths
      (z +   w) + ((- x)  + (- y))   ≡⟨ ( λ i → +-assoc z w ((- x)  + (- y)) (~ i)) ⟩
      (z + ( w  + ((- x)  + (- y)))) ≡⟨ ( λ i → z + (+-assoc w (- x) (- y) i)) ⟩
      (z + ((w  +  (- x)) + (- y)))  ≡⟨ ( λ i → z + ((+-comm w (- x) i) + (- y)) ) ⟩
      (z + (((- x) +  w)  + (- y)))  ≡⟨ ( λ i → z + (+-assoc (- x) w (- y) (~ i))) ⟩
      (z + (( - x) + (w - y)))       ≡⟨ ( λ i → +-assoc z (- x) (w  - y) i ) ⟩
      (z - x) + (w - y) ∎)

    -- 6. (†)
    -- In order to show (†), suppose x + y < z + w.
    -- So, by item 4, we get (x + y) − (x + y) < (z + w) − (x + y), that is, 0 < (z − x) + (w − y).
    -- By item 5, (0 < z − x) ∨ (0 < w − y), and so by item 4 in either case, we get x < z ∨ y < w.
    +-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)
    +-<-extensional w x y z = (
      (x + y)           < (z + w)           ⇒⟨ item-4 (x + y) (z + w) (- (x + y)) ⟩
      (x + y) - (x + y) < (z + w) - (x + y)
        ⇒⟨ transport (λ i → +-rinv (x + y) i < (z + w) + (-isDistributive x y) (~ i))    ⟩

                     0f < (z +   w) + ((- x)  + (- y))   ⇒⟨ transport (λ i → 0f < lemma x y z w i) ⟩
                     0f < (z - x) + (w - y) ⇒⟨ item-5 (z - x) (w - y) ⟩
      (0f < z - x) ⊎ (0f < w - y)           ⇒⟨ (λ{ (inl p) → inl (item-4' z x p)
                                                 ; (inr p) → inr (item-4' w y p)}) ⟩
      ( x < z    ) ⊎ ( y < w    ) ◼)

    -- 6. (∗)
    ·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z)
    ·-preserves-< = item-9

-- Lemma 4.1.12. An ordered field (F, 0, 1, +, · , min, max, <) is a constructive field (F, 0, 1, +, · , #).
lemma-4-1-12 :
  -- NOTE: we do a slightly different thing here
  ∀{ℓ ℓ'} (OF : OrderedField {ℓ} {ℓ'}) →
  let open OrderedField OF
  ----------------------------------------------------
  in (IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ)
lemma-4-1-12 {ℓ} {ℓ'} OF = let -- NOTE: for mentioning the ℓ and ℓ' and not taking them as new "variables"
  open OrderedField OF
  in record
   { -- NOTE: see https://agda.readthedocs.io/en/v2.6.1/language/record-types.html#building-records-from-modules
     --       the following line just picks all same-named thigs from the `OrderedField OF` module
     OrderedField OF
     -- NOTE: alternatively we can specify it explicitly (renaming should work with this syntax):
     --         OrderedField OF using (isCommRing; ·-rinv; ·-linv; ·-inv-back)
     -- NOTE: and of course the "normal" syntax would be
     --           isCommRing      = isCommRing
     --         ; ·-rinv          = ·-rinv
     --         ; ·-linv          = ·-linv
     --         ; ·-inv-back      = ·-inv-back
     --
     -- NOTE: We've proved this before
   ; isApartnessRel  = #'-isApartnessRel <-isStrictPartialOrder
     -- We need to show that + is #-extensional, and that # is tight.
     --
     -- First, assume w + x # y + z. We need to show w # y ∨ x # z.
   ; +-#-extensional = λ where
                       -- Consider the case w + x < y + z, so that we can use (†) to obtain w < y ∨ x < z,
                       --   which gives w # y ∨ x # z in either case.
                       w x y z (inl w+x<y+z) → case +-<-extensional _ _ _ _ w+x<y+z of (
                         (_ → (w # y) ⊎ (x # z)) ∋ λ -- NOTE: here we had to add a (return-)type annotation to the λ
                         { (inl w<y) → inl (inl w<y)
                         ; (inr x<z) → inr (inl x<z)
                         })
                       -- The case w + x > y + z is similar.
                       w x y z (inr y+z<w+x) → case  +-<-extensional _ _ _ _ y+z<w+x of (
                         (_ → (w # y) ⊎ (x # z)) ∋ λ
                         { (inl y<w) → inl (inr y<w)
                         ; (inr z<x) → inr (inr z<x)
                         })
     -- NOTE: I got a "Cannot resolve overloaded projection ≤-antisym because it is not applied to a visible argument" for just `≤-antisym` in a goal
     --       because there were multiple `≤-antisym` exported from `OrderedField`
     -- Tightness follows from the fact that ≤ is antisymmetric, combined with the fact
     --   that ¬(P ∨ Q) is equivalent to ¬P ∧ ¬Q.
   ; #-tight         = λ x y ¬[x<y]⊎¬[y<x] → let (¬[x<y] , ¬[y<x]) = deMorgan₂ ¬[x<y]⊎¬[y<x]
                                             in  ≤-antisym _ _ ¬[y<x] ¬[x<y]
   }

-- We will mainly be concerned with ordered fields, as opposed to the more general con-
-- structive fields. This is because the Archimedean property can be phrased straightforwardly
-- for ordered fields, as in Section 4.3, and because the ordering relation allows us to define loca-
-- tors, as in Chapter 6.
-- 
-- We have defined ordered fields, which capture the algebraic structure of the real numbers.

-- 4.2 Rationals
-- ...
-- NOTE: we have in cubical
--   import Cubical.HITs.Rationals.HITQ
--     ℚ as a higher inductive type
--   import Cubical.HITs.Rationals.QuoQ
--     ℚ as a set quotient of ℤ × ℕ₊₁ (as in the HoTT book)
--   import Cubical.HITs.Rationals.SigmaQ
--     ℚ as the set of coprime pairs in ℤ × ℕ₊₁

-- 4.3 Archimedean property
--
-- We now define the notion of Archimedean ordered fields. We phrase this in terms of a certain
-- interpolation property, that can be defined from the fact that there is a unique morphism of
-- ordered fields from the rationals to every ordered field.

-- Definition 4.3.1.
-- A morphism from an ordered field (F, 0F , 1F , +F , ·F , minF , maxF , <F )
--              to an ordered field (G, 0G , 1G , +G , ·G , minG , maxG , <G )
-- is a map f : F → G such that
-- 1. f is a morphism of rings,
-- 2. f reflects < in the sense that for every x, y : F
--    f (x) <G f (y) ⇒ x <F y.

-- NOTE: see Cubical.Structures.Group.Morphism
--       and Cubical.Structures.Group.MorphismProperties

-- open import Cubical.Structures.Group.Morphism
open import Cubical.Structures.Ring

record IsRingHom
  {ℓ ℓ'}
  (F : Ring {ℓ}) (G : Ring {ℓ'})
  (f : (Ring.Carrier F) → (Ring.Carrier G)) : Type (ℓ-max ℓ ℓ')
  where
  module F = Ring F
  module G = Ring G
  field
    preserves-+ : ∀ a b → f (a F.+ b) ≡ f a G.+ f b
    preserves-· : ∀ a b → f (a F.· b) ≡ f a G.· f b
    perserves-1 : f F.1r ≡ G.1r

record IsOrderedFieldHom
  {ℓ ℓ' ℓₚ ℓₚ'} -- NOTE: this is a lot of levels. Can we get rid of some of these?
  (F : OrderedField {ℓ} {ℓₚ}) (G : OrderedField {ℓ'} {ℓₚ'})
  -- NOTE: `let` is not allowed in a telescope
  --       this was also mentioned in previous github issue about module parameter fixities
  -- (let module F = OrderedField F)
  -- (let module G = OrderedField G)
  (f : (OrderedField.Carrier F) → (OrderedField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  module F = OrderedField F
  module G = OrderedField G
  field
    -- NOTE: the following works, because OrderedField shares all of the same-named properties of Ring
    --       but if this would not be the case, then we could just rename this with the `renaming` syntax
    --       either here, directly or just above
    isRingHom : IsRingHom (record {F}) (record {G}) f
    reflects-< : ∀ x y → f x G.< f y → x F.< y
  -- NOTE: for properties, see https://en.wikipedia.org/wiki/Ring_homomorphism#Properties
    
record OrderedFieldHom {ℓ ℓ' ℓₚ ℓₚ'} (F : OrderedField {ℓ} {ℓₚ}) (G : OrderedField {ℓ'} {ℓₚ'}) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ')) where
  constructor grouphom
  module F = OrderedField F
  module G = OrderedField G
  field
    fun : F.Carrier → G.Carrier
    isOrderedFieldHom : IsOrderedFieldHom F G fun

-- Remark 4.3.2. The contrapositive of reflecting < means preserving ≤.

-- Lemma 4.3.3. For every ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ), there is a unique morphism
-- i of ordered fields from the rationals to F . Additionally, i preserves < in the sense that for every q, r : Q
--   q < r ⇒ i (q) < F i (r ).

-- isContr : Type ℓ → Type ℓ
-- isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)


-- near questions:
--
-- 1. can we continue the same patterns for morphisms as we have with the other structures?
-- 2. what machinery is necessary to express unique existence? (there is ∃! in the standard library)
-- 3. trichotomy of ordered fields ... do we have this? (you write the rationals have)
--
-- far questions:
--
-- - approaches to limits and spaces for mathematical analysis
--   - locales? for topological spaces
--     Also a few years ago I was told that "locales" it the alternative to topological spaces
--     while
--   - limits and filters (see HOL)
--     Some time ago I heard "on the streets" that filters are "not cool" amongst constructive mathematicians but I
--     is that a "thing" or did I just misheard that
-- (un)bounded linear operators, adjoints and bounds

import Cubical.Data.Sigma.Base


-- most of my types are contractible ... not
-- cohesive type theory has a builtin notion of real number
--  balance between continuity and discontinuity
-- therefore it is better suited to do differential geometry and alike

-- classical mathematical starting point
--   locally euclidean, charts, atlasses
-- univalent starting point
--   two manifolds are diffeomorphic exactly when they are equal
--   a function between manifolds is a diffeomorphism
