{-# OPTIONS --cubical --no-import-sorts #-}

module Booij where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ)
open import Cubical.Structures.CommRing
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sigma.Base
open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
open import Cubical.Structures.Poset


-- TODO: merge the notes with Hit.agda
-- there seems to be a convention that
--   We will adopt the convention of denoting the level of the carrier
--   set by ℓ₀ and the level of the relation result by ℓ₁.

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
    ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    +-#-extensional : (w x y z : F) → (w + x) # (y + z) → (w # y) ⊎ (x # z)
    isApartnessRel : IsApartnessRel _#_

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsApartnessRel isApartnessRel public
    renaming
      ( isIrrefl  to #-irrefl
      ; isSym     to #-sym
      ; isCotrans to #-cotrans )

record ConstructiveField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
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

-- Lemma 4.1.6.
-- For a constructive field (F, 0, 1, +, ·, #), the following hold.
-- 1. 1 # 0.
-- 2. Addition + is #-compatible in the sense that for all x, y, z : F
--    x # y ⇔ x + z # y + z.
-- 3. Multiplication · is #-extensional in the sense that for all w, x, y, z : F
--    w · x # y · z ⇒ w # y ∨ x # z.
module Lemmas-4-6-1 (F : ConstructiveField {ℓ} {ℓ'}) where

  open import Function.Base using (it) -- instance search
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

  -- a few facts about rings that might be collected from elsewhere
  a+b-b≡a : ∀ a b → a ≡ (a + b) - b
  a+b-b≡a a b = let P = sym (fst (+-inv b))
                    Q = sym (fst (+-identity a))
                    R = transport (λ i → a ≡ a + P i) Q
                    S = transport (λ i → a ≡ (+-assoc a b (- b)) i ) R
                in S

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
  ... | inr  -z#-z  = ⊥-elim (#-irrefl _ _ -z#-z -z#-z) 

  -- The other direction is similar.
  +-#-compatible-inv : ∀(x y z : Carrier) → x + z # y + z → x # y
  +-#-compatible-inv _ _ _ x+z#y+z with +-#-extensional _ _ _ _ x+z#y+z
  ... | inl x#y = x#y
  ... | inr z#z = ⊥-elim (#-irrefl _ _ z#z z#z)

  -- NOTE: some syntax for "implicational" reasoning
  infix  3 _◼ -- for a list of unicode symbols in agda, see https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html
  infixr 2 _⇒⟨_⟩_

  _⇒⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : Type ℓ'} {R : Type ℓ''} → (P : Type ℓ) → (P → Q) → (Q → R) → (P → R)
  _ ⇒⟨ pq ⟩ qr = qr ∘ pq

  _◼ : ∀{ℓ} (A : Type ℓ) → A → A
  _ ◼ = λ x → x

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

_#'_ : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → Rel X X ℓ'
_#'_ {_<_ = _<_} x y = (x < y) ⊎ (y < x)

swap : ∀{x : Type ℓ} {y : Type ℓ'} → x ⊎ y → y ⊎ x
swap (inl x) = inr x
swap (inr x) = inl x

#'-isApartnessRel : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → IsStrictPartialOrder _<_ → IsApartnessRel (_#'_ {_<_ = _<_})
#'-isApartnessRel {X = X} {_<_ = _<_} isSPO =
  -- decompose record: see https://agda.readthedocs.io/en/v2.6.1/language/let-and-where.html#let-record-pattern
  let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
  in λ where -- anonymous copattern-matching lambda: see https://agda.readthedocs.io/en/v2.6.1/language/record-types.html
    -- clauses work here and case-split does also work!
    -- but I get a "Not implemented: The Agda synthesizer (Agsy) does not support copatterns yet" on proof search
    --.IsApartnessRel.isIrrefl a b a#b (inl b<a) → <-isIrrefl b a b<a {!!}
    --.IsApartnessRel.isIrrefl a b a#b (inr a<b) → {!!}
    .IsApartnessRel.isIrrefl a b (inl a<b) → {!!}
    .IsApartnessRel.isIrrefl a b (inr b<a) → {!!}
    .IsApartnessRel.isSym     → {!!}
    .IsApartnessRel.isCotrans → {!!}

-- 2. we have a preorder defined by
--    x ≤ y := ¬(y < x).
-- 
-- Definition 4.1.8.
-- Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
--   z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
-- and max computes least upper bounds in the sense that for every x, y, z : A, we have
--   max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.
-- 
-- Remark 4.1.9.
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
-- 2. < is a strict order;
-- 3. x : F has a multiplicative inverse iff x # 0, recalling that # is defined as in Lemma 4.1.7;
-- 4. ≤, as in Lemma 4.1.7, is antisymmetric, so that (F, ≤) is a partial order;
-- 5. (F, ≤, min, max) is a lattice.
-- 6. for all x, y, z, w : F:
--    x + y < z + w ⇒ x < z ∨ y < w, (†)
--    0 < z ∧ x < y ⇒ x z < y z.     (∗)
-- Our notion of ordered fields coincides with The Univalent Foundations Program [89, Definition 11.2.7].
-- 
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


-- we have in cubical
--   import Cubical.HITs.Rationals.HITQ
--     ℚ as a higher inductive type
--   import Cubical.HITs.Rationals.QuoQ
--     ℚ as a set quotient of ℤ × ℕ₊₁ (as in the HoTT book)
--   import Cubical.HITs.Rationals.SigmaQ
--     ℚ as the set of coprime pairs in ℤ × ℕ₊₁
