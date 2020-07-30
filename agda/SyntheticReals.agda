{-# OPTIONS --cubical --no-import-sorts #-}

module SyntheticReals where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

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
-- open import Function.Reasoning using (∋-syntax)
open import Function.Base using (it) -- instance search

open import Utils
open import MoreLogic
open MoreLogic.Reasoning
open MoreLogic.Properties
open import MoreAlgebra
open MoreAlgebra.Definitions
open MoreAlgebra.Consequences
open import Bundles
-- open MoreAlgebra.Properties.Group

-- https://www.cs.bham.ac.uk/~abb538/thesis.pdf
-- Booij 2020 - Analysis in Univalent Type Theory

-- Lemma 4.1.6.
import Properties.ConstructiveField

-- Lemma 4.1.11.
import Properties.AlmostOrderedField

-- Lemma 4.1.12. An ordered field (F, 0, 1, +, · , min, max, <) is a constructive field (F, 0, 1, +, · , #).
lemma-4-1-12 :
  -- NOTE: we do a slightly different thing here
  ∀{ℓ ℓ'} (OF : OrderedField {ℓ} {ℓ'}) →
  let open OrderedField OF
  ----------------------------------------------------
  in (IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ)
lemma-4-1-12 {ℓ} {ℓ'} OF = let -- NOTE: for mentioning the ℓ and ℓ' and not taking them as new "variables" we bring them into scope
  open OrderedField OF
  in record -- We need to show that + is #-extensional, and that # is tight.
   { OrderedField OF
   ; isApartnessRel  = #'-isApartnessRel <-isStrictPartialOrder -- NOTE: We've proved this before
   
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

     -- Tightness follows from the fact that ≤ is antisymmetric, combined with the fact
     --   that ¬(P ∨ Q) is equivalent to ¬P ∧ ¬Q.
   ; #-tight         = λ x y ¬[x<y]⊎¬[y<x] → let (¬[x<y] , ¬[y<x]) = deMorgan₂' ¬[x<y]⊎¬[y<x]
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

-- Lemma 4.3.3. For every ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ), there is a unique morphism
-- i of ordered fields from the rationals to F . Additionally, i preserves < in the sense that for every q, r : Q
--   q < r ⇒ i (q) < F i (r ).


