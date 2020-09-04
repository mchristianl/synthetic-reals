{-# OPTIONS --cubical --no-import-sorts  #-}


open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)

open import Cubical.Structures.Group
-- import Cubical.Structures.Group.Properties

module MorePropAlgebra.Properties.Group {ℓ} (G : Group {ℓ}) where
  open Group G
  private
    simplR = GroupLemmas.simplR G

  invUniqueL : {g h : Carrier} → g + h ≡ 0g → g ≡ - h
  invUniqueL {g} {h} p = simplR h (p ∙ sym (invl h))

  -- ported from `Algebra.Properties.Group`
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
