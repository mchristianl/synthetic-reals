{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Consequences where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic

open import Utils
open import MoreLogic.Definitions
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions
open import MorePropAlgebra.Consequences
open import MorePropAlgebra.Structures
open import MorePropAlgebra.Bundles
open import Number.Definitions

-- import Cubical.HITs.Rationals.SigmaQ as ℚ*
-- import Cubical.Data.Nat.Coprime as Coprime
open import Cubical.HITs.Rationals.QuoQ renaming
  ( [_] to [_]ᶠ
  ; _+_ to _+ᶠ_
  ; -_  to -ᶠ_
  ; _*_ to _*ᶠ_
  ; +-assoc to +-assocᶠ
  ; +-comm  to +-commᶠ
  ; *-assoc to *-assocᶠ
  ; *-comm  to *-commᶠ
  )
-- open import Cubical.Data.Nat.Literals public
--
-- instance
--   fromNatℚ : HasFromNat ℚ
--   fromNatℚ = record { Constraint = λ _ → Unit ; fromNat = λ n → [ pos n / 1 ] }
--
-- instance
--   fromNegℚ : HasFromNeg ℚ
--   fromNegℚ = record { Constraint = λ _ → Unit ; fromNeg = λ n → [ neg n / 1 ] }

open import Cubical.HITs.SetQuotients renaming ([_] to [_]ˢ)

-- Define the integers as a HIT by identifying +0 and -0
import Cubical.HITs.Ints.QuoInt
import Cubical.Data.NatPlusOne


open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣
import Cubical.HITs.PropositionalTruncation.Properties as PTrunc

-- -- Set quotients as a higher inductive type:
-- data _/_ {ℓ ℓ'} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
--   [_] : (a : A) → A / R
--   eq/ : (a b : A) → (r : R a b) → [ a ] ≡ [ b ]
--   squash/ : (x y : A / R) → (p q : x ≡ y) → p ≡ q

-- {-# DISPLAY [_]' (Cubical.HITs.Ints.QuoInt.signed Agda.Builtin.Bool.Bool.false 1 / Cubical.Data.NatPlusOne.1+ 0 )= 1ᶠ #-}

{-

we have most properties in `Cubical.HITs.Rationals.QuoQ.Properties`

but we can use `Quoℚ≡Sigmaℚ : Quo.ℚ ≡ Sigma.ℚ` from `Cubical.HITs.Rationals.SigmaQ.Properties`

-}


open import Cubical.Data.Nat as ℕ using (discreteℕ; ℕ; suc; zero)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.Ints.QuoInt hiding (+-identityʳ; *-identityʳ; *-identityˡ; *-distribˡ;*-distribʳ) -- using (ℤ)

-- there is `elimProp` in `Cubical.HITs.SetQuotients` to define properties

-- elimProp {A = ℤ × ℕ₊₁} {R = _∼_} {B = λ(x : ℚ) → ?} ?

-- e.g. we have
-- _∼_ : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → Type₀
-- (a , b) ∼ (c , d) = a * ℕ₊₁→ℤ d ≡ c * ℕ₊₁→ℤ b

open import Cubical.Data.Nat.Order using () renaming (_<_ to _<ⁿ_)

_<ᶻ'_ : ℤ → ℤ → Type₀
_<ᶻ'_ (ℤ.signed s n) b = {!   !}
_<ᶻ'_ (ℤ.posneg i)   b = {!   !}

_<ᶠ''_ : (ℤ × ℕ₊₁) → (ℤ × ℕ₊₁) → Type₀
(aᶻ , aⁿ⁺¹) <ᶠ'' (bᶻ , bⁿ⁺¹) = {! a * ℕ₊₁→ℤ d <ᶻ' c * ℕ₊₁→ℤ b  !}

_<ᶠ'_ : ℚ → ℚ → _
x <ᶠ' y = elimProp2 {A = ℤ × ℕ₊₁} {R = _∼_} {C = C} γ κ x y
  where
  φ : ℚ → ℚ → hProp ℓ-zero
  φ x y = {!   !}
  C : ℚ → ℚ → Type
  C x y = [ φ x y ]
  γ : (x y : ℚ) → isProp (C x y)
  γ x y = {!   !}
  κ : (a b : ℤ × ℕ₊₁) → C [ a ]ᶠ [ b ]ᶠ
  κ a b = {!   !}

_<ᶠ_ : hPropRel ℚ ℚ ℓ-zero
x <ᶠ y = {! elimProp2 {A = ℤ × ℕ₊₁} {R = _∼_} {C = C} γ κ x y   !}
  where
  φ : ℚ → ℚ → hProp ℓ-zero
  φ x y = {!   !}
  C : ℚ → ℚ → Type
  C x y = [ φ x y ]
  γ : (x y : ℚ) → isProp (C x y)
  γ x y = {!   !}
  κ : (a b : ℤ × ℕ₊₁) → C [ a ]ᶠ [ b ]ᶠ
  κ a b = {!   !}

-- and there is `onCommonDenom` in `Cubical.HITs.Rationals.QuoQ.Properties` to define operations

-- open import Cubical.HITs.Ints.QuoInt.Base renaming



_*ᶻ_ = Cubical.HITs.Ints.QuoInt._*_
-- signᶻ = Cubical.HITs.Ints.QuoInt.sign

open import Data.Nat.Base using () renaming
  ( _⊔_ to maxⁿ
  ; _⊓_ to minⁿ
  )

-- NOTE: in `Cubical.HITs.Ints.QuoInt.Base` there is
--         Int→ℤ : Int → ℤ
--         ℤ→Int : ℤ → Int
--         Int≡ℤ : Int ≡ ℤ

open import Cubical.Data.Int using () renaming (pos to ℕ→Int)

ℕ→ℤ : ℕ → ℤ
ℕ→ℤ x = Int→ℤ (ℕ→Int x)


minᶻ : ℤ → ℤ → ℤ
minᶻ x y with sign x | sign y
... | spos | spos = pos (minⁿ (abs x) (abs y))
... | spos | sneg = y
... | sneg | spos = x
... | sneg | sneg = neg (maxⁿ (abs x) (abs y)) -- instead of `- ℕ→ℤ (maxⁿ ...)`

-- maxⁿ' : ℕ → ℕ → ℕ
-- maxⁿ' (zero ) (n    ) = n
-- maxⁿ' (suc m) (zero ) = suc m
-- maxⁿ' (suc m) (suc n) = suc (maxⁿ' m n)
--
-- minⁿ' : ℕ → ℕ → ℕ
-- minⁿ' (zero ) (n    ) = zero
-- minⁿ' (suc m) (zero ) = zero
-- minⁿ' (suc m) (suc n) = suc (minⁿ' m n)

maxⁿ≡0-right : ∀ n  → maxⁿ n 0 ≡ n
maxⁿ≡0-right zero    = refl
maxⁿ≡0-right (suc n) = refl

minⁿ≡0-right : ∀ n  → minⁿ n 0 ≡ 0
minⁿ≡0-right zero    = refl
minⁿ≡0-right (suc n) = refl


lemma : ∀ n → pos 0 ≡ neg (minⁿ n 0)
lemma n = posneg ∙ (λ j → neg (minⁿ≡0-right n (~ j)))
-- lemma n = posneg ∙ (λ j → neg (minⁿ≡0-right n (~ j)))

-- i = i0 ⊢ pos 0
-- i = i1 ⊢ lemma 0 j
-- j = i0 ⊢ pos 0
-- j = i1 ⊢ posneg i
--
-- ———— Constraints ———————————————————————————————————————————
-- posneg i = ?11 (j = i1) : ℤ
-- pos 0 = ?11 (j = i0) : ℤ
-- hcomp (doubleComp-faces (λ _ → pos 0) (λ j₁ → neg zero) j) (posneg j) = ?11 (i = i1) : ℤ
-- pos 0 = ?11 (i = i0) : ℤ

maxᶻ : ℤ → ℤ → ℤ
maxᶻ (pos n₀) (pos n₁) = pos (maxⁿ n₀ n₁)
maxᶻ (pos n₀) (neg n₁) = pos n₀
maxᶻ (neg n₀) (pos n₁) = pos n₁
maxᶻ (neg n₀) (neg n₁) = neg (minⁿ n₀ n₁)
-- pathes
maxᶻ (pos    n) (posneg i) = pos (maxⁿ≡0-right n i)
maxᶻ (neg zero) (posneg i) = posneg i -- `lemma zero i` does not work here
-- NOTE: better not use `lemma (suc n) i` because it creates an unnormalizable term:
--   `hcomp (doubleComp-faces (λ _ → pos 0) (λ j₁ → neg 0) j) (posneg j)`
maxᶻ (neg (suc n)) (posneg i) = posneg i -- lemma (suc n) i -- can also use `posneg i` here
maxᶻ (posneg i) (pos    n) = pos n
maxᶻ (posneg i) (neg    n) = posneg i
maxᶻ (posneg i) (posneg j) = posneg (i ∧ j) -- posneg (i ∧ j)

maxᶻ' : ℤ → ℤ → ℤ
maxᶻ' x y with sign x | sign y
... | spos | spos = pos (maxⁿ (abs x) (abs y))
... | spos | sneg = x
... | sneg | spos = y
... | sneg | sneg = neg (minⁿ (abs x) (abs y))

-- sign' : ℤ → Sign
-- sign' (signed _ zero) = spos
-- sign' (signed s (suc _)) = s
-- sign' (posneg i) = spos

lemma2 : ∀ x y → maxᶻ x y ≡ maxᶻ' x y
lemma2 (pos  zero   ) (pos  zero   ) = refl
lemma2 (pos  zero   ) (pos (suc n₁)) = refl
lemma2 (pos (suc n₀)) (pos  zero   ) = refl
lemma2 (pos (suc n₀)) (pos (suc n₁)) = refl
lemma2 (pos  zero   ) (neg  zero   ) = refl
lemma2 (pos  zero   ) (neg (suc n₁)) = refl
lemma2 (pos (suc n₀)) (neg  zero   ) = refl
lemma2 (pos (suc n₀)) (neg (suc n₁)) = refl
lemma2 (neg  zero   ) (pos  zero   ) = refl
lemma2 (neg  zero   ) (pos (suc n₁)) = refl
lemma2 (neg (suc n₀)) (pos  zero   ) = refl
lemma2 (neg (suc n₀)) (pos (suc n₁)) = refl
lemma2 (neg  zero   ) (neg  zero   ) = sym posneg
lemma2 (neg  zero   ) (neg (suc n₁)) = refl
lemma2 (neg (suc n₀)) (neg  zero   ) = refl
lemma2 (neg (suc n₀)) (neg (suc n₁)) = refl
lemma2 (pos  zero   ) (posneg   j  ) = refl
lemma2 (pos (suc n₀)) (posneg   j  ) = refl
lemma2 (neg  zero   ) (posneg   j  ) = λ i → posneg (j ∧ (~ i))
lemma2 (neg (suc n₀)) (posneg   j  ) = refl
lemma2 (posneg   i  ) (pos  zero   ) = refl
lemma2 (posneg   i  ) (pos (suc n₁)) = refl
lemma2 (posneg   i  ) (neg  zero   ) = λ j → posneg (i ∧ (~ j))
lemma2 (posneg   i  ) (neg (suc n₁)) = refl
lemma2 (posneg   i  ) (posneg   j  ) = λ k → posneg (i ∧ j ∧ (~ k))

-- maxᶻ (signed s₀ n₀) (signed s₁ n₁) = {!   !}
-- maxᶻ (signed s₀ n₀) (posneg j) = {!   !}
-- maxᶻ (posneg i) (signed s₁ n₁) = {!   !}
-- maxᶻ (posneg i) (posneg j) = {!   !}

minᶠ : ℚ → ℚ → ℚ
minᶠ x y = onCommonDenom f g h x y where
  f : ℤ × ℕ₊₁ → ℤ × ℕ₊₁ → ℤ
  f a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) = minᶻ (aᶻ *ᶻ (ℕ₊₁→ℤ bⁿ)) (bᶻ *ᶻ (ℕ₊₁→ℤ aⁿ))
  g : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
    → aᶻ *ᶻ (ℕ₊₁→ℤ bⁿ) ≡ bᶻ *ᶻ (ℕ₊₁→ℤ aⁿ)
    → (ℕ₊₁→ℤ bⁿ) *ᶻ (f a c) ≡ (ℕ₊₁→ℤ aⁿ) *ᶻ (f b c)
  g a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) aᶻ*bⁿ≡bᶻ*aⁿ = {!    !}
  h : (a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) : ℤ × ℕ₊₁)
    → bᶻ *ᶻ (ℕ₊₁→ℤ cⁿ) ≡ cᶻ *ᶻ (ℕ₊₁→ℤ bⁿ)
    → (f a b) *ᶻ (ℕ₊₁→ℤ cⁿ) ≡ (f a c) *ᶻ (ℕ₊₁→ℤ bⁿ)
  h a@(aᶻ , aⁿ) b@(bᶻ , bⁿ) c@(cᶻ , cⁿ) bᶻ*cⁿ≡cᶻ*bⁿ = {!   !}

maxᶠ : ℚ → ℚ → ℚ
maxᶠ x y = {!   !}

0ᶠ 1ᶠ : ℚ
0ᶠ = 0
1ᶠ = 1

<-irreflᶠ       : (a       : ℚ) → [ ¬ (a <ᶠ a) ]
<-transᶠ        : (a b x   : ℚ) → [ a <ᶠ b ] → [ b <ᶠ x ] → [ a <ᶠ x ]
<-cotransᶠ      : (a b     : ℚ) → [ a <ᶠ b ] → (x : ℚ) → [ (a <ᶠ x) ⊔ (x <ᶠ b) ]
·ᶠ-inv''        : (x       : ℚ) → (∥ Σ[ y ∈ ℚ ] x *ᶠ y ≡ 1ᶠ ∥ → [ x <ᶠ 0ᶠ ] ⊎ [ 0ᶠ <ᶠ x ]) × ([ x <ᶠ 0ᶠ ] ⊎ [ 0ᶠ <ᶠ x ] → ∥ Σ[ y ∈ ℚ ] x *ᶠ y ≡ 1ᶠ ∥)
≤-reflᶠ         : (a       : ℚ) → [ ¬ (a <ᶠ a) ]
≤-antisymᶠ      : (a b     : ℚ) → [ ¬ (b <ᶠ a) ] → [ ¬ (a <ᶠ b) ] → [ a ≡ₚ b ]
≤-transᶠ        : (a b x   : ℚ) → [ ¬ (b <ᶠ a) ] → [ ¬ (x <ᶠ b) ] → [ ¬ (x <ᶠ a) ]
is-minᶠ         : (x y z   : ℚ) → [ ¬ (minᶠ x y <ᶠ z) ⇔ ¬ (x <ᶠ z) ⊓ ¬ (y <ᶠ z) ]
is-maxᶠ         : (x y z   : ℚ) → [ ¬ (z <ᶠ maxᶠ x y) ⇔ ¬ (z <ᶠ x) ⊓ ¬ (z <ᶠ y) ]
+ᶠ-<ᶠ-ext       : (w x y z : ℚ) → [ (w +ᶠ x) <ᶠ (y +ᶠ z) ] → [ (w <ᶠ y) ⊔ (x <ᶠ z) ]
·ᶠ-preserves-<ᶠ : (x y z   : ℚ) → [ 0ᶠ <ᶠ z ] → [ x <ᶠ y ] → [ (x *ᶠ z) <ᶠ (y *ᶠ z) ]

<-irreflᶠ       = {!   !}
<-transᶠ        = {!   !}
<-cotransᶠ      = {!   !}
·ᶠ-inv''        = {!   !}
≤-reflᶠ         = {!   !}
≤-antisymᶠ      = {!   !}
≤-transᶠ        = {!   !}
is-minᶠ         = {!   !}
is-maxᶠ         = {!   !}
+ᶠ-<ᶠ-ext       = {!   !}
·ᶠ-preserves-<ᶠ = {!   !}

open PartiallyOrderedField

ℚF : PartiallyOrderedField {ℓ-zero} {ℓ-zero}
ℚF .PartiallyOrderedField.Carrier                  = ℚ
ℚF .PartiallyOrderedField.0f                       = 0 -- [ signed spos 0 , (1+ 0) ]'
ℚF .PartiallyOrderedField.1f                       = 1
ℚF .PartiallyOrderedField._+_                      = _+ᶠ_
ℚF .PartiallyOrderedField.-_                       = -ᶠ_
ℚF .PartiallyOrderedField._·_                      = _*ᶠ_
ℚF .PartiallyOrderedField.min                      = minᶠ
ℚF .PartiallyOrderedField.max                      = maxᶠ
ℚF .PartiallyOrderedField._<_                      = _<ᶠ_
ℚF .PartiallyOrderedField.is-PartiallyOrderedField = record
  { is-AlmostPartiallyOrderedField  = record
    { is-set               = isSetℚ
    ; is-CommRing          = record
      { is-set  = isSetℚ
      ; is-Ring = record
        { is-set    = isSetℚ
        ; +-AbGroup = record
          { is-set   = isSetℚ
          ; is-Group = record
            { is-set     = isSetℚ
            ; is-Monoid  = record
              { is-set       = isSetℚ
              ; is-Semigroup = record
                { is-set   = isSetℚ
                ; is-assoc = +-assocᶠ
                }
              ; is-identity  = λ x → +-identityʳ x , +-identityˡ x
              }
            ; is-inverse = λ x → (+-inverseʳ x) , (+-inverseˡ x)
            }
          ; is-comm  = +-commᶠ
          }
        ; ·-Monoid  = record
          { is-set       = isSetℚ
          ; is-Semigroup = record
            { is-set   = isSetℚ
            ; is-assoc = *-assocᶠ
            }
          ; is-identity  = λ x → *-identityʳ x , *-identityˡ x
          }
        ; is-dist   = λ x y z → sym (*-distribˡ x y z) , sym (*-distribʳ x y z)
        }
      ; ·-comm  = *-commᶠ
      }
    ; <-StrictPartialOrder = record
      { is-irrefl  = <-irreflᶠ
      ; is-trans   = <-transᶠ
      ; is-cotrans = <-cotransᶠ
      }
    ; ·-inv''              = ·ᶠ-inv''
    ; ≤-isLattice          = record
      { ≤-PartialOrder = record
        { is-refl    = ≤-reflᶠ
        ; is-antisym = ≤-antisymᶠ
        ; is-trans   = ≤-transᶠ
        }
      ; is-min         = is-minᶠ
      ; is-max         = is-maxᶠ
      }
    }
  ; +-<-ext                         = +ᶠ-<ᶠ-ext
  ; ·-preserves-<                   = ·ᶠ-preserves-<ᶠ
  }
  where open PartiallyOrderedField ℚF renaming (Carrier to ℚ')

-- 4.3 Archimedean property
--
-- We now define the notion of Archimedean ordered fields. We phrase this in terms of a certain
-- interpolation property, that can be defined from the fact that there is a unique morphism of
-- ordered fields from the rationals to every ordered field.

-- Lemma 4.3.3. For every ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ), there is a unique morphism
-- i of ordered fields from the rationals to F . Additionally, i preserves < in the sense that for every q, r : Q
--   q < r ⇒ i (q) < F i (r ).

-- ∃! : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
-- ∃! A B = isContr (Σ A B)

-- isContr' A = Σ[ x ∈ A ] (∀ y → x ≡ y)

-- ℚ-IsInitialObject : ∀(OF : OrderedField {ℓ} {ℓ'}) → isContr (OrderedFieldMor ℚOF OF)
-- ℚ-IsInitialObject OF = {!!} , {!!}

-- Definition 4.3.5. Let (F, 0 F , 1 F , + F , · F , min F , max F , < F ) be an ordered field, so that we get a
-- canonical morphism i : Q → F of ordered fields, as in Lemma 4.3.3. We say the ordered field
-- (F, 0 F , 1 F , + F , · F , min F , max F , < F ) is Archimedean if
--   (∀x, y : F )(∃q : Q)x < i (q) < y.

-- IsArchimedian : OrderedField {ℓ} {ℓ'} → Type (ℓ-max ℓ ℓ')
-- IsArchimedian OF = let (orderedfieldmor i _) = fst (ℚ-IsInitialObject OF)
--                        open OrderedField OF
--                        ℚ = OrderedField.Carrier ℚOF
--                    in ∀ x y → ∃[ q ∈ ℚ ] (x < i q) × (i q < y)

-- If the ordered field is clear from the context, we will identify rationals q : Q with their in-
-- clusion i (q) in the ordered field, so that we may also say that (F, 0 F , 1 F , + F , · F , min F , max F , < F )
-- is Archimedean if
-- (∀x, y : F )(∃q : Q)x < q < y.

-- Example 4.3.6. In an Archimedean ordered field, all numbers are bounded by rationals. That
-- is, for a given x : F , there exist q, r : Q with q < x < r .

-- Example-4-3-6 : (OF : OrderedField {ℓ} {ℓ'})
--               → IsArchimedian OF
--               → let open OrderedField OF renaming (Carrier to F)
--                     (orderedfieldmor i _) = fst (ℚ-IsInitialObject OF)
--                     ℚ = OrderedField.Carrier ℚOF
--                 in ∀(x : F) → (∃[ q ∈ ℚ ] i q < x) × (∃[ r ∈ ℚ ] x < i r)
-- -- This follows from applying the Archimedean property to x − 1 < x and x < x + 1.
-- Example-4-3-6 OF isArchimedian = {!!}

-- 4.4 Cauchy completeness of real numbers
--
-- We focus on Cauchy completeness, rather than Dedekind or Dedekind-MacNeille completeness,
-- as we will focus on the computation of digit expansions, for which Cauchy completeness suffices.

-- In order to state that an ordered field is Cauchy complete, we need to define when sequences
-- are Cauchy, and when a sequence has a limit. We also take the opportunity to define
-- the set of Cauchy reals in Definition 4.4.9. Surprisingly, this ordered field cannot be shown to
-- be Cauchy complete.

-- Fix an ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ).
module _ {ℓ ℓ'} (OF : PartiallyOrderedField {ℓ} {ℓ'}) where
  open PartiallyOrderedField OF renaming (Carrier to F)
  -- module ℚ = PartiallyOrderedField ℚ
  {-
  open PartiallyOrderedField ℚOF using () renaming (_<_ to _<ᵣ_; 0f to 0ᵣ)
  ℚ = PartiallyOrderedField.Carrier ℚOF
  iᵣ = PartiallyOrderedFieldMor.fun (fst (ℚ-IsInitialObject OF))
  open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)

  -- We get a notion of distance, given by the absolute value as
  --   |x − y| := max F (x − y, −(x − y)).

  distance : ∀(x y : F) → F
  distance x y = max (x - y) (- (x - y))

  -- Consider a sequence x : N → F of elements of F . Classically, we may state that x is Cauchy as
  -- (∀ε : Q + )(∃N : N)(∀m, n : N)m, n ≥ N ⇒ |x m − x n | < ε,
  IsCauchy : (x : ℕ → F) → Type (ℓ-max ℓ' ℚℓ)
  IsCauchy x = ∀(ε : ℚ) → 0ᵣ <ᵣ ε → ∃[ N ∈ ℕ ] ∀(m n : ℕ) → N ≤ₙ m → N ≤ₙ n → distance (x m) (x n) < iᵣ ε

  -- We can interpret the quantifiers as in Definition 2.4.5.
  -- NOTE: this is the case, since `∃ A B = ∥ Σ A B ∥`

  -- Following a propositions-as-types interpretation, we may also state that x is Cauchy as the
  -- structure
  -- (Πε : Q + )(ΣN : N)(Πm, n : N)m, n ≥ N → |x m − x n | < ε.

  -- The dependent sum represents a choice of index N for every error ε, and so we have arrived at the following definition.

  -- Definition 4.4.1.
  -- For a sequence of reals x : N → F , a a modulus of Cauchy convergence is a map M : Q + → N such that
  -- (∀ε : Q + )(∀m, n : N)m, n ≥ M (ε) ⇒ |x m − x n | < ε.

  -- NOTE: do we already call these x "reals" ?
  -- NOTE: we are using the Modulus-type `((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ)` a few times and might abbreviate it

  IsModulusOfCauchyConvergence : (x : ℕ → F) → (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ)) → Type (ℓ-max ℓ' ℚℓ)
  IsModulusOfCauchyConvergence x M = ∀(ε : ℚ) → (p : 0ᵣ <ᵣ ε) → ∀(m n : ℕ)
                                   → let instance _ = p
                                     in M ε ≤ₙ m → M ε ≤ₙ n → distance (x m) (x n) < iᵣ ε

  -- In constructive mathematics, we typically use such sequences with modulus, for example,
  -- because they can sometimes be used to compute limits of Cauchy sequences, avoiding choice axioms.

  -- Definition 4.4.2.
  -- A number l : F is the limit of a sequence x : N → F if the sequence
  -- converges to l in the usual sense:
  --   (∀ε : Q + )(∃N : N)(∀n : N)n ≥ N ⇒ |x n − l | < ε.

  IsLimit : (x : ℕ → F) → (l : F) → Type (ℓ-max ℓ' ℚℓ)
  IsLimit x l = ∀(ε : ℚ) → (0ᵣ <ᵣ ε) → ∃[ N ∈ ℕ ] ∀(n : ℕ) → N ≤ₙ n → distance (x n) l < iᵣ ε

  -- Remark 4.4.3. We do not consider the statement of convergence in propositions-as-types
  --
  --   (Πε : Q + )(ΣN : N)(Πn : N)n ≥ N → |x n − l | < ε,
  --
  -- because if the sequence has a modulus of Cauchy convergence M, then λε.M (ε/2) is a
  -- modulus of convergence to the limit l, so that we get an element of the above type.

  -- Definition 4.4.4.
  -- The ordered field (F, 0 F , 1 F , + F , · F , min F , max F , < F ) is said to be Cauchy complete
  -- if for every sequence x with modulus of Cauchy convergence M, we have a limit of x.
  -- In other words, an ordered field is Cauchy complete iff from a sequence–modulus pair (x, M), we can compute a limit of x.

  IsCauchyComplete : Type (ℓ-max (ℓ-max ℓ ℓ') ℚℓ)
  IsCauchyComplete = (x : ℕ → F)
                   → (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ))
                   → IsModulusOfCauchyConvergence x M
                   → Σ[ l ∈ F ] IsLimit x l

  -- For the remainder of this section, additionally assume that F is Archimedean.
  module _ (isArchimedian : IsArchimedian OF) where

    -- Lemma 4.4.5.
    -- The type of limits of a fixed sequence x : N → F is a proposition.
    Lemma-4-4-5 : ∀(x : ℕ → F) → isProp (Σ[ l ∈ F ] IsLimit x l)
    -- Proof. This can be shown using the usual proof that limits are unique in Archimedean ordered fields, followed by an application of Lemma 2.6.20.
    Lemma-4-4-5 x = {!!}

    -- Corollary 4.4.6.
    -- Fix a given sequence x : N → F . Suppose that we know that there exists a
    -- limit of the sequence. Then we can compute a limit of the sequence.
    Corollary-4-4-6 : ∀(x : ℕ → F) → (∃[ l ∈ F ] IsLimit x l) → Σ[ l ∈ F ] IsLimit x l
    -- Proof. By applying the induction principle of propositional truncations of Definition 2.4.3.
    Corollary-4-4-6 x p = {!!} , {!!}

    -- Corollary 4.4.7.
    -- Fix a given sequence x : N → F . Suppose that, from a modulus of Cauchy
    -- convergence, we can compute a limit of the sequence. Then from the existence of the modulus of
    -- Cauchy convergence we can compute a limit of the sequence.
    Corollary-4-4-7 : (x : ℕ → F)
                    → ( (M : ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ))
                      → (isMCC : IsModulusOfCauchyConvergence x M)
                      → Σ[ l ∈ F ] IsLimit x l
                      )
                    -----------------------------------------------------------------------
                    → ∃[ M ∈ ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ) ] IsModulusOfCauchyConvergence x M
                    → Σ[ l ∈ F ] IsLimit x l
    -- Proof. By applying the induction principle of propositional truncations of Definition 2.4.3.
    Corollary-4-4-7 x f p = {!!}

    -- We can thus compute the limit of x : N → F as the number lim(x, p), where p is a proof
    -- that the limit of x exists. We will rather use the more traditional notation lim n→∞ x n for this
    -- number.

    -- Example 4.4.8 (Exponential function).
    -- In a Cauchy complete Archimedean ordered field, we can define an exponential function exp : F → F by
    --
    --    exp(x) = Σ_{k=0}^{∞} (xᵏ) / (k!)
    --
    -- For a given input x, we obtain the existence of a modulus of Cauchy convergence for the output from boundedness of
    -- x, that is, from the fact that (∃q, r : Q) q < x < r .

    exp : F → F
    exp x = {!!}

    Example-4-4-8 : ∀(x : F) → ∃[ M ∈ ((y : ℚ) → {{0ᵣ <ᵣ y}} → ℕ) ] IsModulusOfCauchyConvergence {!!} M
    Example-4-4-8 x with Example-4-3-6 OF isArchimedian x
    ... | q' , r' = let q : ∃[ q ∈ ℚ ] iᵣ q < x
                        q = q'
                        r : ∃[ r ∈ ℚ ] x < iᵣ r
                        r = r'
                    in {!!}

    -- The point of this work is that, because we have a single language for properties and struc-
    -- ture, we can see more precisely what is needed for certain computations. In the above example,
    -- we explicitly do not require that inputs come equipped with a modulus of Cauchy convergence,
    -- but rather that there exists such a modulus. On the one hand, we do need a modulus to obtain
    -- the limit, but as the limit value is independent of the chosen modulus, existence of such a
    -- modulus suffices.
  -}
