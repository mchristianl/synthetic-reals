{-# OPTIONS --cubical --no-import-sorts --prop #-}

module Instances where

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ)
open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Foundations.Logic
open import Agda.Builtin.Equality  renaming (_≡_ to _≡ᵢ_; refl to reflₚ)

variable
  ℓ ℓ' ℓ'' : Level

-- hProp is just the propertie's target type A with ≡ for all inhabitants attached
_ : (hProp ℓ) ≡ (Σ[ A ∈ Type ℓ ] (∀(x y : A) → x ≡ y))
_ = refl

_ : (hProp ℓ) ≡ (Σ[ A ∈ Type ℓ ] isProp A)
_ = refl

-- PropRel is just the relation R with ≡ for all inhabitants of all target types R a b attached
PropRel' : ∀ {ℓ} (A B : Type ℓ) (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
PropRel' A B ℓ' = Σ[ R ∈ Rel A B ℓ' ] ∀ a b → isProp (R a b)

#-coerceₚ' : ∀{ℓ'} → {P Q : hProp ℓ'} → [ P ] → {{[ P ] ≡ [ Q ]}} → [ Q ]
#-coerceₚ' {ℓ} {[p] , p-isProp} {[q] , q-isProp} p {{ p≡q }} = transport p≡q p


path-to-id : ∀{ℓ} {A : Type ℓ} {x y : A} → x ≡ y → x ≡ᵢ y
path-to-id p = {!!}

-- just for the explanation
record PoorField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    F : Type ℓ
    0f 1f : F
    _#_ : Rel F F ℓ'
    #-isprop : ∀ x y → isProp (x # y)
    instance
      #-isprop' : ∀{x y} {p q : x # y} → p ≡ q -- could we use this in some way?
    
    -- #-rel : PropRel F F ℓ'

  _#ₚ_ : F → F → hProp ℓ'
  x #ₚ y = (x # y) , #-isprop x y

  -- NOTE: this creates a `Goal: fst #-rel ...` everywhere
  --       we might just separate the relation from the isprop
  --       i.e. directly define _#_ and #-isprop
  -- _#_      = fst #-rel
  -- #-isprop = snd #-rel

  -- NOTE: there is an email on the agda mailing list 08.11.18, 21:16 by Martin Escardo "I want implicit coercions in Agda"
  --       although this email thread is about more general coercions which are not straight forward, where hProp should be less of an issue
  #-coerce : ∀{ℓ x y} → ∀{p q} {R : x # y → Type ℓ} → R p → R q
  #-coerce {ℓ} {x} {y} {p} {q} {R} rp = transport (cong R (#-isprop x y p q))rp 

  #-coerceₚ : ∀{ℓ x y} → ∀{p q} {R : [ x #ₚ y ] → Type ℓ} → R p → R q
  #-coerceₚ {ℓ} {x} {y} {p} {q} {R} rp = transport (cong R (#-isprop x y p q)) rp

  field
    _+_ _·_ : F → F → F
    _⁻¹ᶠ    : (x : F) → {{ x # 0f }} → F
    ·-rinv  : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f

   -- for the purposes of explanation we just assume two different proofs of `1 # 0`
    1#0     : 1f # 0f
    1#0'    : 1f # 0f

    -- maybe there is some clever way to define _⁻¹ᶠ in a way where it accepts different proofs
    _⁻¹ᶠ'   : (x : F) → {{ [ x #ₚ 0f ] }} → F
    ·-rinv' : (x : F) → (p : [ x #ₚ 0f ]) → x · (_⁻¹ᶠ' x {{p}}) ≡ 1f
    
    1#0ₚ     : [ 1f #ₚ 0f ]
    1#0ₚ'    : [ 1f #ₚ 0f ]

    _⁻¹ᶠ''   : (x : F) → {{ [ x #ₚ 0f ] }} → F

  -- infix  9 _⁻¹ᶠ
  -- infixl 7 _·_
  -- infixl 5 _+_
  -- infixl 4 _#_

module test-hProp (PF : PoorField {ℓ} {ℓ'}) where
  open PoorField PF
  
  -- of course, this works
  test0 : let instance _ = 1#0 in 1f · (1f ⁻¹ᶠ) ≡ 1f
  test0 = ·-rinv 1f 1#0

  -- now, we try passing in 1#0'
  test1 : let instance _ = 1#0 in 1f · (1f ⁻¹ᶠ) ≡ 1f
  -- ERROR:
  -- PoorField.1#0' /= PoorField.1#0
  -- when checking that the expression 1#0' has type fst #-rel 1f 0f
  test1 = ·-rinv 1f ( #-coerceₚ {_} {1f} {0f} {_} {_} {_} 1#0')

  -- #-coerce seems to have troubles resolving the R
  test2 : let instance _ = 1#0 in 1f · (1f ⁻¹ᶠ) ≡ 1f
  -- ERROR:
  -- Failed to solve the following constraints:
  -- _R_161 _q_160 =< (1f · (1f ⁻¹ᶠ)) ≡ 1f
  -- (1f · (1f ⁻¹ᶠ)) ≡ 1f =< _R_161 _p_159
  test2 = #-coerce (·-rinv 1f 1#0') -- this line is yellow in emacs

  -- it works when we give R explicitly
  test3 : let instance _ = 1#0 in 1f · (1f ⁻¹ᶠ) ≡ 1f
  test3 = #-coerce {R = λ r → 1f · (_⁻¹ᶠ 1f {{r}}) ≡ 1f} (·-rinv 1f 1#0')

  -- a different "result" of this consideration might be that Goals involving hProp-instances need to be formulated in a different way

  test4 : let instance _ = 1#0ₚ in 1f · (1f ⁻¹ᶠ') ≡ 1f
  test4 =   ·-rinv' 1f ( #-coerceₚ' 1#0ₚ' {{{!!}}} )

  test5 : let instance _ = 1#0ₚ in 1f · (1f ⁻¹ᶠ') ≡ 1f
  test5 with 1#0ₚ' | path-to-id {ℓ'} {x = 1#0ₚ} {y = 1#0ₚ'} (#-isprop 1f 0f 1#0ₚ 1#0ₚ')
  ... | .(PoorField.1#0ₚ PF) | reflₚ = {! ·-rinv' 1f 1#0ₚ' !}

-- when using Prop this would be less of an issue
-- but how does it interact with the hProp based cubical library?
record ImpredicativePoorField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    F : Type ℓ
    0f 1f : F
    _#_ : F → F → Prop ℓ'
    _+_ _·_ : F → F → F
    _⁻¹ᶠ    : (x : F) → {{ x # 0f }} → F
    ·-rinv  : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f

   -- for the purposes of explanation we just assume two different proofs of `1 # 0`
    1#0     : 1f # 0f
    1#0'    : 1f # 0f

module test-impredicative (PF : ImpredicativePoorField {ℓ} {ℓ'}) where
  open ImpredicativePoorField PF

  -- now, we try passing in 1#0'
  test1 : let instance _ = 1#0 in 1f · (1f ⁻¹ᶠ) ≡ 1f
  test1 = ·-rinv 1f 1#0' -- just works
