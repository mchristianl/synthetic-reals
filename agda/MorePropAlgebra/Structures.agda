{-# OPTIONS --cubical --no-import-sorts  #-}

module MorePropAlgebra.Structures where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Function.Base using (_∋_; _$_)
open import Cubical.Foundations.Function
-- open import Function.Reasoning using (∋-syntax)
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

-- open import Cubical.Structures.CommRing
-- open import Cubical.Structures.Ring
-- open import Cubical.Structures.Poset

open import Utils
open import MoreLogic.Reasoning
open import MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax to infix -4 ∀〚∶〛-syntax
  )
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions hiding (_≤''_)
open import MorePropAlgebra.Consequences

-- taken from the cubical standard library and adapted to hProps:
--   IsSemigroup
--   IsMonoid
--   IsGroup
--   IsAbGroup
--   IsRing
--   IsCommRing

-- properties tied to some operation `R` on sets
module _ {ℓ : Level} {A : Type ℓ} (R : A → A → A) (is-set : isSet A)
  (let _·_  = R
       _+_  = R
       _≡ˢ_ = λ(x y : A) → [ is-set ] x ≡ˢ y
       infixl 7 _·_
       infixl 5 _+_
       infixl 4 _≡ˢ_
  ) where

  isAssociativeˢ =            ∀[ x ] ∀[ y ] ∀[ z ]   x · (y · z) ≡ˢ (x · y) · z
  isIdentityˢ    = λ(ε : A) → ∀[ x ]               ( x · ε ≡ˢ x) ⊓ ( ε · x ≡ˢ x)
  isCommutativeˢ =            ∀[ x ] ∀[ y ]                x + y ≡ˢ y + x


-- other properties
module _ {ℓ : Level} {A : Type ℓ} where
  is-+-#-Extensional  :             (_+_     : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _
  is-+-<-Extensional  :             (_+_     : A → A → A)              → ∀{ℓ'} → (_<_ : hPropRel A A ℓ')                                                → hProp _
  is-+-<-ExtensionalDisjoint :      (_+_     : A → A → A)              → ∀{ℓ'} → (_<_ : hPropRel A A ℓ')                                                → hProp _
  is-+-<-Extensional' :             (_+_     : A → A → A)              → ∀{ℓ'} → (_<_ : hPropRel A A ℓ') → [ is-+-<-ExtensionalDisjoint _+_ _<_ ]       → hProp _

  is-+-#-Extensional         _+_ _#_      = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ]         (w + x) # (y + z) ⇒                    (w # y) ⊔  (x # z)
  is-+-<-Extensional         _+_ _<_      = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ]         (w + x) < (y + z) ⇒                    (w < y) ⊔  (x < z)
  is-+-<-ExtensionalDisjoint _+_ _<_      = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ]         (w + x) < (y + z) ⇒                    (w < y) ⇒ ¬(x < z)
  is-+-<-Extensional'        _+_ _<_ disj = ∀[ w ] ∀[ x ] ∀[ y ] ∀[ z ] ∀ᵖ[ p ∶ (w + x) < (y + z) ] [ disj w x y z p ] (w < y) ⊎ᵖ (x < z)

  isMin : ∀{ℓ'} → (_≤_ : hPropRel A A ℓ') (min : A → A → A) → hProp _
  isMax : ∀{ℓ'} → (_≤_ : hPropRel A A ℓ') (max : A → A → A) → hProp _

  isMin _≤_ min  = ∀[ x ] ∀[ y ] ∀[ z ] z ≤ (min x y) ⇔ z ≤ x ⊓ z ≤ y
  isMax _≤_ max  = ∀[ x ] ∀[ y ] ∀[ z ] (max x y) ≤ z ⇔ x ≤ z ⊓ y ≤ z

  operation_preserves_when_ : (op : A → A → A) → ∀{ℓ'} → (R : hPropRel A A ℓ') → ∀{ℓ''} → (A → hProp ℓ'') → hProp _
  operation _·_ preserves _<_ when P = ∀[ x ] ∀[ y ] ∀[ z ] P z ⇒ x < y ⇒ (x · z) < (y · z)

-- other properties on sets
module _ {ℓ : Level} {A : Type ℓ} (is-set : isSet A)
  (let _≡ˢ_ = λ(x y : A) → [ is-set ] x ≡ˢ y; infixl 4 _≡ˢ_) where

  -- NOTE: the left  inverse is "on the right" of `_⊓_` (you get it with `snd`)
  --   and the right inverse is "on the left"  of `_⊓_` (you get it with `fst`)
  --   .. this is how it's done in the cubical standard library

  isInverseˢ          : (0g    : A) (_+_     : A → A → A) (-_ : A → A)                                                                                  → hProp _
  isDistributiveˢ     :             (_+_ _·_ : A → A → A)                                                                                               → hProp _
  isNonzeroInverseˢ'  : (0f 1f : A) (    _·_ : A → A → A)                                                  (_⁻¹ : (x : A) → {{ ! [ ¬'(x ≡ 0f) ] }} → A) → hProp _
  isNonzeroInverseˢ   : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ') → (_⁻¹ : (x : A) → {{   [    x # 0f  ] }} → A) → hProp _
  isNonzeroInverseˢ'' : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _
  isInverseNonzeroˢ   : (0f 1f : A) (    _·_ : A → A → A)              → ∀{ℓ'} → (_#_ : hPropRel A A ℓ')                                                → hProp _

  isInverseˢ          0g _+_ -_         = ∀[ x ]                 (   x  + (- x) ≡ˢ 0g)
                                                               ⊓ ((- x) +    x  ≡ˢ 0g)

  isDistributiveˢ     _+_ _·_           = ∀[ x ] ∀[ y ] ∀[ z ]   ( x · (y +  z) ≡ˢ (x · y) + (x · z))
                                                               ⊓ ((x +  y) · z  ≡ˢ (x · z) + (y · z))

  -- classical notion of inverse operating on `¬(x ≡ 0)`
  --   `∀ᵖ!〚_〛_` creates in instance argument of type `!_`
  --   because `¬'(x ≡ 0f)` is a function type with an explicit argument and won't be considered in instance search
  isNonzeroInverseˢ'  0f 1f _·_ _⁻¹     = ∀[ x ] ∀ᵖ!〚 p ∶ ¬'(x ≡ 0f) 〛    (x · (x ⁻¹) {{ p }} ≡ˢ 1f)
                                                                        ⊓ ((x ⁻¹) {{ p }} · x ≡ˢ 1f)

  -- constructive notion of inverse operating on `x # 0`
  --   `∀ᵖ〚_〛_` creates in instance argument
  isNonzeroInverseˢ   0f 1f _·_ _#_ _⁻¹ = ∀[ x ] ∀ᵖ〚 p ∶ x # 0f 〛         (x · (x ⁻¹) {{ p }} ≡ˢ 1f)
                                                                        ⊓ ((x ⁻¹) {{ p }} · x ≡ˢ 1f)

  -- this is the formulation in Booij2020
  --   we need to proof uniqueness of inverses to obtain `_⁻¹` for `isNonzeroInverseˢ`
  isNonzeroInverseˢ'' 0f 1f _·_ _#_     = ∀[ x ]        (∃[ y ] x · y ≡ˢ 1f) ⇔ x # 0f

  isInverseNonzeroˢ   0f 1f _·_ _#_     = ∀[ x ] ∀[ y ] x · y ≡ˢ 1f ⇒ x # 0f ⊓ y # 0f

  -- TODO: comm+invnz''⇒nzinv

record IsSemigroup {A : Type ℓ} (_·_ : A → A → A) : Type ℓ where
  constructor issemigroup
  field
    is-set   : [ isSetᵖ A ]
    is-assoc : [ isAssociativeˢ _·_ is-set ]

isSemigroup : {A : Type ℓ} (_·_ : A → A → A) → hProp ℓ
isSemigroup _·_ .fst = IsSemigroup _·_
isSemigroup _·_ .snd (issemigroup a₀ b₀) (issemigroup a₁ b₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in issemigroup is-set (snd (isAssociativeˢ _·_ is-set) b₀ b₁ i)

record IsMonoid {A : Type ℓ} (ε : A) (_·_ : A → A → A) : Type ℓ where
  constructor ismonoid
  field
    is-set       : [ isSetᵖ A ]
    is-Semigroup : [ isSemigroup _·_ ]
    is-identity  : [ isIdentityˢ _·_ is-set ε ]

  open IsSemigroup is-Semigroup hiding (is-set) public

  is-lid : (x : A) → ε · x ≡ x
  is-lid x = is-identity x .snd

  is-rid : (x : A) → x · ε ≡ x
  is-rid x = is-identity x .fst

isMonoid : {A : Type ℓ} (ε : A) (_·_ : A → A → A) → hProp ℓ
isMonoid ε _·_ .fst = IsMonoid ε _·_
isMonoid ε _·_ .snd (ismonoid a₀ b₀ c₀) (ismonoid a₁ b₁ c₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in ismonoid is-set (snd (isSemigroup _·_) b₀ b₁ i) (snd (isIdentityˢ _·_ is-set ε) c₀ c₁ i)

record IsGroup {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where
  constructor isgroup
  field
    is-set     : [ isSetᵖ G ]
    is-Monoid  : [ isMonoid 0g _+_ ]
    is-inverse : [ isInverseˢ is-set 0g _+_ -_ ]

  open IsMonoid is-Monoid hiding (is-set) public

  infixl 6 _-_

  _-_ : G → G → G
  x - y = x + (- y)

  is-invl : (x : G) → (- x) + x ≡ 0g
  is-invl x = is-inverse x .snd

  is-invr : (x : G) → x + (- x) ≡ 0g
  is-invr x = is-inverse x .fst

isGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) → hProp ℓ
isGroup 0g _+_ -_ .fst = IsGroup 0g _+_ -_
isGroup 0g _+_ -_ .snd (isgroup a₀ b₀ c₀) (isgroup a₁ b₁ c₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in isgroup is-set (snd (isMonoid 0g _+_) b₀ b₁ i) (snd (isInverseˢ is-set 0g _+_ -_) c₀ c₁ i)

record IsAbGroup {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) : Type ℓ where
  constructor isabgroup
  field
    is-set   : [ isSetᵖ G ]
    is-Group : [ isGroup 0g _+_ -_ ]
    is-comm  : [ isCommutativeˢ _+_ is-set ]

  open IsGroup is-Group hiding (is-set) public

isAbGroup : {G : Type ℓ} (0g : G) (_+_ : G → G → G) (-_ : G → G) → hProp ℓ
isAbGroup 0g _+_ -_ .fst = IsAbGroup 0g _+_ -_
isAbGroup 0g _+_ -_ .snd (isabgroup a₀ b₀ c₀) (isabgroup a₁ b₁ c₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in isabgroup is-set (snd (isGroup 0g _+_ -_) b₀ b₁ i) (snd (isCommutativeˢ _+_ is-set) c₀ c₁ i)

record IsRing {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
  constructor isring
  field
    is-set    : [ isSetᵖ R ]
    +-AbGroup : [ isAbGroup 0r _+_ -_ ]
    ·-Monoid  : [ isMonoid  1r _·_ ]
    is-dist   : [ isDistributiveˢ is-set _+_ _·_ ]

  open IsAbGroup +-AbGroup hiding (is-set) public
    renaming
      ( is-assoc     to +-assoc
      ; is-identity  to +-identity
      ; is-lid       to +-lid
      ; is-rid       to +-rid
      ; is-inverse   to +-inv
      ; is-invl      to +-linv
      ; is-invr      to +-rinv
      ; is-comm      to +-comm
      ; is-Semigroup to +-Semigroup
      ; is-Monoid    to +-Monoid
      ; is-Group     to +-Group )

  open IsMonoid ·-Monoid hiding (is-set) public
    renaming
      ( is-assoc     to ·-assoc
      ; is-identity  to ·-identity
      ; is-lid       to ·-lid
      ; is-rid       to ·-rid
      ; is-Semigroup to ·-Semigroup )

  ·-rdist-+ : (x y z : R) → x · (y + z) ≡ (x · y) + (x · z)
  ·-rdist-+ x y z = is-dist x y z .fst

  ·-ldist-+ : (x y z : R) → (x + y) · z ≡ (x · z) + (y · z)
  ·-ldist-+ x y z = is-dist x y z .snd

  -- TODO: prove these somewhere

  -- zero-lid : (x : R) → 0r · x ≡ 0r
  -- zero-lid x = zero x .snd

  -- zero-rid : (x : R) → x · 0r ≡ 0r
  -- zero-rid x = zero x .fst

isRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) → hProp ℓ
isRing 0r 1r _+_ _·_ -_ .fst = IsRing 0r 1r _+_ _·_ -_
isRing 0r 1r _+_ _·_ -_ .snd (isring a₀ b₀ c₀ d₀) (isring a₁ b₁ c₁ d₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in isring is-set (snd (isAbGroup 0r _+_ -_) b₀ b₁ i) (snd (isMonoid 1r _·_) c₀ c₁ i) (snd (isDistributiveˢ is-set _+_ _·_) d₀ d₁ i)

record IsCommRing {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
  constructor iscommring
  field
    is-set  : [ isSetᵖ R ]
    is-ring : [ isRing 0r 1r _+_ _·_ -_ ]
    ·-comm  : [ isCommutativeˢ _·_ is-set ]

  open IsRing is-ring hiding (is-set) public

isCommRing : {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) → hProp ℓ
isCommRing 0r 1r _+_ _·_ -_ .fst = IsCommRing 0r 1r _+_ _·_ -_
isCommRing 0r 1r _+_ _·_ -_ .snd (iscommring a₀ b₀ c₀) (iscommring a₁ b₁ c₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in iscommring is-set (snd (isRing 0r 1r _+_ _·_ -_) b₀ b₁ i) (snd (isCommutativeˢ _·_ is-set) c₀ c₁ i)

-- Definition 4.1.2.
-- A classical field is a set F with points 0, 1 : F, operations +, · : F → F → F, which is a commutative ring with unit, such that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

record IsClassicalField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ ! [ ¬'(x ≡ 0f) ] }} → F) : Type ℓ where
  constructor isclassicalfield

  field
    is-set      : [ isSetᵖ F ]
    is-CommRing : [ isCommRing 0f 1f _+_ _·_ -_ ]
    ·-inv       : [ isNonzeroInverseˢ' is-set 0f 1f _·_ _⁻¹ ]

  ·-linv : (x : F) {{ p : ! [ ¬' (x ≡ 0f) ] }} → ((x ⁻¹) · x) ≡ 1f -- wow, uses `p` already in `⁻¹`
  ·-linv x {{p}} = snd (·-inv x)

  ·-rinv : (x : F) {{ p : ! [ ¬' (x ≡ 0f) ] }} → (x · (x ⁻¹)) ≡ 1f
  ·-rinv x {{p}} = fst (·-inv x)

  open IsCommRing is-CommRing hiding (is-set) public

isClassicalField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_⁻¹ : (x : F) → {{ ! [ ¬'(x ≡ 0f) ] }} → F) → hProp ℓ
isClassicalField 0f 1f _+_ _·_ -_ _⁻¹ .fst = IsClassicalField 0f 1f _+_ _·_ -_ _⁻¹
isClassicalField 0f 1f _+_ _·_ -_ _⁻¹ .snd (isclassicalfield a₀ b₀ c₀) (isclassicalfield a₁ b₁ c₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in isclassicalfield is-set (snd (isCommRing 0f 1f _+_ _·_ -_) b₀ b₁ i) (snd (isNonzeroInverseˢ' is-set 0f 1f _·_ _⁻¹) c₀ c₁ i)

-- Definition 4.1.5.
-- A constructive field is a set F with points 0, 1 : F, binary operations +, · : F → F → F, and a binary relation # such that
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. x : F has a multiplicative inverse iff x # 0;
-- 3. # is tight, i.e. ¬(x # y) ⇒ x = y;
-- 4. + is #-extensional, that is, for all w, x, y, z : F
--    w + x # y + z ⇒ w # y ∨ x # z.

record IsConstructiveField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_#_ : hPropRel F F ℓ') {- (_⁻¹ : (x : F) → {{[ x # 0f ]}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor isconstructivefield

  field
    is-set      : [ isSetᵖ F ]
    is-CommRing : [ isCommRing 0f 1f _+_ _·_ -_ ]
    ·-inv''     : [ isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_ ]
    -- these should follow:
    --   ·-inv       : [ isNonzeroInverseˢ is-set 0f 1f _·_ _#_ _⁻¹ ]
    --   ·-invnz     : [ isInverseNonzeroˢ is-set 0f 1f _·_ _#_ ]
    --   ·-inv-back : ∀ x y → (x · y ≡ 1f) → [ x # 0f ] × [ y # 0f ]
    +-#-ext     : [ is-+-#-Extensional _+_ _#_ ]
    #-tight     : [ isTightˢ''' _#_ is-set ]
    -- #-ApartnessRel  : [ isApartnessRel _#_ ]
  --
  -- ·-linv : (x : F) {{ p : [ x # 0f ] }} → ((x ⁻¹) · x) ≡ 1f -- wow, uses `p` already in `⁻¹`
  -- ·-linv x {{p}} = snd (·-inv x)
  --
  -- ·-rinv : (x : F) {{ p : [ x # 0f ] }} → (x · (x ⁻¹)) ≡ 1f
  -- ·-rinv x {{p}} = fst (·-inv x)
  --
  open IsCommRing is-CommRing hiding (is-set) public
  -- open IsApartnessRelᵖ isApartnessRel public
  --   renaming
  --     ( isIrrefl  to #-irrefl
  --     ; isSym     to #-sym
  --     ; isCotrans to #-cotrans )

isConstructiveField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_#_ : hPropRel F F ℓ') {- (_⁻¹ : (x : F) → {{[ x # 0f ]}} → F) -} → hProp (ℓ-max ℓ ℓ')
isConstructiveField 0f 1f _+_ _·_ -_ _#_ {- _⁻¹ -} .fst = IsConstructiveField 0f 1f _+_ _·_ -_ _#_ {- _⁻¹ -}
isConstructiveField 0f 1f _+_ _·_ -_ _#_ {- _⁻¹ -} .snd (isconstructivefield a₀ b₀ c₀ d₀ e₀) (isconstructivefield a₁ b₁ c₁ d₁ e₁) = φ where
  abstract φ = λ i → let is-set = isSetIsProp a₀ a₁ i in isconstructivefield is-set (snd (isCommRing 0f 1f _+_ _·_ -_) b₀ b₁ i) (snd (isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_) c₀ c₁ i)
                                  (snd (is-+-#-Extensional _+_ _#_) d₀ d₁ i) (snd (isTightˢ''' _#_ is-set) e₀ e₁ i)

-- Definition 4.1.8.
-- Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
--   z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
-- and max computes least upper bounds in the sense that for every x, y, z : A, we have
--   max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.

record IsLattice {A : Type ℓ} (_≤_ : hPropRel A A ℓ') (min max : A → A → A) : Type (ℓ-max ℓ ℓ') where
  constructor islattice
  field
    ≤-PartialOrder : [ isPartialOrder _≤_ ]
    is-min         : [ isMin _≤_ min ]
    is-max         : [ isMax _≤_ max ]
    -- glb      : ∀ x y z → z ≤ min x y → z ≤ x × z ≤ y
    -- glb-back : ∀ x y z → z ≤ x × z ≤ y → z ≤ min x y
    -- lub      : ∀ x y z → max x y ≤ z → x ≤ z × y ≤ z
    -- lub-back : ∀ x y z → x ≤ z × y ≤ z → max x y ≤ z

  open IsPartialOrder ≤-PartialOrder public
    renaming
      ( is-refl    to ≤-refl
      ; is-antisym to ≤-antisym
      ; is-trans   to ≤-trans )

isLattice : {A : Type ℓ} (_≤_ : hPropRel A A ℓ') (min max : A → A → A) → hProp (ℓ-max ℓ ℓ')
isLattice _≤_ min max .fst = IsLattice _≤_ min max
isLattice _≤_ min max .snd (islattice a₀ b₀ c₀) (islattice a₁ b₁ c₁) = φ where
  abstract φ = λ i → islattice (snd (isPartialOrder _≤_) a₀ a₁ i) (snd (isMin _≤_ min) b₀ b₁ i) (snd (isMax _≤_ max) c₀ c₁ i)


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

record IsAlmostOrderedField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor isalmostorderedfield

  _≤_ : hPropRel F F ℓ'
  x ≤ y = ¬ (y < x)

  field
    is-set : isSet F
    -- 1.
    is-CommRing : [ isCommRing 0f 1f _+_ _·_ -_ ]
    -- 2.
    <-StrictPartialOrder : [ isStrictPartialOrder _<_ ]

  open IsCommRing is-CommRing hiding (is-set) public
  open IsStrictPartialOrder <-StrictPartialOrder public
    renaming
      ( is-irrefl  to <-irrefl
      ; is-trans   to <-trans
      ; is-cotrans to <-cotrans )

  <-asym : [ isAsym _<_ ]
  <-asym = irrefl+trans⇒asym _<_ <-irrefl <-trans

  _#_ : hPropRel F F ℓ'
  x # y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

  field
    -- 3.
    ·-inv''     : [ isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_ ]
    -- ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    -- ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    -- ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    -- 4. NOTE: we already have ≤-isPartialOrder in ≤-isLattice
    -- ≤-isPartialOrder : IsPartialOrder _≤_
    -- 5.
    ≤-isLattice : [ isLattice _≤_ min max ]

  open IsLattice ≤-isLattice public

isAlmostOrderedField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} → hProp (ℓ-max ℓ ℓ')
isAlmostOrderedField {ℓ = ℓ} {ℓ' = ℓ'} {F = F} 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .fst = IsAlmostOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -}
isAlmostOrderedField {ℓ = ℓ} {ℓ' = ℓ'} {F = F} 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .snd (isalmostorderedfield a₀ b₀ c₀ d₀ e₀) (isalmostorderedfield a₁ b₁ c₁ d₁ e₁) = φ where
  abstract φ = λ i → let -- we are doing basically "the same" as in `IsAlmostOrderedField`
                         _≤_                  : hPropRel F F ℓ'
                         x ≤ y                = ¬ (y < x)
                         is-set               = isSetIsProp a₀ a₁ i
                         is-CommRing          = snd (isCommRing 0f 1f _+_ _·_ -_) b₀ b₁ i
                         <-StrictPartialOrder = snd (isStrictPartialOrder _<_) c₀ c₁ i
                         open IsStrictPartialOrder <-StrictPartialOrder
                           renaming
                             ( is-irrefl  to <-irrefl
                             ; is-trans   to <-trans
                             ; is-cotrans to <-cotrans )
                         <-asym               : [ isAsym _<_ ]
                         <-asym               = irrefl+trans⇒asym _<_ <-irrefl <-trans
                         _#_                  : hPropRel F F ℓ'
                         x # y                = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)
                         ·-inv''              = snd (isNonzeroInverseˢ'' is-set 0f 1f _·_ _#_) d₀ d₁ i
                         ≤-isLattice          = snd (isLattice _≤_ min max) e₀ e₁ i
                     in isalmostorderedfield is-set is-CommRing <-StrictPartialOrder ·-inv'' ≤-isLattice

record IsOrderedField {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} : Type (ℓ-max ℓ ℓ') where
  constructor isorderedfield
  field
    -- 1. 2. 3. 4. 5.
    is-AlmostOrderedField : [ isAlmostOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ᶠ -} ]
    -- 6. (†)
    -- NOTE: this is 'shifted' from the pevious definition of #-extensionality for + .. does the name still fit?
    +-<-ext : [ is-+-<-Extensional _+_ _<_ ] -- ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)
    -- 6. (∗)
    ·-preserves-< : [ operation _·_ preserves _<_ when (λ z → 0f < z) ] -- ∀ x y z → 0f < z → x < y → (x · z) < (y · z)
  open IsAlmostOrderedField is-AlmostOrderedField public

isOrderedField : {F : Type ℓ} (0f 1f : F) (_+_ _·_ : F → F → F) (-_ : F → F) (_<_ : hPropRel F F ℓ') (min max : F → F → F) {- (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) -} → hProp (ℓ-max ℓ ℓ')
isOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .fst = IsOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -}
isOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ -} .snd (isorderedfield a₀ b₀ c₀) (isorderedfield a₁ b₁ c₁) = φ where
  abstract φ = λ i → isorderedfield (snd (isAlmostOrderedField 0f 1f _+_ _·_ -_ _<_ min max {- _⁻¹ᶠ -}) a₀ a₁ i) (snd (is-+-<-Extensional _+_ _<_) b₀ b₁ i) (snd (operation _·_ preserves _<_ when (λ z → 0f < z)) c₀ c₁ i)
