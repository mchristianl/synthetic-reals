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
  ; ∃[]-syntax  to infix -4 ∃[]-syntax   --
  ; ∃[∶]-syntax to infix -4 ∃[∶]-syntax  --
  ; ∀[∶]-syntax to infix -4 ∀[∶]-syntax  --
  ; ∀[]-syntax  to infix -4 ∀[]-syntax   --
  )
-- open import Cubical.Data.Unit.Base using (Unit)
open import Cubical.HITs.PropositionalTruncation.Base -- ∣_∣

open import Utils
open import MoreLogic.Reasoning
open import MoreLogic.Definitions renaming
  ( _ᵗ⇒_ to infixr 0 _ᵗ⇒_
  ; ∀ᵖ[∶]-syntax  to infix -4 ∀ᵖ[∶]-syntax
  ; ∀ᵖ〚∶〛-syntax  to infix -4 ∀ᵖ〚∶〛-syntax
  ; ∀ᵖ!〚∶〛-syntax to infix -4 ∀ᵖ!〚∶〛-syntax
  ; ∀〚∶〛-syntax   to infix -4 ∀〚∶〛-syntax
  ; Σᵖ[]-syntax   to infix -4 Σᵖ[]-syntax
  ; Σᵖ[∶]-syntax  to infix -4 Σᵖ[∶]-syntax
  ) hiding (≡ˢ-syntax)
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions hiding (_≤''_)
open import MorePropAlgebra.Consequences
open import MorePropAlgebra.Bundles

module MorePropAlgebra.Booij2020 where

{-
record BooijAssumptions {ℓ ℓ'} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
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
-}

module BooijResults {ℓ ℓ'} (assumptions : AlmostOrderedField {ℓ} {ℓ'}) where
  -- NOTE: modules with overlapping operations need to be defined first to not be chosen as "the" prefix in Goal/Have display
  import MorePropAlgebra.Properties.Group
  module Group'Properties  = MorePropAlgebra.Properties.Group   record { AlmostOrderedField assumptions ; is-Group = AlmostOrderedField.+-Group assumptions }
  module Group'            =                            Group   record { AlmostOrderedField assumptions ; is-Group = AlmostOrderedField.+-Group assumptions }
  (      Group')           =                            Group ∋ record { AlmostOrderedField assumptions ; is-Group = AlmostOrderedField.+-Group assumptions }
  module GroupLemmas'      = Group'Properties.GroupLemmas'

  import MorePropAlgebra.Properties.Ring
  module Ring'Properties  = MorePropAlgebra.Properties.Ring   record { AlmostOrderedField assumptions }
  module Ring'            =                            Ring   record { AlmostOrderedField assumptions }
  (      Ring')           =                            Ring ∋ record { AlmostOrderedField assumptions }
  module RingTheory'      = Ring'Properties.RingTheory'

  open AlmostOrderedField assumptions renaming (Carrier to F; _-_ to _-_) -- atlernative to module telescope

  private
    infixl 4 _≡ˢ_
    _≡ˢ_ = λ(x y : F) → MoreLogic.Definitions.≡ˢ-syntax x y {is-set} -- [ is-set ] x ≡ˢ y

    ≡ˢ-sym : ∀ a b → [ (a ≡ˢ b) ⇔ (b ≡ˢ a) ]
    ≡ˢ-sym a b .fst a≡b = sym a≡b
    ≡ˢ-sym a b .snd b≡a = sym b≡a

  import Cubical.HITs.PropositionalTruncation.Properties as PTrunc

  abstract
    ≡ˢ-symᵗ : ∀ a b → (a ≡ˢ b) ≡ (b ≡ˢ a)
    ≡ˢ-symᵗ a b = let (p , q) = ≡ˢ-sym a b in ⇔toPath p q

    -dist' : [ ∀[ a ] ∀[ b ] -(a + b) ≡ˢ (- b) + (- a) ]
    -dist  : [ ∀[ a ] ∀[ b ] -(a + b) ≡ˢ (- a) + (- b) ]
    -dist' a b = GroupLemmas'.invDistr a b
    -dist  a b = -dist' a b ∙ +-comm _ _

    ·-inv#0 : ∀ x y → x · y ≡ 1f → [ (x # 0f) ⊓ (y # 0f) ]
    ·-inv#0 x y x·y≡1 .fst = ·-inv'' x .fst ∣ (y ,              x·y≡1) ∣
    ·-inv#0 x y x·y≡1 .snd = ·-inv'' y .fst ∣ (x , ·-comm y x ∙ x·y≡1) ∣

    -- ∀(a b c : F) → {{_ : [ c # 0f ]}} → [ (a · c ≡ˢ b · c) ⇒ (a ≡ˢ b) ]
    ·-reflects-≡ : [ operation _·_ reflects _≡ˢ_ when (λ c → c # 0f) ]
    ·-reflects-≡ a b c p = PTrunc.rec (isProp[] ((a · c ≡ˢ b · c) ⇒ (a ≡ˢ b) )) γ (·-inv'' c .snd p) where
      γ : Σ[ c⁻¹ ∈ F ] [ c · c⁻¹ ≡ˢ 1f ] → [ (a · c ≡ˢ b · c) ⇒ a ≡ˢ b ]
      γ (c⁻¹ , c·c⁻¹≡1) a·c≡b·c =
         a              ≡⟨ sym (fst (·-identity a)) ∙ cong (a ·_) (sym c·c⁻¹≡1) ∙ ·-assoc _ _ _ ⟩
        (a · c) · (c⁻¹) ≡⟨ cong (_· c⁻¹) a·c≡b·c ⟩
        (b · c) · (c⁻¹) ≡⟨ sym (·-assoc _ _ _) ∙ cong (b ·_) c·c⁻¹≡1 ∙ fst (·-identity b)  ⟩
         b ∎

    -- uniqueness of inverses from `·-assoc` + `·-comm` + `·-lid` + `·-rid`
    ·-rinv-unique'' : (x y z : F) → [ x · y ≡ˢ 1f ] → [ x · z ≡ˢ 1f ] → [ y ≡ˢ z ]
    ·-rinv-unique'' x y z x·y≡1 x·z≡1 =
      (      x  · y  ≡ˢ     1f ⇒ᵖ⟨ (λ x·y≡1 i → z · x·y≡1 i) ⟩
        z · (x  · y) ≡ˢ z · 1f ⇒ᵖ⟨ pathTo⇒ (λ i → ·-assoc z x y i ≡ˢ ·-rid z i) ⟩
       (z ·  x) · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → (·-comm z x i) · y  ≡ˢ z) ⟩
       (x ·  z) · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → x·z≡1 i · y  ≡ˢ z) ⟩
          1f    · y  ≡ˢ z      ⇒ᵖ⟨ pathTo⇒ (λ i → ·-lid y i ≡ˢ z) ⟩
                  y  ≡ˢ z      ◼ᵖ) .snd x·y≡1

    -- inverse function from `·-rinv-unique''` and `∀[ x ] (∃[ y ] x · y ≡ˢ 1f) ⇔ x # 0f`
    _⁻¹'' : ∀ x → {{[ x # 0f ]}} → Σ[ y ∈ F ] x · y ≡ 1f
    (x ⁻¹'') {{x#0f}} = PTrunc.rec γ (λ p → p) (·-inv'' x .snd x#0f) where
       γ : isProp (Σ[ y ∈ F ] x · y ≡ 1f)
       γ (a , x·a≡1) (b , x·b≡1) = let a≡b = ·-rinv-unique'' x a b x·a≡1 x·b≡1
                                   in Σ≡Prop (λ c → isProp[] (x · c ≡ˢ 1f)) a≡b

    _⁻¹ : ∀ x → {{[ x # 0f ]}} → F
    (x ⁻¹) {{p}} = (x ⁻¹'') .fst

    infix  9 _⁻¹

    ·-rinv : ∀ x → (p : [ x # 0f ]) → [ x · (x ⁻¹) {{p}} ≡ˢ 1f ]
    ·-rinv x p = (x ⁻¹'') {{p}} .snd

    ·-linv : ∀ x → (p : [ x # 0f ]) → [ (x ⁻¹) {{p}} · x ≡ˢ 1f ]
    ·-linv x p = ·-comm _ _ ∙ ·-rinv x p

    ·-linv-unique : (x y : F) → x · y ≡ 1f → (p : [ y # 0f ]) → x ≡ (y ⁻¹) {{p}}
    ·-linv-unique x y x·y≡1 p = sym $ ·-rinv-unique'' y ((y ⁻¹) {{p}}) x (·-rinv y p) (·-comm _ _ ∙ x·y≡1)

    -- ·-preserves-≡ : [ operation _·_ preserves _≡ˢ_ when (λ c → c # 0f) ]
    -- ·-preserves-≡ a b c p a≡b i = a≡b i · c

    -- _⁻¹ : ∀(c : F) → {{_ : [ c # 0f ]}} →
    -- (c ⁻¹) {{p}} = {!   !}

    -- ·-preserves-< : ∀ x y z → [ 0f < z ] → [ x < y ] → [ (x · z) < (y · z) ]
    -- ·-preserves-< = {!   !}
    --
    -- ·-reflects-<0 : ∀ x y → [ 0f < x · y ] → [ (0f < x) ⊓ (0f < y) ]
    -- ·-reflects-<0 = {!   !}
    --
    --
  -- -- ·-linv-unique : (x y : F) (x·y≡1 : (x ·₁ y) ≡ 1f) → x ≡ (y ⁻¹ᶠ₁)
  -- module _ (x y : F) (x·y≡1 : x · y ≡ 1f) where
  --   y#0 = snd (·-inv#0 _ _ x·y≡1) -- duplicated inhabitant (see notes)
  --   instance _ = y # 0f ∋ y#0
  --   import Cubical.Structures.Group
  --
  --   -- NOTE: ported from Cubical.Structures.Group.GroupLemmas
  --   abstract
  --     ·-linv-unique' : Σ[ p ∈ y # 0f ] (x ≡ _⁻¹ᶠ y {{p}})
  --     ·-linv-unique' = it , (
  --       x · y ≡ 1f        ⇒⟨ transport (λ i → x · y ≡ ·-linv y it (~ i)) ⟩
  --       x · y ≡ y ⁻¹ᶠ · y ⇒⟨ simplR _  ⟩
  --       x     ≡ y ⁻¹ᶠ     ◼) x·y≡1

  -- Bridges' definition of _≤__
  _≤''_ : hPropRel F F (ℓ-max ℓ ℓ')
  x ≤'' y = ∀[ ε ] (y < ε) ⇒ (x < ε)
  infixl 4 _≤''_

  Item-1  = ∀[ x ] ∀[ y ]                                 x ≤ y ⇔ ¬(y < x)                          -- (definition of _≤_)
  Item-2  = ∀[ x ] ∀[ y ]                                 x # y ⇔ [ <-asym x y ] (x < y) ⊎ᵖ (y < x) -- (definition of _#_)
  Item-3  = ∀[ x ] ∀[ y ] ∀[ z ]                          x ≤ y ⇔ x + z ≤ y + z                     -- +-creates-≤
  Item-4  = ∀[ x ] ∀[ y ] ∀[ z ]                          x < y ⇔ x + z < y + z                     -- +-creates-<
  Item-5  = ∀[ x ] ∀[ y ]        0f < x + y          ⇒ (0f < x) ⊔ (0f < y)                          -- 0<-reflects-+
  Item-6  = ∀[ x ] ∀[ y ] ∀[ z ]  x < y     ⇒  y ≤ z ⇒    x     <     z                             -- <-≤-trans
  Item-7  = ∀[ x ] ∀[ y ] ∀[ z ]  x ≤ y     ⇒  y < z ⇒    x     <     z                             -- ≤-<-trans
  Item-8  = ∀[ x ] ∀[ y ] ∀[ z ]  x ≤ y     ⇒ 0f ≤ z ⇒    x · z ≤ y · z                             -- ·-preserves-≤
  Item-9  = ∀[ x ] ∀[ y ] ∀[ z ] 0f < z     ⇒            (x < y ⇔ x · z < y · z)                    -- ·-creates-<
  Item-10 =                      0f < 1f                                                            -- 0<1

  -- see Bridges1999.agda for
  --   <-cotrans⇒Item-6
  --   <-cotrans⇒Item-7
  --   Item-7+<-irrefl⇒[≤-⇔-≤'']
  --   <-cotrans+<-irrefl⇒[≤-⇔-≤'']

  --  1. x ≤ y ⇔ ¬(y < x),
  item-1 : [ Item-1 ]
  item-1 _ _ .fst x≤y = x≤y -- holds definitionally
  item-1 _ _ .snd x≤y = x≤y

  --  2. x # y ⇔ (x < y) ∨ (y < x)
  item-2 : [ Item-2 ]
  item-2 _ _ .fst  x#y        =  x#y -- holds definitionally
  item-2 _ _ .snd [x<y]⊎[y<x] = [x<y]⊎[y<x]

  item-6' : [ Item-6 ]
  item-6' x y z x<y y≤z = ⊔-elim (x < z) (z < y) (λ _ → x < z) (λ x<z → x<z) (λ z<y → ⊥-elim (y≤z z<y)) (<-cotrans _ _ x<y z)

  item-7' : [ Item-7 ]
  item-7' x y z x≤y y<z = ⊔-elim (y < x) (x < z) (λ _ → x < z) (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z) (<-cotrans y z y<z x)

  -- Booij's _≤_ ⇔ Brigdes' _≤''_
  ≤-⇔-≤'' : ∀ x y → [ (x ≤ y) ⇔ (x ≤'' y) ]
  ≤-⇔-≤'' x y .fst x≤y ε y<ε = item-7' x y ε x≤y y<ε
  ≤-⇔-≤'' x y .snd x≤''y y<x = <-irrefl x (x≤''y x y<x)

  module +-<-ext+·-preserves-<⇒
    (+-<-ext       : [ is-+-<-Extensional _+_ _<_ ])
    (·-preserves-< : [ operation _·_ preserves _<_ when (λ z → 0f < z) ])
    where
    abstract
      -- NOTE: just a plain copy of the previous proof
      +-preserves-< : ∀ a b x → [ a < b ] → [ a + x < b + x ]
      +-preserves-< a b x = snd (
         a            <  b            ⇒ᵖ⟨ transport (λ i → [ sym (fst (+-identity a)) i < sym (fst (+-identity b)) i ]) ⟩
         a +    0f    <  b +    0f    ⇒ᵖ⟨ transport (λ i → [ a + sym (+-rinv x) i < b + sym (+-rinv x) i ]) ⟩
         a + (x  - x) <  b + (x  - x) ⇒ᵖ⟨ transport (λ i → [ +-assoc a x (- x) i < +-assoc b x (- x) i ]) ⟩
        (a +  x) - x  < (b +  x) - x  ⇒ᵖ⟨ +-<-ext (a + x) (- x) (b + x) (- x) ⟩
        (a + x < b + x) ⊔ (- x < - x) ⇒ᵖ⟨ (λ q → case q as (a + x < b + x) ⊔ (- x < - x) ⇒ a + x < b + x of λ
                                          { (inl a+x<b+x) → a+x<b+x -- somehow ⊥-elim needs a hint in the next line
                                          ; (inr  -x<-x ) → ⊥-elim {A = λ _ → [ a + x < b + x ]} (<-irrefl (- x) -x<-x)
                                          }) ⟩
         a + x < b + x ◼ᵖ)

      +-reflects-< : ∀ x y z → [ x + z < y + z ] → [ x < y ]
      +-reflects-< x y z = snd
        ( x + z < y + z              ⇒ᵖ⟨ +-preserves-< _ _ (- z) ⟩
          (x + z) - z  < (y + z) - z ⇒ᵖ⟨ transport (λ i → [ +-assoc x z (- z) (~ i) < +-assoc y z (- z) (~ i) ]) ⟩
          x + (z - z) < y + (z - z)  ⇒ᵖ⟨ transport (λ i → [ x + +-rinv z i < y + +-rinv z i ]) ⟩
          x + 0f < y + 0f            ⇒ᵖ⟨ transport (λ i → [ fst (+-identity x) i < fst (+-identity y) i ]) ⟩
          x < y                      ◼ᵖ)


      --  3. x ≤ y ⇔ x + z ≤ y + z,
      item-3 : [ Item-3 ] -- ∀ x y z → x ≤ y → x + z ≤ y + z
      item-3 x y z .fst = snd ( -- unfold the definition
         x     ≤ y          ⇒ᵖ⟨ (λ z → z) ⟩
        (y     < x     ⇒ ⊥) ⇒ᵖ⟨ (λ f → f ∘ (+-reflects-< y x z) ) ⟩
        (y + z < x + z ⇒ ⊥) ⇒ᵖ⟨ (λ z → z) ⟩
         x + z ≤ y + z      ◼ᵖ) -- refold the definition
      item-3 x y z .snd = snd (
         x + z ≤ y + z      ⇒ᵖ⟨ (λ z → z) ⟩ -- unfold the definition
        (y + z < x + z ⇒ ⊥) ⇒ᵖ⟨ (λ f p → f (+-preserves-< y x z p)) ⟩ -- just a variant of the above
        (y     < x     ⇒ ⊥) ⇒ᵖ⟨ (λ z → z) ⟩ -- refold the definition
         x     ≤ y          ◼ᵖ)

    --  4. x < y ⇔ x + z < y + z,
    item-4 : [ Item-4 ]
    item-4 x y z .fst = +-preserves-< x y z
    item-4 x y z .snd = +-reflects-<  x y z

    abstract
      --  5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
      item-5 : [ Item-5 ]
      item-5 x y = snd (
        (0f      < x + y)   ⇒ᵖ⟨ transport (λ i → [ fst (+-identity 0f) (~ i) < x + y ]) ⟩
        (0f + 0f < x + y)   ⇒ᵖ⟨ +-<-ext 0f 0f x y ⟩
        (0f < x) ⊔ (0f < y) ◼ᵖ)

      --  6. x < y ≤ z ⇒ x < z,
      item-6 : [ Item-6 ]
      item-6 x y z x<y y≤z = snd (
         x      <  y      ⇒ᵖ⟨ +-preserves-< _ _ _ ⟩
         x + z  <  y + z  ⇒ᵖ⟨ pathTo⇒ (λ i → x + z < +-comm y z i) ⟩
         x + z  <  z + y  ⇒ᵖ⟨ +-<-ext x z z y ⟩
        (x < z) ⊔ (z < y) ⇒ᵖ⟨ (λ q → case q as (x < z) ⊔ (z < y) ⇒ (x < z) of λ
                              { (inl x<z) → x<z
                              ; (inr z<y) → ⊥-elim (y≤z z<y)
                              }) ⟩
         x < z            ◼ᵖ) x<y

      --  7. x ≤ y < z ⇒ x < z,
      item-7 : [ Item-7 ]
      item-7 x y z x≤y = snd ( -- very similar to the previous one
         y      <  z      ⇒ᵖ⟨ +-preserves-< y z x ⟩
         y + x  <  z + x  ⇒ᵖ⟨ pathTo⇒ (λ i → +-comm y x i < z + x) ⟩
         x + y  <  z + x  ⇒ᵖ⟨ +-<-ext x y z x ⟩
        (x < z) ⊔ (y < x) ⇒ᵖ⟨ (λ q → case q as (x < z) ⊔ (y < x) ⇒ (x < z) of λ
                              { (inl x<z) → x<z
                              ; (inr y<x) → ⊥-elim (x≤y y<x)
                              }) ⟩
         x < z  ◼ᵖ)

      -- 10. 0f < 1f
      item-10 : [ Item-10 ]

      ⁻¹-preserves-sign : ∀ z z⁻¹ → [ 0f < z ] → z · z⁻¹ ≡ 1f → [ 0f < z⁻¹ ]
      ⁻¹-preserves-sign z z⁻¹ 0<z z·z⁻¹≡1 with snd (·-inv#0 z z⁻¹ z·z⁻¹≡1)
      ... | inl z⁻¹<0 = snd (
        z⁻¹     < 0f     ⇒ᵖ⟨ ·-preserves-< _ _ z 0<z ⟩
        z⁻¹ · z < 0f · z ⇒ᵖ⟨ transport (λ i → [ (·-comm _ _ ∙ z·z⁻¹≡1) i < RingTheory'.0-leftNullifies z i ]) ⟩
        1f      < 0f     ⇒ᵖ⟨ <-trans _ _ _ item-10 ⟩
        0f      < 0f     ⇒ᵖ⟨ <-irrefl _ ⟩
                ⊥        ⇒ᵖ⟨ ⊥-elim ⟩
             0f < z⁻¹    ◼ᵖ) z⁻¹<0
      ... | inr 0<z⁻¹ = 0<z⁻¹

      --  8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
      -- item-8 : ∀ x y z → x ≤ y → 0f ≤ z → x · z ≤ y · z
      item-8 : [ Item-8 ]
      -- For item 8, suppose x ≤ y and 0 ≤ z and yz < xz.
      item-8 x y z x≤y 0≤z y·z<x·z = let
        -- Then 0 < z (x − y) by (†),
        i   = (  y · z            <  x · z                ⇒ᵖ⟨ pathTo⇒ (λ i → ·-comm y z i < ·-comm x z i) ⟩
                 z · y            <  z · x                ⇒ᵖ⟨ +-preserves-< _ _ _ ⟩
                (z · y) - (z · y) < (z · x) - (z ·    y ) ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ (+-rinv (z · y))
                                                               ( λ i → (z · x) + sym (RingTheory'.-commutesWithRight-· z y) i )) ⟩
                               0f < (z · x) + (z · (- y)) ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ refl (sym (fst (is-dist z x (- y))))) ⟩ -- [XX]
                               0f <  z · (x - y)          ◼ᵖ) .snd y·z<x·z
        instance z·[x-y]#0 = [ z · (x - y) # 0f ] ∋ inr i
        -- and so, being apart from 0, z (x − y) has a multiplicative inverse w.
        w   = (z · (x - y)) ⁻¹
        ii  : 1f ≡ (z · (x - y)) · w
        ii  = sym (·-rinv _ _)
        -- Hence z itself has a multiplicative inverse w (x − y),
        iii : 1f ≡ z · ((x - y) · w)
        iii = transport (λ i → 1f ≡ ·-assoc z (x - y) w (~ i)) ii
        instance z#0f = [ z # 0f ] ∋ fst (·-inv#0 _ _ (sym iii))
        -- and so 0 < z ∨ z < 0, where the latter case contradicts the assumption 0 ≤ z, so that we have 0 < z.
        instance _    = [ 0f < z ] ∋ case z#0f of λ where
                        (inl z<0) → ⊥-elim (0≤z z<0)
                        (inr 0<z) → 0<z
        -- Now w (x − y) has multiplicative inverse z, so it is apart from 0,
        iv  : [ (x - y) · w # 0f ]
        iv  = snd (·-inv#0 _ _ (sym iii))
        -- that is (0 < w (x − y)) ∨ (w (x − y) < 0).
        in case iv of λ where
          -- By (∗), from 0 < w (x − y) and yz < xz we get yzw (x − y) < xzw (x − y), so y < x, contradicting our assumption that x ≤ y.
          (inr 0<[x-y]·w) → (
             y ·  z                   <  x ·  z                    ⇒ᵖ⟨ ·-preserves-< _ _ _ 0<[x-y]·w ⟩
            (y ·  z) · ((x - y) · w)  < (x ·  z) · ((x - y) · w)   ⇒ᵖ⟨ pathTo⇒ (λ i →
                                                                          (·-assoc y z ((x - y) · w)) (~ i)
                                                                        < (·-assoc x z ((x - y) · w)) (~ i)) ⟩
             y · (z  · ((x - y) · w)) <  x · (z  · ((x - y) · w))  ⇒ᵖ⟨ pathTo⇒ (λ i →
                                                                         y · (iii (~ i)) < x · (iii (~ i))) ⟩
             y · 1f                   <  x · 1f                    ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_
                                                                        (fst (·-identity y)) (fst (·-identity x))) ⟩
             y                        <  x                         ⇒ᵖ⟨ x≤y ⟩
                                      ⊥                            ◼ᵖ) .snd y·z<x·z
          -- In the latter case, from (∗) we get zw (x − y) < 0, i.e.
          -- 1 < 0 which contradicts item 10, so that we have 0 < w (x − y).
          (inl p) → (
                 (x - y) · w      < 0f     ⇒ᵖ⟨ ·-preserves-< _ _ _ it ⟩
                ((x - y) · w) · z < 0f · z ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ (·-comm _ _) (RingTheory'.0-leftNullifies z)) ⟩
            z · ((x - y) · w)     < 0f     ⇒ᵖ⟨ pathTo⇒ (λ i → iii (~ i) < 0f) ⟩
                               1f < 0f     ⇒ᵖ⟨ <-trans _ _ _  item-10 ⟩
                               0f < 0f     ⇒ᵖ⟨ <-irrefl _ ⟩
                                  ⊥        ◼ᵖ) .snd p

      --  9. 0 < z ⇒ (x < y ⇔ x z < y z),
      item-9 : [ Item-9 ]
      item-9 x y z 0<z .fst = ·-preserves-< x y z 0<z
      -- For the other direction of item 9, assume 0 < z and xz < yz,
      item-9 x y z 0<z .snd x·z<y·z = let
        instance _ = (          x · z  <  y · z            ⇒ᵖ⟨ +-preserves-< _ _ _ ⟩
                     (x · z) - (x · z) < (y · z) - (x · z) ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                    0f < (y · z) - (x · z) ◼ᵖ) .snd x·z<y·z
                 _ = [ (y · z) - (x · z) # 0f ] ∋ inr it
        -- so that yz − xz has a multiplicative inverse w,
        w = ((y · z) - (x · z)) ⁻¹
        o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (RingTheory'.-commutesWithLeft-· x z) (~ i)) ⟩
              (y · z) + ((- x) · z) ≡⟨ sym (snd (is-dist y (- x) z)) ⟩
              (y - x) · z           ∎)
        instance _ = [ (y - x) · z # 0f ] ∋ pathTo⇒ (λ i → o i # 0f) it
        -- and so z itself has multiplicative inverse w (y − x).
        instance _ = (          x · z  <  y · z            ⇒ᵖ⟨ +-preserves-< _ _ _ ⟩
                     (x · z) - (x · z) < (y · z) - (x · z) ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                                    0f < (y · z) - (x · z) ◼ᵖ) .snd x·z<y·z
                 _ = [ (y · z) - (x · z) # 0f ] ∋ inr it
        1≡z·[w·[y-x]] = (
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
        instance _ = [ z # 0f ] ∋ inr 0<z
        z⁻¹ = w · (y - x)
        z⁻¹≡w·[y-x] : z ⁻¹ ≡ (w · (y - x))
        z⁻¹≡w·[y-x] = sym ((·-linv-unique (w · (y - x)) z (sym 1≡[w·[y-x]]·z)) it)
        instance _ = 0<z
        0<z⁻¹ : [ 0f < z ⁻¹ ]
        0<z⁻¹ = ⁻¹-preserves-sign z (z ⁻¹) it (·-rinv z it)
        instance _ = [ 0f < w · (y - x) ] ∋ pathTo⇒ (λ i → 0f < z⁻¹≡w·[y-x] i) 0<z⁻¹
        in (  x ·  z         <  y ·  z         ⇒ᵖ⟨ ·-preserves-< _ _ z⁻¹ it ⟩
             (x ·  z) · z⁻¹  < (y ·  z) · z⁻¹  ⇒ᵖ⟨ pathTo⇒ (λ i → ·-assoc x z z⁻¹ (~ i) < ·-assoc y z z⁻¹ (~ i)) ⟩
              x · (z  · z⁻¹) <  y · (z  · z⁻¹) ⇒ᵖ⟨ pathTo⇒ (λ i → x · 1≡z·[w·[y-x]] (~ i) < y · 1≡z·[w·[y-x]] (~ i)) ⟩
              x · 1f         <  y · 1f         ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ (fst (·-identity x)) (fst (·-identity y))) ⟩
              x              <  y              ◼ᵖ) .snd x·z<y·z

      -- 10. 0 < 1.
      item-10 with ·-inv#0 _ _ (·-identity 1f .fst) .fst
      -- For item 10, since 1 has multiplicative inverse 1, it is apart from 0, hence 0 < 1 ∨ 1 < 0.
      ... | inl 1<0 = snd (
        -- If 1 < 0 then by item 4 we have 0 < −1 and so by (∗) we get 0 < (−1) · (−1), that is, 0 < 1, so by transitivity 1 < 1, contradicting irreflexivity of <.
          1f          < 0f                ⇒ᵖ⟨ +-preserves-< 1f 0f (- 1f) ⟩
          1f    - 1f  < 0f - 1f           ⇒ᵖ⟨ transport (λ i → [ +-rinv 1f i < snd (+-identity (- 1f)) i ]) ⟩
          0f          <    - 1f           ⇒ᵖ⟨ ( λ 0<-1 → ·-preserves-< 0f (- 1f) (- 1f) 0<-1 0<-1) ⟩
          0f · (- 1f) <   (- 1f) · (- 1f) ⇒ᵖ⟨ pathTo⇒ (cong₂ _<_ (RingTheory'.0-leftNullifies (- 1f)) refl) ⟩
          0f          <   (- 1f) · (- 1f) ⇒ᵖ⟨ transport (λ i → [ 0f < RingTheory'.-commutesWithRight-· (- 1f) (1f)   i  ]) ⟩
          0f          < -((- 1f) ·    1f )⇒ᵖ⟨ transport (λ i → [ 0f < RingTheory'.-commutesWithLeft-·  (- 1f)  1f (~ i) ]) ⟩
          0f          < (-(- 1f))·    1f  ⇒ᵖ⟨ transport (λ i → [ 0f < (Group'Properties.-involutive 1f i · 1f) ]) ⟩
          0f          <      1f  ·    1f  ⇒ᵖ⟨ transport (λ i → [ 0f < fst (·-identity 1f) i ]) ⟩
          0f          <      1f           ⇒ᵖ⟨ <-trans _ _ _ 1<0 ⟩
          1f          <      1f           ⇒ᵖ⟨ <-irrefl 1f ⟩
                      ⊥                   ⇒ᵖ⟨ ⊥-elim ⟩
          0f          <      1f           ◼ᵖ) 1<0
      ... | inr 0<1 = 0<1

  -- Conversely, assume the 10 listed items—in particular, items 4, 5 and 9.
  module item459⇒ -- 4. 5. 9. ⇒ 6.
    (item-4 : [ Item-4 ]) -- ∀[ x ] ∀[ y ] ∀[ z ]                          x < y ⇔ x + z < y + z
    (item-5 : [ Item-5 ]) -- ∀[ x ] ∀[ y ]        0f < x + y          ⇒ (0f < x) ⊔ (0f < y)
    (item-9 : [ Item-9 ]) -- ∀[ x ] ∀[ y ] ∀[ z ] 0f < z              ⇒   (x < y ⇔ x · z < y · z)
    where
    abstract
      item-4' : ∀ x y → [ 0f < x - y ] → [ y < x ]
      +-<-ext : [ is-+-<-Extensional _+_ _<_ ]
      private
        lemma : ∀ x y z w → (z + w) + ((- x) + (- y)) ≡ (z - x) + (w - y)

      item-4' x y = snd (
        0f     <  x - y         ⇒ᵖ⟨ fst (item-4 0f (x + (- y)) y) ⟩
        0f + y < (x - y) + y    ⇒ᵖ⟨ transport (λ i → [ snd (+-identity y) i < sym (+-assoc x (- y) y) i ]) ⟩
             y <  x + (- y + y) ⇒ᵖ⟨ transport (λ i → [ y < x + snd (+-inv y) i ]) ⟩
             y <  x + 0f        ⇒ᵖ⟨ transport (λ i → [ y < fst (+-identity x) i ]) ⟩
             y <  x ◼ᵖ)

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
      +-<-ext x y z w = snd (
        (x + y)           < (z + w)                     ⇒ᵖ⟨ fst (item-4 (x + y) (z + w) (- (x + y))) ⟩
        (x + y) - (x + y) < (z + w) - (x + y)           ⇒ᵖ⟨ transport (λ i → [ +-rinv (x + y) i < (z + w) + (-dist x y) i ]) ⟩
                       0f < (z +   w) + ((- x) + (- y)) ⇒ᵖ⟨ transport (λ i → [ 0f < lemma x y z w i ]) ⟩
                       0f < (z - x) + (w - y)           ⇒ᵖ⟨ item-5 (z - x) (w - y) ⟩
        (0f < z - x) ⊔ (0f < w - y)                     ⇒ᵖ⟨ (λ q → case q as (0f < z - x) ⊔ (0f < w - y) ⇒ ((x < z) ⊔ (y < w)) of λ
                                                            { (inl p) → inlᵖ (item-4' z x p)
                                                            ; (inr p) → inrᵖ (item-4' w y p)
                                                            }) ⟩
        ( x < z    ) ⊔ ( y < w    ) ◼ᵖ)

    -- 6. (∗)
    ·-preserves-< : [ operation _·_ preserves _<_ when (λ z → 0f < z) ] -- ∀ x y z → 0f < z → x < y → (x · z) < (y · z)
    ·-preserves-< x y z 0<z = item-9 x y z 0<z .fst
