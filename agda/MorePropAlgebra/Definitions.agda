{-# OPTIONS --cubical --no-import-sorts  #-}

module MorePropAlgebra.Definitions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
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


import MoreLogic
open import MoreLogic.Definitions renaming (_ᵗ⇒_ to infixr 0 _ᵗ⇒_)

-- hProps of relations
module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where

  isRefl      =                      ∀[ a ]    R a a
  isIrrefl    =                      ∀[ a ] ¬ (R a a)

  isTrans     =                      ∀[ a ] ∀[ b ] ∀[ x ] R a b ⇒         R b x ⇒ R a x
  isCotrans   =                      ∀[ a ] ∀[ b ]        R a b ⇒ (∀[ x ] R a x ⊔ R x b)

  -- two variants of asymmetry
  --
  --   IsAsym  R = ∀ a b → [     R a b   ⇒ ¬ R b a ]
  --   IsAsym' R = ∀ a b → [ ¬ (R a b   ⊓    R b a) ]
  --
  -- which are equivalent
  --
  --   isAsymᵖ≡'  :  isAsym  R ≡ isAsym'  R
  --
  -- but it seems that this one is not equivalent:
  --
  --   ∀ a b → [ (¬ R b a) ⇒ R a b ]

  isSym       =                      ∀[ a ] ∀[ b ]     R a b ⇒   R b a
  isAsym      =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬ R b a
  isAsym'     =                      ∀[ a ] ∀[ b ] ¬ (R a b ⊓    R b a)
  isAsym''    =                      ∀[ a ] ∀[ b ] ¬  R a b ⇒    R b a  -- not equivalent! (weaker)

  isAntisym   =                      ∀[ a ] ∀[ b ]     R a b ⇒             R b a   ⇒            a ≡ₚ b
  isAntisymˢ  = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒             R b a   ⇒ ([ isset ] a ≡ˢ b)
  isAntisym'  =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬(          a ≡ₚ b) ⇒            R b a
  isAntisymˢ' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒ ¬([ isset ] a ≡ˢ b) ⇒            R b a

  -- tightness is closely related to antisymmetry:
  --
  --   R-antisym : [    R a b ] → [    R b a ] → a ≡ b
  --   R-tight   : [ ¬ R a b ] → [ ¬ R b a ] → a ≡ b
  --
  -- this becomes even more obvious if we regard the intended use: when _≤_ and _#_ are derived from _<_
  --
  --    a ≤ b = ¬ (b < a)
  --    a # b = ¬ ([ a < b ] ⊎ [ b < a ])
  --
  -- and indeed, we get
  --
  --   isTight   _<_ ≡ isAntisym   (λ a b → ¬ (b < a))
  --   isTight'  _<_ ≡ isTight'''  (λ a b → (a < b) ⊔ (b < a))
  --
  -- In that case, `≤-antisym` and `#-tight` are almost the same, definitionally:
  --
  --   ≤-antisym : [ ¬ (b < a) ] → [ ¬ (a < b) ] → a ≡ b
  --   ≤-antisym : [ ¬ (b < a) ] × [ ¬ (a < b) ] → a ≡ b -- by curry/uncurry
  --   ≤-antisym : ¬ᵗ ( [ b < a ]  ⊎     [ a < b ]) → a ≡ b -- by deMorgan
  --   #-tight   : [ ¬ (a < b) ] → [ ¬ (b < a) ] → a ≡ b
  --   #-tight   : [ ¬ (a < b) ] × [ ¬ (b < a) ] → a ≡ b -- by curry/uncurry
  --   #-tight   : ¬ᵗ ( [ a < b ]  ⊎     [ b < a ]) → a ≡ b -- by deMorgan
  --
  -- We provide a few variants of tightness
  --
  --   IsTight           R = ∀ a b → [ ¬    R a b   ⇒   ¬ R b a      ⇒   a ≡ₚ b ] -- on _<_, "canonical"
  --   IsTightˢ    isset R = ∀ a b → [ ¬    R a b ] → [ ¬ R b a ]    →   a ≡  b   -- on _<_
  --   IsTight'          R = ∀ a b → [ ¬ (  R a b   ⊔      R b a  )   ⇒   a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ'≡'''`
   --   IsTightˢ'   isset R = ∀ a b → [ ¬ (  R a b   ⊔      R b a  ) ] →   a ≡  b   -- on _<_
  --   IsTight''         R = ∀ a b →   ¬ᵗ  ([ R a b ] ⊎ [    R b a ])   → [ a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ''≡'''`
   --   IsTightˢ''  isset R = ∀ a b →   ¬ᵗ  ([ R a b ] ⊎ [    R b a ])   →   a ≡  b   -- on _<_, "convenient"
  --   IsTight'''        R = ∀ a b → [ ¬    R a b                     ⇒   a ≡ₚ b ] -- on _#_
  --   IsTightˢ''' isset R = ∀ a b →   ¬ᵗ   [ R a b ]                   →   a ≡  b   -- on _#_, also "convenient"
  --
  -- where the very first one, `IsTight` corresponds to a "canonical" definition,
  -- the later one, `IsTightˢ''` is the "most convenient" one to use for `a # b = ¬ ([ a < b ] ⊎ [ b < a ])` on sets.
  -- and the last ones `IsTight'''` and `IsTightˢ'''` are for "_#_" instead of "_<_".
  --
  -- These tightness definitions are all equivalent in the following sense:
  --
  --   isTight-ˢ≡        : (is-set : isSet A)         → isTightˢ    is-set _<_ ≡ isTight     _<_
  --   isTight-ˢ'≡'      : (is-set : isSet A)         → isTightˢ'   is-set _<_ ≡ isTight'    _<_
  --   isTight-ˢ''≡''    : (is-set : isSet A)         → isTightˢ''  is-set _<_ ≡ isTight''   _<_
  --   isTight-ˢ'''≡'''  : (is-set : isSet A)         → isTightˢ''' is-set _#_ ≡ isTight'''  _#_
  --   isTight-≡'        :                              isTight            _<_ ≡ isTight'    _<_
  --   isTight-'≡''      :                              isTight'           _<_ ≡ isTight''   _<_
  --   isTight-'≡'''     :                              isTight'           _<_ ≡ isTight'''  (λ a b →                (a < b) ⊔  (b < a))
  --   isTight-''≡'''    : (<-asym : [ isAsym  _<_ ]) → isTight''          _<_ ≡ isTight'''  (λ a b → [ <-asym a b ] (a < b) ⊎ᵖ (b < a))
  --
  -- where `isTight-ᵖ'≡'''`  and `isTight-ᵖ''≡'''`  hold definitionally.

  isTight     =                      ∀[ a ] ∀[ b ]      ¬ R a b   ⇒  ¬ R b a      ⇒           a ≡ₚ b
  isTightˢ    = λ(isset : isSet A) → ∀[ a ] ∀[ b ]      ¬ R a b   ⇒  ¬ R b a      ⇒ [ isset ] a ≡ˢ b
  isTight'    =                      ∀[ a ] ∀[ b ]  ¬  (  R a b   ⊔    R b a   )  ⇒           a ≡ₚ b
  isTightˢ'   = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬  (  R a b   ⊔    R b a   )  ⇒ [ isset ] a ≡ˢ b
  isTight''   =                      ∀[ a ] ∀[ b ] (¬ᵗ ([ R a b ] ⊎  [ R b a ])) ᵗ⇒           a ≡ₚ b
  isTightˢ''  = λ(isset : isSet A) → ∀[ a ] ∀[ b ] (¬ᵗ ([ R a b ] ⊎  [ R b a ])) ᵗ⇒ [ isset ] a ≡ˢ b
  isTight'''  =                      ∀[ a ] ∀[ b ]  ¬     R a b                   ⇒           a ≡ₚ b
  isTightˢ''' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬     R a b                   ⇒ [ isset ] a ≡ˢ b

-- common definitions of less equal _≤_ and apartness _#_ with respect to _<_
module _ {ℓ ℓ'} {X : Type ℓ} {_<_ : hPropRel X X ℓ'} where

  _#'_ : hPropRel X X ℓ'
  _#'_ x y = (x < y) ⊔ (y < x)

  -- a variant that omits propositional truncation by using asymmetry of _<_
  _#''_ : {<-asym : [ isAsym  _<_ ]} → hPropRel X X ℓ'
  _#''_ {<-asym = <-asym} x y = [ <-asym x y ] (x < y) ⊎ᵖ (y < x)

  _≤'_ : hPropRel X X ℓ'
  _≤'_ x y = ¬ (y < x)

  -- this is how Bridges 1999 defines _≤_
  _≤''_ : hPropRel X X (ℓ-max ℓ ℓ')
  x ≤'' y = ∀[ ε ] (y < ε) ⇒ (x < ε) -- (∀ ε → [ y < ε ] → [ x < ε ]) , isPropΠ2 (λ ε y<ε → isProp[] (x < ε))

-- combined hProps of relations
module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where

  record IsApartnessRel : Type (ℓ-max ℓ ℓ') where
    constructor isapartnessrel
    field
      is-irrefl  : [ isIrrefl   R ]
      is-sym     : [ isSym      R ]
      is-cotrans : [ isCotrans  R ]

  isApartnessRel  : hProp (ℓ-max ℓ ℓ')
  isApartnessRel  .fst = IsApartnessRel
  isApartnessRel  .snd (isapartnessrel a₀ b₀ c₀) (isapartnessrel a₁ b₁ c₁) = φ where
    abstract φ = λ i → isapartnessrel (snd (isIrrefl  R) a₀ a₁ i) (snd (isSym  R) b₀ b₁ i) (snd (isCotrans  R) c₀ c₁ i)

  record IsStrictPartialOrder : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorder
    field
      is-irrefl  : [ isIrrefl   R ]
      is-trans   : [ isTrans    R ]
      is-cotrans : [ isCotrans  R ]

  isStrictPartialOrder  : hProp (ℓ-max ℓ ℓ')
  isStrictPartialOrder  .fst = IsStrictPartialOrder
  isStrictPartialOrder  .snd (isstrictpartialorder a₀ b₀ c₀) (isstrictpartialorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → isstrictpartialorder (snd (isIrrefl  R) a₀ a₁ i) (snd (isTrans  R) b₀ b₁ i) (snd (isCotrans  R) c₀ c₁ i)

  record IsPreorder : Type (ℓ-max ℓ ℓ') where
    constructor ispreorder
    field
      is-refl    : [ isRefl   R ]
      is-trans   : [ isTrans  R ]

  isPreorder  : hProp (ℓ-max ℓ ℓ')
  isPreorder  .fst = IsPreorder
  isPreorder  .snd (ispreorder a₀ b₀) (ispreorder a₁ b₁) = φ where
    abstract φ = λ i → ispreorder (snd (isRefl  R) a₀ a₁ i) (snd (isTrans  R) b₀ b₁ i)

  record IsPartialOrder : Type (ℓ-max ℓ ℓ') where
    constructor ispartialorder
    field
      is-refl    : [ isRefl     R ]
      is-antisym : [ isAntisym  R ]
      is-trans   : [ isTrans    R ]

  isParialOrder  : hProp (ℓ-max ℓ ℓ')
  isParialOrder  .fst = IsPartialOrder
  isParialOrder  .snd (ispartialorder a₀ b₀ c₀) (ispartialorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → ispartialorder (snd (isRefl  R) a₀ a₁ i) (snd (isAntisym  R) b₀ b₁ i) (snd (isTrans  R) c₀ c₁ i)
