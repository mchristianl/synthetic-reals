{-# OPTIONS --cubical --no-import-sorts  #-}

module MorePropAlgebra.Definitions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)-- ¬ᵗ_
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import MoreLogic.Definitions

-- hProps of relations
module _ {ℓ ℓ' : Level} {A : Type ℓ} (R : hPropRel A A ℓ') where

  isReflᵖ     =                      ∀[ a ]    R a a
  isIrreflᵖ   =                      ∀[ a ] ¬ (R a a)

  isTransᵖ    =                      ∀[ a ] ∀[ b ] ∀[ x ] R a b ⇒         R b x ⇒ R a x
  isCotransᵖ  =                      ∀[ a ] ∀[ b ]        R a b ⇒ (∀[ x ] R a x ⊔ R x b)

  -- two variants of asymmetry
  --
  --   IsAsym  R = ∀ a b → [     R a b   ⇒ ¬ R b a ]
  --   IsAsym' R = ∀ a b → [ ¬ (R a b   ⊓    R b a) ]
  --
  -- which are equivalent
  --
  --   isAsymᵖ≡ᵖ' :  isAsymᵖ R ≡ isAsymᵖ' R
  --
  -- but it seems that this one is not equivalent:
  --
  --   ∀ a b → [ (¬ R b a) ⇒ R a b ]

  isSymᵖ      =                      ∀[ a ] ∀[ b ]     R a b ⇒   R b a
  isAsymᵖ     =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬ R b a
  isAsymᵖ'    =                      ∀[ a ] ∀[ b ] ¬ (R a b ⊓    R b a)
  isAsymᵖ''   =                      ∀[ a ] ∀[ b ] ¬  R a b ⇒    R b a  -- not equivalent! (weaker)

  isAntisymᵖ  =                      ∀[ a ] ∀[ b ]     R a b ⇒             R b a   ⇒            a ≡ₚ b
  isAntisymˢ  = λ(isset : isSet A) → ∀[ a ] ∀[ b ]     R a b ⇒             R b a   ⇒ ([ isset ] a ≡ˢ b)
  isAntisymᵖ' =                      ∀[ a ] ∀[ b ]     R a b ⇒ ¬(          a ≡ₚ b) ⇒            R b a
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
  --   isTightᵖ  _<_ ≡ isAntisymᵖ  (λ a b → ¬ (b < a))
  --   isTightᵖ' _<_ ≡ isTightᵖ''' (λ a b → (a < b) ⊔ (b < a))
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
  --   IsTight'          R = ∀ a b → [ ¬ (  R a b   ⊔      R b a  )   ⇒   a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ'≡ᵖ'''`
  --   IsTightˢ'   isset R = ∀ a b → [ ¬ (  R a b   ⊔      R b a  ) ] →   a ≡  b   -- on _<_
  --   IsTight''         R = ∀ a b →   ¬ᵗ  ([ R a b ] ⊎ [    R b a ])   → [ a ≡ₚ b ] -- on _<_, definitional `isTight-ᵖ''≡ᵖ'''`
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
  --   isTight-ˢ≡ᵖ       : (isset : isSet A)          → isTightˢ    isset _<_ ≡ isTightᵖ    _<_
  --   isTight-ˢ'≡ᵖ'     : (isset : isSet A)          → isTightˢ'   isset _<_ ≡ isTightᵖ'   _<_
  --   isTight-ˢ''≡ᵖ''   : (isset : isSet A)          → isTightˢ''  isset _<_ ≡ isTightᵖ''  _<_
  --   isTight-ˢ'''≡ᵖ''' : (isset : isSet A)          → isTightˢ''' isset _#_ ≡ isTightᵖ''' _#_
  --   isTight-ᵖ≡ᵖ'      :                              isTightᵖ          _<_ ≡ isTightᵖ'   _<_
  --   isTight-ᵖ'≡ᵖ''    :                              isTightᵖ'         _<_ ≡ isTightᵖ''  _<_
  --   isTight-ᵖ'≡ᵖ'''   :                              isTightᵖ'         _<_ ≡ isTightᵖ''' (λ a b →  ( a < b ) ⊔ ( b < a )   )
  --   isTight-ᵖ''≡ᵖ'''  : (<-asym : [ isAsymᵖ _<_ ]) → isTightᵖ''        _<_ ≡ isTightᵖ''' (λ a b → ([ a < b ] ⊎ [ b < a ]) , ⊎-isProp (a < b) (b < a) (inl (<-asym a b)))
  --
  -- where `isTight-ᵖ'≡ᵖ'''` and `isTight-ᵖ''≡ᵖ'''` hold definitionally.

  isTightᵖ    =                      ∀[ a ] ∀[ b ]      ¬ R a b   ⇒  ¬ R b a      ⇒           a ≡ₚ b
  isTightˢ    = λ(isset : isSet A) → ∀[ a ] ∀[ b ]      ¬ R a b   ⇒  ¬ R b a      ⇒ [ isset ] a ≡ˢ b
  isTightᵖ'   =                      ∀[ a ] ∀[ b ]  ¬  (  R a b   ⊔    R b a   )  ⇒           a ≡ₚ b
  isTightˢ'   = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬  (  R a b   ⊔    R b a   )  ⇒ [ isset ] a ≡ˢ b
  isTightᵖ''  =                      ∀[ a ] ∀[ b ] (¬ᵗ ([ R a b ] ⊎  [ R b a ])) ᵗ⇒           a ≡ₚ b
  isTightˢ''  = λ(isset : isSet A) → ∀[ a ] ∀[ b ] (¬ᵗ ([ R a b ] ⊎  [ R b a ])) ᵗ⇒ [ isset ] a ≡ˢ b
  isTightᵖ''' =                      ∀[ a ] ∀[ b ]  ¬     R a b                   ⇒           a ≡ₚ b
  isTightˢ''' = λ(isset : isSet A) → ∀[ a ] ∀[ b ]  ¬     R a b                   ⇒ [ isset ] a ≡ˢ b

-- common definitions of less equal _≤_ and apartness _#_ with respect to _<_
module _ {ℓ ℓ'} {X : Type ℓ} {_<_ : hPropRel X X ℓ'} where

  _#'_ : hPropRel X X ℓ'
  _#'_ x y = (x < y) ⊔ (y < x)

  -- a variant that omits propositional truncation by using asymmetry of _<_
  _#''_ : {<-asym : [ isAsymᵖ _<_ ]} → hPropRel X X ℓ'
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
      isIrrefl  : [ isIrreflᵖ  R ]
      isSym     : [ isSymᵖ     R ]
      isCotrans : [ isCotransᵖ R ]

  isApartnessRelᵖ : hProp (ℓ-max ℓ ℓ')
  isApartnessRelᵖ .fst = IsApartnessRel
  isApartnessRelᵖ .snd (isapartnessrel a₀ b₀ c₀) (isapartnessrel a₁ b₁ c₁) = φ where
    abstract φ = λ i → isapartnessrel (snd (isIrreflᵖ R) a₀ a₁ i) (snd (isSymᵖ R) b₀ b₁ i) (snd (isCotransᵖ R) c₀ c₁ i)

  record IsStrictPartialOrder : Type (ℓ-max ℓ ℓ') where
    constructor isstrictpartialorder
    field
      isIrrefl  : [ isIrreflᵖ  R ]
      isTrans   : [ isTransᵖ   R ]
      isCotrans : [ isCotransᵖ R ]

  isStrictPartialOrderᵖ : hProp (ℓ-max ℓ ℓ')
  isStrictPartialOrderᵖ .fst = IsStrictPartialOrder
  isStrictPartialOrderᵖ .snd (isstrictpartialorder a₀ b₀ c₀) (isstrictpartialorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → isstrictpartialorder (snd (isIrreflᵖ R) a₀ a₁ i) (snd (isTransᵖ R) b₀ b₁ i) (snd (isCotransᵖ R) c₀ c₁ i)

  record IsPreorder : Type (ℓ-max ℓ ℓ') where
    constructor ispreorder
    field
      isRefl    : [ isReflᵖ  R ]
      isTrans   : [ isTransᵖ R ]

  isPreorderᵖ : hProp (ℓ-max ℓ ℓ')
  isPreorderᵖ .fst = IsPreorder
  isPreorderᵖ .snd (ispreorder a₀ b₀) (ispreorder a₁ b₁) = φ where
    abstract φ = λ i → ispreorder (snd (isReflᵖ R) a₀ a₁ i) (snd (isTransᵖ R) b₀ b₁ i)

  record IsPartialOrder : Type (ℓ-max ℓ ℓ') where
    constructor ispartialorder
    field
      isRefl    : [ isReflᵖ    R ]
      isAntisym : [ isAntisymᵖ R ]
      isTrans   : [ isTransᵖ   R ]

  isParialOrderᵖ : hProp (ℓ-max ℓ ℓ')
  isParialOrderᵖ .fst = IsPartialOrder
  isParialOrderᵖ .snd (ispartialorder a₀ b₀ c₀) (ispartialorder a₁ b₁ c₁) = φ where
    abstract φ = λ i → ispartialorder (snd (isReflᵖ R) a₀ a₁ i) (snd (isAntisymᵖ R) b₀ b₁ i) (snd (isTransᵖ R) c₀ c₁ i)
