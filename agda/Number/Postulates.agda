{-# OPTIONS --cubical --no-import-sorts #-}

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

module Number.Postulates where

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base -- Rel

-- open import Data.Nat.Base using (ℕ) renaming (_≤_ to _≤ₙ_)
-- open import Cubical.Data.Nat using (zero; suc) renaming (ℕ to Nat; _+_ to _+ₙ_)
-- open import Cubical.Data.Nat.Order renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

-- open import Cubical.Data.Unit.Base -- Unit
-- open import Cubical.Data.Empty -- ⊥
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
-- open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
-- open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`
-- open import Cubical.Data.Maybe.Base
open import Cubical.Relation.Binary.Base -- Rel
open import Function.Base using (_∋_)

postulate
  ℝℓ ℝℓ' : Level

open import Number.Structures ℝℓ ℝℓ'
open import Number.Bundles    ℝℓ ℝℓ'
open import Number.Inclusions ℝℓ ℝℓ'

import MoreAlgebra


Lift₂ : {A : Type₀} → Rel A A ℓ-zero → Rel (Lift {ℓ-zero} {ℓ} A) (Lift {ℓ-zero} {ℓ} A) ℓ'
Lift₂ _•_ (lift x) (lift y) = Lift (x • y)

Lift₂' : {A : Type₀} → (A → A → A) → (Lift {ℓ-zero} {ℓ} A) → (Lift {ℓ-zero} {ℓ} A) → (Lift {ℓ-zero} {ℓ} A)
Lift₂' _•_ (lift x) (lift y) = lift (x • y)


module ℕ* where
  import Cubical.Data.Nat as Nat --  using (ℕ; zero; suc) renaming (_+_ to _+ₙ_)
  import Cubical.Data.Nat.Order as Order -- renaming (zero-≤ to z≤n; suc-≤-suc to s≤s; _≤_ to _≤ₙ_; _<_ to _<ₙ_)

  module Postulates where
    postulate
      min max : Nat.ℕ → Nat.ℕ → Nat.ℕ
      isROrderedCommSemiring : IsROrderedCommSemiring
        (Lift₂  {ℓ = ℝℓ} {ℓ' = ℝℓ'} Order._<_)
        (Lift₂  {ℓ = ℝℓ} {ℓ' = ℝℓ'} Order._≤_)
        (Lift₂  {ℓ = ℝℓ} {ℓ' = ℝℓ'} (MoreAlgebra.Definitions._#'_ {_<_ = Order._<_}))
        (Lift₂' {ℓ = ℝℓ}            min)
        (Lift₂' {ℓ = ℝℓ}            max)
        (lift   {j = ℝℓ}           Nat.zero)
        (lift   {j = ℝℓ}           1)
        (Lift₂' {ℓ = ℝℓ}            Nat._+_)
        (Lift₂' {ℓ = ℝℓ}            Nat._*_)

  -- NOTE: only when
  --       1. making an instance
  --       2. opening the instance
  --       we get the possibility to inspect their inner definition
  --       this is not possible when defining a module first with
  --         `module Module = ROrderedCommSemiring (record {...})`
  --       and then making an instance out of it with
  --         `Bundle : ROrderedCommSemiring`
  --         `Bundle = record { Module }`
  --       then, we can only inspect up to ℕ.Carrier and not further
  module Bundle = ROrderedCommSemiring {ℝℓ} {ℝℓ'}
  Bundle = ROrderedCommSemiring {ℝℓ} {ℝℓ'}

  -- NOTE: a prefix alo appears to a symbol in Have/Goal if the corresponding symbol is imported multiple times
  --       that can be checked with `C-c C-w` 

  -- module members are not normalized on `C-c` `C-.` (only after `C-u`-ing) which is helpful for not cluttering the Have/Goal with "implementation details" of the underlying Carrier type
  -- but if we wanted to 
  
  ℕ = Lift {ℓ-zero} {ℝℓ} Nat.ℕ
  Carrier = ℕ
  -- _<_ = Lift₂  {ℓ = ℝℓ} {ℓ' = ℝℓ'} Order._<_
  -- _≤_ = Lift₂  {ℓ = ℝℓ} {ℓ' = ℝℓ'} Order._≤_
  -- _#_ = Lift₂  {ℓ = ℝℓ} {ℓ' = ℝℓ'} (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
  -- min = Lift₂' {ℓ = ℝℓ}            Postulates.min
  -- max = Lift₂' {ℓ = ℝℓ}            Postulates.max
  -- 0f  = lift   {j = ℝℓ}            Nat.zero
  -- 1f  = lift   {j = ℝℓ}            (Nat.suc Nat.zero)
  -- _+_ = Lift₂' {ℓ = ℝℓ}            Nat._+_
  -- _·_ = Lift₂' {ℓ = ℝℓ}            Nat._*_
  -- isROrderedCommSemiring = Postulates.isROrderedCommSemiring

  {-
  bundle : Bundle
  bundle = (record
    { Carrier = Carrier
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; isROrderedCommSemiring = isROrderedCommSemiring
    })
  -}

  -- NOTE: an `abstract` here would blocks the inner inspection again
  --       unfortunately we cannot "break" this on the "call site"
  --       i.e. we cannot inspect or case-split into the inner structure of these definitions
  --         but this is a necessity
  --       on the other hand, we do want this to be short sometimes
  --       "Abstract applies to only definitions like data definitions, record type definitions and function clauses."

  bundle : Bundle
  bundle = (record
    { Carrier = ℕ -- Lift {ℓ-zero} {ℝℓ} Nat.ℕ
    ; _<_ = Lift₂  Order._<_
    ; _≤_ = Lift₂  Order._≤_
    ; _#_ = Lift₂  (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
    ; min = Lift₂' Postulates.min
    ; max = Lift₂' Postulates.max
    ; 0f  = lift   Nat.zero
    ; 1f  = lift   (Nat.suc Nat.zero)
    ; _+_ = λ x y → Lift₂' Nat._+_ x y
    ; _·_ = Lift₂' Nat._*_
    ; isROrderedCommSemiring = Postulates.isROrderedCommSemiring
    })

  {-
  abstract
    bundle' : Bundle
    bundle' = (record
      { Carrier = Lift {ℓ-zero} {ℝℓ} Nat.ℕ
      ; _<_ = Lift₂  Order._<_
      ; _≤_ = Lift₂  Order._≤_
      ; _#_ = Lift₂  (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
      ; min = Lift₂' Postulates.min
      ; max = Lift₂' Postulates.max
      ; 0f  = lift   Nat.zero
      ; 1f  = lift   (Nat.suc Nat.zero)
      ; _+_ = Lift₂' Nat._+_
      ; _·_ = Lift₂' Nat._*_
      ; isROrderedCommSemiring = Postulates.isROrderedCommSemiring
      })
  -}

  -- Bundle : ROrderedCommSemiring
  -- Bundle = record { Module }

  {-
  module Translated = ROrderedCommSemiring Bundle
      renaming
      ( Carrier to ℕ
      ; _<_ to _<ⁿ_
      ; _≤_ to _≤ⁿ_
      ; _#_ to _#ⁿ_
      ; min to minⁿ
      ; max to maxⁿ
      ; 0f  to 0ⁿ 
      ; 1f  to 1ⁿ 
      ; _+_ to _+ⁿ_
      ; _·_ to _·ⁿ_
      ; isROrderedCommSemiring to isROrderedCommSemiringⁿ
      )
  -}

  {- NOTE
  it seems that the last module which brings something into scope will be used on C-u C-c C-*
  therefore, we have to open this module ℕ directly and not via a proxy-module called `Module` that lives inside of it
  the "translated" module then is a separate one, which is just called ℕⁿ

  this also applies to the "call site", so when we are opening `Agda.Builtin.Nat` and we have not opened our own ℕ-module
    then 2× and 0× `C-u` will display the used `Carrier` as `Nat`
  -}

  -- module Module where
  --   open ROrderedCommSemiring Bundle public
  --   open import Agda.Builtin.Nat using () renaming (Nat to ℕ₀) public -- this makes ℕ₀ prettier in goals

  -- open Bundle bundle using () renaming (Carrier to ℕ) public
  -- ℕ = Bundle.Carrier bundle

  -- NOTE: for the non-operations 0f and 1f it does not matter,
  --       but for the operations min, max, _+_ and _·_ we need this "roundabout" instead of a direct opening of `bundle`
  --       this causes that the Have/Goal type of `x + y` is not immediately expanded but remains a nice `ℕ`
  --       only after `C-u`-ing it gets normalized
  -- NOTE: so although it looks a little ugly, we just write this out here again

  _<_ = Bundle._<_ bundle
  _≤_ = Bundle._≤_ bundle
  _#_ = Bundle._#_ bundle
  min = Bundle.min bundle
  max = Bundle.max bundle
  0f  = Bundle.0f  bundle
  1f  = Bundle.1f  bundle
  _+_ = Bundle._+_ bundle
  _·_ = Bundle._·_ bundle
  isROrderedCommSemiring = Bundle.isROrderedCommSemiring bundle

  open IsROrderedCommSemiring isROrderedCommSemiring public

  {-
  --open Bundle bundle hiding (_<_) public --  renaming (Carrier to ℕ) public
  -- open Module renaming (Carrier to ℕ) public
  ℕ = Bundle.Carrier bundle
  -- Carrier = Bundle.Carrier bundle
  _<_ = Bundle._<_ bundle
  _≤_ = Bundle._≤_ bundle
  _#_ = Bundle._#_ bundle
  min = Bundle.min bundle
  max = Bundle.max bundle
  0f  = Bundle.0f  bundle
  1f  = Bundle.1f  bundle
  _+_ = Bundle._+_ bundle
  _·_ = Bundle._·_ bundle
  isROrderedCommSemiring = Bundle.isROrderedCommSemiring bundle
  -}
  
  {-
  Carrier = Lift {ℓ-zero} {ℝℓ} Nat.ℕ
  isROrderedCommSemiring
  -}

  -- Carrier = ℕ
  -- ℕ = Carrier
  open import Agda.Builtin.Nat using () renaming (Nat to ℕ₀) public -- this makes ℕ₀ prettier in goals
  -- import Agda.Builtin.Nat
  -- ℕ₀ = Agda.Builtin.Nat.Nat
  --ℕ₀ = Nat.ℕ

{-
module ℕⁿ where
  Carrierⁿ = ℕ.Carrier
  _<ⁿ_ = ℕ._<_
  _≤ⁿ_ = ℕ._≤_
  _#ⁿ_ = ℕ._#_
  minⁿ = ℕ.min
  maxⁿ = ℕ.max
  0ⁿ   = ℕ.0f 
  1ⁿ   = ℕ.1f 
  _+ⁿ_ = ℕ._+_
  _·ⁿ_ = ℕ._·_
  isROrderedCommSemiringⁿ = ℕ.isROrderedCommSemiring
-}

module ℕ = ℕ* hiding (ℕ; ℕ₀)

module ℕⁿ = ℕ* -- .Bundle
    -- hiding (ℕ)
    renaming
    ( Carrier to Carrierⁿ
    ; _<_ to _<ⁿ_
    ; _≤_ to _≤ⁿ_
    ; _#_ to _#ⁿ_
    ; min to minⁿ
    ; max to maxⁿ
    ; 0f  to 0ⁿ 
    ; 1f  to 1ⁿ 
    ; _+_ to _+ⁿ_
    ; _·_ to _·ⁿ_
    ; isROrderedCommSemiring to isROrderedCommSemiringⁿ
    )

-- NOTE: this needs to come after ℕⁿ to have a the symbols in Have/Goal displayed with a ℕ-prefix instead of the ℕⁿ-prefix
--       ... but this conflicts with a usage of
--       - first, opening ℕⁿ
--       - afterwards, optionally opening ℕ
--       because after opening ℕⁿ things are still prefixed with ℕ.x
--       so ℕⁿ somehow must be the last module that is stated
-- module ℕ = ℕ' hiding (ℕ; ℕ₀)

-- THESIS: so the order in which modules are stated/imported matters because only the last path will be displayed as "the" prefix in Have/Goal
--         this means the prefix that is added to a symbol when it's module is not (!) opened
--         so this affects symbols that are reachable via multiple "pathes"
--           this is likely inherited from how the function clause definition's scope is created to the call-site
--           so the function clause definition "decides" which path it means for which symbol
--           this would make the prefix(-path) a property of the function clause definition
--           and we can only "remove" parts of this path by opening modules
--         when a symbols module is opened, then it is displayed in Have/Goal without a prefix
--         when a symbols module is opened multiple times, then again a prefix is displayed because of ambiguity

-- NOTE: so we might try again the variant with "global" ℕ ℤ ℚ ℝ and ℂ

--  Carrier = ℕ
--  open import Agda.Builtin.Nat using () renaming (Nat to ℕ₀) public -- this makes ℕ₀ prettier in goals
  
  
      
  {-
  open ROrderedCommSemiring (record
    { Carrier = Lift {ℓ-zero} {ℝℓ} Nat.ℕ
    ; _<_ = Lift₂  Order._<_
    ; _≤_ = Lift₂  Order._≤_
    ; _#_ = Lift₂  (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
    ; min = Lift₂' Postulates.min
    ; max = Lift₂' Postulates.max
    ; 0f  = lift   Nat.zero
    ; 1f  = lift   (Nat.suc Nat.zero)
    ; _+_ = Lift₂' Nat._+_
    ; _·_ = Lift₂' Nat._*_
    ; isROrderedCommSemiring = Postulates.isROrderedCommSemiring
    }) public

  -- module Module     = ROrderedCommSemiring Bundle
  Bundle : ROrderedCommSemiring
  Bundle = 
    ( record
    { Carrier = Carrier
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; isROrderedCommSemiring = isROrderedCommSemiring
    } )
  -}

  {-
  module Translated = ROrderedCommSemiring
    ( record
    { Carrier = Carrier
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; isROrderedCommSemiring = isROrderedCommSemiring
    } )
    renaming
    ( Carrier to ℕ
    ; _<_ to _<ⁿ_
    ; _≤_ to _≤ⁿ_
    ; _#_ to _#ⁿ_
    ; min to minⁿ
    ; max to maxⁿ
    ; 0f  to 0ⁿ 
    ; 1f  to 1ⁿ 
    ; _+_ to _+ⁿ_
    ; _·_ to _·ⁿ_
    ; isROrderedCommSemiring to isROrderedCommSemiringⁿ
    )
  module Module = ROrderedCommSemiring
    ( record
    { Carrier = Carrier
    ; _<_ = _<_
    ; _≤_ = _≤_
    ; _#_ = _#_
    ; min = min
    ; max = max
    ; 0f  = 0f 
    ; 1f  = 1f 
    ; _+_ = _+_
    ; _·_ = _·_
    ; isROrderedCommSemiring = isROrderedCommSemiring
    } )
  
  open ROrderedCommSemiring (record
    { Carrier = Lift {ℓ-zero} {ℝℓ} Nat.ℕ
    ; _<_ = Lift₂  Order._<_
    ; _≤_ = Lift₂  Order._≤_
    ; _#_ = Lift₂  (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
    ; min = Lift₂' Postulates.min
    ; max = Lift₂' Postulates.max
    ; 0f  = lift   Nat.zero
    ; 1f  = lift   (Nat.suc Nat.zero)
    ; _+_ = Lift₂' Nat._+_
    ; _·_ = Lift₂' Nat._*_
    ; isROrderedCommSemiring = Postulates.isROrderedCommSemiring
    }) renaming (Carrier to ℕ') public
  -}

  

{-
module Foo where
  -- open import Agda.Builtin.Nat using () renaming (Nat to ℕ₀)
  -- open ℕⁿ
  open import Agda.Builtin.Nat using (Nat)
  -- open ℕⁿ
  -- open ROrderedCommSemiring ℕ.Bundle
  _ =  {! ℕⁿ !}
-}

module ℤ where
  module Bundle = ROrderedCommRing     {ℝℓ} {ℝℓ'}
  postulate
    bundle  : ROrderedCommRing     {ℝℓ} {ℝℓ'}

  open Bundle bundle public
  ℤ = Carrier
  
module ℤᶻ = ℤ.Bundle
    renaming
    ( Carrier to ℤ
    ; _<_ to _<ᶻ_
    ; _≤_ to _≤ᶻ_
    ; _#_ to _#ᶻ_
    ; min to minᶻ
    ; max to maxᶻ
    ; 0f  to 0ᶻ
    ; 1f  to 1ᶻ
    ; _+_ to _+ᶻ_
    ; _·_ to _·ᶻ_
    ; -_  to -ᶻ_ 
    ; isROrderedCommRing to isROrderedCommRingᶻ
    )

module ℚ where
  module Bundle = ROrderedField {ℝℓ} {ℝℓ'} renaming (Carrier to ℚ)
  postulate
    bundle   : ROrderedField        {ℝℓ} {ℝℓ'}

  open Bundle bundle public
  Carrier = ℚ

-- NOTE: for removing an instance from an operation, it seem that we have to open that instance at the "call site"
--       e.g. `_#_` from  `ROrderedField` get an additional argument `ℚ.bundle` to which instance it refers to
--       so it becomes
--         `ROrderedField._#_ ℚ.bundle (ℤ↪ℚ x) (ROrderedField.0f ℚ.bundle)`
--       unfortunatelty this is displayed with `_#_` with infix notation in a confusing manner as
--         `(ℚ.bundle ROrderedField.# ℤ↪ℚ x) (ROrderedField.0f ℚ.bundle)`
--       so we need to state a
--         `open ℚᶠ ℚ.bundle`
--       to get a nice looking
--          `ℤ↪ℚ x #ᶠ 0ᶠ`
--       interestingly the `ℚ.bundle` needs to occur at the call-site
--       when we define here 
--         `module ℚᶠ = ℚ.Bundle ℚ.bundle`
--       and then just call `open ℚᶠ` at the call site, this does not work out for hiding the `ℚ.bundle` in Have/Goal
--       but luckily we can do the translation once in the "library" part and use the short idiom `open ℚᶠ ℚ.bundle` at the callsite
-- NOTE: this also makes both the module ℤ and the type ℤ available which is possible in Agda
--       i.e. ℤ refers to both and when using ℤ.something the module ℤ is meant
--       this works out because modules are special "citizens" and cannot occur in places where variables occur and vice versa

module ℚᶠ = ℚ.Bundle
  renaming
  ( _<_ to _<ᶠ_
  ; _≤_ to _≤ᶠ_
  ; _#_ to _#ᶠ_
  ; min to minᶠ
  ; max to maxᶠ
  ; 0f  to 0ᶠ
  ; 1f  to 1ᶠ
  ; _+_ to _+ᶠ_
  ; _·_ to _·ᶠ_
  ; -_  to -ᶠ_ 
  ; _⁻¹ to _⁻¹ᶠ
  ; isROrderedField to isROrderedFieldᶠ
  )

module ℝ where
  module Bundle = ROrderedField {ℝℓ} {ℝℓ'}
  postulate
    bundle : ROrderedField {ℝℓ} {ℝℓ'}

  open Bundle bundle public
  ℝ = Carrier

module ℝʳ = ℝ.Bundle
    renaming
    ( Carrier to ℝ
    ; _<_ to _<ʳ_
    ; _≤_ to _≤ʳ_
    ; _#_ to _#ʳ_
    ; min to minʳ
    ; max to maxʳ
    ; 0f  to 0ʳ
    ; 1f  to 1ʳ
    ; _+_ to _+ʳ_
    ; _·_ to _·ʳ_
    ; -_  to -ʳ_ 
    ; _⁻¹ to _⁻¹ʳ
    ; isROrderedField to isROrderedFieldʳ
    )

module ℂ where
  module Bundle = RField               {ℝℓ} {ℝℓ'}
  postulate
    bundle    : RField               {ℝℓ} {ℝℓ'}

  open Bundle bundle public
  ℂ = Carrier

module ℂᶜ = ℂ.Bundle
    renaming
    ( Carrier to ℂ
    ; _#_ to _#ᶜ_
    ; 0f  to 0ᶜ
    ; 1f  to 1ᶜ
    ; _+_ to _+ᶜ_
    ; _·_ to _·ᶜ_
    ; -_  to -ᶜ_
    ; _⁻¹ to _⁻¹ᶜ
    ; isRField to isRFieldᶜ
    )


module _ where
  open ℕ* using (ℕ)
  postulate
    ℕ↪ℤ    : ℕ → ℤ.ℤ
    ℕ↪ℤinc : IsROrderedCommSemiringInclusion ℕ.bundle (record { ℤ.Bundle ℤ.bundle }) ℕ↪ℤ

    ℕ↪ℚ    : ℕ → ℚ.ℚ
    ℕ↪ℚinc : IsROrderedCommSemiringInclusion ℕ.bundle (record { ℚ.Bundle ℚ.bundle }) ℕ↪ℚ

    ℕ↪ℂ    : ℕ → ℂ.ℂ
    ℕ↪ℂinc : Isℕ↪ℂ ℕ.bundle ℂ.bundle ℕ↪ℂ

    ℕ↪ℝ    : ℕ → ℝ.ℝ
    ℕ↪ℝinc : IsROrderedCommSemiringInclusion ℕ.bundle (record { ℝ.Bundle ℝ.bundle }) ℕ↪ℝ

    ℤ↪ℚ    : ℤ.ℤ → ℚ.ℚ
    ℤ↪ℚinc : IsROrderedCommRingInclusion ℤ.bundle (record { ℚ.Bundle ℚ.bundle }) ℤ↪ℚ

    ℤ↪ℝ    : ℤ.ℤ → ℝ.ℝ
    ℤ↪ℝinc : IsROrderedCommRingInclusion ℤ.bundle (record { ℝ.Bundle ℝ.bundle }) ℤ↪ℝ

    ℤ↪ℂ    : ℤ.ℤ → ℂ.ℂ
    ℤ↪ℂinc : Isℤ↪ℂ ℤ.bundle ℂ.bundle ℤ↪ℂ

    ℚ↪ℝ    : ℚ.ℚ → ℝ.ℝ
    ℚ↪ℝinc : IsROrderedFieldInclusion ℚ.bundle (record { ℝ.Bundle ℝ.bundle }) ℚ↪ℝ

    ℚ↪ℂ    : ℚ.ℚ → ℂ.ℂ
    ℚ↪ℂinc : IsRFieldInclusion (record { ℚ.Bundle ℚ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℚ↪ℂ

    ℝ↪ℂ    : ℝ.ℝ → ℂ.ℂ
    ℝ↪ℂinc : IsRFieldInclusion (record { ℝ.Bundle ℝ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℝ↪ℂ


{-
module Translated where
  open ℕⁿ public
  open ℤᶻ public
  open ℚᶠ public
  open ℝʳ public
  open ℂᶜ public
-}

{-
ℕ = ℕ.ℕ
ℤ = ℤ.ℤ
ℚ = ℚ.ℚ
ℝ = ℝ.ℝ
ℂ = ℂ.ℂ
-}
