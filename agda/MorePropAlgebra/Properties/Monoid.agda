{-# OPTIONS --cubical --no-import-sorts  #-}

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Function.Base using (_∋_; _$_)
import Cubical.Algebra.Monoid as Std
open import MorePropAlgebra.Bundles

module MorePropAlgebra.Properties.Monoid {ℓ} (assumptions : Monoid {ℓ}) where
open Monoid assumptions renaming (Carrier to F)

import MorePropAlgebra.Properties.Semigroup
module Semigroup'Properties = MorePropAlgebra.Properties.Semigroup   (record { Monoid assumptions })
module Semigroup'           =                            Semigroup   (record { Monoid assumptions })
(      Semigroup')          =                            Semigroup ∋ (record { Monoid assumptions })

stdIsMonoid : Std.IsMonoid ε _·_
stdIsMonoid  .Std.IsMonoid.isSemigroup = Semigroup'Properties.stdIsSemigroup
stdIsMonoid  .Std.IsMonoid.identity    = is-identity

stdMonoid : Std.Monoid {ℓ}
stdMonoid = record { Monoid assumptions ; isMonoid = stdIsMonoid }
