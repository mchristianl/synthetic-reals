{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Definitions where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic

open import Utils
open import MoreLogic.Definitions
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions
open import MorePropAlgebra.Consequences
open import MorePropAlgebra.Structures
