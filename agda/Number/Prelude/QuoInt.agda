{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Prelude.QuoInt where

open import Cubical.HITs.Ints.QuoInt public using
  ( ℤ
  ; HasFromNat
  ; HasFromNeg
  ; Int≡ℤ
  ; signed
  ; posneg
  ; ℤ→Int
  ; sucℤ
  ; predℤ
  ; pos
  ; neg
  ; sucℤ-+ʳ
  ; Sign
  ; spos
  ; sneg
  ) renaming
  ( isSetℤ         to is-setᶻ
  ; _+_            to _+ᶻ_
  ; _*_            to _·ᶻ_
  ; -_             to infixl 6 -ᶻ_
  ; *-comm         to ·ᶻ-comm
  ; *-assoc        to ·ᶻ-assoc
  ; +-comm         to +ᶻ-comm
  ; +-assoc        to +ᶻ-assoc
  ; sign           to signᶻ
  ; abs            to absᶻ
  ; _*S_           to _·ˢ_
  )

open import Number.Instances.QuoInt public using
  ( ℤlattice
  ; ⊕-identityʳ
  ) renaming
  ( is-LinearlyOrderedCommRing to is-LinearlyOrderedCommRingᶻ
  ; min                   to minᶻ
  ; max                   to maxᶻ
  ; _<_                   to _<ᶻ_
  ; ·-reflects-<          to ·ᶻ-reflects-<ᶻ
  ; ·-reflects-<ˡ         to ·ᶻ-reflects-<ᶻˡ
  ; 0<1                   to 0<1
  ; +-reflects-<          to +ᶻ-reflects-<ᶻ
  ; +-preserves-<         to +ᶻ-preserves-<ᶻ
  ; +-creates-<           to +ᶻ-creates-<ᶻ
  ; suc-creates-<         to suc-creates-<ᶻ
  ; +-creates-≤           to +ᶻ-creates-≤ᶻ
  ; ·-creates-<           to ·ᶻ-creates-<ᶻ
  ; ·-creates-≤           to ·ᶻ-creates-≤ᶻ
  ; ·-creates-≤-≡         to ·ᶻ-creates-≤ᶻ-≡
  ; ≤-dicho               to ≤ᶻ-dicho
  ; ≤-min-+               to ≤ᶻ-minᶻ-+ᶻ
  ; ≤-max-+               to ≤ᶻ-maxᶻ-+ᶻ
  ; ≤-min-·               to ≤ᶻ-minᶻ-·ᶻ
  ; ≤-max-·               to ≤ᶻ-maxᶻ-·ᶻ
  ; +-min-distribʳ        to +ᶻ-minᶻ-distribʳ
  ; ·-min-distribʳ        to ·ᶻ-minᶻ-distribʳ
  ; +-max-distribʳ        to +ᶻ-maxᶻ-distribʳ
  ; ·-max-distribʳ        to ·ᶻ-maxᶻ-distribʳ
  ; +-min-distribˡ        to +ᶻ-minᶻ-distribˡ
  ; ·-min-distribˡ        to ·ᶻ-minᶻ-distribˡ
  ; +-max-distribˡ        to +ᶻ-maxᶻ-distribˡ
  ; ·-max-distribˡ        to ·ᶻ-maxᶻ-distribˡ
  ; pos<pos[suc]          to pos<ᶻpos[suc]
  ; 0<ᶻpos[suc]           to 0<ᶻpos[suc]
  ; ·-nullifiesˡ          to ·ᶻ-nullifiesˡ
  ; ·-nullifiesʳ          to ·ᶻ-nullifiesʳ
  ; ·-preserves-0<        to ·ᶻ-preserves-0<ᶻ
  ; ·-reflects-0<         to ·ᶻ-reflects-0<ᶻ
  ; ·-creates-<-≡         to ·ᶻ-creates-<ᶻ-≡
  ; -flips-<0             to -flips-<ᶻ0
  ; -flips-<              to -ᶻ-flips-<ᶻ
  ; -identity-·           to -ᶻ-identity-·ᶻ
  ; -distˡ                to -ᶻ-distˡ
  ; ·-reflects-<-flippedˡ to ·ᶻ-reflects-<ᶻ-flippedˡ
  ; ·-reflects-<-flippedʳ to ·ᶻ-reflects-<ᶻ-flippedʳ
  ; #-dicho               to #ᶻ-dicho
  ; ·-preserves-signˡ     to ·ᶻ-preserves-signᶻˡ
  ; #⇒≢                   to #ᶻ⇒≢
  ; <-split-pos           to <ᶻ-split-pos
  ; <-split-neg           to <ᶻ-split-neg
  ; <0-sign               to <ᶻ0-signᶻ
  ; 0<-sign               to 0<ᶻ-signᶻ
  ; sign-pos              to signᶻ-pos
  )

open import Number.Structures2
open IsLinearlyOrderedCommRing is-LinearlyOrderedCommRingᶻ public using () renaming
  ( _-_           to _-ᶻ_
  ; <-irrefl      to <ᶻ-irrefl
  ; <-trans       to <ᶻ-trans
  ; +-<-ext       to +ᶻ-<-ext
  ; +-rinv        to +ᶻ-rinv
  ; +-identity    to +ᶻ-identity
  ; _≤_           to _≤ᶻ_
  ; ·-preserves-< to ·ᶻ-preserves-<ᶻ
  ; <-tricho      to <ᶻ-tricho
  ; <-asym        to <ᶻ-asym
  ; _#_           to _#ᶻ_
  ; ·-identity    to ·ᶻ-identity
  )

open import MorePropAlgebra.Properties.Lattice ℤlattice
open OnSet is-setᶻ public using () renaming
  ( min-≤              to minᶻ-≤ᶻ
  ; max-≤              to maxᶻ-≤ᶻ
  ; ≤-reflectsʳ-≡      to ≤ᶻ-reflectsʳ-≡
  ; ≤-reflectsˡ-≡      to ≤ᶻ-reflectsˡ-≡
  ; min-identity       to minᶻ-identity
  ; min-identity-≤     to minᶻ-identity-≤ᶻ
  ; max-identity-≤     to maxᶻ-identity-≤ᶻ
  ; min-comm           to minᶻ-comm
  ; min-assoc          to minᶻ-assoc
  ; max-identity       to maxᶻ-identity
  ; max-comm           to maxᶻ-comm
  ; max-assoc          to maxᶻ-assoc
  ; min-max-absorptive to minᶻ-maxᶻ-absorptive
  ; max-min-absorptive to maxᶻ-minᶻ-absorptive
  )
