{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Instances.QuoIntFromInt where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything hiding (⋆) renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Foundations.Logic renaming (inl to inlᵖ; inr to inrᵖ)

open import Cubical.Relation.Nullary.Base renaming (¬_ to ¬ᵗ_)
open import Cubical.Relation.Binary.Base
open import Cubical.Data.Sum.Base renaming (_⊎_ to infixr 4 _⊎_)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool using (Bool; not; true; false)
open import Cubical.Data.Empty renaming (elim to ⊥-elim; ⊥ to ⊥⊥) -- `⊥` and `elim`
open import Cubical.Foundations.Logic renaming (¬_ to ¬ᵖ_; inl to inlᵖ; inr to inrᵖ)
open import Function.Base using (it; _∋_; _$_)
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation --.Properties

open import Utils using (!_; !!_)
open import MoreLogic.Reasoning
open import MoreLogic.Definitions
open import MoreLogic.Properties
open import MorePropAlgebra.Definitions hiding (_≤''_)
open import MorePropAlgebra.Structures
open import MorePropAlgebra.Bundles
open import MorePropAlgebra.Consequences
open import Number.Structures2
open import Number.Bundles2

import Agda.Builtin.Int as Builtin
import Data.Integer.Base as BuiltinBase
import Data.Integer.Properties as BuiltinProps

open import Number.Instances.Nat using (lemma10''; lemma12'') renaming
  ( _<_ to _<ⁿ_
  ; <-irrefl  to <ⁿ-irrefl
  ; <-cotrans to <ⁿ-cotrans
  ; suc-creates-< to sucⁿ-creates-<ⁿ
  ; 0<suc to 0<ⁿsuc
  ; *-nullifiesʳ to *ⁿ-nullifiesʳ
  ; *-nullifiesˡ to *ⁿ-nullifiesˡ
  ; ·-preserves-< to ·ⁿ-preserves-<ⁿ
  ; +-createsʳ-< to +ⁿ-createsʳ-<ⁿ
  ; +-createsˡ-< to +ⁿ-createsˡ-<ⁿ
  ; ¬suc<0       to ¬suc<ⁿ0
  ; min-comm     to minⁿ-comm
  ; min-tightˡ   to minⁿ-tightˡ
  ; min-tightʳ   to minⁿ-tightʳ
  ; min-identity to minⁿ-identity
  ; max-comm     to maxⁿ-comm
  ; max-tightˡ   to maxⁿ-tightˡ
  ; max-tightʳ   to maxⁿ-tightʳ
  ; max-identity to maxⁿ-identity
  )
open import Data.Nat.Base using () renaming
  ( _⊔_ to maxⁿ
  ; _⊓_ to minⁿ
  ; _+_ to _+ⁿ_
  ; _*_ to _*ⁿ_
  ; pred to predⁿ
  )

open import Cubical.Data.Int renaming
  ( Int to ℤ
  ; isSetInt to isSetℤ
  -- ; neg to infix 8 -_
  ; _-_ to infix 7 _-_
  ; _+_ to infix 5 _+_
  )
-- open import Cubical.HITs.Ints.QuoInt.Properties
open import Cubical.Data.Nat using (suc; zero; ℕ) renaming
  ( +-comm to +ⁿ-comm
  ; +-assoc to +ⁿ-assoc
  ; *-comm to *ⁿ-comm
  ; *-suc to *ⁿ-suc
  ; *-assoc to *ⁿ-assoc
  ; +-suc to +ⁿ-suc
  ; *-distribˡ to *ⁿ-distribˡ
  ; *-distribʳ to *ⁿ-distribʳ
  ; *-identityʳ to *ⁿ-identityʳ
  ; snotz to snotzⁿ
  ; injSuc to injSucⁿ
  )
open import Cubical.Data.Nat.Order using () renaming
  ( <-trans to <ⁿ-trans
  ; _<_ to _<ⁿᵗ_
  ; _≟_ to _≟ⁿ_
  ; lt to ltⁿ
  ; gt to gtⁿ
  ; eq to eqⁿ
  ; ¬-<-zero to ¬-<ⁿ-zero
  )

import Cubical.HITs.Ints.QuoInt as QuoInt

open import Cubical.Foundations.Univalence

open import Number.Instances.Int hiding (ℤbundle)

open import Cubical.Data.Int as Int renaming
  ( Int to ℤ
  ; isSetInt to isSetℤ
  -- ; neg to infix 8 -_
  ; _-_ to infix 7 _-_
  ; _+_ to infix 5 _+_
  )
import Cubical.HITs.Ints.QuoInt as QuoInt

_·_ = QuoInt._*_
Z   = QuoInt.ℤ
Z≡ℤ = sym QuoInt.Int≡ℤ

_*ᶻ_ : ℤ → ℤ → ℤ
_*ᶻ_ = transport (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._*_

QuoInt*≡*ᶻ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._*_ _*ᶻ_
QuoInt*≡*ᶻ i = transp (λ j → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j)) (~ i) QuoInt._*_

lemma1 : ∀ a b → b +ⁿ a *ⁿ suc b ≡ a *ⁿ b +ⁿ (a +ⁿ b)
lemma1 a b =
  b +ⁿ a *ⁿ suc b    ≡⟨ (λ i → b +ⁿ *ⁿ-suc a b i) ⟩
  b +ⁿ (a +ⁿ a *ⁿ b) ≡⟨ +ⁿ-assoc b a (a *ⁿ b) ⟩
  (b +ⁿ a) +ⁿ a *ⁿ b ≡⟨ (λ i → +ⁿ-comm b a i +ⁿ a *ⁿ b) ⟩
  (a +ⁿ b) +ⁿ a *ⁿ b ≡⟨ +ⁿ-comm (a +ⁿ b) (a *ⁿ b) ⟩
  a *ⁿ b +ⁿ (a +ⁿ b) ∎

*ᶻ≡*' : ∀ a b → a *ᶻ b ≡ a * b
*ᶻ≡*' (pos      0 ) (pos      0 )   = refl
*ᶻ≡*' (pos      0 ) (pos (suc b))   = refl
*ᶻ≡*' (pos (suc a)) (pos      0 )   = refl
*ᶻ≡*' (pos (suc a)) (pos (suc b))   = refl
*ᶻ≡*' (pos      0 ) (negsuc   b )   = refl
*ᶻ≡*' (pos (suc a)) (negsuc   b ) i = negsuc (lemma1 a b i)
*ᶻ≡*' (negsuc   a ) (pos      0 ) i = QuoInt.ℤ→Int (QuoInt.signed sneg (*ⁿ-nullifiesʳ a i))
*ᶻ≡*' (negsuc   a ) (pos (suc b)) i = negsuc (lemma1 a b i)
*ᶻ≡*' (negsuc   a ) (negsuc   b )   = refl

*ᶻ≡* : _*ᶻ_ ≡ _*_
*ᶻ≡* i a b = *ᶻ≡*' a b i

QuoInt*≡* : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._*_ _*_
QuoInt*≡* = J (λ _⋆_ _ → PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._*_ _⋆_) QuoInt*≡*ᶻ *ᶻ≡*

-- *-assoc''''' : ∀ a b c → a * (b * c) ≡ (a * b) * c
-- *-assoc''''' = transport γ QuoInt.*-assoc where
--   γ : ((m n o : Z) → m · (n · o) ≡ (m · n) · o)
--     ≡ ((a b c : ℤ) → a * (b * c) ≡ (a * b) * c)
--   γ i = let _⋆_ = QuoInt*≡* i in (x y z : Z≡ℤ i) → x ⋆ (y ⋆ z) ≡ (x ⋆ y) ⋆ z

_+ᶻ_ : ℤ → ℤ → ℤ
_+ᶻ_ = transport (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._+_

QuoInt+≡+ᶻ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._+_ _+ᶻ_
QuoInt+≡+ᶻ i = transp (λ j → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j)) (~ i) QuoInt._+_

sucInt-preserves-ℤ→Int : ∀ a → sucInt (QuoInt.ℤ→Int a) ≡ QuoInt.ℤ→Int (QuoInt.sucℤ a)
sucInt-preserves-ℤ→Int (QuoInt.signed spos n) = refl
sucInt-preserves-ℤ→Int (QuoInt.signed sneg zero) = refl
sucInt-preserves-ℤ→Int (QuoInt.signed sneg (suc zero)) = refl
sucInt-preserves-ℤ→Int (QuoInt.signed sneg (suc (suc n))) = refl
sucInt-preserves-ℤ→Int (QuoInt.posneg i) = refl

predInt-preserves-ℤ→Int : ∀ a → predInt (QuoInt.ℤ→Int a) ≡ QuoInt.ℤ→Int (QuoInt.predℤ a)
predInt-preserves-ℤ→Int (QuoInt.signed spos zero) = refl
predInt-preserves-ℤ→Int (QuoInt.signed spos (suc n)) = refl
predInt-preserves-ℤ→Int (QuoInt.signed sneg zero) = refl
predInt-preserves-ℤ→Int (QuoInt.signed sneg (suc n)) = refl
predInt-preserves-ℤ→Int (QuoInt.posneg i) = refl

-sucℤ-sucℤ≡id : ∀ a → QuoInt.- QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ a) ≡ a
-sucℤ-sucℤ≡id (QuoInt.signed spos n) = refl
-sucℤ-sucℤ≡id (QuoInt.signed sneg zero) = QuoInt.posneg
-sucℤ-sucℤ≡id (QuoInt.signed sneg (suc n)) = refl
-sucℤ-sucℤ≡id (QuoInt.posneg i) j = QuoInt.posneg (i ∧ j)

sucℤ-sucℤ-≡id : ∀ a → QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ (QuoInt.- a)) ≡ a
sucℤ-sucℤ-≡id (QuoInt.signed spos zero) i = QuoInt.posneg (~ i)
sucℤ-sucℤ-≡id (QuoInt.signed spos (suc n)) = refl
sucℤ-sucℤ-≡id (QuoInt.signed sneg n) = refl
sucℤ-sucℤ-≡id (QuoInt.posneg i) j = QuoInt.posneg (i ∨ (~ j))

-sucℤ-sucℤ≡sucℤ-sucℤ- : ∀ a → QuoInt.- QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ a) ≡ QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ (QuoInt.- a))
-sucℤ-sucℤ≡sucℤ-sucℤ- a = -sucℤ-sucℤ≡id a ∙ sym (sucℤ-sucℤ-≡id a)

+ᶻ≡'+ : ∀ a b → a +ᶻ b ≡ a + b
+ᶻ≡'+ (pos      0 ) (pos      0 )   = refl
+ᶻ≡'+ (pos      0 ) (pos (suc b))  i = sucInt (+-comm (pos b) 0 i)
+ᶻ≡'+ (pos (suc a)) (pos      0 )  i = QuoInt.ℤ→Int (QuoInt.sucℤ (QuoInt.+-comm (QuoInt.pos a) 0 i))
+ᶻ≡'+ (pos (suc a)) (pos (suc b))   =
  (pos (suc a) +ᶻ pos (suc b))  ≡⟨ sym (sucInt-preserves-ℤ→Int (QuoInt.signed spos a QuoInt.+ QuoInt.signed spos (suc b))) ⟩
  sucInt (pos a +ᶻ pos (suc b)) ≡⟨ (λ i → sucInt $ (+ᶻ≡'+ (pos a) (pos (suc b)) ∙ sucInt+ (pos a) (pos b)) i) ⟩
  sucInt (pos (suc a) +pos b)   ∎
+ᶻ≡'+ (pos      0 ) (negsuc   b )   = sym (+negsuc-identityˡ b)
+ᶻ≡'+ (pos (suc a)) (negsuc   b )   =
  (pos (suc a) +ᶻ negsuc b)  ≡⟨ sym $ sucInt-preserves-ℤ→Int (QuoInt.signed spos a QuoInt.+ QuoInt.signed sneg (suc b)) ⟩
  sucInt (pos a +ᶻ negsuc b) ≡⟨ (λ i → sucInt $ +ᶻ≡'+ (pos a) (negsuc b) i) ⟩
  sucInt (pos a +  negsuc b) ≡⟨ sucInt+ (pos a) (negsuc b) ⟩
  (pos (suc a) +negsuc b)    ∎
+ᶻ≡'+ (negsuc   a ) (pos      0 )   i = QuoInt.ℤ→Int $ QuoInt.-_ $  QuoInt.sucℤ $ QuoInt.-_ $ QuoInt.+-comm (QuoInt.signed sneg a) (QuoInt.pos 0) i
+ᶻ≡'+ (negsuc   a ) (pos (suc b))   =
  (negsuc a +ᶻ pos (suc b))  ≡⟨ (λ i → QuoInt.ℤ→Int $ QuoInt.- QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ-+ʳ (QuoInt.signed sneg a) (QuoInt.signed spos b) (~ i))) ⟩
  QuoInt.ℤ→Int (QuoInt.- QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ (QuoInt.signed sneg a QuoInt.+ QuoInt.signed spos b))) ≡⟨ (λ i → QuoInt.ℤ→Int $ -sucℤ-sucℤ≡sucℤ-sucℤ- (QuoInt.signed sneg a QuoInt.+ QuoInt.signed spos b) i) ⟩
  QuoInt.ℤ→Int (QuoInt.sucℤ (QuoInt.- QuoInt.sucℤ (QuoInt.- (QuoInt.signed sneg a QuoInt.+ QuoInt.signed spos b)))) ≡⟨ sym $ sucInt-preserves-ℤ→Int (QuoInt.- QuoInt.sucℤ (QuoInt.- (QuoInt.signed sneg a QuoInt.+ QuoInt.signed spos b))) ⟩
  sucInt (negsuc a +ᶻ pos b) ≡⟨ (λ i → sucInt $ +ᶻ≡'+ (negsuc a) (pos b) i) ⟩
  sucInt (negsuc a +pos b)   ∎
+ᶻ≡'+ (negsuc zero) (negsuc b) = sym $ negsuc+negsuc≡+ⁿ 0 b
+ᶻ≡'+ (negsuc (suc a)) (negsuc b) =
 (negsuc (suc a) +ᶻ negsuc b)   ≡⟨ sym $ predInt-preserves-ℤ→Int (QuoInt.- QuoInt.sucℤ (QuoInt.- (QuoInt.signed sneg a QuoInt.+ QuoInt.signed sneg (suc b)))) ⟩
 predInt (negsuc a +ᶻ negsuc b) ≡⟨ (λ i → predInt $ +ᶻ≡'+ (negsuc a) (negsuc b) i) ⟩
 predInt (negsuc a +  negsuc b) ≡⟨ predInt+ (negsuc a) (negsuc b) ⟩
 (negsuc (suc a) +negsuc b)     ∎

+ᶻ≡+ : _+ᶻ_ ≡ _+_
+ᶻ≡+ i a b = +ᶻ≡'+ a b i

QuoInt+≡+ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._+_ _+_
QuoInt+≡+ = J (λ _+ᶻ_ _ → PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) QuoInt._+_ _+ᶻ_) QuoInt+≡+ᶻ +ᶻ≡+

-ᶻ_ : ℤ → ℤ
-ᶻ_ = transport (λ i → (Z≡ℤ i → Z≡ℤ i)) QuoInt.-_

QuoInt-≡-ᶻ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i)) QuoInt.-_ -ᶻ_
QuoInt-≡-ᶻ i = transp (λ j → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j)) (~ i) QuoInt.-_

-ᶻ≡'- : ∀ a → -ᶻ a ≡ - a
-ᶻ≡'- (pos zero) = refl
-ᶻ≡'- (pos (suc n)) = refl
-ᶻ≡'- (negsuc n) = refl

-ᶻ≡- : (-ᶻ_) ≡ (-_)
-ᶻ≡- i a = -ᶻ≡'- a i

QuoInt-≡- : PathP (λ i → (Z≡ℤ i → Z≡ℤ i)) (QuoInt.-_) (-_)
QuoInt-≡- = J (λ -ᶻ_ _ → PathP (λ i → (Z≡ℤ i → Z≡ℤ i)) QuoInt.-_ -ᶻ_) QuoInt-≡-ᶻ -ᶻ≡-

minᶠ : QuoInt.ℤ → QuoInt.ℤ → QuoInt.ℤ
minᶠ x y with QuoInt.sign x | QuoInt.sign y
... | QuoInt.spos | QuoInt.spos = QuoInt.pos (minⁿ (QuoInt.abs x) (QuoInt.abs y))
... | QuoInt.spos | QuoInt.sneg = y
... | QuoInt.sneg | QuoInt.spos = x
... | QuoInt.sneg | QuoInt.sneg = QuoInt.neg (maxⁿ (QuoInt.abs x) (QuoInt.abs y))

maxᶠ : QuoInt.ℤ → QuoInt.ℤ → QuoInt.ℤ
maxᶠ x y with QuoInt.sign x | QuoInt.sign y
... | QuoInt.spos | QuoInt.spos = QuoInt.pos (maxⁿ (QuoInt.abs x) (QuoInt.abs y))
... | QuoInt.spos | QuoInt.sneg = x
... | QuoInt.sneg | QuoInt.spos = y
... | QuoInt.sneg | QuoInt.sneg = QuoInt.neg (minⁿ (QuoInt.abs x) (QuoInt.abs y))

minᶻ : ℤ → ℤ → ℤ
minᶻ = transport (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) minᶠ

maxᶻ : ℤ → ℤ → ℤ
maxᶻ = transport (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) maxᶠ

minᶠ≡minᶻ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) minᶠ minᶻ
minᶠ≡minᶻ i = transp (λ j → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j)) (~ i) minᶠ

maxᶠ≡maxᶻ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) maxᶠ maxᶻ
maxᶠ≡maxᶻ i = transp (λ j → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j)) (~ i) maxᶠ

minᶻ≡'min : ∀ a b → minᶻ a b ≡ min a b
minᶻ≡'min (pos      0 ) (pos      0 ) = refl
minᶻ≡'min (pos      0 ) (pos (suc b)) = refl
minᶻ≡'min (pos (suc a)) (pos      0 ) = refl
minᶻ≡'min (pos (suc a)) (pos (suc b)) = refl
minᶻ≡'min (pos      0 ) (negsuc   b ) = refl
minᶻ≡'min (pos (suc a)) (negsuc   b ) = refl
minᶻ≡'min (negsuc   a ) (pos      0 ) = refl
minᶻ≡'min (negsuc   a ) (pos (suc b)) = refl
minᶻ≡'min (negsuc   a ) (negsuc   b ) = refl

maxᶻ≡'max : ∀ a b → maxᶻ a b ≡ max a b
maxᶻ≡'max (pos      0 ) (pos      0 ) = refl
maxᶻ≡'max (pos      0 ) (pos (suc b)) = refl
maxᶻ≡'max (pos (suc a)) (pos      0 ) = refl
maxᶻ≡'max (pos (suc a)) (pos (suc b)) = refl
maxᶻ≡'max (pos      0 ) (negsuc   b ) = refl
maxᶻ≡'max (pos (suc a)) (negsuc   b ) = refl
maxᶻ≡'max (negsuc   a ) (pos      0 ) = refl
maxᶻ≡'max (negsuc   a ) (pos (suc b)) = refl
maxᶻ≡'max (negsuc   a ) (negsuc   b ) = refl

minᶻ≡min : minᶻ ≡ min
minᶻ≡min i a b = minᶻ≡'min a b i

maxᶻ≡max : maxᶻ ≡ max
maxᶻ≡max i a b = maxᶻ≡'max a b i

minᶠ≡min : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) minᶠ min
minᶠ≡min = J (λ minᶻ _ → PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) minᶠ minᶻ) minᶠ≡minᶻ minᶻ≡min

maxᶠ≡max : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) maxᶠ max
maxᶠ≡max = J (λ maxᶻ _ → PathP (λ i → (Z≡ℤ i → Z≡ℤ i → Z≡ℤ i)) maxᶠ maxᶻ) maxᶠ≡maxᶻ maxᶻ≡max

_<ᶠ_ : ∀(x y : QuoInt.ℤ) → hProp ℓ-zero
x <ᶠ y with QuoInt.sign x | QuoInt.sign y
... | QuoInt.spos | QuoInt.spos = QuoInt.abs x <ⁿ QuoInt.abs y
... | QuoInt.spos | QuoInt.sneg = ⊥
... | QuoInt.sneg | QuoInt.spos = ⊤
... | QuoInt.sneg | QuoInt.sneg = QuoInt.abs y <ⁿ QuoInt.abs x

_<ᶻ_ : ℤ → ℤ → hProp ℓ-zero
_<ᶻ_ = transport (λ i → (Z≡ℤ i → Z≡ℤ i → hProp ℓ-zero)) _<ᶠ_

<ᶠ≡<ᶻ : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → hProp ℓ-zero)) _<ᶠ_ _<ᶻ_
<ᶠ≡<ᶻ i = transp (λ j → Z≡ℤ (i ∧ j) → Z≡ℤ (i ∧ j) → hProp ℓ-zero) (~ i) _<ᶠ_

<ᶻ⇔< : ∀ a b → [ (a <ᶻ b) ⇔ (a < b) ]
<ᶻ⇔< (pos      0 ) (pos      0 ) .fst pᶻ = pᶻ
<ᶻ⇔< (pos      0 ) (pos (suc b)) .fst pᶻ = pᶻ
<ᶻ⇔< (pos (suc a)) (pos      0 ) .fst pᶻ = pᶻ
<ᶻ⇔< (pos (suc a)) (pos (suc b)) .fst pᶻ = pᶻ
<ᶻ⇔< (pos      0 ) (negsuc   b ) .fst pᶻ = pᶻ
<ᶻ⇔< (pos (suc a)) (negsuc   b ) .fst pᶻ = pᶻ
<ᶻ⇔< (negsuc   a ) (pos      0 ) .fst pᶻ = pᶻ
<ᶻ⇔< (negsuc   a ) (pos (suc b)) .fst pᶻ = pᶻ
<ᶻ⇔< (negsuc   a ) (negsuc   b ) .fst pᶻ = sucⁿ-creates-<ⁿ b a .snd pᶻ
<ᶻ⇔< (pos      0 ) (pos      0 ) .snd p  = p
<ᶻ⇔< (pos      0 ) (pos (suc b)) .snd p  = p
<ᶻ⇔< (pos (suc a)) (pos      0 ) .snd p  = p
<ᶻ⇔< (pos (suc a)) (pos (suc b)) .snd p  = p
<ᶻ⇔< (negsuc   a ) (pos      0 ) .snd p  = p
<ᶻ⇔< (negsuc   a ) (pos (suc b)) .snd p  = p
<ᶻ⇔< (negsuc   a ) (negsuc   b ) .snd p  = sucⁿ-creates-<ⁿ b a .fst p

<ᶻ≡< : _<ᶻ_ ≡ _<_
<ᶻ≡< i a b = ⇔toPath {P = a <ᶻ b} {Q = a < b} (<ᶻ⇔< a b .fst) (<ᶻ⇔< a b .snd) i

<ᶠ≡< : PathP (λ i → (Z≡ℤ i → Z≡ℤ i → hProp ℓ-zero)) _<ᶠ_ _<_
<ᶠ≡< = J (λ _<ᶻ_ _ → PathP (λ i → (Z≡ℤ i → Z≡ℤ i → hProp ℓ-zero)) _<ᶠ_ _<ᶻ_) <ᶠ≡<ᶻ <ᶻ≡<

is-LinearlyOrderedCommRingᶻ : [ isLinearlyOrderedCommRing 0 1 QuoInt._+_ QuoInt._*_ QuoInt.-_ _<ᶠ_ minᶠ maxᶠ ]
is-LinearlyOrderedCommRingᶻ = transport γ is-LinearlyOrderedCommRing where
  γ : [ isLinearlyOrderedCommRing 0 1 _+_ _*_ -_ _<_ min max ]
    ≡ [ isLinearlyOrderedCommRing 0 1 QuoInt._+_ QuoInt._*_ QuoInt.-_ _<ᶠ_ minᶠ maxᶠ ]
  γ i = [ isLinearlyOrderedCommRing 0ⁱ 1ⁱ _+ⁱ_ _*ⁱ_ -ⁱ_ _<ⁱ_ minⁱ maxⁱ ] where
    0ⁱ = transport (λ j → Z≡ℤ (~ i ∧ j)) 0
    1ⁱ = transport (λ j → Z≡ℤ (~ i ∧ j)) 1
    _+ⁱ_ = QuoInt+≡+ (~ i)
    _*ⁱ_ = QuoInt*≡* (~ i)
    -ⁱ_  = QuoInt-≡- (~ i)
    _<ⁱ_ = <ᶠ≡< (~ i)
    minⁱ = minᶠ≡min (~ i)
    maxⁱ = maxᶠ≡max (~ i)

ℤbundle : LinearlyOrderedCommRing {ℓ-zero} {ℓ-zero}
ℤbundle .LinearlyOrderedCommRing.Carrier                    = QuoInt.ℤ
ℤbundle .LinearlyOrderedCommRing.0f                         = 0
ℤbundle .LinearlyOrderedCommRing.1f                         = 1
ℤbundle .LinearlyOrderedCommRing._+_                        = QuoInt._+_
ℤbundle .LinearlyOrderedCommRing._·_                        = QuoInt._*_
ℤbundle .LinearlyOrderedCommRing.-_                         = QuoInt.-_
ℤbundle .LinearlyOrderedCommRing.min                        = minᶠ
ℤbundle .LinearlyOrderedCommRing.max                        = maxᶠ
ℤbundle .LinearlyOrderedCommRing._<_                        = _<ᶠ_
ℤbundle .LinearlyOrderedCommRing.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRingᶻ

_*ᶠ_ = QuoInt._*_

·-reflects-<ᶠ : (x y z : QuoInt.ℤ) → [ 0 <ᶠ z ] → [ (x *ᶠ z) <ᶠ (y *ᶠ z) ] → [ x <ᶠ y ]
·-reflects-<ᶠ = transport γ ·-reflects-< where
  γ : ((x y z :        ℤ) → [ 0 <  z ] → [  x *  z  <   y *  z  ] → [ x <  y ])
    ≡ ((x y z : QuoInt.ℤ) → [ 0 <ᶠ z ] → [ (x *ᶠ z) <ᶠ (y *ᶠ z) ] → [ x <ᶠ y ])
  γ i = let _*'_ = QuoInt*≡* (~ i); _<'_ = <ᶠ≡< (~ i); 0ⁱ = transport (λ j → Z≡ℤ (~ i ∧ j)) 0 in
      ((x y z :    Z≡ℤ (~ i)) → [ 0ⁱ <' z ] → [ (x *' z) <' (y *' z) ] → [ x <' y ])
