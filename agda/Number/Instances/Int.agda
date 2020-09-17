{-# OPTIONS --cubical --no-import-sorts #-}

module Number.Instances.Int where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
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
  )
open import Data.Nat.Base using () renaming
  ( _⊔_ to maxⁿ
  ; _⊓_ to minⁿ
  ; _+_ to _+ⁿ_
  ; _*_ to _*ⁿ_
  )

open import Cubical.Data.Int renaming
  ( Int to ℤ
  ; isSetInt to isSetℤ
  -- ; neg to infix 8 -_
  )
-- open import Cubical.HITs.Ints.QuoInt.Properties
open import Cubical.Data.Nat using (suc; zero; ℕ) renaming
  ( +-comm to +ⁿ-comm
  ; +-assoc to +ⁿ-assoc
  ; *-comm to *ⁿ-comm
  ; *-suc to *ⁿ-suc
  ; *-assoc to *ⁿ-assoc
  ; +-suc to +ⁿ-suc
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

Int≅Builtin : Iso ℤ Builtin.Int
Int≅Builtin .Iso.fun      (        pos    n) = Builtin.pos n
Int≅Builtin .Iso.fun      (        negsuc n) = Builtin.negsuc n
Int≅Builtin .Iso.inv      (Builtin.pos    n) = pos n
Int≅Builtin .Iso.inv      (Builtin.negsuc n) = negsuc n
Int≅Builtin .Iso.rightInv (Builtin.pos    n) = refl
Int≅Builtin .Iso.rightInv (Builtin.negsuc n) = refl
Int≅Builtin .Iso.leftInv  (        pos    n) = refl
Int≅Builtin .Iso.leftInv  (        negsuc n) = refl

Int≡Builtin : ℤ ≡ Builtin.Int
Int≡Builtin = isoToPath Int≅Builtin

Sign : Type₀
Sign = Bool

pattern spos = Bool.false
pattern sneg = Bool.true

_*S_ : Sign → Sign → Sign
_*S_ = Bool._⊕_

sign : ℤ → Sign
sign (pos n)    = spos
sign (negsuc n) = sneg

signed : Sign → ℕ → ℤ
signed spos      x  = pos x
signed sneg  zero   = 0
signed sneg (suc x) = neg (suc x)

-_ : ℤ → ℤ
- pos zero = pos zero
- pos (suc n) = negsuc n
- negsuc n = pos (suc n)

infix 8 -_

_*_ : ℤ → ℤ → ℤ
pos      a  * pos      b  = pos (a *ⁿ b)
pos  zero   * negsuc   b  = pos 0
pos (suc a) * negsuc   b  = negsuc (a *ⁿ b +ⁿ (a +ⁿ b))
-- pos (suc a) * negsuc   b  = negsuc (a *ⁿ b +ⁿ (a +ⁿ b))
-- pos (suc a) * negsuc zero = negsuc a
-- pos (suc a) * negsuc (suc b) = {! suc a * suc suc b  !}
negsuc   a  * pos  zero   = pos 0
negsuc   a  * pos (suc b) = negsuc (a *ⁿ b +ⁿ (a +ⁿ b))
negsuc   a  * negsuc   b  = pos (suc a *ⁿ suc b)

_*'_ : ℤ → ℤ → ℤ
x *' y  = signed (sign x *S sign y) (abs x *ⁿ abs y)

-- test15 : ∀ a b → suc a *ⁿ suc b ≡ suc (b +ⁿ a *ⁿ suc b) -- ≡ a * b + a + b + 1
-- test15 a b = refl

private
  lemma : ∀ a b → a *ⁿ b +ⁿ (a +ⁿ b) ≡ b +ⁿ a *ⁿ suc b
  lemma a b = a *ⁿ b +ⁿ (a +ⁿ b)  ≡⟨ (λ i → +ⁿ-assoc (a *ⁿ b) a b i) ⟩
              (a *ⁿ b +ⁿ a) +ⁿ b  ≡⟨ (λ i → +ⁿ-comm (a *ⁿ b) a i +ⁿ b) ⟩
              (a +ⁿ a *ⁿ b) +ⁿ b  ≡⟨ (λ i → +ⁿ-comm (a +ⁿ a *ⁿ b) b i) ⟩
              b +ⁿ (a +ⁿ a *ⁿ b)  ≡⟨ (λ i → b +ⁿ *ⁿ-suc a b (~ i)) ⟩
              b +ⁿ a *ⁿ suc b     ∎

*≡*' : ∀ x y → x * y ≡ x *' y
*≡*' (pos a) (pos b) = refl
*≡*' (pos zero) (negsuc b) = refl
*≡*' (pos (suc a)) (negsuc b) =
  negsuc   (a *ⁿ b +ⁿ (a +ⁿ b))  ≡⟨ (λ i → negsuc $ lemma a b i) ⟩
  negsuc   (b +ⁿ a *ⁿ suc b)     ≡⟨ refl ⟩
  neg (suc (b +ⁿ a *ⁿ suc b))    ∎
*≡*' (negsuc a) (pos zero) = λ i → signed sneg $ *ⁿ-nullifiesʳ a (~ i)
*≡*' (negsuc a) (pos (suc b)) = λ i → negsuc $ lemma a b i
*≡*' (negsuc a) (negsuc b) = refl

+-identityʳ : ∀ x → x + 0 ≡ x
+-identityʳ x = refl

+-identityˡ : ∀ x → 0 + x ≡ x
+-identityˡ x = +-comm 0 x ∙ +-identityʳ x

*-nullifiesˡ : ∀ x → 0 * x ≡ 0
*-nullifiesˡ (pos n) = refl
*-nullifiesˡ (negsuc n) = refl

*-identityˡ : ∀ x → 1 * x ≡ x
*-identityˡ (pos n) = λ i → pos $ +ⁿ-comm n 0 i
*-identityˡ (negsuc n) = refl

-- *'-assoc : ∀ a b c → (a *' b) *' c ≡ a *' (b *' c)
-- *'-assoc (pos    a) (pos    b) (pos    c) = λ i → pos $ *ⁿ-assoc a b c (~ i)
-- *'-assoc (pos    a) (pos    b) (negsuc c) = {!   !}
-- *'-assoc (pos    a) (negsuc b) (pos    c) = {!   !}
-- *'-assoc (pos    a) (negsuc b) (negsuc c) = {!   !}
-- *'-assoc (negsuc a) (pos    b) (pos    c) = {!   !}
-- *'-assoc (negsuc a) (pos    b) (negsuc c) = {!   !}
-- *'-assoc (negsuc a) (negsuc b) (pos    c) = {!   !}
-- *'-assoc (negsuc a) (negsuc b) (negsuc c) = {!   !}
--
-- *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
-- *-assoc (pos    a) (pos    b) (pos    c) = λ i → pos $ *ⁿ-assoc a b c (~ i)
-- *-assoc (pos    a) (pos    b) (negsuc c) = {!   !}
-- *-assoc (pos    a) (negsuc b) (pos    c) = {!   !}
-- *-assoc (pos    a) (negsuc b) (negsuc c) = {!   !}
-- *-assoc (negsuc a) (pos    b) (pos    c) = {!   !}
-- *-assoc (negsuc a) (pos    b) (negsuc c) = {!   !}
-- *-assoc (negsuc a) (negsuc b) (pos    c) = {!   !}
-- *-assoc (negsuc a) (negsuc b) (negsuc c) = {!   !}

-distrˡ : ∀ a b → -(a * b) ≡ (- a) * b
-distrˡ (pos   zero ) (pos  zero  ) = refl
-distrˡ (pos   zero ) (pos (suc b)) = refl
-distrˡ (pos (suc a)) (pos  zero  ) = λ i → - pos (*ⁿ-nullifiesʳ a i)
-distrˡ (pos (suc a)) (pos (suc b)) = λ i → negsuc $ lemma a b (~ i)
-distrˡ (pos  zero  ) (negsuc   b ) = refl
-distrˡ (pos (suc a)) (negsuc   b ) = λ i → pos $ suc $ lemma a b i
-distrˡ (negsuc   a ) (pos  zero  ) = λ i → pos (*ⁿ-nullifiesʳ a (~ i))
-distrˡ (negsuc   a ) (pos (suc b)) = λ i → pos $ suc $ lemma a b i
-distrˡ (negsuc   a ) (negsuc   b ) = λ i → negsuc $ lemma a b (~ i)

-1*≡- : ∀ a → negsuc 0 * a ≡ - a
-1*≡- (pos zero) = refl
-1*≡- (pos (suc n)) = refl
-1*≡- (negsuc n) = λ i → pos $ suc $ +ⁿ-comm n 0 i

*-comm : ∀ a b → a * b ≡ b * a
*-comm (pos      a ) (pos      b ) = λ i → pos $ *ⁿ-comm a b i
*-comm (pos  zero  ) (negsuc   b ) = refl
*-comm (pos (suc a)) (negsuc   b ) = λ i → negsuc $ *ⁿ-comm a b i +ⁿ +ⁿ-comm a b i
*-comm (negsuc   a ) (pos  zero  ) = refl
*-comm (negsuc   a ) (pos (suc b)) = λ i → negsuc $ *ⁿ-comm a b i +ⁿ +ⁿ-comm a b i
*-comm (negsuc   a ) (negsuc   b ) =
  pos (suc (b +ⁿ a *ⁿ suc b))    ≡⟨ (λ i → pos $ suc $ b +ⁿ *ⁿ-suc a b i) ⟩
  pos (suc (b +ⁿ (a +ⁿ a *ⁿ b))) ≡⟨ (λ i → pos $ suc $ +ⁿ-assoc b a (a *ⁿ b) i) ⟩
  pos (suc ((b +ⁿ a) +ⁿ a *ⁿ b)) ≡⟨ (λ i → pos $ suc $ +ⁿ-comm b a i +ⁿ a *ⁿ b) ⟩
  pos (suc ((a +ⁿ b) +ⁿ a *ⁿ b)) ≡⟨ (λ i → pos $ suc $ +ⁿ-assoc a b (a *ⁿ b) (~ i)) ⟩
  pos (suc (a +ⁿ (b +ⁿ a *ⁿ b))) ≡⟨ (λ i → pos $ suc $ a +ⁿ (b +ⁿ *ⁿ-comm a b i)) ⟩
  pos (suc (a +ⁿ (b +ⁿ b *ⁿ a))) ≡⟨ (λ i → pos $ suc $ a +ⁿ *ⁿ-suc b a (~ i)) ⟩
  pos (suc (a +ⁿ b *ⁿ suc a))    ∎

-distrʳ : ∀ a b → -(a * b) ≡ a * (- b)
-distrʳ a b = (λ i → - *-comm a b i) ∙ -distrˡ b a ∙ *-comm (- b) a

*-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
*-assoc (pos zero) b c =
  (pos 0 * b) * c  ≡⟨ (λ i → *-nullifiesˡ b i * c) ⟩
   pos 0      * c  ≡⟨ *-nullifiesˡ c ⟩
   pos 0           ≡⟨ sym $ *-nullifiesˡ (b * c) ⟩
   pos 0 * (b * c) ∎
*-assoc (pos (suc n)) b c = let r = *-assoc (pos n) b c in *-assoc-ind n b c r where
  *-assoc-ind : ∀ n b c
              → ((pos n * b) * c) ≡ (pos n * (b * c))
              → ((pos (suc n) * b) * c) ≡ (pos (suc n) * (b * c))
  *-assoc-ind n (pos      b ) (pos      c ) p = {!    !}
    -- pos ((b +ⁿ n *ⁿ b) *ⁿ c)
    -- pos (b *ⁿ c +ⁿ (n *ⁿ b) *ⁿ c)
    -- pos (b *ⁿ c +ⁿ n *ⁿ (b *ⁿ c))
  *-assoc-ind n (pos  zero  ) (negsuc   c ) p = p
  *-assoc-ind n (pos (suc b)) (negsuc   c ) p = {!   !}
    -- (b+n(b+1))c+(b+n(b+1)+c)
    -- (b+nb+n)c+b+nb+n+c
    -- bc+nbc+nc+b+nb+n+c
    -- bc+nbc+nc+n+nb+b+c
    -- nb+nbc+nc+n+bc+b+c
    -- nbc+nb+nc+n+bc+b+c
    -- n(bc+b+c)+n+bc+b+c
    -- negsuc ((b +ⁿ n *ⁿ suc b) *ⁿ c +ⁿ (b +ⁿ n *ⁿ suc b +ⁿ c))
    -- negsuc (n *ⁿ (b *ⁿ c +ⁿ (b +ⁿ c)) +ⁿ (n +ⁿ (b *ⁿ c +ⁿ (b +ⁿ c))))
  *-assoc-ind n (negsuc   b ) (pos  zero  ) p = λ i → pos $ *ⁿ-nullifiesʳ n (~ i)
  *-assoc-ind n (negsuc   b ) (pos (suc c)) p = {!   !}
    -- negsuc ((n *ⁿ b +ⁿ (n +ⁿ b)) *ⁿ c +ⁿ (n *ⁿ b +ⁿ (n +ⁿ b) +ⁿ c))
    -- negsuc (n *ⁿ (b *ⁿ c +ⁿ (b +ⁿ c)) +ⁿ (n +ⁿ (b *ⁿ c +ⁿ (b +ⁿ c))))
  *-assoc-ind n (negsuc   b ) (negsuc   c ) p = {!   !}
    -- pos (suc (c +ⁿ (n *ⁿ b +ⁿ (n +ⁿ b)) *ⁿ suc c))
    -- pos (suc (c +ⁿ b *ⁿ suc c +ⁿ n *ⁿ suc (c +ⁿ b *ⁿ suc c)))
*-assoc (negsuc zero) b c =
  (negsuc 0 * b) * c  ≡⟨ (λ i → -1*≡- b i * c) ⟩
  (         - b) * c  ≡⟨ sym $ -distrˡ b c ⟩
            - (b * c) ≡⟨ sym $ -1*≡- (b * c) ⟩
   negsuc 0 * (b * c) ∎
*-assoc (negsuc (suc n)) b c = let r = *-assoc (negsuc n) b c in *-assoc-ind n b c r where
  *-assoc-ind : ∀ n b c
              → ((negsuc n * b) * c) ≡ (negsuc n * (b * c))
              → ((negsuc (suc n) * b) * c) ≡ (negsuc (suc n) * (b * c))
  *-assoc-ind n (pos  zero  ) (pos      c ) p = refl
  *-assoc-ind n (pos (suc b)) (pos      c ) p = {!   !}
    -- negsuc (b +ⁿ n *ⁿ b +ⁿ suc (n +ⁿ b)) * pos c
    -- negsuc (suc n) * pos (c +ⁿ b *ⁿ c)
  *-assoc-ind n (pos  zero  ) (negsuc   c ) p = p
  *-assoc-ind n (pos (suc b)) (negsuc   c ) p = {!   !}
    -- pos (suc (c +ⁿ (b +ⁿ n *ⁿ b +ⁿ suc (n +ⁿ b)) *ⁿ suc c))
    -- pos (suc (b *ⁿ c +ⁿ (b +ⁿ c) +ⁿ suc (b *ⁿ c +ⁿ (b +ⁿ c) +ⁿ n *ⁿ suc (b *ⁿ c +ⁿ (b +ⁿ c)))))
  *-assoc-ind n (negsuc   b ) (pos  zero  ) p = λ i → pos $ *ⁿ-nullifiesʳ (b +ⁿ suc (b +ⁿ n *ⁿ suc b)) i
  *-assoc-ind n (negsuc   b ) (pos (suc c)) p = {!   !}
    -- pos (suc (c +ⁿ (b +ⁿ suc (b +ⁿ n *ⁿ suc b)) *ⁿ suc c)) ≡
    -- pos (suc (b *ⁿ c +ⁿ (b +ⁿ c) +ⁿ suc (b *ⁿ c +ⁿ (b +ⁿ c) +ⁿ n *ⁿ suc (b *ⁿ c +ⁿ (b +ⁿ c)))))
  *-assoc-ind n (negsuc   b ) (negsuc   c ) p = {!   !}
    -- negsuc ((b +ⁿ suc (b +ⁿ n *ⁿ suc b)) *ⁿ c +ⁿ (b +ⁿ suc (b +ⁿ n *ⁿ suc b) +ⁿ c))
    -- negsuc (c +ⁿ b *ⁿ suc c +ⁿ n *ⁿ (c +ⁿ b *ⁿ suc c) +ⁿ suc (n +ⁿ (c +ⁿ b *ⁿ suc c)))

*-assocᵖ : ∀{ℓ} {A : Type ℓ} (isset : isSet A) (_*_ : A → A → A) → hProp ℓ
*-assocᵖ isset _*_ =  ∀[ a ] ∀[ b ] ∀[ c ] ([ isset ] a * (b * c) ≡ˢ (a * b) * c)

-- lemma2 : *-assocᵖ

*-assoc'' : ∀ a b c → a * (b * c) ≡ (a * b) * c
*-assoc'' = transport {!   !} QuoInt.*-assoc where
  γ : ((m n o : QuoInt.ℤ) → m QuoInt.* (n QuoInt.* o) ≡ m QuoInt.* n QuoInt.* o)
    ≡ ((a b c :        ℤ) → a * (b * c) ≡ (a * b) * c)
  γ = {! funExt⁻ {B = λ x i → QuoInt.Int≡ℤ i}   !}
--   let a' = transport Int≡Builtin a
--       b' = transport Int≡Builtin b
--       c' = transport Int≡Builtin c
--   in {! transport (sym Int≡Builtin) $ transport Int≡Builtin c    !} -- BuiltinProps.*-assoc a' b' c'

*-nullifiesʳ : ∀ x → x * 0 ≡ 0
*-nullifiesʳ x = *-comm x 0 ∙ *-nullifiesˡ x

*-identityʳ : ∀ x → x * 1 ≡ x
*-identityʳ x = *-comm x 1 ∙ *-identityˡ x

*-distribˡ : ∀ o m n → (o * m) + (o * n) ≡ o * (m + n)
*-distribˡ (pos zero) m n = {!   !}
*-distribˡ (pos (suc o)) m n = let r = *-distribˡ (pos o) m n in {!   !} where
  lhs = (pos (suc o) * m) + (pos (suc o) * n)  ≡⟨ {!   !} ⟩
        (m + (pos o * m)) + (n + (pos o * n))  ≡⟨ {!   !} ⟩
         m + ((pos o * m) + (n + (pos o * n))) ≡⟨ {!   !} ⟩
         m + ((n + (pos o * n)) + (pos o * m)) ≡⟨ {!   !} ⟩
         m + (n + ((pos o * n) + (pos o * m))) ≡⟨ {!   !} ⟩
        (m + n) + (pos o * (m + n))            ∎
        -- (pos (suc o) * (m + n))                  ∎
        -- then use +-preserves-<
*-distribˡ (negsuc zero) m n = {!   !}
*-distribˡ (negsuc (suc o)) m n = let r = *-distribˡ (negsuc o) m n in {!   !}

*-distribʳ : ∀ m n o → (m * o) + (n * o) ≡ (m + n) * o
*-distribʳ m n o = transport (sym λ i → *-comm m o i + *-comm n o i ≡ *-comm (m + n) o i) $ *-distribˡ o m n

-- hProp-valued _<_
_<_ : ∀(x y : ℤ) → hProp ℓ-zero
pos    x < pos    y = x <ⁿ y
pos    x < negsuc y = ⊥
negsuc x < pos    y = ⊤
negsuc x < negsuc y = y <ⁿ x

min : ℤ → ℤ → ℤ
min (pos    x) (pos    y) = pos (minⁿ x y)
min (pos    x) (negsuc y) = negsuc y
min (negsuc x) (pos    y) = negsuc x
min (negsuc x) (negsuc y) = negsuc (maxⁿ x y)

max : ℤ → ℤ → ℤ
max (pos    x) (pos    y) = pos (maxⁿ x y)
max (pos    x) (negsuc y) = pos x
max (negsuc x) (pos    y) = pos y
max (negsuc x) (negsuc y) = negsuc (minⁿ x y)

<-irrefl : (a : ℤ) → [ ¬ (a < a) ]
<-irrefl (pos  zero  ) = <ⁿ-irrefl 0
<-irrefl (pos (suc n)) = <ⁿ-irrefl (suc n)
<-irrefl (negsuc   n ) = <ⁿ-irrefl n

<-trans : (a b c : ℤ) → [ a < b ] → [ b < c ] → [ a < c ]
<-trans (pos    a) (pos    b) (pos    c) a<b b<c = <ⁿ-trans a<b b<c
<-trans (negsuc a) (pos    b) (pos    c) a<b b<c = tt
<-trans (negsuc a) (negsuc b) (pos    c) a<b b<c = tt
<-trans (negsuc a) (negsuc b) (negsuc c) a<b b<c = <ⁿ-trans b<c a<b

<-cotrans : (a b : ℤ) → [ a < b ] → (x : ℤ) → [ (a < x) ⊔ (x < b) ]
<-cotrans (pos    a) (pos    b) a<b (pos    x) = <ⁿ-cotrans _ _ a<b x
<-cotrans (pos    a) (pos    b) a<b (negsuc x) = inrᵖ tt
<-cotrans (negsuc a) (pos    b) a<b (pos    x) = inlᵖ tt
<-cotrans (negsuc a) (pos    b) a<b (negsuc x) = inrᵖ tt
<-cotrans (negsuc a) (negsuc b) a<b (pos    x) = inlᵖ tt
<-cotrans (negsuc a) (negsuc b) a<b (negsuc x) = pathTo⇒ (⊔-comm (b <ⁿ x) (x <ⁿ a)) (<ⁿ-cotrans _ _ a<b x)

data Trichotomy (m n : ℤ) : Type₀ where
  lt : [ m < n ] → Trichotomy m n
  eq :   m ≡ n   → Trichotomy m n
  gt : [ n < m ] → Trichotomy m n

_≟_ : ∀ m n → Trichotomy m n
pos    a ≟ pos    b with a ≟ⁿ b
... | ltⁿ p = lt p
... | eqⁿ p = eq λ i → pos (p i)
... | gtⁿ p = gt p
pos    a ≟ negsuc b = gt tt
negsuc a ≟ pos    b = lt tt
negsuc a ≟ negsuc b with a ≟ⁿ b
... | ltⁿ p = gt p
... | eqⁿ p = eq λ i → negsuc (p i)
... | gtⁿ p = lt p

is-min : (x y z : ℤ) → [ ¬ᵖ (min x y < z) ⇔ ¬ᵖ (x < z) ⊓ ¬ᵖ (y < z) ]
is-min = {!   !}

is-max : (x y z : ℤ) → [ ¬ᵖ (z < max x y) ⇔ ¬ᵖ (z < x) ⊓ ¬ᵖ (z < y) ]
is-max = {!  !}

possuc+negsuc≡0 : ∀ n → (pos (suc n) +negsuc n) ≡ pos 0
possuc+negsuc≡0 zero = refl
possuc+negsuc≡0 (suc n) = let r = possuc+negsuc≡0 n in sym ind ∙ r where
  ind =           pos      (suc n)   +negsuc n  ≡⟨ refl ⟩
         predInt (pos (suc (suc n))) +negsuc n  ≡⟨ sym $ predInt+negsuc n (pos (suc (suc n))) ⟩
         predInt (pos (suc (suc n))  +negsuc n) ∎

sucInt[negsuc+pos]≡0 : ∀ n → sucInt (negsuc n +pos n) ≡ pos 0
sucInt[negsuc+pos]≡0 zero = refl
sucInt[negsuc+pos]≡0 (suc n) = let r = sucInt[negsuc+pos]≡0 n in sym ind ∙ r where
  ind = sucInt (        negsuc n        +pos n ) ≡⟨ refl ⟩
        sucInt (sucInt (negsuc (suc n)) +pos n ) ≡⟨ (λ i → sucInt $ sucInt+pos n (negsuc (suc n)) (~ i)) ⟩
        sucInt (sucInt (negsuc (suc n)  +pos n)) ∎

+-inverseʳ : ∀ a → a + (- a) ≡ 0
+-inverseʳ (pos  zero  ) = refl
+-inverseʳ (pos (suc n)) = possuc+negsuc≡0 n
+-inverseʳ (negsuc   n ) = sucInt[negsuc+pos]≡0 n

+-inverseˡ : ∀ a → (- a) + a ≡ 0
+-inverseˡ a = +-comm (- a) a ∙ +-inverseʳ a

+-inverse : (x : ℤ) → (x + (- x) ≡ pos 0) × ((- x) + x ≡ pos 0)
+-inverse x .fst = +-inverseʳ x
+-inverse x .snd = +-inverseˡ x

-- sucInt--<
-- predInt--<

+-reflects-< : ∀ a b x → [ (a + x) < (b + x) ] → [ a < b ]
+-reflects-< (pos a) (pos b) (pos zero) a+x<b+x = a+x<b+x
+-reflects-< (pos a) (pos b) (pos (suc x)) a+x<b+x = {!   !}
+-reflects-< (pos a) (pos b) (negsuc zero) a+x<b+x = {!   !}
+-reflects-< (pos a) (pos b) (negsuc (suc x)) a+x<b+x = let r = +-reflects-< (pos a) (pos b) (negsuc x) in {!    !}
+-reflects-< (pos a) (negsuc b) (pos (suc x)) a+x<b+x = {!   !}
+-reflects-< (pos    a) (negsuc b) (negsuc x) a+x<b+x = {!   !}
+-reflects-< (negsuc a) (pos    b) (pos    x) a+x<b+x = tt
+-reflects-< (negsuc a) (pos    b) (negsuc x) a+x<b+x = tt
+-reflects-< (negsuc a) (negsuc b) (pos    x) a+x<b+x = {!   !}
+-reflects-< (negsuc a) (negsuc b) (negsuc x) a+x<b+x = {!   !}

+-<-ext : (w x y z : ℤ) → [ (w + x) < (y + z) ] → [ (w < y) ⊔ (x < z) ]
+-<-ext w x y z r with w ≟ y | x ≟ z
... | lt w<y | q = inlᵖ w<y
... | eq w≡y | q = inrᵖ {! +-injˡ y x z   !}
... | gt y<w | q = {!   !}

·-preserves-< : (x y z : ℤ) → [ 0 < z ] → [ x < y ] → [ (x * z) < (y * z) ]
·-preserves-< = {!    !}

+-Semigroup : [ isSemigroup _+_ ]
+-Semigroup .IsSemigroup.is-set   = isSetℤ
+-Semigroup .IsSemigroup.is-assoc = +-assoc

·-Semigroup : [ isSemigroup _*_ ]
·-Semigroup .IsSemigroup.is-set   = isSetℤ
·-Semigroup .IsSemigroup.is-assoc x y z = sym (*-assoc x y z)

+-Monoid : [ isMonoid 0 _+_ ]
+-Monoid .IsMonoid.is-Semigroup = +-Semigroup
+-Monoid .IsMonoid.is-identity x = +-identityʳ x , +-identityˡ x

·-Monoid : [ isMonoid 1 _*_ ]
·-Monoid .IsMonoid.is-Semigroup = ·-Semigroup
·-Monoid .IsMonoid.is-identity x = *-identityʳ x , *-identityˡ x

is-Semiring : [ isSemiring 0 1 _+_ _*_ ]
is-Semiring .IsSemiring.+-Monoid = +-Monoid
is-Semiring .IsSemiring.·-Monoid = ·-Monoid
is-Semiring .IsSemiring.+-comm   = +-comm
is-Semiring .IsSemiring.is-dist x y z = sym (*-distribˡ x y z) , sym (*-distribʳ x y z)

is-CommSemiring : [ isCommSemiring 0 1 _+_ _*_ ]
is-CommSemiring .IsCommSemiring.is-Semiring = is-Semiring
is-CommSemiring .IsCommSemiring.·-comm      = *-comm

<-StrictLinearOrder : [ isStrictLinearOrder _<_ ]
<-StrictLinearOrder .IsStrictLinearOrder.is-irrefl = <-irrefl
<-StrictLinearOrder .IsStrictLinearOrder.is-trans  a b c = <-trans a b c
<-StrictLinearOrder .IsStrictLinearOrder.is-tricho a b with a ≟ b
... | lt a<b = inl (inl a<b)
... | eq a≡b = inr ∣ a≡b ∣
... | gt b<a = inl (inr b<a)

≤-isLattice : [ isLattice (λ x y → ¬ᵖ (y < x)) min max ]
≤-isLattice .IsLattice.≤-PartialOrder = linearorder⇒partialorder _ (≤'-isLinearOrder <-StrictLinearOrder)
≤-isLattice .IsLattice.is-min         = is-min
≤-isLattice .IsLattice.is-max         = is-max

is-LinearlyOrderedCommSemiring : [ isLinearlyOrderedCommSemiring 0 1 _+_ _*_ _<_ min max ]
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.is-CommSemiring     = is-CommSemiring
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.<-StrictLinearOrder = <-StrictLinearOrder
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.≤-isLattice         = ≤-isLattice
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.+-<-ext             = +-<-ext
is-LinearlyOrderedCommSemiring .IsLinearlyOrderedCommSemiring.·-preserves-<       = ·-preserves-<

is-LinearlyOrderedCommRing : [ isLinearlyOrderedCommRing 0 1 _+_ _*_ -_ _<_ min max ]
is-LinearlyOrderedCommRing .IsLinearlyOrderedCommRing.is-LinearlyOrderedCommSemiring = is-LinearlyOrderedCommSemiring
is-LinearlyOrderedCommRing .IsLinearlyOrderedCommRing.+-inverse                      = +-inverse

ℤbundle : LinearlyOrderedCommRing {ℓ-zero} {ℓ-zero}
ℤbundle .LinearlyOrderedCommRing.Carrier                    = ℤ
ℤbundle .LinearlyOrderedCommRing.0f                         = 0
ℤbundle .LinearlyOrderedCommRing.1f                         = 1
ℤbundle .LinearlyOrderedCommRing._+_                        = _+_
ℤbundle .LinearlyOrderedCommRing._·_                        = _*_
ℤbundle .LinearlyOrderedCommRing.-_                         = -_
ℤbundle .LinearlyOrderedCommRing.min                        = min
ℤbundle .LinearlyOrderedCommRing.max                        = max
ℤbundle .LinearlyOrderedCommRing._<_                        = _<_
ℤbundle .LinearlyOrderedCommRing.is-LinearlyOrderedCommRing = is-LinearlyOrderedCommRing
