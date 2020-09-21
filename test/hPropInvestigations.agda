{-# OPTIONS --cubical --no-import-sorts #-}


module hPropInvestigations where

open import Agda.Primitive renaming (_⊔_ to ℓ-max; lsuc to ℓ-suc; lzero to ℓ-zero)

private
  variable
    ℓ ℓ' ℓ'' : Level

open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ; assoc to ∙-assoc)
open import Cubical.Data.Sigma.Base renaming (_×_ to infixr 4 _×_)
open import Cubical.Foundations.Prelude
open import Function.Base using (_∋_)
open import Cubical.Foundations.Logic
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty renaming (elim to ⊥-elim) renaming (⊥ to ⊥⊥) -- `⊥` and `elim`

import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit.Base

import Cubical.Structures.Axioms

-- NOTE:
--   we have both:
--   the "classic" bundle/unbundle record-based definition of a CommRing from `Cubical.Structures.CommRing`
--
--     record IsCommRing {R : Type ℓ} (0r 1r : R) (_+_ _·_ : R → R → R) (-_ : R → R) : Type ℓ where
--       field
--         isRing : IsRing 0r 1r _+_ _·_ -_
--         ·-comm : (x y : R) → x · y ≡ y · x
--     record CommRing : Type (ℓ-suc ℓ) where
--       field
--         Carrier    : Type ℓ
--         0r         : Carrier
--         1r         : Carrier
--         _+_        : Carrier → Carrier → Carrier
--         _·_        : Carrier → Carrier → Carrier
--         -_         : Carrier → Carrier
--         isCommRing : IsCommRing 0r 1r _+_ _·_ -_
--
--   and a CommRingΣTheory
--
--     CommRingAxioms R (_+_ , 1r , _·_) = RingAxioms R (_+_ , 1r , _·_) × ((x y : R) → x · y ≡ y · x)
--     CommRingStructure = AxiomsStructure RawRingStructure CommRingAxioms
--     CommRingΣ         = TypeWithStr ℓ CommRingStructure
--     CommRingEquivStr  : StrEquiv CommRingStructure ℓ
--     CommRingEquivStr  = AxiomsEquivStr RawRingEquivStr CommRingAxioms
--
--   especially when we look at
--
--     CommRingEquivStr = AxiomsEquivStr RawRingEquivStr CommRingAxioms
--
--   here `AxiomsEquivStr` from `Cubical.Structures.Axioms`
--   
--     AxiomsEquivStr : {S : Type ℓ → Type ℓ₁} (ι : StrEquiv S ℓ₁') (axioms : (X : Type ℓ) → S X → Type ℓ₂)
--                    → StrEquiv (AxiomsStructure S axioms) ℓ₁'
--     AxiomsEquivStr ι axioms (X , (s , a)) (Y , (t , b)) e = ι (X , s) (Y , t) e
--   
--   takes the two arguments `RawRingEquivStr` and `CommRingAxioms`
--   
--     RawRingEquivStr = AutoEquivStr RawRingStructure
--     
--     CommRingAxioms : (R : Type ℓ) (s : RawRingStructure R) → Type ℓ
--     CommRingAxioms R (_+_ , 1r , _·_) = RingAxioms R (_+_ , 1r , _·_) × ((x y : R) → x · y ≡ y · x)
--   
--   where `AutoEquivStr` is a macro from `Cubical.Structures.Auto`
--   
--     -- (S : Type ℓ → Type ℓ₁) → StrEquiv (AutoStructure S) _
--     AutoEquivStr : R.Term → R.Term → R.TC Unit
--     AutoEquivStr t hole =
--       newMeta (tDesc R.unknown) >>= λ d →
--       R.unify hole (R.def (quote MacroEquivStr) [ varg d ]) >>
--       autoDesc' t d


import Cubical.Structures.CommRing
open import Cubical.Data.Sigma.Properties
import Cubical.Foundations.Transport
import Cubical.Foundations.Path

¬[P⊓¬P] : ∀(P : hProp ℓ) → [ ¬(P ⊓ ¬ P) ]
¬[P⊓¬P] _ (p , q) = q p

lemma-comm : ∀(P : hProp ℓ) → P ⊓ ¬ P ≡ ¬ P ⊓ P
lemma-comm P = ⊓-comm P (¬ P) 

lemma-comm-elm-forward : ∀(P : hProp ℓ) → [ P ⊓ ¬ P ] → [ ¬ P ⊓ P ]
lemma-comm-elm-forward P (p , ¬p) = (¬p , p)

lemma-comm-elm-back : ∀(P : hProp ℓ) → [ ¬ P ⊓ P ] → [ P ⊓ ¬ P ]
lemma-comm-elm-back P (¬p , p) = (p , ¬p)

comm-elm-iso : ∀(P : hProp ℓ) → Iso [ P ⊓ ¬ P ] [ ¬ P ⊓ P ]
comm-elm-iso P = λ where
  .Iso.fun        → lemma-comm-elm-forward P
  .Iso.inv        → lemma-comm-elm-back P
  .Iso.rightInv _ → refl
  .Iso.leftInv  _ → refl

-- let A = fst P
-- [ P ⊓ ¬ P ] : A × (A → ⊥)
-- [ ¬ P ⊓ P ] : (A → ⊥) × A
-- we have `P ⊓ ¬ P ≡ ¬ P ⊓ P`
-- and we have ≡ for the witness-type `[ P ⊓ ¬ P ] ≡ [ ¬ P ⊓ P ]`
-- because `A × (A → ⊥) ≢ (A → ⊥) × A`

lemma-Σ-swap-≡ : ∀(A B : Type ℓ) → (A × B) ≡ (B × A)
lemma-Σ-swap-≡ A B = isoToPath (Σ-swap-Iso {A = A} {A' = B})

lemma-comm-elm' : ∀(P : hProp ℓ) → [ P ⊓ ¬ P ] ≡ [ ¬ P ⊓ P ]
lemma-comm-elm' P = lemma-Σ-swap-≡ _ _

lemma-comm-elm : ∀(P : hProp ℓ) → [ P ⊓ ¬ P ] ≡ [ ¬ P ⊓ P ]
lemma-comm-elm P = isoToPath (comm-elm-iso P)

-- see `2.8 Classical principles` in Booij's thesis
weak-LEM' : ∀(P : hProp ℓ) → [ (¬ ¬ P) ⊔ (¬ P) ]
weak-LEM' {ℓ = ℓ} P = {! (¬[P⊓¬P] P) ∘ pathTo⇒ (⊓-comm (¬ P) P) !} -- (⊓-comm P (¬ P)) ∘ (¬[P⊓¬P] P)
  where
    γ : P ⊓ ¬ P ≡ ¬ P ⊓ P
    -- γ : PathP (λ i → ?)
    γ = ⊓-comm P (¬ P)
    κ : [ P ⊓ ¬ P ⇒ ¬ P ⊓ P ]
 -- κ : [ P ⊓ ¬ P ] → [ ¬ P ⊓ P ] -- is the same !
    κ = pathTo⇒ γ
    η : [ P ⊓ ¬ P ] → [ ¬ P ⊓ P ]
    η p = κ p
    φ : [ ¬ (¬ P ⊓ P) ] -- and from here we would need deMorgan₁ to obtain the goal which is not provable without further assumptions
    φ = (¬[P⊓¬P] P) ∘ pathTo⇒ (⊓-comm (¬ P) P)
    -- (p , q) = Iso.inv ΣPathIsoPathΣ γ
    pq : Σ[ p ∈ fst (P ⊓ ¬ P) ≡ fst (¬ P ⊓ P) ] PathP (λ i → isProp (p i)) (snd (P ⊓ ¬ P)) (snd (¬ P ⊓ P))
    pq = Iso.inv ΣPathIsoPathΣ γ
    p : fst (P ⊓ ¬ P) ≡ fst (¬ P ⊓ P)
    p = fst pq
    q : PathP (λ i → isProp (fst pq i)) (snd (P ⊓ ¬ P)) (snd (¬ P ⊓ P))
    q = snd pq
    k = transport {ℓ = ℓ} {A = isProp (fst (P ⊓ ¬ P))} {B = isProp (fst (¬ P ⊓ P))} {! κ  !}
    l = {! Σ[ A ∈ Type ℓ ] isProp A!}
-- ⊓-comm P (¬ P) : P ⊓ ¬ P ≡ ¬ P ⊓ P
-- [ ¬ ¬ P ⊔ ¬ P ]
-- [ ¬ (¬ P ⊓ P) ]
-- hProp ℓ = Σ[ A ∈ Type ℓ ] (∀(x y : A) → x ≡ y)
--         = Σ[ A ∈ Type ℓ ] isProp A
-- HOTT: Definition 3.3.1. A type P is a mere proposition if for all x, y : P we have x = y.
-- NOTE: so `isMere P = isProp P`
-- _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
-- _≡_ {A = A} = PathP (λ i → A)
-- transport : {A B : Type ℓ} → A ≡ B → A → B
-- transport p a = transp (λ i → p i) i0 a
-- pathTo⇒ : P ≡ Q → [ P ⇒ Q ]
-- PathP is dependent path type (builtin)
-- Path is non-dependent path type
--   PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 →  Set ℓ
--   Path  : ∀ {ℓ} (A :    Type ℓ) → A    → A    → Type ℓ
--   Path A a b = PathP (λ _ → A) a b
-- Direct definitions of lower h-levels
--   isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)
--   isProp  A = (x y : A) → x ≡ y
--   isSet   A = (x y : A) → isProp (x ≡ y)
--
-- an element of   hProp   states what the proposition is    - the element is the proposition
-- an element of [ hProp ] states that the proposition holds - the element is the proof
-- pathes such as `P ⊓ ¬ P ≡ ¬ P ⊓ P` just state that the propositions are the same
-- we cannot use `transport` on `P ⊓ ¬ P ≡ ¬ P ⊓ P`
-- `⇔toPath` can be used to get equality of the propositions from forward and backward implication based on the witnesses
--   ⇔toPath : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q
-- similar with `hProp≡`
--   hProp≡ : [ P ] ≡ [ Q ] → P ≡ Q
-- there is `pathTo⇒` and `pathTo⇐` to create witness-based implications
--   pathTo⇒ : P ≡ Q → [ P ⇒ Q ]
--   pathTo⇐ : P ≡ Q → [ Q ⇒ P ]
-- here, we have that `[ P ⇒ Q ]` is definitionally equivalent to `[ P ] → [ Q ]`
-- because `[ P ] → [ Q ]` is the first element of the tuple `P ⇒ Q` which gets projected out with `[_]`
--   A ⇒ B = ([ A ] → [ B ]) , isPropΠ λ _ → isProp[] B
-- we can use `isoToPath` to create a path `[ P ] ≡ [ Q ]` but only when we are able to formulate an isomorphism
-- so `[ P ] ≡ [ Q ]` is what we can transport the witnesses along
--   isoToPath  : Iso A B → A ≡ B
--   isoToEquiv : Iso A B → A ≃ B
-- with
--   A ≃ B = Σ[ f ∈ A → B ] isEquiv f
-- where `isEquiv` is basically
--   isEquiv = (f : A → B) → ∀(y : B) → isContr (fiber f y)
-- but it seems to be a very strong property of two ≡-equal propositions to have their elements being ≡-equal too
--   is it? Or can we always find an isomorphism `Iso [ P ] [ Q ]` for every path `P ≡ Q`? I guess not



-- ∥¬A∥≡¬∥A∥
_ = hProp≡
_ = transport
_ = ∥ {!!} ∥
_ = _≡_
_ = Path


-- Propositions
-- 
-- Definition 2.4.1. A proposition is a type P all whose elements are identical, which is expressed type-theoretically as
-- 
--   isHProp(P) := (Π p, q : P) (p =ₚ q).
-- 
-- We have the type
-- 
--   HProp := (Σ P : U) isHProp(P)
-- 
-- of all propositions, and we identify elements of HProp with their underlying type, that is, their first projection.
-- The letter ‘H’ stands for homotopy, which we briefly touch on in Section 2.5.4.
-- 
-- checkout p.31 ff of Booij's thesis
--
-- Definition 2.4.5. Univalent logic is defined by the following, where P, Q : HProp and R : X → HProp [91, Definition 3.7.1]:
--
--   ⊤              := 1
--   ⊥              := 0
--   P ∧ Q          := P × Q
--   P ⇒ Q          := P → Q
--   P ⇔ Q          := P = Q
--   ¬P             := P → 0
--   P ∨ Q          := ∥ P + Q ∥
--   (∀ x : X) R(x) :=  (Π x : X) R(x)
--   (∃ x : X) R(x) := ∥ (Σ x : X) R(x) ∥
--
-- NOTE: the important sentence is "we identify elements of HProp with ... their first projection"
--       therefore Agda's first projection `[_]` is not present in Booij's writing (it's implicit)


import Cubical.Functions.Embedding

-- Embeddings are generalizations of injections. The usual
-- definition of injection as:
--
--    f x ≡ f y → x ≡ y
--
-- is not well-behaved with higher h-levels, while embeddings
-- are.
--
--   isEmbedding : (A → B) → Type _
--   isEmbedding f = ∀ w x → isEquiv {A = w ≡ x} (cong f)

-- injEmbedding
--   : {f : A → B}
--   → isSet A → isSet B
--   → (∀{w x} → f w ≡ f x → w ≡ x)
--   → isEmbedding f
