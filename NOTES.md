

These are some personal notes, discoveries, conclusions and ideas that should not spill the source code so much.

## general notes

- [a list of unicode symbols in agda](https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html)


## unresolved metas when using mere propositions in implicit arguments


```agda
implicationₚ : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ P ⇒ ¬ Q ]
implicationₚ {ℓ = ℓ} P Q ¬[p⊓q] p q = ⊥-elim (¬[p⊓q] (p , q))
-- the following was an attempt to return `fst` of something in order to help agda resolving some metas when using `implicationₚ` but it did not help
--   so maybe these unresolved metas have a different source
-- yes: we need to pass `snd P` and `snd Q` into `implicationₚ` in order to resolve correctly `[ P ⇒ ¬ Q ]` and alike
{-
 let
 γ : (A : Type ℓ') → [ P ] → [ Q ] → A
 γ A = λ p q → ⊥-elim {A = λ _ → A} (¬[p⊓q] (p , q))
 --prop : Σ (Type ℓ) (λ A → (x y : A) → x ≡ y)
 --prop = [ P ⇒ ¬ Q ] ,  λ x y → funExt-⊥₂ x y
 in fst {B = λ _ → (x y : ⊥.⊥) → x ≡ y} (γ ⊥.⊥ , λ x ())  -- (⊥-elim ⊥) , (⊥-elim ⊥)
-}
```

when using "mere propositions" like `[ P ]`, for P being an hProp, we need to pass in `snd P` to get it resolved correctly
therefore we might follow the convention to pass P as an explicit argument (and not an implicit one)

## deMorgan₁ is not provable without further assumptions

my attempt so far was

```agda
deMorgan₁ : (P Q : hProp ℓ) → [ ¬ (P ⊓ Q) ] → [ ¬ P ⊔ ¬ Q ]
deMorgan₁ {ℓ = ℓ} P Q ¬[p⊓q] = let
  ¬[q⊓p] : [ ¬ (Q ⊓ P) ]
  ¬[q⊓p] = (transport (λ i →  [ ¬ (⊓-comm P Q i) ] ) ¬[p⊓q] )
  a : [ P ⇒ ¬ Q ]
  a = implicationₚ P Q  ¬[p⊓q]
  b : [ Q ⇒ ¬ P ]
  b = implicationₚ Q P ¬[q⊓p]
  in {! !}
```

https://en.wikipedia.org/wiki/De_Morgan_algebra

In a De Morgan algebra, the laws

```
¬x ∨ x = 1 (law of the excluded middle), and
¬x ∧ x = 0 (law of noncontradiction)
```

do not always hold.

In the presence of the De Morgan laws, either law implies the other, and an algebra which satisfies them becomes a Boolean algebra.

https://ncatlab.org/nlab/show/weak+excluded+middle#de_morgans_law

In intuitionistic logic, de Morgan’s law often refers to the one of de Morgan's four laws that is not an intuitionistic tautology, namely ¬(P ∧ Q) → (¬ P ∨ ¬ Q) for any P,Q.

Theorem. De Morgan’s law is equivalent to weak excluded middle.

```agda
deMorgan₁ : ∀ x y → ¬ (x × y) ≡ (¬ x) ⊎ (¬ y)
deMorgan₁ x y = lemma (x × y) (¬ x ⊎ ¬ y) lem₁ lem₂
  where
  lem₁ = (
    (x × y) × (¬ x ⊎ ¬ y)          ≡⟨ {! ×-⊎-distribˡ _ _ _ !} ⟩
    (x × y) × ¬ x ⊎ (x × y) × ¬ y  ≡⟨ {! ⊎-congʳ $ ×-congʳ $ ×-comm _ _ !} ⟩
    (y × x) × ¬ x ⊎ (x × y) × ¬ y  ≡⟨ {! ×-assoc _ _ _ ⟨ ⊎-cong ⟩ ⟩ ×-assoc _ _ _ !} ⟩
    y × (x × ¬ x) ⊎ x × (y × ¬ y)  ≡⟨ {! (×-congˡ $ ×-complementʳ _) ⟨ ⊎-cong ⟩
                                      (×-congˡ $ ×-complementʳ _) !} ⟩
    (y × ⊥) ⊎ (x × ⊥)              ≡⟨ {! ×-zeroʳ _ ⟨ ⊎-cong ⟩ ⟩ ×-zeroʳ _ !} ⟩
    ⊥ ⊎ ⊥                          ≡⟨ {! ⊎-identityʳ _ !} ⟩
    ⊥                              ∎)

  lem₃ = (
    (x × y) ⊎ ¬ x          ≡⟨ {! ⊎-×-distribʳ _ _ _ !} ⟩
    (x ⊎ ¬ x) × (y ⊎ ¬ x)  ≡⟨ {! ×-congʳ $ ⊎-complementʳ _ !} ⟩
    ⊤ × (y ⊎ ¬ x)          ≡⟨ {! ×-identityˡ _ !} ⟩
    y ⊎ ¬ x                ≡⟨ {! ⊎-comm _ _ !} ⟩
    ¬ x ⊎ y                ∎)

  lem₂ = (
    (x × y) ⊎ (¬ x ⊎ ¬ y)  ≡⟨ {! ⊎-assoc _ _ _ !} ⟩
    ((x × y) ⊎ ¬ x) ⊎ ¬ y  ≡⟨ {! ⊎-congʳ lem₃ !} ⟩
    (¬ x ⊎ y) ⊎ ¬ y        ≡⟨ {! ⊎-assoc _ _ _ !} ⟩
    ¬ x ⊎ (y ⊎ ¬ y)        ≡⟨ {! ⊎-congˡ $ ⊎-complementʳ _ !} ⟩
    ¬ x ⊎ ⊤                ≡⟨ {! ⊎-zeroʳ _ !} ⟩
    ⊤                      )
```

## more logic for LEM

the following does only hold when LEM is available (e.g. in a BooleanAlgebra)

```agda
import Algebra.Properties.BooleanAlgebra
import Algebra.Consequences.Setoid

⊔-complementˡ : (x : hProp ℓ) → ¬ x ⊔ x ≡ ⊤↑
⊔-complementˡ = {! comm+invʳ⇒invˡ ⊔-comm ⊔-complementʳ !}

⊔-complementʳ : (x : hProp ℓ) → x ⊔ ¬ x ≡ ⊤↑
⊔-complementʳ x =
 ⇒∶ (λ _ → lift tt) -- we can always create a ⊤↑
 ⇐∶ λ _ → {!!}

⊔-complement : ((x : hProp ℓ) → ¬ x ⊔ x ≡ ⊤↑) × ((x : hProp ℓ) → x ⊔ ¬ x ≡ ⊤↑)
⊔-complement = ⊔-complementˡ , ⊔-complementʳ

⊓-complementˡ : (x : hProp ℓ) → ¬ x ⊓ x ≡ ⊥↑
⊓-complementˡ = {! isProp!} -- comm+invʳ⇒invˡ ⊓-comm ⊓-complementʳ

⊓-complementʳ : (x : hProp ℓ) → x ⊓ ¬ x ≡ ⊥↑
⊓-complementʳ = {!!}

⊓-complement : ((x : hProp ℓ) → ¬ x ⊓ x ≡ ⊥↑) × ((x : hProp ℓ) → x ⊓ ¬ x ≡ ⊥↑)
⊓-complement = ⊓-complementˡ , ⊓-complementʳ


private
  lemma : (x y : hProp ℓ) → x ⊓ y ≡ ⊥↑ → x ⊔ y ≡ ⊤↑ → ¬ x ≡ y
  lemma x y x⊓y=⊥ x⊔y=⊤ = (
    ¬ x                    ≡⟨ sym (⊓-identityʳ-↑ _) ⟩
    ¬ x ⊓ ⊤↑               ≡⟨ (λ i → ¬ x ⊓ x⊔y=⊤ (~ i) ) ⟩
    ¬ x ⊓ (x ⊔ y)          ≡⟨ ⊓-⊔-distribˡ (¬ x) x y  ⟩
    (¬ x ⊓ x) ⊔ (¬ x ⊓ y)  ≡⟨ (λ i → ⊓-complementˡ x i ⊔ (¬ x ⊓ y)) ⟩
    ⊥↑ ⊔ (¬ x ⊓ y)         ≡⟨ (λ i → x⊓y=⊥ (~ i) ⊔ (¬ x ⊓ y)) ⟩
    (x ⊓ y) ⊔ (¬ x ⊓ y)    ≡⟨  sym (⊓-⊔-distribʳ y x (¬ x)) ⟩
    (x ⊔ ¬ x) ⊓ y          ≡⟨ (λ i → (⊔-complementʳ x) i ⊓ y ) ⟩
    ⊤↑ ⊓ y                 ≡⟨ ⊓-identityˡ-↑ _ ⟩
    y                      ∎)
```

## some notes/observations about coding conventions

for some properties where it is applicable we should supply both variants:
  the tuple variant and the l/r-variant
and we might choose that the tuple variant is the field and the l/r-variant is the projection

an example

```agda
 ·-inv      : (x : F) → (p : x # 0f) → (x · (_⁻¹ᶠ x {{p}}) ≡ 1f) × ((_⁻¹ᶠ x {{p}}) · x ≡ 1f)
 ·-rinv     : (x : F) → (p : x # 0f) →  x · (_⁻¹ᶠ x {{p}}) ≡ 1f
 ·-linv     : (x : F) → (p : x # 0f) →                              (_⁻¹ᶠ x {{p}}) · x ≡ 1f
```

and then we have also

```agda
·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
```

also, the old standard library defines things with the identity element on the right side

```agda
LeftInverse  e _⁻¹ _∙_ = ∀ x → ((x ⁻¹) ∙ x) ≈ e
RightInverse e _⁻¹ _∙_ = ∀ x → (x ∙ (x ⁻¹)) ≈ e
Inverse      e  ⁻¹  ∙  = (LeftInverse e ⁻¹) ∙ × (RightInverse e ⁻¹ ∙)
```

so maybe we take as a convention to have the "more complex" term on the LHS and the "eliminated" or "normalized" term on the RHS of ≡, e.g.

```agda
_*_ DistributesOverˡ _+_ = ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))
_*_ DistributesOverʳ _+_ = ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
```

is there a reason for the ˡ ʳ convention in this case?
Also, in these definitions of `DistributesOver` we have that the multiply-occuring parameter (`x` in this case) is the first one

also recall that

```agda
_⇒_ will associate to the right in

  infixr 20 _⇒_
  _ : x ⇒  y ⇒  z  ≡   x ⇒ (y  ⇒  z)

_⇒’_ will associate to the left in

  infixl 20 _⇒’_
  _ : x ⇒’ y ⇒’ z  ≡  (x ⇒’ y) ⇒’ z
```

so in

```agda
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))
```

we have the "left associated" term on the LHS and the "right associated" term

NOTE: Generally, it seems a good convention that the order of parameters in the definition should match the left hand side. This makes it easier to determine which parameters need to be plugged into the definition when having a left hand side (e.g. with `_≡⟨_⟩` reasoning).

there seems to be a convention that
> "We will adopt the convention of denoting the level of the carrier set by ℓ₀ and the level of the relation result by ℓ₁."

### more interesting conventions

in the master thesis of Frederik Hanghøj Iversen https://fredefox.github.io/cat/Cat.Category.html

```agda
-- FIXME It seems counter-intuitive that the normal-form is on the
-- right-hand-side.
IsAssociative : Set (ℓa ⊔ ℓb)
IsAssociative = ∀ {A B C D} {f : Arrow A B} {g : Arrow B C} {h : Arrow C D}
   → h <<< (g <<< f) ≡ (h <<< g) <<< f
```

```agda
-- Having two terminal objects induces an isomorphism between them - and
-- because of univalence this is equivalent to equality.
propTerminal : isProp Terminal
propTerminal Xt Yt = res
  where
  open Σ Xt renaming (fst to X ; snd to Xit)
  open Σ Yt renaming (fst to Y ; snd to Yit)
  open Σ (Xit {Y}) renaming (fst to Y→X) using ()
  open Σ (Yit {X}) renaming (fst to X→Y) using ()
  ...
  res : Xt ≡ Yt
  res i = p0 i , p1 i
```

```agda
propIsInitial : ∀ I → isProp (IsInitial I)
propIsInitial I x y i {X} = res X i
  where
  module _ (X : Object) where
    open Σ (x {X}) renaming (fst to fx ; snd to cx)
    open Σ (y {X}) renaming (fst to fy ; snd to cy)
    fp : fx ≡ fy
    fp = cx fy
    prop : (x : Arrow I X) → isProp (∀ f → x ≡ f)
    prop x = propPi (λ y → arrowsAreSets x y)
    cp : (λ i → ∀ f → fp i ≡ f) [ cx ≡ cy ]
    cp = lemPropF prop _ _ fp
    res : (fx , cx) ≡ (fy , cy)
    res i = fp i , cp **
```

```agda
-- We make this a record so that isEquiv can be proved using
-- copatterns. This is good because copatterns don't get unfolded
-- unless a projection is applied so it should be more efficient.
record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    equiv-proof : (y : B) → isContr (fiber f y)
```

in `Algebra.Consequences.Propositional` shows how type of module parameters can be deduced by its corresponding definitions

```agda
module _ {_•_ _⁻¹ ε} where

  assoc+id+invʳ⇒invˡ-unique : Associative _•_ → Identity ε _•_ →
                              RightInverse ε _⁻¹ _•_ →
                              ∀ x y → (x • y) ≡ ε → x ≡ (y ⁻¹)
  assoc+id+invʳ⇒invˡ-unique = Base.assoc+id+invʳ⇒invˡ-unique (cong₂ _)
```

in `Relation.Binary.PropositionalEquality.Properties` we have some "default instances"

```agda
isEquivalence        :                         IsEquivalence    {A = A} _≡_
isDecEquivalence     : Decidable _≡_         → IsDecEquivalence {A = A} _≡_
isPreorder           :                         IsPreorder       {A = A} _≡_ _≡_
setoid               : Set a                 → Setoid _ _
decSetoid            : Decidable {A = A} _≡_ → DecSetoid _ _
preorder             : Set a                 → Preorder _ _ _

isEquivalence        = record { refl = refl ; sym = sym ; trans = trans }
isDecEquivalence _≟_ = record { isEquivalence = isEquivalence ; _≟_ = _≟_ }
isPreorder           = record { isEquivalence = isEquivalence ; reflexive = id ; trans = trans }
setoid A             = record { Carrier = A ; _≈_ = _≡_ ; isEquivalence = isEquivalence }
decSetoid _≟_        = record { _≈_ = _≡_ ; isDecEquivalence = isDecEquivalence _≟_ }
preorder A           = record { Carrier = A; _≈_ = _≡_; _∼_ = _≡_; isPreorder = isPreorder}
```

[in the manual](https://agda.readthedocs.io/en/v2.6.1/language/record-types.html#) it is written:

- _"if x is an implicit or instance field, then it is omitted from new-fields."_

_"The reason for treating implicit and instance fields specially is to allow code like the following:"_

```agda
data Vec (A : Set) : Nat → Set where
[] : Vec A zero
_∷_ : ∀{n} → A → Vec A n → Vec A (suc n)

record R : Set where
field
{length} : Nat
vec      : Vec Nat length
-- More fields ...

xs : R
xs = record { vec = 0 ∷ 1 ∷ 2 ∷ [] }

ys = record xs { vec = 0 ∷ [] }
```

_"Without the special treatment the last expression would need to include a new binding for length (for instance length = _)"_.

Irrelevant record fields are [prefixed with a dot](https://agda.readthedocs.io/en/v2.6.1/language/irrelevance.html#irrelevant-record-fields):

```agda
record InterestingNumbers : Set where
  field
    n      : Nat
    m      : Nat
    .prop1 : n + m ≡ n * m + 2
    .prop2 : suc m ≤ n
```

these are called ["irrelevancy annotations"](https://agda.readthedocs.io/en/v2.6.1/language/irrelevance.html#irrelevant-record-fields)

## naming scheme

- my personal (LEGACY) approach was:
  - there is `Properties` and `Consequences`
    - the difference somehow is, that we do want to open `Consequences` directly
    - but we do not want to open `Properties` directly, because it might have a name clash
    - e.g. there is `Properties.Group` which clashes with `Cubical.Structures.Group.Group` when opening `Properties`
    - but it is totally fine to open `Properties.Group` directly because it does not export a `Group`
  - this does also not help much, since we would need a single `Properties` module anyways
  - having a sub-folder `Group.Properties` would help

### how the non-cubical Agda standard library does it:

common file names are `find . -iname "*.agda" | awk 'sub( /.\/.*\//,"",$0 )' | sort | uniq -c | sort -h`

```
Instances.agda     ( 9×)
Literals.agda      ( 9×)
Indexed.agda       (10×)
All.agda           (12×)
Categorical.agda   (12×)
WithK.agda         (18×)
Core.agda          (21×)
Setoid.agda        (22×)
Propositional.agda (23×)
Base.agda          (31×)
Properties.agda    (90×)
```

- there are some deprecation warnings that "document" the design decisions
  - "Algebra.FunctionProperties.Consequences.Propositional was deprecated in v1.3. Use Algebra.Consequences.Propositional instead."
  - "Algebra.FunctionProperties.Consequences was deprecated in v1.3. Use Algebra.Consequences.Setoid instead."
- the non-cubical standard library has two folders in `Algebra`: `Consequences` and `Properties` to collect them for each sub-structure
  - e.g. `Consequences` contains `Propositional` and `Setoid`
  - and `Properties` contains `Group`, `Lattice`, `Ring`, ...
- there can be both: a `Properties` module and a `Properties` folder which provide what we need
- we have that "Properties" are parametrized modules by their corresponding algebraic structure, e.g. `module Algebra.Properties.AbelianGroup {a ℓ} (G : AbelianGroup a ℓ) where`
- and "Consequences" makes use of "raw" Definitions, e.g. `Associative`, `Identity`, ...
- where I do annotate hProps with `ᵖ`, in the cubical standard library they are just lowercased
  - my reason is to have the unannotated version as a record field of some combined property
  - but maybe we just use a "short name" for this purpose, e.g.
    - `associative` for the hProp
    - `Associative = [ associative ]` for the underlying type
    - `is-assoc : [ associative ]` for an instance (because this should not conflict with `sym` for pathes)
    - `+-assoc : [ associative ]` when multiple instances need to be distinguished
    - `f-preserves-P : P x → P (f x)`
    - `f-reflects-P : P (f x) → P x`
    - `f-creates-P : P x ↔ P (f x)` (as suggested on the #agda freenode channel _"In category theory, a similar property of functors is called 'creates'. Like 'f creates Ps'. the idea of 'creates' is that you have a structure on A, and it completely determines the analogous structure in B via f"_)
      - is this related to the nomer "extensional" as in "+ is <-extensional" ? (because the one single `+-<-extensional` property generates "all" properties that relate `_+_` and `_<_`)
    - `over`, e.g. `dne-over-≡ : ∀[ x ] ∀[ y ] ¬ ¬ (x ≡ₚ y) ⇔ (x ≡ₚ y)` because in `¬ ¬ (x ≡ₚ y)`, when its syntax tree is drawn with the root node `¬_` on top, then it is "over" `_≡ₚ_` which is below
    - `under`, the other way around (is this useful?)

.

In the 1.4-rc1 changelog we see that the wording NonZero, Positive, Negative, NonPositive and NonNegative already corresponds to our wording (TODO: adjust the case).
But they seem to suffix a number with `ℤ` where we use `ᶻ`, e.g. `0ℤ` instead of `0ᶻ`.
I found that superscript letters carry a little less weight and make formulas more readable when they make heavy use of different number types and I use the "fat" `ℤ` prefix for properties or functions that carry a "written out" name.

> * Added new types and constructors to `Data.Integer.Base`
>
> ```agda
> NonZero     : Pred ℤ 0ℓ
> Positive    : Pred ℤ 0ℓ
> Negative    : Pred ℤ 0ℓ
> NonPositive : Pred ℤ 0ℓ
> NonNegative : Pred ℤ 0ℓ
>
> ≢-nonZero   : p ≢ 0ℤ → NonZero p
> >-nonZero   : p > 0ℤ → NonZero p
> <-nonZero   : p < 0ℤ → NonZero p
> positive    : p > 0ℤ → Positive p
> negative    : p < 0ℤ → Negative p
> nonPositive : p ≤ 0ℤ → NonPositive p
> nonNegative : p ≥ 0ℤ → NonNegative p
> ```

They write _"See `Data.Nat.Base` for a discussion on the design of these"_.

> Simple predicates
>
> Defining `NonZero` in terms of `⊤` and `⊥` allows Agda to
> automatically infer nonZero-ness for any natural of the form
> `suc n`. Consequently in many circumstances this eliminates the need
> to explicitly pass a proof when the NonZero argument is either an
> implicit or an instance argument.
>
> It could alternatively be defined using a datatype with an instance
> constructor but then it would not be inferrable when passed as an
> implicit argument.
>
> See `Data.Nat.DivMod` for an example.

### naming of lemmas

in `Algebra.Consequences.Setoid {a ℓ} (S : Setoid a ℓ)` we have

```agda
comm+cancelˡ⇒cancelʳ        : LeftCancellative _•_   → RightCancellative _•_
comm+cancelʳ⇒cancelˡ        : RightCancellative _•_  → LeftCancellative _•_
comm+idˡ⇒idʳ                : LeftIdentity e _•_     → RightIdentity e _•_
comm+idʳ⇒idˡ                : RightIdentity e _•_    → LeftIdentity e _•_
comm+zeˡ⇒zeʳ                : LeftZero e _•_         → RightZero e _•_
comm+zeʳ⇒zeˡ                : RightZero e _•_        → LeftZero e _•_
comm+invˡ⇒invʳ              : LeftInverse e _⁻¹ _•_  → RightInverse e _⁻¹ _•_
comm+invʳ⇒invˡ              : RightInverse e _⁻¹ _•_ → LeftInverse e _⁻¹ _•_
assoc+id+invʳ⇒invˡ-unique   : Associative _•_ → Identity e _•_ → RightInverse e _⁻¹ _•_ → ∀ x y → (x • y) ≈ e → x ≈ (y ⁻¹)
assoc+id+invˡ⇒invʳ-unique   : Associative _•_ → Identity e _•_ → LeftInverse  e _⁻¹ _•_ → ∀ x y → (x • y) ≈ e → y ≈ (x ⁻¹)
comm+distrˡ⇒distrʳ          : _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
comm+distrʳ⇒distrˡ          : _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
comm⇒sym[distribˡ]          : ∀ x → Symmetric (λ y z → (x ◦ (y • z)) ≈ ((x ◦ y) • (x ◦ z)))
assoc+distribʳ+idʳ+invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ → RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ → LeftZero 0# _*_
assoc+distribˡ+idʳ+invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ → RightIdentity 0# _+_ → RightInverse 0# _⁻¹ _+_ → RightZero 0# _*_
subst+comm⇒sym              : Symmetric (λ a b → P (f a b))
wlog                        : ∀ {r} {_R_ : Rel _ r} → Total _R_ → (∀ a b → a R b → P (f a b)) → ∀ a b → P (f a b)
```

in `Algebra.Consequences.Propositional` we have

```agda
assoc+id+invʳ⇒invˡ-unique   : Associative _•_ → Identity ε _•_ → RightInverse ε _⁻¹ _•_ → ∀ x y → (x • y) ≡ ε → x ≡ (y ⁻¹)
assoc+id+invˡ⇒invʳ-unique   : Associative _•_ → Identity ε _•_ → LeftInverse ε _⁻¹ _•_ → ∀ x y → (x • y) ≡ ε → y ≡ (x ⁻¹)
assoc+distribʳ+idʳ+invʳ⇒zeˡ : Associative _+_ → _*_ DistributesOverʳ _+_ → RightIdentity 0# _+_ → RightInverse 0# -_ _+_ → LeftZero 0# _*_
assoc+distribˡ+idʳ+invʳ⇒zeʳ : Associative _+_ → _*_ DistributesOverˡ _+_ → RightIdentity 0# _+_ → RightInverse 0# -_ _+_ → RightZero 0# _*_
comm+distrˡ⇒distrʳ          : _•_ DistributesOverˡ _◦_ → _•_ DistributesOverʳ _◦_
comm+distrʳ⇒distrˡ          : _•_ DistributesOverʳ _◦_ → _•_ DistributesOverˡ _◦_
comm⇒sym[distribˡ]          : ∀ x → Symmetric (λ y z → (x ◦ (y • z)) ≡ ((x ◦ y) • (x ◦ z)))
sel⇒idem                    : Selective _•_ → Idempotent _•_
subst+comm⇒sym              : ∀ {f} (f-comm : Commutative f) → Symmetric (λ a b → P (f a b))
wlog                        : ∀ {f} (f-comm : Commutative f) → ∀ {r} {_R_ : Rel _ r} → Total _R_ → (∀ a b → a R b → P (f a b)) → ∀ a b → P (f a b)
```

## open module afterwards in where clause

https://agda.readthedocs.io/en/v2.6.1/language/copatterns.html#copatterns

```agda
backward-2 : {A : Set} → Enumeration A → A → A
backward-2 e a = backward (backward a)
  where
    open Enumeration e
```

## dot-postfix notation for record fields / projections (copatterns?)

This does only works for "(co)patterns" somehow. It somehow only works on "projections" from "constructor-projection-pairs", meaning that it works on the field-projection functions of a record but not on general functions.

(Is the important "property" of patterns and copatterns here, that they make a "normalized term"?)

In any case: instead of `fst u` we can write `u .fst` or even `u .Σ.fst` (or `Σ.fst u`) which are all definitionally equal.

```agda
test1' : {A : Type ℓ} {B : A → Type ℓ'} → (u : Σ A B) → fst u ≡ u .fst
test1' u = refl

test2' : {A : Type ℓ} {B : A → Type ℓ'} → (u : Σ A B) → fst u ≡ u .Σ.fst
test2' u = refl
```

[the manual](https://agda.readthedocs.io/en/v2.6.1/language/record-types.html) writes about "copattnerns":

_Elements of record types can be defined using a record expression [...] or using copatterns._
_Copatterns may be used prefix_

```agda
p34 : Pair Nat Nat
Pair.fst p34 = 3
Pair.snd p34 = 4
```

_**suffix (in which case they are written prefixed with a dot)**_

```agda
p56 : Pair Nat Nat
p56 .Pair.fst = 5
p56 .Pair.snd = 6
```

_or using an anonymous copattern-matching lambda (you may only use the suffix form of copatterns in this case)_

```agda
p78 : Pair Nat Nat
p78 = λ where
  .Pair.fst → 7
  .Pair.snd → 8
```

in `Agda.Builtin.Cubical.Glue` it is written that _copatterns don't get unfolded unless a projection is applied_

```agda
-- We make this a record so that isEquiv can be proved using
-- copatterns. This is good because copatterns don't get unfolded
-- unless a projection is applied so it should be more efficient.
record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    equiv-proof : (y : B) → isContr (fiber f y)
```

## copatterns

My copattern example would be:

```agda
-- suppose this function
test2' : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test2' a₁₂₃₄ = {!   !} -- Goal: B₁ × (B₂ × (B₃ × B₄))

-- we can "split" the RHS and give two separate "clauses" to construct the RHS
test3' : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test3' a₁₂₃₄ .fst = {!   !} -- Goal : B₁
test3' a₁₂₃₄ .snd = {!   !} -- Goal : B₂ × (B₃ × B₄)

-- instead of writing `fst` and `snd` as a suffix to the LHS of the clauses, we can write them as a prefix (without the dot) or even mix the style for different clauses
test3'ᵇ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
fst (test3'ᵇ a₁₂₃₄) = {!   !} -- Goal : B₁
snd (test3'ᵇ a₁₂₃₄) = {!   !} -- Goal : B₂ × (B₃ × B₄)

-- `fst` and `snd` are in scope, but if they would not be in scope, we could prefix them with their module name
test3'ᶜ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
Σ.fst (test3'ᶜ a₁₂₃₄) = {!   !} -- Goal : B₁
Σ.snd (test3'ᶜ a₁₂₃₄) = {!   !} -- Goal : B₂ × (B₃ × B₄)

-- alternatively we can also use an "anonymous copattern-matching lambda" to create "sub-clauses"
test3'ᵈ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test3'ᵈ a₁₂₃₄ = λ where
  .fst → {!   !} -- Goal : B₁
  .snd → {!   !} -- Goal : B₂ × (B₃ × B₄)

-- where we can move the arguments (in our case only a₁₂₃₄) to the sub-clauses like so
test3'ᵈ' : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test3'ᵈ' = λ where
   a₁₂₃₄ .fst → {!   !} -- Goal : B₁
   a₁₂₃₄ .snd → {!   !} -- Goal : B₂ × (B₃ × B₄)

-- the "sub-clauses" of an "anonymous copattern-matching lambda" do only allow for the dotted suffix copattern-notation
-- meaning, that we have to write `a₁₂₃₄ .fst → {!   !}` and we cannot write `fst a₁₂₃₄ → {!   !}`

-- again, if `fst` and `snd` where not in scope, we could prefix them by their
test3'ᵉ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test3'ᵉ a₁₂₃₄ = λ where
  .Σ.fst → {!   !} -- Goal : B₁
  .Σ.snd → {!   !} -- Goal : B₂ × (B₃ × B₄)

-- copatterns can be "stacked" "on-top" of each other
test4' : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test4' a₁₂₃₄ .fst      = {!   !} -- Goal : B₁
test4' a₁₂₃₄ .snd .fst = {!   !} -- Goal : B₂
test4' a₁₂₃₄ .snd .snd = {!   !} -- Goal : B₃ × B₄

-- which corresponds to the following prefix-notation (where brackets are put around the LHS just to make proper right-alignment possible)
test4'ᵇ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
(     fst (test4'ᵇ a₁₂₃₄) ) = {!   !} -- Goal : B₁
(fst (snd (test4'ᵇ a₁₂₃₄))) = {!   !} -- Goal : B₂
(snd (snd (test4'ᵇ a₁₂₃₄))) = {!   !} -- Goal : B₃ × B₄

-- without the brackets it just looks like
test4'ᶜ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
fst      (test4'ᶜ a₁₂₃₄)  = {!   !} -- Goal : B₁
fst (snd (test4'ᶜ a₁₂₃₄)) = {!   !} -- Goal : B₂
snd (snd (test4'ᶜ a₁₂₃₄)) = {!   !} -- Goal : B₃ × B₄

-- of course, (regular) pattern matching does still work for each clause separately
test5' : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test5' ( a₁₂₃      , a₄) .fst      = {!   !} -- Goal : B₁
test5' ( a₁₂₃      , a₄) .snd .fst = {!   !} -- Goal : B₂
test5' ((a₁₂ , a₃) , a₄) .snd .snd = {!   !} -- Goal : B₃ × B₄

-- and copatterns also stack in an "anonymous copattern-matching lambda"
test5'ᵈ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test5'ᵈ (a₁₂₃ , a₄) = λ where
  .fst      → {!   !} -- Goal : B₁
  .snd .fst → {!   !} -- Goal : B₂
  .snd .snd → {!   !} -- Goal : B₃ × B₄

-- and all the previous "techniques" can be mixed arbitrarily
test5'ᶠ : {A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Type ℓ} → ((A₁ × A₂) × A₃) × A₄ → B₁ × (B₂ × (B₃ × B₄))
test5'ᶠ (a₁₂₃₄    ) .fst = {!  !} -- Goal : B₁
test5'ᶠ (a₁₂₃ , a₄) .snd = λ where
  .fst → {!   !} -- Goal : B₂
  .snd → {!   !} -- Goal : B₃ × B₄

-- and so on and so forth ...
test6' : {A₁ A₂ A₃ A₄ A₅ A₆ : Type ℓ}
       → ((((A₁ ×  A₂) ×  A₃) ×  A₄) ×  A₅) × A₆
       →     A₁ × (A₂  × (A₃  × (A₄  × (A₅  × A₆))))
test6' a₁₂₃₄₅₆ = λ where
  .fst → a₁₂₃₄₅₆ .fst .fst .fst .fst .fst
  .snd .fst → a₁₂₃₄₅₆ .fst .fst .fst .fst .snd
  .snd .snd .fst → a₁₂₃₄₅₆ .fst .fst .fst .snd
  .snd .snd .snd .fst → a₁₂₃₄₅₆ .fst .fst .snd
  .snd .snd .snd .snd .fst → a₁₂₃₄₅₆ .fst .snd
  .snd .snd .snd .snd .snd      → a₁₂₃₄₅₆ .snd
```

### example from the standard library

```agda
module Test1 {A : Type ℓ} {B : Type ℓ'} (i : Iso A B) where
  open Iso i renaming ( fun to f; inv to g; rightInv to s; leftInv to t)

  -- an implementation of `isoToIsEquiv` with one clause is
  isoToIsEquiv⁰ : isEquiv f
  -- ?0-Goal : A
  -- ?1-Goal : f ?0 ≡ y
  -- ?2-Goal (?0 , ?1) ≡ z
  isoToIsEquiv⁰ = record { equiv-proof = λ y → ({!   !} , {!   !}) , λ z → {!    !} }

  -- with the use of copatterns, it is possible to expand this single clause into three separate clauses
  -- and it is possible to bring `y` and `z` to the LHS of these clauses

  -- the following is the variant which is used in the standard library where they note
  --   "We make [isEquiv] a record so that isEquiv can be proved using copatterns."
  --   "This is good because copatterns don't get unfolded unless a projection is applied so it should be more efficient."
  isoToIsEquivᵃ : isEquiv f
  isoToIsEquivᵃ .equiv-proof y .fst .fst = {!  !} -- ?0-Goal : A
  isoToIsEquivᵃ .equiv-proof y .fst .snd = {!  !} -- ?1-Goal : f ?0 ≡ y
  isoToIsEquivᵃ .equiv-proof y .snd z    = {!  !} -- ?2-Goal : fst (isoToIsEquivᵃ .equiv-proof y) ≡ z

  -- it is equivalent to the following prefix-variant
  isoToIsEquivᵇ : isEquiv f
  (fst (fst ((equiv-proof isoToIsEquivᵇ) y))   ) = {!  !} -- ?0-Goal : A
  (snd (fst ((equiv-proof isoToIsEquivᵇ) y))   ) = {!  !} -- ?1-Goal : f ?0 ≡ y
  (    (snd ((equiv-proof isoToIsEquivᵇ) y)) z ) = {!  !} -- ?2-Goal : fst (isoToIsEquiv .equiv-proof y) ≡ z
```

I guess that a "clause" is the smallest unit of computation that agda can "unfold" / "evaluate" (just like in Haskell, I guess).
If we build a structure and directly project out the first component (such as we do with hProps)
then it would make sense that only the necessary clauses are "evaluated".

Interestingly, clauses will only be unfolded when they have been "defined", meaning that when we postpone the clauses of a function definition, then all "code" inbetween the function declaration and the clause definition will not unfold the clause. (maybe this does also help to reorder clauses of a single function to help the termination checker (?))

So, if we "evaluate" / "normalize" / "unfold" (?) `fst (fst ((equiv-proof isoToIsEquivᵇ) y)` and this happens to be the first of three copattern clauses (like above),
then only this copattern clause should be evaluated and the other two copattern clauses can be ignored completely.

That might be what is more "efficient" about copatterns.

The reason then to use a record `isEquiv` with a single field `equiv-proof` is, that copatterns can only be used for record fields ("constructor-projection-pairs" ?).

| term                                                 |   | normal form (C-c C-n)                     | unfolding       |
|------------------------------------------------------|---|-------------------------------------------|-----------------|
| `isoToIsEquivᵇ`                                      | ⊢ | `isoToIsEquivᵇ`                           | no              |
| `equiv-proof isoToIsEquivᵇ`                          | ⊢ | `equiv-proof isoToIsEquivᵇ`               | no              |
| `λ(y : B) → equiv-proof isoToIsEquivᵇ y`             | ⊢ | `λ y → equiv-proof isoToIsEquivᵇ y`       | no              |
| `λ(y : B) → snd (equiv-proof isoToIsEquivᵇ y)`       | ⊢ | `λ y z → ?2 (i = i) (y = y) (z = z)`      | yes (clause ?2) |
| `λ(y : B) → fst (equiv-proof isoToIsEquivᵇ y)`       | ⊢ | `λ y → fst (equiv-proof isoToIsEquivᵇ y)` | no              |
| `λ(y : B) → fst (fst (equiv-proof isoToIsEquivᵇ y))` | ⊢ | `λ y → ?0 (i = i) (y = y)`                | yes (clause ?0) |
| `λ(y : B) → snd (fst (equiv-proof isoToIsEquivᵇ y))` | ⊢ | `λ y → ?1 (i = i) (y = y)`                | yes (clause ?1) |

This does only work for "root-level" patterns and copatterns and not for "anonymous copattern-matching lambdas". For example the following definition

```agda
isoToIsEquivᶜ : isEquiv f
isoToIsEquivᶜ = λ where
  .equiv-proof y .fst .fst → {!  !} -- ?0-Goal : A
  .equiv-proof y .fst .snd → {!  !} -- ?1-Goal : f ?0 ≡ y
  .equiv-proof y .snd z    → {!  !} -- ?2-Goal : fst (isoToIsEquiv .equiv-proof y) ≡ z
```

makes the normal form of `isoToIsEquivᶜ` to

```agda
λ { .equiv-proof y .fst .fst → ?0 (i = i) (y = y)
  ; .equiv-proof y .fst .snd → ?1 (i = i) (y = y)
  ; .equiv-proof y .snd z → ?2 (i = i) (y = y) (z = z)
  }
```

and the normal form of `equiv-proof isoToIsEquivᶜ` gets even longer

```agda
equiv-proof
(λ { .equiv-proof y .fst .fst → ?0 (i = i) (y = y)
   ; .equiv-proof y .fst .snd → ?1 (i = i) (y = y)
   ; .equiv-proof y .snd z → ?2 (i = i) (y = y) (z = z)
   })
```

and the normal form of `λ(y : B) → equiv-proof isoToIsEquivᶜ y` gets even longer

```agda
λ y →
  equiv-proof
  (λ { .equiv-proof y .fst .fst → ?0 (i = i) (y = y)
     ; .equiv-proof y .fst .snd → ?1 (i = i) (y = y)
     ; .equiv-proof y .snd z → ?2 (i = i) (y = y) (z = z)
     })
  y
```

finally the normal form of `λ(y : B) → snd (equiv-proof isoToIsEquivᶜ y)` reduces to the same "clause 2" as for the previous version

```agda
λ y z → ?2 (i = i) (y = y) (z = z)
```

Similar things happen for `isoToIsEquiv⁰ = record { equiv-proof = λ y → ({!   !} , {!   !}) , λ z → {!    !} }` although a bit better.

We have that the normal form of `isoToIsEquiv⁰` is

```agda
record
{ equiv-proof = λ y →
    ( ?0 (i = i) (y = y)
    , ?1 (i = i) (y = y))
    , (λ z → ?2 (i = i) (y = y) (z = z)
    )
}
```

and the normal form of `equiv-proof isoToIsEquiv⁰` is a little bit smaller

```agda
λ y →
  ( ?0 (i = i) (y = y)
  , ?1 (i = i) (y = y))
  , (λ z → ?2 (i = i) (y = y) (z = z)
  )
```

the normal form of `λ(y : B) → equiv-proof isoToIsEquiv⁰ y` is the same as before (its effect is just that `y` gets renamed to `y` again).

And finally the normal form of `λ(y : B) → snd (equiv-proof isoToIsEquiv⁰ y)` becomes "clause 2"

```agda
λ y z → ?2 (i = i) (y = y) (z = z)
```

We get a similar behaviour with

```agda
isoToIsEquivᵈ = record { equiv-proof = λ y → (a y , b y) , c y } where
  a = λ y   → {!  !} -- ?0-Goal
  b = λ y   → {!  !} -- ?1-Goal
  c = λ y z → {!  !} -- ?2-Goal
```

and also the `where` clauses are immediately "inlined" into the normalized form when the `where`'s clause is "available" such that for

```agda
isoToIsEquivᵉ : isEquiv f
isoToIsEquivᵉ .equiv-proof y = (a , b) , c where
  a =       {!  !} -- ?0-Goal
  b =       {!  !} -- ?1-Goal
  c = λ z → {!  !} -- ?2-Goal
```

we have that `λ(y : B) → (equiv-proof isoToIsEquivᵈ y)` normalizes to

```agda
λ y →
  ( ?0 (i = i) (y = y)
  , ?1 (i = i) (y = y))
  , (λ z → ?2 (i = i) (y = y) (z = z)
  )
```

But I guess that copatterns within a where block work as intended .. TODO: check this

### My theses

- Patterns allow to split a "computation" (function) into several independent "pieces" (clauses), based on the type(-destructors/projections?) on the LHS.
- Copatterns allow to split a "computation" (function) into several independent "pieces" (clauses), based on the type(-destructors/projections?) on the RHS.
- Mixing (nesting) patterns and copatterns allows to split a "computation" (function) into several independent "pieces" (clauses) based on the type(-destructors/projections?) in the (function-)signature.
- A term will only "normalize further", when it is able to determine a single "piece" (clause). Otherwise it is "blocked" or "already normalized".
- splitting into copatterns makes sense to allow the partial computation of a partially applied function without "waiting" for its arguments

Also note that case splitting on `_⊎_` blocks further evaluation until `inl` or `inr` is known of the argument.

Therefore I would propose to define algebraic properties with copatterns like so:

```agda
isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
isCotransᵖ R .fst =                                         ∀ a b →     [ R a b ⇒ (∀[ x ] R a x ⊔ R x b) ]
isCotransᵖ R .snd = isprop where abstract isprop = isPropΠ2 λ a b → snd ( R a b ⇒ (∀[ x ] R a x ⊔ R x b) )
```

and generally use copatterns as much as possible.

Well, the "intended" use is

```agda
isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
isCotransᵖ R = ∀[ a ] ∀[ b ] R a b ⇒ (∀[ x ] R a x ⊔ R x b)
```

which is the same (almost definitinally).

This normalizes to

```agda
( ((a b : A) → fst (R a b) → (x : A) → ∥ fst (R a x) ⊎ fst (R x b) ∥)
, (λ f g i a b aRb c → squash (f a b aRb c) (g a b aRb c) i)
)
```

and we could indeed make it a copattern-definition like so

```agda
isCotransᵖ : {ℓ ℓ' : Level} {A : Type ℓ} → (R : hPropRel A A ℓ') → hProp (ℓ-max ℓ ℓ')
isCotransᵖ {A = A} R .fst = (a b : A) → fst (R a b) → (x : A) → ∥ fst (R a x) ⊎ fst (R x b) ∥
isCotransᵖ {A = A} R .snd f g i a b aRb c = squash (f a b aRb c) (g a b aRb c) i
```

but this destroys all readability. Also it seems to make no difference in type-checking-time.

There is also the wording of two terms being "equal on the nose". What does it exactly mean? That two unnormalized terms are equal and there is no need to unfold them?

There is also an email of Andrea Vezzosi "Re: [Agda] Identifying inefficiency" (09.04.19, 16:42) on the agda mailing list

> I have found that efficiency problems with algebraic structures can be mitigated by disabling (definitional) eta rules for such record types and defining instances by copatterns. (Ulf gave a talk partly on this at the AIM in Leuven).

He explains what the `no-eta-equality` does in

```agda
record isEquiv {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} (f : A → B) : Set (ℓ ⊔ ℓ') where
  no-eta-equality
  field
    equiv-proof : (y : B) → isContr (fiber f y)
```

namely:

> This will make it so an element of isEquiv defined by copatterns will
only be definitionally equal to itself, so things get compared by name
and arguments.
>
> This is similar to what happens with functions defined by standard
pattern matching, when they cannot reduce.
>
> pathToEquiv is defined by copatterns, but now without eta for isEquiv
the typechecker will not try to observe what happens at each
projection.
>
> Then eta can still be proven propositionally by pattern matching on
the record constructor.
(Or in cubical one can define the corresponding path also by copatterns).

also see [eta expansion in the manual](https://agda.readthedocs.io/en/v2.6.0.1/language/record-types.html#eta-expansion)

> The eta rule for a record type [...] states that every `x : R` is definitionally equal to `record { a = R.a x ; b = R.b x ; c = R.c x }`.

### example of "cluttered" normalized term

E.g. `≤-≡-≤''` normalizes to 760 lines which might be fine for emacs, but it kills the atom plugin.

NOTE: These 760 lines are instantly normalized in emacs. This is totally an issue of the atom plugin displaying this term.

```agda
bridges-R3-5 : ∀ x y z → [ x ≤ y ] → [ y < z ] → [ x < z ]
bridges-R3-5 x y z x≤y y<z = ⊔-elim (y < x) (x < z) (λ _ → x < z) (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z) (<-cotrans y z y<z x)

≤''-implies-≤ : ∀ x y → [ x ≤'' y ] → [ x ≤ y ]
≤''-implies-≤ x y x≤''y y<x = <-irrefl x (x≤''y x y<x)

≤-implies-≤'' : ∀ x y → [ x ≤ y ] → [ x ≤'' y ]
≤-implies-≤'' x y x≤y ε y<ε = bridges-R3-5 x y ε x≤y y<ε

≤-≡-≤'' : ∀ x y → (Liftᵖ {ℓ'} {ℓ} (x ≤ y)) ≡ (x ≤'' y)
≤-≡-≤'' x y = ⇔toPath
              ((≤-implies-≤'' x y) ∘ (unliftᵖ (x ≤ y))) -- (λ{ (lift p) → ≤-implies-≤'' x y p})
              ((liftᵖ (x ≤ y)) ∘ (≤''-implies-≤ x y))
```

in these 760 lines of normalized term, there occur

- `Agda.Builtin.Cubical.Glue.primGlue`
- `Cubical.HITs.PropositionalTruncation.elim`
- `Cubical.Data.Sum.Base.elim`
- `⊥-elim`
- `isProp⊥`
- `transp`
- `hcomp`
- `isoToEquiv`
- `<-irrefl`
- `<-cotrans`
- `idEquiv`
- `isProp[]`

the normalized terms of `≤-implies-≤''`, `≤''-implies-≤`, `_≤''_` and `bridges-R3-5` do not look that ugly:

```agda
≤-implies-≤'' =
 λ x₁ y x≤y ε y<ε →
  Cubical.HITs.PropositionalTruncation.elim
   (λ x₂ → snd (x₁ < ε))
   (Cubical.Data.Sum.Base.elim (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z))
   (<-cotrans y ε y<ε x₁)

≤''-implies-≤ = λ x₁ y x≤''y y<x → <-irrefl x₁ (x≤''y x₁ y<x)

_≤''_ =
 λ x₁ y →
  ( ((ε : Carrier) → fst (y < ε) → fst (x₁ < ε))
  , (λ f g i x₂ x₃ → snd (x₁ < x₂) (f x₂ x₃) (g x₂ x₃) i)
  )

bridges-R3-5 =
 λ x₁ y z x≤y y<z →
  Cubical.HITs.PropositionalTruncation.elim
   (λ x₂ → snd (x₁ < z))
   (Cubical.Data.Sum.Base.elim (λ y<x → ⊥-elim (x≤y y<x)) (λ x<z → x<z))
   (<-cotrans y z y<z x₁)
```

THESIS: Maybe we can also make use of copatterns in the `MorePropAlgebra` module to help Agda normalizing this term into something smaller.

## using equivalences instead of `lemma` and `lemma-back`

- when using "implicational" reasoning `_⇒⟨_⟩` agda is pretty good in determining the arguments within `⟨_⟩`
- but all arguments become necessary when being inside of a path, e.g. for using `transport`
- so it might be a good strategy to have all the "tactics" (well, not really tactics, but
  - the most used "proof machinery" at least) available as explicit functions, such that only a single function
  - needs to be applied in each step
- often, just using `cong₂` instead of a path as the argument of `transport` already helps
  - well, no. see [XX]
- this is observable in the standard library to some degree `grep -RHni ≡⟨ ~/agda/cubical/`
- there is also a `≡⟨⟩` just for the identity which is useful for folding/unfolding definition
  - i.e. steps that hold definitionally
  - `_≡⟨⟩_ : ∀ (x {y} : A) → x ≡ y → x ≡ y`
  - `_ ≡⟨⟩ x≡y = x≡y`
  - `infixr 2 _≡⟨⟩_`
- this just avoids the use of `≡⟨ λ x → x ⟩`
- I am doing this for the n'th time now ...
- these four cases can surely be omitted by using correct equivalences (TODO)
- I think I am very close. Sometimes it amounts just to dropping `transport` to have the equivalence
- so there is still some exercise for getting used to this
- there is Tactic.MonoidSolver in the old standard library
- and https://github.com/UlfNorell/agda-prelude/blob/master/src/Tactic/Monoid.agda
  and https://github.com/UlfNorell/agda-prelude/blob/master/test/MonoidTactic.agda
- and https://github.com/agda/agda-stdlib/blob/experimental/README/Solvers/ReflectiveMonoid.agda
- and maybe a few more ...

```agda
+-preserves-≡ʳ : ∀ x y z → x ≡ y → x + z ≡ y + z
+-preserves-≡ʳ x y z x≡y = transport (λ i → x + z ≡ x≡y i + z) refl

+-preserves-≡ˡ : ∀ x y z → x ≡ y → z + x ≡ z + y
+-preserves-≡ˡ x y z x≡y = transport (λ i → z + x ≡ z + x≡y i) refl
```

## some research about hProps

Booij writes "we identify elements of HProp with ... their first projection". Therefore Agda's first projection `[_]` is not present in Booij's writing (it's implicit).

| Booij                                  | Agda                                                                     |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `⊤              := 1                 ` | `⊤ : hProp _                                                           ` |
|                                        | `⊤ = Unit , (λ _ _ _ → tt)                                             ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `⊥              := 0                 ` | `⊥ : hProp _                                                           ` |
|                                        | `⊥ = ⊥.⊥ , λ ()                                                        ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `P ∧ Q          := P × Q             ` | `A ⊓′ B = A × B                                                        ` |
|                                        | `A ⊓ B = [ A ] ⊓′ [ B ] , isOfHLevelΣ 1 (isProp[] A) (\ _ → isProp[] B)` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `P ⇒ Q          := P → Q             ` | `A ⇒ B = ([ A ] → [ B ]) , isPropΠ λ _ → isProp[] B                    ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `P ⇔ Q          := P = Q             ` | `A ⇔ B = (A ⇒ B) ⊓ (B ⇒ A)                                             ` |
|                                        | `⇔toPath : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q                               ` |
|                                        | `pathTo⇒ : P ≡ Q → [ P ⇒ Q ]                                           ` |
|                                        | `pathTo⇐ : P ≡ Q → [ Q ⇒ P ]                                           ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `¬P             := P → 0             ` | `¬ A = ([ A ] → ⊥.⊥) , isPropΠ λ _ → ⊥.isProp⊥                         ` |
|                                        | `x ≢ₚ y = ¬ x ≡ₚ y                                                     ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `P ∨ Q          := ∥ P + Q ∥         ` | `A ⊔′ B = ∥ A ⊎ B ∥                                                    ` |
|                                        | `P ⊔ Q = ∥ [ P ] ⊎ [ Q ] ∥ₚ                                            ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `(∀ x : X) R(x) :=  (Π x : X) R(x)   ` | `∀[∶]-syntax {A = A} P = (∀ x → [ P x ]) , isPropΠ (isProp[] ∘ P)      ` |
|                                        | `∀[]-syntax  {A = A} P = (∀ x → [ P x ]) , isPropΠ (isProp[] ∘ P)      ` |
|                                        | `syntax ∀[∶]-syntax {A = A} (λ a → P) = ∀[ a ∶ A ] P                   ` |
|                                        | `syntax  ∀[]-syntax (λ a → P)          = ∀[ a ] P                      ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `(∃ x : X) R(x) := ∥ (Σ x : X) R(x) ∥` | `∃[∶]-syntax {A = A} P = ∥ Σ A ([_] ∘ P) ∥ₚ                            ` |
|                                        | `∃[]-syntax  {A = A} P = ∥ Σ A ([_] ∘ P) ∥ₚ                            ` |
|                                        | `syntax ∃[∶]-syntax {A = A} (λ x → P) = ∃[ x ∶ A ] P                   ` |
|                                        | `syntax ∃[]-syntax          (λ x → P) = ∃[ x ] P                       ` |
| -------------------------------------- | ------------------------------------------------------------------------ |
| `isHProp(P)   := (Π p, q : P)(p =ₚ q)` | `isProp A = (x y : A) → x ≡ y                                          ` |
| `HProp       := (Σ P : 𝓤) isHProp(P)` | `hProp  ℓ = Σ[ A ∈ Type ℓ ] isProp A                                   ` |

the equivalences might be proven together
this could be done with `⇒∶_⇐∶_` and `⇐∶_⇒∶_` from `Cubical.Foundations.Logic`

```agda
  ⊓-assoc : (P : hProp ℓ) (Q : hProp ℓ') (R : hProp ℓ'') → P ⊓ Q ⊓ R ≡ (P ⊓ Q) ⊓ R
  ⊓-assoc _ _ _ =
    ⇒∶ (λ {(x , (y , z)) →  (x , y) , z})
    ⇐∶ (λ {((x , y) , z) → x , (y , z) })
```

which makes use of

```agda
  ⇔toPath : [ P ⇒ Q ] → [ Q ⇒ P ] → P ≡ Q
  ⇔toPath : {ℓ : Level} {P Q : hProp ℓ}
          → (fst P → fst Q)
          → (fst Q → fst P)
          -------------------------------------------------------------
          → P ≡ Q
```

where we have

```agda
  hProp ℓ = Σ[ A ∈ Type ℓ ] (∀(x y : A) → x ≡ y)
```

and

```agda
  _⇒_ : (A : hProp ℓ) → (B : hProp ℓ') → hProp _
  A ⇒ B = ([ A ] → [ B ]) , isPropΠ λ _ → isProp[] B
```

and `[_]` and `isProp[]` being the projections of hProp

```agda
  [_] : hProp ℓ → Type ℓ
  [_] = fst

  isProp[] : (A : hProp ℓ) → isProp [ A ]
  isProp[] = snd
```

which are `fst` and `snd` from the sigma type Σ, coming from `hProp` being implemented via `TypeWithStr`

```agda
  hProp        ℓ   = TypeOfHLevel ℓ    1
  TypeOfHLevel ℓ n = TypeWithStr  ℓ   (isOfHLevel n)
  TypeWithStr  ℓ S = Σ[ X ∈ Type  ℓ ]  S X
```

where the "S-structure" is `isOfHLevel n : Type ℓ → Type ℓ`

```agda
  isOfHLevel      0        A = isContr A
  isOfHLevel      1        A = isProp  A
  isOfHLevel (suc (suc n)) A = (x y : A) → isOfHLevel (suc n) (x ≡ y)
```

so we get

```agda
  hProp ℓ = Σ[ X ∈ Type ℓ ] isProp X
```

[quote:]
A structure is a type-family S : Type ℓ → Type ℓ', i.e. for X : Type ℓ and s : S X,
the pair (X , s) : TypeWithStr ℓ S means that X is equipped with a S-structure, witnessed by s.

```agda
  TypeWithStr : (ℓ : Level) (S : Type ℓ → Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
  TypeWithStr ℓ S = Σ[ X ∈ Type ℓ ] S X
```

it's two projections are

```agda
  typ = fst
  str = snd
```

these [ P ] and [ Q ] are called "mere propositions"

## questions from the first web-meeting

1. Q: can we continue the same patterns for morphisms as we have with the other structures?
   A: yes! There is nothing that speaks against using `record`
2. Q: What machinery is necessary to express unique existence? (there is ∃! in the standard library)
   A: give ∃! from the standard library a try
3. Q: trichotomy of ordered fields ... do we have this? (you write the rationals have)
   A: no! We do not have trichotomy

## notes from the first web-meeting

- most of my types are contractible ... not
- cohesive type theory has a builtin notion of real number
  - balance between continuity and discontinuity
- therefore it is better suited to do differential geometry and alike
- classical mathematical starting point
  - locally euclidean, charts, atlasses
- univalent starting point
  - two manifolds are diffeomorphic exactly when they are equal
  - a function between manifolds is a diffeomorphism

## more vague questions/ideas for the far future

- approaches to limits and spaces for mathematical analysis
  - locales? for topological spaces
    Also a few years ago I was told that "locales" it the alternative to topological spaces
    while
  - limits and filters (see HOL)
    Some time ago I heard "on the streets" that filters are "not cool" amongst constructive mathematicians but I
    is that a "thing" or did I just misheard that
(un)bounded linear operators, adjoints and bounds

## anonymous copattern-matching lambda

see https://agda.readthedocs.io/en/v2.6.1/language/record-types.html

decompose record: see https://agda.readthedocs.io/en/v2.6.1/language/let-and-where.html#let-record-pattern

```agda
#'-isApartnessRel : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → (isSPO : IsStrictPartialOrder _<_) → IsApartnessRel (_#'_ {_<_ = _<_})
#'-isApartnessRel {X = X} {_<_ = _<_} isSPO =
  --
  let (isstrictpartialorder <-irrefl <-trans <-cotrans) = isSPO
  in λ where
    -- clauses work here and case-split does also work!
    -- but I get a "Not implemented: The Agda synthesizer (Agsy) does not support copatterns yet" on proof search
    .IsApartnessRel.isIrrefl a (inl a<a) → <-irrefl _ a<a
    .IsApartnessRel.isIrrefl a (inr a<a) → <-irrefl _ a<a
    .IsApartnessRel.isSym    a b p → swap p
    .IsApartnessRel.isCotrans a b (inl a<b) x → case (<-cotrans _ _ a<b x) of λ where -- case x of f = f x
      -- NOTE: here we have proof search again
      (inl a<x) → inl (inl a<x)
      (inr x<b) → inr (inl x<b)
    .IsApartnessRel.isCotrans a b (inr b<a) x → case (<-cotrans _ _ b<a x) of λ where
      (inl b<x) → inr (inr b<x)
      (inr x<a) → inl (inr x<a)
```

## instance syntax collection

there are a few in the code, but more here:

```agda
·-inv-same-sign : ∀ x y → 0f < x → 1f ≡ x · y → 0f < y
·-inv-same-sign x y 0<x 1=x·y = let
  instance _ = 0<x -- this is to multiply with
  instance _ = x # 0f ∋ inr 0<x -- this is to make use of ⁻¹
  in (0f < 1f    ⇒⟨ {!!} ⟩
      0f < x · y ⇒⟨ {!!} ⟩
      (x ⁻¹ᶠ) · 0f < x ⁻¹ᶠ · (x · y) ⇒⟨ {!!} ⟩
      0f < (x ⁻¹ᶠ · x) · y ⇒⟨ {!!} ⟩
      0f < y ◼) item-10

      0 < x · y
```

## more issues with instances

in the following, the `·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f`
"creates" new properties `x # 0f` and `y # 0f` that are different (!) from possibly existing "previous" ones

meaning, that this conflicts a usage where we might recreate these properties somewhere (inside of a module or a function)

and having the result-type depending on them

we can't use the result "outside" then, because it' differs in this `x # 0f` and `y # 0f` entity

although we might not see it (because instance arguments are hidden)

there is another NOTE of this

```agda
record IsOrderedField {F : Type ℓ}
                 (0f 1f : F) (_+_ : F → F → F) (-_ : F → F) (_·_ min max : F → F → F) (_<_ _#_ _≤_ : Rel F F ℓ') (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) : Type (ℓ-max ℓ ℓ') where
  constructor isorderedfield
  field
    -- 1.
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    -- 2.
    <-isStrictPartialOrder : IsStrictPartialOrder _<_
    -- 3.
    ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    -- 4. NOTE: we already have ≤-isPartialOrder in <-isLattice
    -- ≤-isPartialOrder : IsPartialOrder _≤_
    -- 5.
    <-isLattice : IsLattice _≤_ min max
    -- 6. (†)
    -- NOTE: this is 'shifted' from the pevious definition of #-extensionality for + .. does the name still fit?
    +-<-extensional : ∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)
    -- 6. (∗)
    ·-preserves-< : ∀ x y z → 0f < z → x < y → (x · z) < (y · z)

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsStrictPartialOrder <-isStrictPartialOrder public
    renaming
      ( isIrrefl  to <-irrefl
      ; isTrans   to <-trans
      ; isCotrans to <-cotrans )
  open IsLattice <-isLattice public
```

and then we might want to add some general instances to convert `0f # x` or `x < 0f` or `0f < x` into `x # 0f`

because there is always some fiddling necessary when using `_⁻¹ᶠ`

e.g. see poof of `item-8` below where we also had to turn `0f ≤ z` and `z # 0` into `0f < z` because `·-preserves-<` was defined in terms of `0f < z`

in:

```agda
record OrderedField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  constructor orderedfield
  field
    Carrier : Type ℓ
    0f 1f   : Carrier
    _+_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    min max : Carrier → Carrier → Carrier
    _<_     : Rel Carrier Carrier ℓ'

  _#_ = _#'_ {_<_ = _<_}
  _≤_ = _≤'_ {_<_ = _<_}

  field
    _⁻¹ᶠ    : (x : Carrier) → {{x # 0f}} → Carrier
    isOrderedField : IsOrderedField 0f 1f _+_ -_ _·_ min max _<_ _#_ _≤_ _⁻¹ᶠ
```

### detailed issue description

I got the error in a context

```
Goal: (z ⁻¹ᶠ) ≡ ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x))
Have: (z ⁻¹ᶠ) ≡ ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x))
```

here, we have

```agda
_⁻¹ᶠ     : (x₁ : F) {{ _ : x₁ #' 0f }} → F
-- where
_#'_ {_<_ = _<_} x y = (x < y) ⊎ (y < x)
```

so we need two special instances in scope to make use of `_⁻¹ᶠ`

```
z # 0f
(y · z) - (x · z) # 0f
```

or rather

```
(z < 0f) ⊎ (0f < z)
((y · z) - (x · z) < 0f) ⊎ (0f < ((y · z) - (x · z))
```

But these are not the two troublesome instances. The `(y · z) - (x · z) # 0f` does not cause the issue that we are surveying, but it might be involved in a subtle way.

There are the following instances in scope (just a dump)

```agda
_        : z #' 0f   (instance)
_        = (z #' 0f) ∋ inr 0<z
_        : ((y - x) ·₁ z) #' 0f   (instance)
_        = (((y - x) ·₁ z) #' 0f) ∋
           transport
           (λ i →
              ((y ·₁ z) - (x ·₁ z) ≡⟨
               (λ i₁ → (y ·₁ z) +₁ -commutesWithLeft-· x z (~ i₁)) ⟩
               ((y ·₁ z) +₁ ((-₁ x) ·₁ z)) ≡⟨
               (λ i₁ → snd (dist y (-₁ x) z) (~ i₁)) ⟩ ((y - x) ·₁ z) ∎)
              i
              #' 0f)
           it
_        : ((y ·₁ z) - (x ·₁ z)) #' 0f   (instance)
_        = (((y ·₁ z) - (x ·₁ z)) #' 0f) ∋ inr it
_        : 0f <₁ ((y ·₁ z) - (x ·₁ z))   (instance)
_        = (((x ·₁ z) <₁ (y ·₁ z)) ⇒⟨
            +-preserves-< (x ·₁ z) (y ·₁ z) (-₁ (x ·₁ z)) ⟩
            (((x ·₁ z) - (x ·₁ z)) <₁ ((y ·₁ z) - (x ·₁ z))) ⇒⟨
            transport (λ i → +-rinv (x ·₁ z) i <₁ ((y ·₁ z) - (x ·₁ z))) ⟩
            (0f <₁ ((y ·₁ z) - (x ·₁ z))) ◼)
           x·z<y·z
```

Now, the issue is that when giving the Hole with the same displayed type as the Goal from above

```
sym (snd (·-linv-unique (w · (y - x)) z (sym 1≡[w·[y-x]]·z)))
```

it gets rejected. This is due to the instances ① and ② being created with

```agda
① = z # 0f ∋ inr 0<z
_ = (x · z            <  y · z
      ⇒⟨ +-preserves-< _ _ _ ⟩
    (x · z) - (x · z) < (y · z) - (x · z)
      ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
    0f < (y · z) - (x · z) ◼) x·z<y·z
_ = (y · z) - (x · z) # 0f ∋ inr it
...
w     = ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x))
w·z≡1 = (λ i → transport
          (λ i → 1f ≡ ·-comm z ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x)) i)
          γ (~ i))
② = z # 0f ∋ snd (·-inv-back _ _ w·z≡1)
```

and `·-linv-unique` creates its instance ② differently than ① was crated

```agda
·-linv-unique : (w z : F) → ((w · z) ≡ 1f) → Σ[ p ∈ z # 0f ] w ≡ (_⁻¹ᶠ z {{p}})
·-linv-unique = let
  z#0 = snd (·-inv-back _ _ w·z≡1) -- duplicated inhabitant (see notes)
  instance _ = z # 0f ∋ z#0
  ...
  in ...
```

Here, `fst (·-linv-unique ...)` is the instance of `z # 0f` which is used for the resulting `w ≡ z ⁻¹ᶠ`.

So we have two instances ① and ② of `z # 0f` around and the "Goal" type's `_⁻¹ᶠ` assumes ① where the the "Have" type's `_⁻¹ᶠ` assumes ②. The instance ② makes a roundabout with `·-inv-back` applied to a fact `1≡[w·[y-x]]·z` that in turn used `·-linv` to get derived.

```agda
·-linv     : ∀ x → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
·-inv-back : ∀(x y : F) → (x · y ≡ 1f) → (x # 0f) × (y # 0f)
```

So we are turning ① with `·-linv` into a "fresh" instance of `z ⁻¹ᶠ · z ≡ 1f` and use `·-inv-back` to turn this into the "fresh" instance ② which "differs" from ①.

The previously mentioned hole then gets rejected with the error message

```agda
fst
(·-linv-unique' ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x)) z
 (λ i →
    transport
    (λ i → 1f ≡ ·-comm z ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x)) i)
    γ (~ i)))
!= inr 0<z of type (z < 0f) ⊎ (0f < z)
when checking that the expression
sym (snd (·-linv-unique (w · (y - x)) z (sym 1≡[w·[y-x]]·z))) has
type (z ⁻¹ᶠ) ≡ ((((y · z) - (x · z)) ⁻¹ᶠ) · (y - x))
```

which is basically saying

```agda
② != ① of type z # 0f
when checking that the expression
"in the Hole" has type "of the Goal"
```

To sum up:
Although Hole-Type and Goal-Type display the same, their hidden arguments differ.
Of these hidden arguments, the two instances ① and ② differ because ② is created with a roundabout from ① and we have no equality on the apartness type `_#_` (or rather the order type `_<_`).

The question is now, whether it is possible to make agda silently use such a coercion when it is available. I could imagine that using `hProp` still makes Agda reject such a situation because we need to explicitly tell that the `hProp`-coercion has to be used for converting the "Have" type into the "Goal" type. This is because two definitionally distinct `hProps` are still definitionally distinct.

There is the [Prop](https://agda.readthedocs.io/en/v2.6.0/language/prop.html) sort in agda for which _"all elements of a type in Prop are considered to be (definitionally) equal"_.

[a related github issue?](https://github.com/agda/agda/issues/3649)
> Any Prop is trivially a hProp so one direction is easy. For the other direction it is not possible in general to convert a hProp into a Prop; for example the singleton type Σ A λ x → x₀ ≡ x is a hProp but it cannot be made into a Prop because you can extract the first component from it (more about this and other examples in our [paper](https://hal.inria.fr/hal-01859964)).
>
> During the Agda meeting in Tokyo, @UlfNorell started to work on a new kind of implicit argument which is solved by a custom macro. Your application seems to be a perfect use-case for this new feature, since it gives you much more freedom to guide the proof search than with instance search. Performance of reflection-based proof search is also something we are planning to look into in the future.

[more issues tagges with "prop"](https://github.com/agda/agda/issues?q=Prop+label%3Aprop)

like so?

```agda
data Prop2Type (P : Prop ℓ) : Type (ℓ-suc ℓ) where
  inₚ : (p : P) → Prop2Type P

Prop-to-hProp : Prop ℓ → hProp (ℓ-suc ℓ)
Prop-to-hProp P = Prop2Type P ,  λ{ (inₚ x) (inₚ y) → refl }
```

## about implicit arguments

making `_<_` an implicit argument in

```agda
_#'_ : ∀{X : Type ℓ} {_<_ : Rel X X ℓ'} → Rel X X ℓ'
_#'_ {_<_ = _<_} x y = (x < y) ⊎ (y < x)
```

and lateron "using" this in a module telescope with

```
  (let _#_ = _#'_ {_<_ = _<_}; infixl 4 _#_)
```

which enables to write `_#_` and displays `_#'_` but still takes only two arguments (so at least it displays correctly).

## some properties that are not necessary anymore

- there is also PropRel in Cubical.Relation.Binary.Base which uses
- **one needs these "all-lowercase constructors" to make use of copatterns**
- see also Relation.Binary.Indexed.Homogeneous.Definitions.html
- see also Algebra.Definitions.html

```agda
IsConnexive : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsConnexive {A = A} R = ∀ a b → (R a b) ⊎ (R b a)

record IsTotalOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor istotalorder
  field
    isAntisym   : IsAntisym R
    isTrans     : BinaryRelation.isTrans R
    isConnexive : IsConnexive R

IsAsym : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsAsym {A = A} R = ∀ a b → R a b → ¬ R b a

IsTrichotomous : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsTrichotomous {A = A} R = ∀ a b → ((R a b) ⊎ (R b a)) ⊎ (a ≡ b)

record IsStrictTotalOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor isstricttotalorder
  field
    isTrans        : BinaryRelation.isTrans R
    isTrichotomous : IsTrichotomous R
    isIrrefl       : IsIrrefl R
    isAsym         : IsAsym R
```

## infix for module parameters

well, there is some syntax for this: https://lists.chalmers.se/pipermail/agda/2018/010217.html

also see https://github.com/agda/agda/issues/1235

BUT: it adds a ₁ to every symbol in the goal preview, even when normalizing

```agda
module Lemma-4-1-11
  --------------------------------------- structures
  (F       : Type ℓ)
  (0f 1f   : F)
  (_+_     : F → F → F)
  (-_      : F → F)
  (_·_     : F → F → F)
  (min max : F → F → F)
  (_<_     : Rel F F ℓ')
  --------------------------------------- definitions (fixites)
  -- https://lists.chalmers.se/pipermail/agda/2018/010217.html
  --   Those lets are not parameters of the module
  (let _·_  = _·_ ; infixl 7 _·_ )
  (let -_   = -_  ; infix  6 -_ )
  (let _+_  = _+_ ; infixl 5 _+_ )
  (let _<_  = _<_ ; infixl 4 _<_ )
  --------------------------------------- properties
  -- 1.
  (isCommRing : IsCommRing 0f 1f _+_ _·_ -_)
  -- 2.
  (<-isStrictTotalOrder : IsStrictPartialOrder _<_)
  --------------------------------------- definitions
  (let _#_ = _#'_ {_<_ = _<_}; infixl 4 _#_)
  (let _≤_ = _≤'_ {_<_ = _<_}; infixl 4 _≤_)
  --------------------------------------- structures
  (_⁻¹ᶠ    : (x : F) → {{x # 0f}} → F)
  (let _⁻¹ᶠ = _⁻¹ᶠ; infix  9 _⁻¹ᶠ)
  --------------------------------------- properties
  -- 3.
  (·-rinv     : ∀ x → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f)
  (·-linv     : ∀ x → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f)
  (·-inv-back : ∀(x y : F) → (x · y ≡ 1f) → (x # 0f) × (y # 0f) )
  -- 4.
  (≤-isPartialOrder : IsPartialOrder _≤_)
  -- 5.
  (<-isLattice : IsLattice _≤_ min max)
  --------------------------------------- definitions (fixites)
  -- https://lists.chalmers.se/pipermail/agda/2018/010217.html
  --   Those lets are not parameters of the module
  -- this one is tricky: its usually from `Group` and we get it by opening `IsCommRing`
  -- (let _-_  = λ(x y : F) → x + (- y) ; infixl 6 _-_)
  where
  --------------------------------------- populating the scope
  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsStrictPartialOrder <-isStrictTotalOrder public
    renaming
      ( isIrrefl  to <-irrefl
      ; isTrans   to <-trans
      ; isCotrans to <-cotrans )
  open IsPartialOrder ≤-isPartialOrder public
    renaming
      ( isRefl    to ≤-refl
      ; isAntisym to ≤-antisym
      ; isTrans   to ≤-trans )
  open IsLattice <-isLattice public

----8<---------------------------8<--------------------------8<----

  -- ....
```

## populating the module scope with a field AND a ring

in the following, `open Cubical.Structures.Ring.Theory R` also creates additional `Ring.Carrier (makeRing ...)` in the "Goal/Have-previews", except when using C-u C-u C-... then these get normalized fine

using this `R` makes it a little better

it seems to be an issue to have overlapping `_+_`, `_·_`, `-_` in one scope

```agda
module Lemmas-4-6-1 (F : ConstructiveField {ℓ} {ℓ'}) where
  open ConstructiveField F
  open import Cubical.Structures.Ring
  R = (makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)
  open Cubical.Structures.Ring.Theory R

  ...
```

one better way to do this might be to use the `module F = ...` syntax as in

```agda
record IsRingHom
  {ℓ ℓ'}
  (F : Ring {ℓ}) (G : Ring {ℓ'})
  (f : (Ring.Carrier F) → (Ring.Carrier G)) : Type (ℓ-max ℓ ℓ')
  where
  module F = Ring F
  module G = Ring G
  field
    preserves-+ : ∀ a b → f (a F.+ b) ≡ f a G.+ f b
    preserves-· : ∀ a b → f (a F.· b) ≡ f a G.· f b
    perserves-1 : f F.1r ≡ G.1r
```

this got better when moving the Ring-Lemmas into a different scope (where just the Ring's `_+_`, `_·_`, `-_` are made visible) and just importing them back

```agda
module FieldProperties (F : Field) where
-- do not (yet) open the Field
  module RingProperties (R : Ring) where
    open Ring R -- populate the scope with the Ring's `_+_`, `_·_`, `-_` and alike

    ring-lemma1 : ∀ x y → x + y ≡ y + x -- state some properties
    ring-lemma1 = ...


  open Field F -- populate the scope with the Field's `_+_`, `_·_`, `-_` and alike
  R = makeRing ... -- use the Field's `_+_`, `_·_`, `-_` and alike
  open RingProperties R -- only make ring-lemmas available for the Field's fields

  -- continue using the Field's `_+_`, `_·_`, `-_` and alike and the corresponding ring-lemmas
```

Finally, when directly "constructing" the record anonymously with the `record {...}` syntax in the same line where opening the module, the names will be normalized correctly, even without `C-u C-u C-x C-,`. E.g. suppose in the following that we want to use the `0-leftNullifies` fact on Rings from `Cubical.Structures.Ring.Theory`:

```agda
module Theory (R' : Ring {ℓ}) where
  open Ring R' renaming ( Carrier to R )

  0-leftNullifies : (x : R) → 0r · x ≡ 0r
  0-leftNullifies x = ...
```

but we want to use this fact on a "Ring-derived" structure `AlmostOrderedField`. There are several ways to bring `0-leftNullifies` into scope, but they add a projection to the un-normalized terms:

```agda
module Lemma-4-1-11 (AOF : AlmostOrderedField {ℓ} {ℓ'}) where
  open AlmostOrderedField AOF renaming (Carrier to F)

  module Test1 where
    open import Cubical.Structures.Ring
    RR = (Cubical.Structures.Ring.makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)
    open Cubical.Structures.Ring.Theory RR

    -- Have: (x : Ring.Carrier RR) → (RR Ring.· Ring.0r RR) x ≡ Ring.0r RR
    _ = {! 0-leftNullifies !}

  module Test2 where
    open import Cubical.Structures.Ring renaming (Ring to R)
    RR = (Cubical.Structures.Ring.makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)
    open Cubical.Structures.Ring.Theory RR

    -- Have: (x : R.Carrier RR) → (RR R.· R.0r RR) x ≡ R.0r RR
    _ = {! 0-leftNullifies !}

  module Test3 where
    module AOFM = AlmostOrderedField AOF
    import Cubical.Structures.Ring
    open Cubical.Structures.Ring.Theory (record {AOFM})

    -- Have: (x : AOFM.Carrier) → AOFM.0f AOFM.· x ≡ AOFM.0f
    _ = {! 0-leftNullifies !}

  module Test4 where
    import Cubical.Structures.Ring
    open Cubical.Structures.Ring.Theory (record {AlmostOrderedField AOF})

    -- Have: (x : F) → 0f · x ≡ 0f
    _ = {! 0-leftNullifies !}
```

So only the last way in `module Test4` works out nicely. This simple syntax with `record {AlmostOrderedField AOF}` only works out when `Ring` and `AlmostOrderedField` share exactly the same field names. When this is not the case, we need to (back-)rename these fields. But this could be done once in the `AlmostOrderedField` module wich then re-exports all the properties.

## some ring and field lemma stubs

```agda
·-inv-same-sign : ∀ x → (p : 0f < x) → (0f < _⁻¹ᶠ x {{inr p}})
·-inv-same-sign x p = {!!}

·-inv-unique : ∀ x y z → x · y ≡ 1f → x · z ≡ 1f → y ≡ z
·-inv-unique = {!!}
```

```agda
<-isStrictPartialOrder : IsStrictPartialOrder _<_
<-isStrictPartialOrder = record
  { isIrrefl  = <-irrefl
  ; isTrans   = <-trans
  ; isCotrans = λ where
    a b a<b x →
      ( a      <  b      ⇒⟨ +-preserves-< _ _ _ ⟩
        a + x  <  b + x  ⇒⟨ transport (λ i → a + x < (+-comm b x) i) ⟩
        a + x  <  x + b  ⇒⟨ +-<-extensional b a x x ⟩
       (a < x) ⊎ (x < b) ◼) a<b
  }
```

```agda
open IsPartialOrder ≤-isPartialOrder public
  renaming
    ( isRefl    to ≤-refl
    ; isAntisym to ≤-antisym
    ; isTrans   to ≤-trans )
```

## "reading" • from left to right

∙ reads from left to right, e.g. "step1 ∙ step2 ∙ step3", e.g. in

```agda
simplR : {a b : F} (c : F) {{_ : c # 0f}} → a · c ≡ b · c → a ≡ b
simplR {a} {b} c {{_}} a·c≡b·c =
   a                ≡⟨ sym (fst (·-identity a)) ∙ cong (a ·_) (sym (·-rinv c it)) ∙ ·-assoc _ _ _ ⟩
  (a · c) · (c ⁻¹ᶠ) ≡⟨ cong (_· c ⁻¹ᶠ) a·c≡b·c ⟩
  (b · c) · (c ⁻¹ᶠ) ≡⟨ sym (·-assoc _ _ _) ∙ cong (b ·_) (·-rinv c it) ∙ fst (·-identity b)  ⟩
   b ∎
```

## the use of anonymous modules to "set up" instance arguments

while this might make it "easier" to read at some point, we broke the signature into two parts

```agda
-- ·-linv-unique : (x y : F) (x·y≡1 : (x ·₁ y) ≡ 1f) → x ≡ (y ⁻¹ᶠ₁)
module _ (x y : F) (x·y≡1 : x · y ≡ 1f) where
  y#0 = snd (·-inv-back _ _ x·y≡1) -- (* )
  instance _ = y#0
  import Cubical.Structures.Group

  -- NOTE: ported from Cubical.Structures.Group.GroupLemmas
  abstract
    ·-linv-unique' : Σ[ p ∈ y # 0f ] (x ≡ _⁻¹ᶠ y {{p}})
    ·-linv-unique' = it , (
      x · y ≡ 1f        ⇒⟨ transport (λ i → x · y ≡ ·-linv y it (~ i)) ⟩
      x · y ≡ y ⁻¹ᶠ · y ⇒⟨ simplR _  ⟩
      x     ≡ y ⁻¹ᶠ     ◼) x·y≡1

  ·-linv-unique : (x y : F) → ((x · y) ≡ 1f) → Σ[ p ∈ y # 0f ] x ≡ (_⁻¹ᶠ y {{p}})
  ·-linv-unique = ·-linv-unique'
```

(* ) IMPORTANT!

- this (* ) line "creates" a "new" `y#0`
- now, this is apriori not equal to previous `y#0`s because `·-inv-back` does not give us a prop
- therefore I am observing a situation where I have exactly the goal
  - Goal: (z ⁻¹ᶠ₁) ≡ ((((y ·₁ z) - (x ·₁ z)) ⁻¹ᶠ₁) ·₁ (y - x))
  - Have: (z ⁻¹ᶠ₁) ≡ ((((y ·₁ z) - (x ·₁ z)) ⁻¹ᶠ₁) ·₁ (y - x))
- but Agda refuses to take what I have with the following message
  - ERROR
    - [almost what I was giving agda, but expanded] != inr 0<z of type (z <₁ 0f) ⊎ (0f <₁ z)
  - when checking that the expression
    - [what I was giving agda] has type [the goal type]
- so this might be mitigated by using Prop instead
- although some more thinking should go into this kind of instance usage

a variant for not having to state the `let instance` twice (but this needs an indentation)

```agda
module _ (z : F) (z#0 : z # 0f) where
  private
    instance _ = z#0
    z⁻¹ = z ⁻¹ᶠ -- NOTE: interestingly, the instance argument is not applied and y remains normalized in terms of z
              --       so we get `y : {{ _ : z #' 0f }} → F` here
    z⁻¹#0 = snd (·-inv-back z z⁻¹ (·-rinv z it))
    -- NOTE: for some reason I get "There are instances whose type is still unsolved when checking that the expression it has type z #' 0f"
    --       typing `y : F` did not help much. therefore this goes in two lines
    instance _ = z⁻¹#0
    z⁻¹⁻¹ = z⁻¹ ⁻¹ᶠ

  -- NOTE: this should be similar to `right-helper` + `-involutive`
  ⁻¹ᶠ-involutive : (z ⁻¹ᶠ) ⁻¹ᶠ ≡ z
  ⁻¹ᶠ-involutive = (
     z⁻¹⁻¹              ≡⟨ sym (fst (·-identity _)) ⟩
     z⁻¹⁻¹ ·      1f    ≡⟨ (λ i →  z⁻¹⁻¹ · ·-linv _ it (~ i)) ⟩
     z⁻¹⁻¹ · (z⁻¹  · z) ≡⟨ ·-assoc _ _ _ ⟩
    (z⁻¹⁻¹ ·  z⁻¹) · z  ≡⟨ (λ i → ·-linv z⁻¹ it i · z) ⟩
          1f       · z  ≡⟨  snd (·-identity _)  ⟩
                     z  ∎)
```

## failed proof attempts for "item 9"

```agda
module _ (x y z : F) (0<z : 0f < z) (x·z<y·z : x · z < y · z) where
  -- For the other direction of item 9, assume 0 < z and xz < yz,
  instance _ = (          x · z  <  y · z            ⇒⟨ +-preserves-< _ _ _ ⟩
               (x · z) - (x · z) < (y · z) - (x · z) ⇒⟨ transport (cong₂ _<_ (+-rinv (x · z)) refl) ⟩
                              0f < (y · z) - (x · z) ◼) x·z<y·z
  instance _ = (y · z) - (x · z) # 0f ∋ inr it
  -- so that yz − xz has a multiplicative inverse w,
  w = ((y · z) - (x · z)) ⁻¹ᶠ
  o = ( (y · z) - (   x  · z) ≡⟨ ( λ i → (y · z) + (-commutesWithLeft-· x z) (~ i)) ⟩
        (y · z) + ((- x) · z) ≡⟨ sym (snd (dist y (- x) z)) ⟩
        (y - x) · z ∎)
  instance _ = (y - x) · z # 0f ∋  transport (λ i → o i # 0f) it
  -- and so z itself has multiplicative inverse w (y − x).
  1≡z·[w·[y-x]] : 1f ≡ z · (w · (y - x))
  1≡z·[w·[y-x]] = γ where
    abstract
      γ = (
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
  instance _ = z # 0f ∋ inr 0<z
  z⁻¹ = w · (y - x)
  --  ·-linv-unique _ _ (sym iii)
  z⁻¹≡w·[y-x] : z ⁻¹ᶠ ≡ (w · (y - x))
  z⁻¹≡w·[y-x] = {! sym (·-linv-unique _ _ (sym 1≡[w·[y-x]]·z)) !}
  --   (⁻¹ᶠ-preserves-sign z 0<z)
  -- transport (λ i → z⁻¹≡w·[y-x] i)
  iv : 0f < (z ⁻¹ᶠ) → 0f < ((((y · z) + (- (x · z))) ⁻¹ᶠ) · (y + (- x)))
  iv = {! transport (λ i → 0f < z⁻¹≡w·[y-x] i) !}
  -- (⁻¹ᶠ-preserves-sign z 0<z)
  instance _ = 0f < w · (y - x) ∋ {!    !}
  item-9-back : x < y
  item-9-back =
     (  x ·  z         <  y ·  z         ⇒⟨ ·-preserves-< _ _ z⁻¹ it ⟩
       (x ·  z) · z⁻¹  < (y ·  z) · z⁻¹  ⇒⟨ transport (λ i → ·-assoc x z z⁻¹ (~ i) < ·-assoc y z z⁻¹ (~ i)) ⟩
        x · (z  · z⁻¹) <  y · (z  · z⁻¹) ⇒⟨ transport (λ i → x · 1≡z·[w·[y-x]] (~ i) < y · 1≡z·[w·[y-x]] (~ i)) ⟩
        x · 1f         <  y · 1f         ⇒⟨ transport (cong₂ _<_ (fst (·-identity x)) (fst (·-identity y))) ⟩
        x              <  y              ◼) x·z<y·z
```

```agda
let
  instance _ = z # 0f ∋ inr 0<z -- make the instance available
  z⁻¹ = z ⁻¹ᶠ
  #-sym : ∀{a b} → a # b → b # a
  #-sym {a} {b} = swap
  0#z⁻¹ =  #-sym (snd (·-inv-back z z⁻¹ (·-rinv z (inr 0<z))))
  0<z⁻¹ : 0f < z ⁻¹ᶠ
  0<z⁻¹ = {! ·-preserves-< 0f 1f  !}
  -- 0 < 1
  -- 0 < z · z⁻¹
in (
(x · z) < (y · z) ⇒⟨ {! ·-preserves-< (x · z) (y · z) z⁻¹!} ⟩
(x · z) · z⁻¹ < (y · z) · z⁻¹ ⇒⟨ {!!} ⟩
x · (z · z⁻¹) < y · (z · z⁻¹) ⇒⟨ {!!} ⟩
x · 1f < y · 1f ⇒⟨ {!!} ⟩
x < y ◼)
```

## building records in Agda (lemma-4-1-12: "ordered fields are constructive fields")

the following works, because OrderedField shares all of the same-named properties of Ring but if this would not be the case, then we could just rename this with the `renaming` syntax either here, directly or just above

```agda
record IsOrderedFieldHom
  {ℓ ℓ' ℓₚ ℓₚ'} -- NOTE: this is a lot of levels. Can we get rid of some of these?
  (F : OrderedField {ℓ} {ℓₚ}) (G : OrderedField {ℓ'} {ℓₚ'})
  -- (let module F = OrderedField F) -- NOTE: `let` is not allowed in a telescope
  -- (let module G = OrderedField G)
  (f : (OrderedField.Carrier F) → (OrderedField.Carrier G)) : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓₚ ℓₚ'))
  where
  module F = OrderedField F
  module G = OrderedField G
  field
    isRingHom : IsRingHom (record {F}) (record {G}) f
    reflects-< : ∀ x y → f x G.< f y → x F.< y
```

```agda
lemma-4-1-12 :
  -- NOTE: we do a slightly different thing here
  ∀{ℓ ℓ'} (OF : OrderedField {ℓ} {ℓ'}) →
  let open OrderedField OF
  ----------------------------------------------------
  in (IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ)
lemma-4-1-12 {ℓ} {ℓ'} OF = let -- NOTE: for mentioning the ℓ and ℓ' and not taking them as new "variables"
  open OrderedField OF
  in record
   { -- NOTE: see https://agda.readthedocs.io/en/v2.6.1/language/record-types.html#building-records-from-modules
     --       the following line just picks all same-named thigs from the `OrderedField OF` module
     OrderedField OF
     -- NOTE: alternatively we can specify it explicitly (renaming should work with this syntax):
     --         OrderedField OF using (isCommRing; ·-rinv; ·-linv; ·-inv-back)
     -- NOTE: and of course the "normal" syntax would be
     --           isCommRing      = isCommRing
     --         ; ·-rinv          = ·-rinv
     --         ; ·-linv          = ·-linv
     --         ; ·-inv-back      = ·-inv-back
     --
     -- NOTE: We've proved this before
   ; isApartnessRel  = #'-isApartnessRel <-isStrictPartialOrder
     -- We need to show that + is #-extensional, and that # is tight.
     --
     -- First, assume w + x # y + z. We need to show w # y ∨ x # z.
   ; +-#-extensional = λ where
                       -- Consider the case w + x < y + z, so that we can use (†) to obtain w < y ∨ x < z,
                       --   which gives w # y ∨ x # z in either case.
                       w x y z (inl w+x<y+z) → case +-<-extensional _ _ _ _ w+x<y+z of (
                         (_ → (w # y) ⊎ (x # z)) ∋ λ -- NOTE: here we had to add a (return-)type annotation to the λ
                         { (inl w<y) → inl (inl w<y)
                         ; (inr x<z) → inr (inl x<z)
                         })
                       -- The case w + x > y + z is similar.
                       w x y z (inr y+z<w+x) → case  +-<-extensional _ _ _ _ y+z<w+x of (
                         (_ → (w # y) ⊎ (x # z)) ∋ λ
                         { (inl y<w) → inl (inr y<w)
                         ; (inr z<x) → inr (inr z<x)
                         })
     -- Tightness follows from the fact that ≤ is antisymmetric, combined with the fact
     --   that ¬(P ∨ Q) is equivalent to ¬P ∧ ¬Q.
   ; #-tight         = λ x y ¬[x<y]⊎¬[y<x] → let (¬[x<y] , ¬[y<x]) = deMorgan₂' ¬[x<y]⊎¬[y<x]
                                             in  ≤-antisym _ _ ¬[y<x] ¬[x<y]
   }
```

## weird error messages

- I got a "Cannot resolve overloaded projection ≤-antisym because it is not applied to a visible argument" for just `≤-antisym` in a goal
  because there were multiple `≤-antisym` exported from `OrderedField`
- `let` is not allowed in a telescope
  this was also mentioned in previous github issue about module parameter fixities
- "Not implemented: The Agda synthesizer (Agsy) does not support copatterns yet"
- for some reason I get "There are instances whose type is still unsolved when checking that the expression it has type z #' 0f"
  typing `y : F` did not help much. therefore this goes in two lines
  ```agda
  instance _ = z⁻¹#0
  z⁻¹⁻¹ = z⁻¹ ⁻¹ᶠ
  ```
- for some reason the instance resolution does only work in let-blocks
  I get a "Terms marked as eligible for instance search should end with a name, so 'instance' is ignored here. when checking the definition of my-instance"


## "preserve" and "reflect"

e.g. from http://www.mat.uc.pt/~mmc/courses/CategoryTheory.pdf
>  A functor `F : A → B` preserves property (P) of  morphisms  (of  objects) if `F f` has that property whenever `f` has it
>
>  `[ P f ⇒ P (F f) ]`
>
>  A functor `F : A → C` reflects one property if `f` fulfils that property whenever `F f` does
>
>  `[ P (F f) ⇒ P f ]`

```agda
_Preserves_⟶_ : ∀{Aℓ Bℓ ℓ ℓ'} {A : Type Aℓ} {B : Type Bℓ} → (A → B) → Rel A A ℓ → Rel B B ℓ' → Set _
f Preserves P ⟶ Q = ∀{x y} → P x y → Q (f x) (f y)

_Reflects_⟶_ : ∀{Aℓ Bℓ ℓ ℓ'} {A : Type Aℓ} {B : Type Bℓ} → (A → B) → Rel A A ℓ → Rel B B ℓ' → Set _
f Reflects P ⟶ Q = ∀{x y} → Q (f x) (f y) → P x y
```

there is from `Relation.Binary.Core`

```agda
  _Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
  f Preserves P ⟶ Q = P =[ f ]⇒ Q
```

which is a synonym for `_=[_]⇒_`

```agda
  _=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
  P =[ f ]⇒ Q = P ⇒ (Q on f)
```

with `⇒`

```agda
  P ⇒ Q = ∀ {x y} → P x y → Q x y
```

and `_on_` from `Function.Base`

```agda
  _on_ : (B → B → C) → (A → B) → (A → A → C)
  _*_ on f = λ x y → f x * f y
```

## ideas for the "number" module

### naming scheme

```
ℕ ⁿ
ℤ ᶻ
ℚ ᶠ
ℝ ʳ
ℂ ᶜ

𝕂 ᵏ

𝕏₀⁺ᵏ
```

### notes

coercion should preserve
- identity: a ≡ b ⇔ coerce a ≡ coerce b
- `_#_`, `_<_` and `_≤_`
- min max and basically all other "operations"

- so it is a Field-morphism
- ..unless we are making use of ℂ which does not have the lattice properties
- so, when we have a function like the inner product ⟨_,_⟩ : V → V → ℂ
- which has the property that ⟨ x , x ⟩ ∈ ℝ, how do we formalize that?
- well, we have for `z = ⟨ x , x ⟩` that `z ≡ conj z` and therefore `imag z ≡ 0`
- so we might add `real` and `imag` to our ℂ and allow a coercion only when `imag z ≡ 0`

generally we do not have back-inclusion

the chain goes like ℕ ↪ ℤ ↪ ℚ ↪ ℝ ↪ ℂ

ℕ, ℤ, ℚ and ℝ share `_+_`, `_·_`, the lattice-like parts `_<_`, `_≤_`, `_#_`, `min`, `max` and also `abs`


```
.....| ℕ ℤ ℚ ℝ ℂ | ℝ₀⁺ ℝ⁺ Finₖ
-----|-----------|-------------
0ᶠ   | ✓ ✓ ✓ ✓ ✓ | ✓   ✗   ✓
1ᶠ   | ✓ ✓ ✓ ✓ ✓ | ✓   ✓   *
_+_  | ✓ ✓ ✓ ✓ ✓ | ✓   ✓   p
_-_  | p ✓ ✓ ✓ ✓ | p   p   p
_·_  | ✓ ✓ ✓ ✓ ✓ | ✓   ✓   p
_⁻¹  | ✗ ✗ * * * | *   ✓   ✗
_<_  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
_≤_  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
_#_  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
min  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
max  | ✓ ✓ ✓ ✓ ✗ | ✓   ✓   ✓
-----|-----------|-------------
abs  | • ✓ ✓ ✓ ✓ | •   •   •
sqrt | p p p * * | ✓   ✓   p
conj | • • • • ✓ | •   •   •

• = trivial
✓ = total
* = almost completely / special
p = partial
✗ = not available
```

- what about congruence classes (ℤ mod M)?
- we might exclude ℂ from this coercion system, because they are too different since they are not an ordered field
  - but we might have a separate just-field-coercion system that allows for 𝕂
- the "usual" number domains are
  - ℝ
  - ℝ₀⁺ -- nonnegative
  - ℝ⁺  -- nonnegative, nonzero
  - ℚ
  - ℚ₀⁺ -- nonnegative
  - ℚ⁺  -- nonnegative, nonzero
  - ℕ
  - ℕ⁺  -- nonzero
  - ℤ
  - ℤ₀⁺ -- nonnegative
  - ℤ⁺  -- nonnegative, nonzero
  - ℂ
  - ℂ⁺  -- nonzero
  - 𝕂  -- ℂ or ℝ
  - 𝕂⁺ -- nonzero

- how to set up these injections?
  - https://en.wikipedia.org/wiki/Inverse_function#Left_and_right_inverses
    - A function f with a left inverse is necessarily injective.
    - In classical mathematics, every injective function f with a nonempty domain necessarily has a left inverse;
      - however, this may fail in constructive mathematics.
    - For instance, a left inverse of the inclusion {0,1} → R of the two-element set in the reals violates indecomposability
      - by giving a retraction of the real line to the set {0,1}.
  - https://en.wikipedia.org/wiki/Indecomposability

- partial morphisms
  - e.g. for `x > 0` as a prerequisite for an inclusion to ℝ⁺
    ```
    (φ ↪ ℝ) ≅ ℝ⁺
    Σ ℝ φ ≅ ℝ⁺
    ```
- Maybe we add a "new" Σ type with an implicit instance argument
  - a function might suffice
- we need the differing properties
- but it is also somehow the definition of ℝ⁺
- so can we "just" replace the carrier of ℝ⁺ to `Σ ℝ φ` ?
  - or we define a subspace with an explicit inclusion anihilating these things
- if we want to add 0ᶠ from ℝ to some x from ℝ⁺ (which does not contain 0ᶠ) then we might not want to have explicit inclusions
  - `(x , 0 < x)`
- More generally, it seems that we are tracking properties such as
  - isNat isInt isRat isReal isNonnegative isNonzero
- attached to the corresponding numbers
- An inclusion into ℝ might not be necessary
- we could do this with a small domain specific language / small coercion grammar

### coercions

```agda
record Coercion' (Y : Type ℓ') (P : Y → Type ℓ'') {X : Type ℓ} (x : X) : Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
  field
    coerce' : Σ Y P

instance
  coerce-id' : {X : Type ℓ} {x : X} → Coercion' X (λ _ → Unit) {X = X} x
  coerce-id' {x = x} = record { coerce' = x , tt }

coerce : {X : Type ℓ} {Y : Type ℓ'} → (x : X) → {{c : Coercion' Y (λ _ → Y) x}}  → Y
coerce = λ x ⦃ c ⦄ → fst (Coercion'.coerce' c)
```

- now the issue is, that while we can define operations that work on a general Number type with hidden instance arguments
  - the output of such an operation still needs to be of "some" type
- we cannot output the resulting number and an instance with its properties,
  - at least not in a way where the instance is immediately taken up for instance serach
  - e.g. in equational reasoning with `_≡⟨_⟩` which is a single term and cannot introduce additional instances mid-term
- therefore these operations output

### number hierarchy

Frobenius theorem: The only finite-dimensional associative division algebras over the reals are
- the reals themselves,
- the complex numbers,
- and the quaternions.

"Nonzero ring" means "not the trivial ring, the ring with one element".

- we have different "levels"
  - Lattice
    - `Finₖ ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺`
  - OrderedCommSemiring (ring without additive inverse)
    - `ℕ ℤ ℚ ℚ₀⁺ ℚ⁺ ℝ ℝ₀⁺ ℝ⁺`
  - OrderedCommRing
    - `ℤ ℚ ℝ`
  - OrderedField (ring with multiplicative inverse for nonzero elements)
    - `ℚ ℝ`
- but we also have
  - OrderedSemifield (no additive inverse, but multiplicative inverse for nonzero elements)
    - `ℚ₀⁺ ℝ₀⁺`
  - OrderedSemifieldWithoutZero (no additive inverse, no 0, all multiplicative inverses)
    - `ℚ⁺ ℝ⁺`
- for all x from a subspace of ℝ, it's "defining property" is that
  - `Σ[ z ∈ 𝕏 ] 𝕏↪ℝ z ≡ x`
- when we have a subspace like 𝕏₀⁺ then additionally we get
  - `0f ≤ x`
- and for 𝕏⁺ we get
  - `0f < x`
- for all these "levels" we have incusions 𝕏↪ℝ into ℝ
  - an included element "carries" the missing properties

### other approaches

- reals in Coq
  - https://arxiv.org/abs/0809.1644
  - Kaliszyk, O'Connor 2009 - Computing with Classical Real Numbers
  - Finally, the CReals structure is defined on top of the COrderedField structure. The full list of structures is given below.
    ```
    CSetoid    - constructive setoid
    CSemiGroup - semi group
    CMonoid    - monoid
    CGroup     - group
    CAbGroup   - Abelian group
    CRing      - ring
    CField     - field
    COrdField  - ordered field
    CReals     - real number structure
    ```
- https://perso.crans.org/cohen/CoqWS2018.pdf
  - Cohen 2018 - Classical analysis with Coq
  - .. has an overview of current implementations in different proof assistants


## enumerations

on

```agda
data NumberKind : Type where
  isNat     : NumberKind
  isInt     : NumberKind
  isRat     : NumberKind
  isReal    : NumberKind
  isComplex : NumberKind
```

the final approach to lift `_≤_`, `min` and `max` from ℕ ended up in `Enumeration.agda`. We get:

```agda
_≤'_ : Rel A A ℓ-zero
min' : A → A → A
max' : A → A → A

max'-sym         : ∀ a b → max' a b ≡ max' b a
max'-implies-≤'₁ : ∀ a b →  a ≤' max' a b
max-implies-≤'   : ∀ a b → (a ≤' max' a b) × (b ≤' max' a b)
```

### the previous approach to define an enumeration via `Fin k`

... turned out to be not necessary.

```agda
NLE : NumberKind → Fin 5
NLE isNat     = 0 , it
NLE isInt     = 1 , it
NLE isRat     = 2 , it
NLE isReal    = 3 , it
NLE isComplex = 4 , it

_^ᶠ_ : ∀{A : Type ℓ} → (A → A) → ℕ₀ → A → A
_^ᶠ_ f zero x = x
_^ᶠ_ f (suc zero) x = (f x)
_^ᶠ_ f (suc n) x = (f ^ᶠ n) (f x)

private
  pattern suc⁵ x = suc (suc (suc (suc (suc x))))

NLE⁻¹ : Fin 5 → NumberKind
NLE⁻¹ (0 , p) = isNat
NLE⁻¹ (1 , p) = isInt
NLE⁻¹ (2 , p) = isRat
NLE⁻¹ (3 , p) = isReal
NLE⁻¹ (4 , p) = isComplex
NLE⁻¹ (suc⁵ fst₁ , p) = ⊥-elim {A =  λ _ → NumberKind} $ ¬[k+x<k] 5 fst₁ p

NLE-id¹ : ∀ x → fst (NLE (NLE⁻¹ x)) ≡ fst x
NLE-id¹ (0 , p) = refl
NLE-id¹ (1 , p) = refl
NLE-id¹ (2 , p) = refl
NLE-id¹ (3 , p) = refl
NLE-id¹ (4 , p) = refl
NLE-id¹ (suc⁵ fst₁ , p) = ⊥-elim {A =  λ _ → fst (NLE (NLE⁻¹ (suc⁵ fst₁ , p))) ≡ suc⁵ fst₁} $ ¬[k+x<k] 5 fst₁ p

NLE-id² : ∀ x → NLE⁻¹ (NLE x) ≡ x
NLE-id² isNat     = refl
NLE-id² isInt     = refl
NLE-id² isRat     = refl
NLE-id² isReal    = refl
NLE-id² isComplex = refl

_≤ₙₗ_ : NumberKind → NumberKind → Type
a ≤ₙₗ b = fst (NLE a) ≤ₙ fst (NLE b)
```

## redefining pattern-preference for case-split

suppose that we have a simple type

```agda
data PositivityLevelOrderedRing : Type where
  anyPositivityᵒʳ : PositivityLevelOrderedRing
  isNonzeroᵒʳ     : PositivityLevelOrderedRing
  isNonnegativeᵒʳ : PositivityLevelOrderedRing
  isPositiveᵒʳ    : PositivityLevelOrderedRing
  isNegativeᵒʳ    : PositivityLevelOrderedRing
  isNonpositiveᵒʳ : PositivityLevelOrderedRing

```

and want to make shortcuts of it available in two different flavours:

```agda
module PatternsType where
  pattern X   = anyPositivityᵒʳ
  pattern X⁺⁻ = isNonzeroᵒʳ
  pattern X₀⁺ = isNonnegativeᵒʳ
  pattern X⁺  = isPositiveᵒʳ
  pattern X⁻  = isNegativeᵒʳ
  pattern X₀⁻ = isNonpositiveᵒʳ

module PatternsProp where
  pattern ⁇x⁇ = anyPositivityᵒʳ
  pattern x#0 = isNonzeroᵒʳ
  pattern 0≤x = isNonnegativeᵒʳ
  pattern 0<x = isPositiveᵒʳ
  pattern x<0 = isNegativeᵒʳ
  pattern x≤0 = isNonpositiveᵒʳ
```

When bringing both patterns into scope, both can be used. But there is a "preference" which patterns agda will use for case-split:

```agda
tmp0 : PositivityLevelOrderedRing → {!!}
-- C-c C-c expands to the original definition
tmp0 anyPositivityᵒʳ = {!!}
tmp0 isNonzeroᵒʳ     = {!!}
tmp0 isNonnegativeᵒʳ = {!!}
tmp0 isPositiveᵒʳ    = {!!}
tmp0 isNegativeᵒʳ    = {!!}
tmp0 isNonpositiveᵒʳ = {!!}

open PatternsProp

tmp1 : PositivityLevelOrderedRing → {!!}
-- C-c C-c expands to patterns in PatternsProp
tmp1 ⁇x⁇ = {!!}
tmp1 x#0 = {!!}
tmp1 0≤x = {!!}
tmp1 0<x = {!!}
tmp1 x<0 = {!!}
tmp1 x≤0 = {!!}

open PatternsType

tmp2 : PositivityLevelOrderedRing → {!!}
-- C-c C-c expands to patterns in PatternsType
tmp2 X   = {!!}
tmp2 X⁺⁻ = {!!}
tmp2 X₀⁺ = {!!}
tmp2 X⁺  = {!!}
tmp2 X⁻  = {!!}
tmp2 X₀⁻ = {!!}

open PatternsProp

tmp3 : PositivityLevelOrderedRing → {!!}
-- C-c C-c still expands to patterns in PatternsType
tmp3 X   = {!!}
tmp3 X⁺⁻ = {!!}
tmp3 X₀⁺ = {!!}
tmp3 X⁺  = {!!}
tmp3 X⁻  = {!!}
tmp3 X₀⁻ = {!!}

pattern ⁇x⁇ = anyPositivityᵒʳ
pattern x#0 = isNonzeroᵒʳ
pattern 0≤x = isNonnegativeᵒʳ
pattern 0<x = isPositiveᵒʳ
pattern x<0 = isNegativeᵒʳ
pattern x≤0 = isNonpositiveᵒʳ
pattern ⁇x⁇ = anyPositivityᶠ
pattern x#0 = isNonzeroᶠ

tmp4 : PositivityLevelOrderedRing → {!!}
-- C-c C-c still expands to the lastly defined patterns
tmp4 ⁇x⁇ = {!!}
tmp4 x#0 = {!!}
tmp4 0≤x = {!!}
tmp4 0<x = {!!}
tmp4 x<0 = {!!}
tmp4 x≤0 = {!!}

pattern X   = anyPositivityᵒʳ
pattern X⁺⁻ = isNonzeroᵒʳ
pattern X₀⁺ = isNonnegativeᵒʳ
pattern X⁺  = isPositiveᵒʳ
pattern X⁻  = isNegativeᵒʳ
pattern X₀⁻ = isNonpositiveᵒʳ
pattern X   = anyPositivityᶠ
pattern X⁺⁻ = isNonzeroᶠ

tmp5 : PositivityLevelOrderedRing → {!!}
-- C-c C-c still expands to the lastly defined patterns
tmp5 X = {!!}
tmp5 X⁺⁻ = {!!}
tmp5 X₀⁺ = {!!}
tmp5 X⁺ = {!!}
tmp5 X⁻ = {!!}
tmp5 X₀⁻ = {!!}

pattern ⁇x⁇ = anyPositivityᵒʳ
pattern x#0 = isNonzeroᵒʳ
pattern 0≤x = isNonnegativeᵒʳ
pattern 0<x = isPositiveᵒʳ
pattern x<0 = isNegativeᵒʳ
pattern x≤0 = isNonpositiveᵒʳ
pattern ⁇x⁇ = anyPositivityᶠ
pattern x#0 = isNonzeroᶠ

tmp6 : PositivityLevelOrderedRing → {!!}
-- C-c C-c still expands to the lastly defined patterns
tmp6 ⁇x⁇ = {!!}
tmp6 x#0 = {!!}
tmp6 0≤x = {!!}
tmp6 0<x = {!!}
tmp6 x<0 = {!!}
tmp6 x≤0 = {!!}

-- and so on...
```

## convenient Goal/Have resolution

when a clause is "evaluated" / "unfolded", then the imports from its context will be used at the "call-site"

e.g.

```agda
NumberKindInterpretation : (x : NumberKind) → Type (NumberKindLevel x)
NumberKindInterpretation isNat     = ℕ*.ℕ
NumberKindInterpretation isInt     = ℤ*.ℤ
NumberKindInterpretation isRat     = ℚ*.ℚ
NumberKindInterpretation isReal    = ℝ*.ℝ
NumberKindInterpretation isComplex = ℂ*.ℂ
```

will result in displaying `ℕ*.ℕ` even when `ℕ*` is opened at the call-site and `ℕ` would be directly available.

This can be adjusted with opening the module `ℕ*` in the pattern

```
NumberKindInterpretation : (x : NumberKind) → Type (NumberKindLevel x)
NumberKindInterpretation isNat     = let open ℕ* in ℕ
NumberKindInterpretation isInt     = let open ℤ* in ℤ
NumberKindInterpretation isRat     = let open ℚ* in ℚ
NumberKindInterpretation isReal    = let open ℝ* in ℝ
NumberKindInterpretation isComplex = let open ℂ* in ℂ
```

This is also the reason, why `x - y` or `x + (- y)` will show up: it will be the way that is used in the "evaluated" / "unfolded" clause.
Which is quite the only thing it can do:

- although `_-_` is defined in terms of `-_`, it will not be unfolded (until forced with C-u C-u C-,)
- and `-_` will not consume the `_+_` to produce a `_-_` unless we set this up with a `DISPLAY` pragma.

There might be some other magic that forces `[_]` to display everytime when dealing with hprops.
Well ... when thinking about that, it might just be that `[ ∀[ x ] x ≤ x ] y` reduces to `[ y ≤ y ]` "because" that is how `∀[_]` is implemented:

```agda
∀[]-syntax {A = A} P = (∀ x → [ P x ]) , isPropΠ (isProp[] ∘ P)
```

So no "magic" is involved. It's just that `[_]` occurs at many places being the reason that it shows up again, even after applying `y`:

```
  [ ∀[ x ]   x ≤ x ]  y
⊢  (∀  x → [ x ≤ x ]) y
⊢          [ y ≤ y ]
```

### result

Now, we have explored a state where

```agda
open ℕⁿ
tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
tmp (x ,, p) = {!! x +ⁿ x !}
```

creates on `C-c C-.`

```agda
Have: ℕ
p : 0ⁿ ≤ⁿ x
x : ℕ
```

and on `C-u C-c C-.`

```agda
Have: ROrderedCommSemiring.Carrier bundle
p : Ip isNat isNonnegative x
x : Il isNat
```

and on `C-u C-u C-c C-.`

```agda
Have: Lift ℕ₀
p : Lift (Σ ℕ₀ (λ k → (k Agda.Builtin.Nat.+ 0) ≡ lower x))
x : Lift ℕ₀
```

where additionally opening ℕ brings _+_ into scope (as _+ⁿ_)

```agda
open ℕⁿ
open ℕ hiding (ℕ; ℕ₀)
tmp : Number (isNat ,, isNonnegative) → Number (isNat ,, isPositive)
tmp (x ,, p) = {! x + x !}
```

creates on `C-c C-.`

```agda
Have: ℕ
p : 0ⁿ ≤ⁿ x
x : ℕ
```

and on `C-u C-c C-.`

```agda
Have: ROrderedCommSemiring.Carrier ℕⁿ.bundle
p : Ip isNat isNonnegative x
x : Il isNat
```

and on `C-u C-u C-c C-.`

```agda
Have: Lift ℕ₀
p : Lift (Σ ℕ₀ (λ k → (k Agda.Builtin.Nat.+ 0) ≡ lower x))
x : Lift ℕ₀
```

### how-to

These are just the different tries before cleanup. The final version is in `Number.Postulates`

```agda

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
        (Order._<_)
        (Order._≤_)
        ((MoreAlgebra.Definitions._#'_ {_<_ = Order._<_}))
        (min)
        (max)
        (Nat.zero)
        (1)
        (Nat._+_)
        (Nat._*_)

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
  module Bundle = ROrderedCommSemiring {ℕℓ} {ℕℓ'}
  Bundle = ROrderedCommSemiring {ℕℓ} {ℕℓ'}

  -- NOTE: a prefix alo appears to a symbol in Have/Goal if the corresponding symbol is imported multiple times
  --       that can be checked with `C-c C-w`

  -- module members are not normalized on `C-c` `C-.` (only after `C-u`-ing) which is helpful for not cluttering the Have/Goal with "implementation details" of the underlying Carrier type
  -- but if we wanted to

  ℕ = Nat.ℕ
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
    ; _<_ = Order._<_
    ; _≤_ = Order._≤_
    ; _#_ = (MoreAlgebra.Definitions._#'_ { _<_ = Order._<_ })
    ; min = Postulates.min
    ; max = Postulates.max
    ; 0f  = Nat.zero
    ; 1f  = (Nat.suc Nat.zero)
    ; _+_ = Nat._+_
    ; _·_ = Nat._*_
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
```

```agda
module ℚ where
  module Bundle = ROrderedField {ℚℓ} {ℚℓ'} renaming (Carrier to ℚ)
  postulate
    bundle   : ROrderedField        {ℚℓ} {ℚℓ'}

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
```

as written in the `NOTE`s above, it has some effect, putting new modules at the end of `Number.Postulates` which we did not do at the end:

```agda

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

```

## multiple instance resolution and negation

see Agda email from 28.08.20, 17:32

```agda
module _ where
  abstract
    -- `ab` for "abstractify", short like `id` for "identity"
    ab : ∀{ℓ} {X : Type ℓ} → X → X
    ab R = R

    ab-≡ : ∀{ℓ} {X : Type ℓ} → ab X ≡ X
    ab-≡ = refl

    ab-≡ᵖ : ∀{ℓ} (P : hProp ℓ) → ab P ≡ P
    ab-≡ᵖ P = refl

    -- ab-≡ᵖ² : ∀{ℓ ℓ'} {X : Type ℓ} (R : hPropRel X X ℓ') → ab R ≡ R
    -- ab-≡ᵖ² R = refl

    ab-≡ᵖ² : ∀{ℓ ℓ'} {X : Type ℓ} (R : hPropRel X X ℓ') → ∀ x y → ab (R x y) ≡ R x y
    ab-≡ᵖ² R x y = refl

    [ab] : ∀{ℓ} {X : Type ℓ} → X → ab X
    [ab] {X = X} x = transport (sym (ab-≡ {X = X})) x
    {-
    infix 1 !_
    infix 1 !!_
    infix 1 !!⁻¹_

    !_ : ∀{ℓ} {X : Type ℓ} → X → X
    ! R = R

    !-≡ : ∀{ℓ} {X : Type ℓ} → (! X) ≡ X
    !-≡ = refl

    !!_ : ∀{ℓ} {X : Type ℓ} → X → ! X
    !!_ {X = X} x = transport (sym (!-≡ {X = X})) x

    !!⁻¹_ : ∀{ℓ} {X : Type ℓ} → ! X → X
    !!⁻¹_ {X = X} x = transport (!-≡ {X = X}) x
    -}

-- NOTE: this smells like "CPO" https://en.wikipedia.org/wiki/Complete_partial_order
record CompletePartiallyOrderedFieldWithSqrt {ℓ ℓ' : Level} : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier : Type ℓ
    0f      : Carrier
    1f      : Carrier
    _+_     : Carrier → Carrier → Carrier
    _·_     : Carrier → Carrier → Carrier
    -_      : Carrier → Carrier
    _<_     : hPropRel Carrier Carrier ℓ'
    <-irrefl : [ isIrreflᵖ _<_ ]
    <-trans  : [ isTransᵖ _<_ ]
    isset   : isSet Carrier

  _≤_ : hPropRel Carrier Carrier ℓ'
  x ≤ y = ¬ᵖ(y < x)

  _≤ⁱ_ : hPropRel Carrier Carrier ℓ'
  -- x ≤ᵢ y = ({{p : [ y < x ]}} → ⊥⊥) , λ f g → instanceFunExt {A = [ y < x ]} {B = λ q i → ⊥⊥} {f = f} {g = g} λ {{r}} → ⊥-elim {A = λ _ → f ≡ g} f
  -- x ≤ᵢ y = ({{p : [ y < x ]}} → ⊥⊥) , λ f g → instanceFunExt (λ {{_}} → ⊥-elim {A = λ _ → f ≡ g} f)
  x ≤ⁱ y = ¬ⁱ(y < x)

  ≤-≡-≤ⁱ : ∀ x y → x ≤ y ≡ x ≤ⁱ y
  ≤-≡-≤ⁱ x y = ¬-≡-¬ⁱ (y < x)
    -- ⇒∶ (λ f {{p}} → f   p  )
    -- ⇐∶ (λ f   p   → f {{p}})

  ≤ⁱ-inst : ∀{x y} → [ x ≤ y ] → [ x ≤ⁱ y ]
  ≤ⁱ-inst x≤y = pathTo⇒ (≤-≡-≤ⁱ _ _) x≤y

  _≤ᵃ_ : hPropRel Carrier Carrier ℓ'
  _≤ᵃ_ x y = ab (x ≤ y)

  ≤-≡-≤ᵃ : ∀ x y → x ≤ y ≡ x ≤ᵃ y
  ≤-≡-≤ᵃ x y = sym (ab-≡ᵖ (x ≤ y)) -- (ab-≡ᵖ² _≤_ x y)

  ≤ᵃ-inst : ∀{x y} → [ x ≤ y ] → [ x ≤ᵃ y ]
  ≤ᵃ-inst x≤y = pathTo⇒ (≤-≡-≤ᵃ _ _) x≤y

  field
    -- NOTE: `[ 0f ≤ x ]` normalizes to `fst (x < 0f) → ⊥⊥` and therefore it takes an explicit argument `fst (x < 0f)`
    --       when making this an instance argument, agda complains
    --         Instance arguments with explicit arguments are never considered by instance search
    -- we circumvent this by introducing `_≤ⁱ_`
    sqrt₀⁺    : (x : Carrier) → {{    [ 0f ≤ⁱ x ] }} → Carrier
    sqrt₀⁺'   : (x : Carrier) → {{    [ 0f ≤ᵃ x ] }} → Carrier
    sqrt₀⁺''  : (x : Carrier) → {{ ab [ 0f ≤  x ] }} → Carrier
    sqrt₀⁺''' : (x : Carrier) → {{  ! [ 0f ≤  x ] }} → Carrier

  -- sqrt-test : (x y : Carrier) → [ 0f ≤ x ] → [ 0f ≤ y ] → Carrier
  -- sqrt-test x y 0≤x 0≤y = let instance itx = ≤ⁱ-inst 0≤x
  --                             instance ity = ≤ⁱ-inst 0≤y
  --                         in sqrt₀⁺ x

  sqrt-test' : (x y : Carrier) → [ 0f ≤ x ] → [ 0f ≤ y ] → Carrier
  sqrt-test' x y 0≤x 0≤y = let instance _ = ≤ᵃ-inst 0≤x
                               instance _ = ≤ᵃ-inst 0≤y
                           in sqrt₀⁺' x

  sqrt-test'' : (x y : Carrier) → [ 0f ≤ x ] → [ 0f ≤ y ] → Carrier
  sqrt-test'' x y 0≤x 0≤y = let instance _ = [ab] 0≤x -- transport (sym ab-≡) 0≤x
                                instance _ = [ab] 0≤y
                            in (sqrt₀⁺'' x) + (sqrt₀⁺'' y)

  -- other syntax
  sqrt-test''' : (x y : Carrier) → [ 0f ≤ x ] → [ 0f ≤ y ] → Carrier
  sqrt-test''' x y 0≤x 0≤y = let instance _ = !! 0≤x -- transport (sym ab-≡) 0≤x
                                 instance _ = !! 0≤y
                             in (sqrt₀⁺''' x) + (sqrt₀⁺''' y)

  <-asym : [ isAsymᵖ _<_ ]
  <-asym = irrefl+trans→asym _<_ <-irrefl <-trans

  _#_ : hPropRel Carrier Carrier ℓ'
  x # y = ([ x < y ] ⊎ [ y < x ]) , isProp-P⊎Q (x < y) (y < x) (inl (<-asym x y))

  field
    _⁻¹ : (x : Carrier) → {{p : [ x # 0f ]}} → Carrier
```


## antisymmetry and antisymmetry on sets

we have

```
IsAntisym        R = ∀ a b → [ R a b   ⇒   R b a   ⇒ a ≡ₚ b ]
IsAntisymˢ isset R = ∀ a b → [ R a b ] → [ R b a ] → a ≡  b
```

both are equivalent (on sets):

```
isAntisym-ˢ≡ᵖ : (isset : isSet A) → isAntisymˢ isset R ≡ isAntisymᵖ R
```

Wikipedia writes that

```
if R(a, b) with a ≠ b, then R(b, a) must not hold,
```

is equivalent to

```
if R(a, b) and R(b, a), then a = b.
```

but is this an equivalence constructively?
I guess that `[ R a b ] → [ R b a ] → a ≡ b` implies `[ R a b ] →  [ a # b ] → [ ¬ R b a ]` in the following way:

```
[ R a b ] → [ R b a ] → a ≡ b        --
[ R a b ] × [ R b a ] → a ≡ b        -- by curry/uncurry
[ R a b   ⊓   R b a ] → a ≡ b        -- definitionally
¬(a ≡ b) → ¬ [ R a b ⊓ R b a ]       -- by contraposition (NOTE: contraposition is not an equivalence)
¬(a ≡ b) →   [ R a b ] → [ ¬ R b a ] -- by [P⇒¬Q]≡¬[P⊓Q]
[ R a b ] →  ¬(a ≡ b)  → [ ¬ R b a ] -- swap arguments
[ R a b ] →  [ a # b ] → [ ¬ R b a ] -- when `a # b ⇒ ¬(a ≡ b)` (by #-irrefl) (NOTE: also not an equivalence)
```

- Here we see that `antisymmetry + irreflexivity ⇒ asymmetry`
  - wikipedia also writes `trans + irrefl ⇒ asym`

```
isTightᵖ _<_ ≡ isAntisymᵖ  (λ a b → ¬ᵖ (b < a))
#-tight : [ ¬ (a < b) ] → [ ¬ (b < a) ] → a ≡ b
          [ ¬ (a # b) ]                 → a ≡ b
```

- `<-irrefl ⇒ #-irrefl`
  - which gives `a ≡ b → [ ¬ (a # b) ]`
- so we do have `¬#-≡-≡` when `#` is tight?
- on `¬#` we do have double negation elimintation (`¬¬¬# ≡ ¬#`)
- so `#` gives us `≡-dne` ?? hmm......

the other way could be

```
[ R a b ] → [ a # b ] → [ ¬ R b a  ]     --
[ R a b ] → [ a # b ] → [   R b a  ] → ⊥ -- by ¬
[ R a b ] → [ R b a ] → [   a # b  ] → ⊥ -- swap arguments
[ R a b ] → [ R b a ] → [ ¬(a # b) ]     -- by ¬
[ R a b ] → [ R b a ] →     a ≡ b        -- when `¬(a # b) ⇒ a ≡ b` (by #-tight)

[ R a b ] →   ¬(a ≡ b)   → [   ¬ R b a   ]     --
[ R a b ] →   ¬(a ≡ b)   → [     R b a   ] → ⊥ -- by ¬
[ R a b ] → [   R b a  ] →     ¬(a ≡ b)    → ⊥ -- swap arguments
[ R a b ] → [   R b a  ] →   ¬(¬(a ≡ b))       -- by ¬
[ R a b ] → [   R b a  ] →       a ≡ b        -- when `¬(¬(a ≡ b)) ⇒ a ≡ b`
```

let's call the weaker one isAntisym'. we have then

```
isIrrefl _<_ → isAntisym _≤_ ≡ (isAntisym' _≤_ + dne-on-≡) ≡ isTight''' _#_
isIrrefl _<_ ≡ isIrrefl _#_
isIrrefl _#_ → isTight''' _#_ → dne-on-≡
```

## splitting the reals

```agda
≤-split : ∀ x → [ 0f ≤ x ] → ( x ≡ 0f ) ⊎ [ 0f < x ]
≤-split x p = let _ = {! [ 0f ≤'' x ]  !} in {! λ(ε : Carrier) → λ(0<ε : [ 0f < ε ]) → <-cotrans 0f ε 0<ε x  !}
```

- well, I think that this is not possible
- to obtain the RHS `( x ≡ 0f ) ⊎ [ 0f < x ]` or `[ x ≡ᵖ 0f ⊔ 0f < x ]`
- we need to decide `inlᵖ` or `inrᵖ`
- on the LHS which is `[ ¬ (x < 0f) ]` or `∀ ε → [ x < ε ] → [ 0f < ε ]`
- in either case, we need to split x
- recalling that we do NOT have `∀ x → [ x # 0 ] ⊎ x ≡ 0` nor `∀ x → [ x # 0 ⊔ x ≡ᵖ 0 ]`
- we cannot split x at all
- because we cannot split a real number
- but what we might be able to do is, to provide an eliminator `≤-elim`

```agda
≤-elim : ∀{ℓ} → (P : Carrier → Carrier → Type ℓ) → ∀ x y → [ x ≤ y ] → (x ≡ y → P x y) → ([ x < y ] → P x y) → P x y
≤-elim P x y x≤y f g = {!   !}
```

- this way we do not decide anything ... or do we?
- e.g. we might want something like `[ x < 0 ⊔ x ≡ 0 ⊔ 0 < x ]`
- but this is trichotomy and we do not have it on the reals
- so an eliminator dealing with all the cases is not complete
- because we cannot proof that these are all cases
- since that would constructively amount to picking one of the cases
- I guess this is what it means that "you cannot split the reals"
- nonetheless, I think that

```agda
bridges-R3-5 : ∀ x y z → [ x ≤ y ] → [ y < z ] → [ x < z ]
bridges-R3-6 : ∀ x y z → [ x < y ] → [ y ≤ z ] → [ x < z ]
```

- already have what it takes to implement the generic number functions on subspaces of ℝ
- so we might continue anyways

the following `(ε : Carrier) (0<ε : [ 0f < ε ]) → [ 0f < x ⊔ x < ε ]`

does not imply `[ (0f < x) ⊔ (∀[ ε ] ∀[ 0<ε : [ 0f < ε ] ] x < ε) ]`

or does it?

```
-- (ε : Carrier) (0<ε : [ 0f < ε ]) → [ 0f < x ⊔ x < ε ]
-- (ε : Carrier) (0<ε : [ 0f < ε ]) → [ 0f < x ] ⊎ [ x < ε ]
```
