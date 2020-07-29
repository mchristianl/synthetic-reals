

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

there seems to be a convention that
> "We will adopt the convention of denoting the level of the carrier set by ℓ₀ and the level of the relation result by ℓ₁."



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
