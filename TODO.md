
## immediate TODOs

- split `·-reflects-<` into `·-reflects-<ˡ` and `·-reflects-<ʳ`
- we use `·-reflects-≡ˡ` where the standard library uses the nomer "injective" like `*-injˡ` (or something similar)
  - since `preserves-≡` is automatic, we might switch to `·-injectiveˡ` instead of `·-reflects-≡ˡ`
- we have `+-rinv`, `+-inverse` and `ʳ` `ˡ` variants in use ⇒ unify them!
- in equivalences, we still need to follow the convention that the "simpler" term is the RHS
  e.g. `·-creates-< : ∀ a b x → [ 0 < x ] → [ (a < b) ⇔ ((a · x) < (b · x)) ]` is wrong
  (this needs to be checked)

## general TODOs

- Lemma 6.7.1. contains more properties that are provable on ordered fields already
  - some of them look like we've proven them for Bridges1999 already
- is it possible to proof `comm`, `assoc` and `absorbs` from `isMin` and `isMax`?
- merge the notes with Hit.agda
- check whether this `rinv` `linv` `lemmaʳ` `lemmaˡ` is the way its done in the standard library
- is `+-<-extensional` the right name for `∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)`?
- get the absolute value function `abs` into the number hierarchy
- get the square root function `sqrt` into the number hierarchy
- complete all necessary axioms in the number hierarchy
  - then divide into necessary axioms and derivable theorems
    - and try to proof the theorems

## ongoing TODOs

- use equivalences intstead of `lemma` and `lemma-back`
- can we use `preserves` and `reflects` instead of `lemma` and `lemma-back`?
  - "f preserves P: P A ⇒ P (f A)"
  - "f reflects  P: P (f A) ⇒ P A"
- name the "items" (from Bridges 1999)
- can't we just use ℚ from the non-cubical standard library?
  - yes ... but we need to add missing properties (e.g. `_<_` and `min`, `max`)

## ongoing concerns

- likely due to [#1646](https://github.com/agda/agda/issues/1646) we might flatten-out the module hierarchy for better performance
- How to structure the algebraic number hierarchy: bundling/unbundling and "What makes a bundle-morphism"?
  - `isX : IsX` is called "the unbundle"
  - `x : X` without its `isX : IsX` is called "raw"
  - there is a recent email on the agda mailing list from Arjen Rouvoet (10.08.20, 18:27)
    > The problem you encounter is wellknown under the name 'the (un)bundling problem':
    > i.e., the problem of choosing which fields should be parameters, and which should be fields.
    > The problem is hard, in the sense that every permutation you can think of has applications.
    > The Agda standard library chooses to do what most other languages have done previously: i.e., provide a unbundled IsStructure, and a bundled Structure.
  - also see [#876](https://github.com/agda/agda-stdlib/issues/876)
  - also see the [short discussion](https://github.com/mchristianl/synthetic-reals/commit/efd0548b72be70395cbe64adb3d8c8b46c9d0e39#commitcomment-41404077)
  - there is [the isabelle tutorial](https://isabelle.in.tum.de/doc/tutorial.pdf) with "8.4.5  The Numeric Type Classes"
    - semiring and ordered_semiring
    - ring and ordered_ring ... **An ordered ring includes the absolute value function, abs.**
    - field and ordered_field
    - division_by_zero includes all types where `inverse 0 = 0` and `a / 0 = 0`.
      These include all of Isabelle’s standard numeric types. However, the basic properties of fields are derived without assuming division by zero.

## later TODOs

- make use of .lagda.md for the parts that literally follow Booij's thesis

## TODOs after later TODOs

- in `Cubical.Functions.Bundle` we have a definition of fibre bundle
- the `Categories` part of the cubical standard library is quite readable!

## stuff to check out

- subsets and embeddings
  - checkout `Cubical.Foundations.Logic`
    ```agda
    -- We show that the powerset is the subtype classifier
    -- i.e. ℙ X ≃ Σ[A ∈ Type ℓ] (A ↪ X)
    Embedding→Subset : {X : Type ℓ} → Σ[ A ∈ Type ℓ ] (A ↪ X) → ℙ X
    Embedding→Subset (_ , f , isPropFiber) x = fiber f x , isPropFiber x

    Subset→Embedding : {X : Type ℓ} → ℙ X → Σ[ A ∈ Type ℓ ] (A ↪ X)
    Subset→Embedding {X = X} A = D , f , ψ
      where ...
    ```
    where
    ```agda
    hasPropFibers : (A → B) → Type _
    hasPropFibers f = ∀ y → isProp (fiber f y)

    _↪_ : Type ℓ → Type ℓ → Type ℓ
    A ↪ B = Σ[ f ∈ (A → B) ] hasPropFibers f
    ```
  - there is also
- check out `Relation.Binary.Structures` where we can also find `IsStrictPartialOrder` (whether we can use this)
  - also see in `Data.Nat.Properties` the definition of `Structures` and `Bundles`
    - here, under `Structures` we find the `IsX` records, where under `Bundles` there is the corresponding `X` record
    - the cubical standard library uses `Cubical.Data.Nat` and `Cubical.Data.Nat.Order`
- check out `Foreign.Haskell.Coerce` for a coercion mechanism
  ```agda
  data Coercible (A : Set a) (B : Set b) : Set where
    TrustMe : Coercible A B

  postulate coerce : {{_ : Coercible A B}} → A → B
  ```
- check out `Agda.Builtin.FromNat` for a coercion mechanism
  ```agda
  record Number {a} (A : Set a) : Set (lsuc a) where
    field
      Constraint : Nat → Set a
      fromNat : ∀ n → {{_ : Constraint n}} → A

  open Number {{...}} public using (fromNat)

  {-# BUILTIN FROMNAT fromNat #-}
  {-# DISPLAY Number.fromNat _ n = fromNat n #-}
  ```
  - this is used in `Cubical.Data.Nat.Literals` and in `Cubical.HITs.Rationals.QuoQ.Base`
- check out what is meant by "Instance modules" in non-cubical 1.4-rc1
  ```agda
  Category.Monad.Partiality.Instances
  Codata.Stream.Instances
  Codata.Covec.Instances
  Data.List.Instances
  Data.List.NonEmpty.Instances
  Data.Maybe.Instances
  Data.Vec.Instances
  Function.Identity.Instances
  ```
  - check out _"New standardised numeric predicates `NonZero`, `Positive`, `Negative`, `NonPositive`, `NonNegative`, especially designed to work as instance arguments."_
  - the use of instances seems to be very recent, since they also write _"First instance modules, which provide `Functor`, `Monad`, `Applicative` instances for various datatypes. Found under `Data.X.Instances`."_
- check out ["irrelevancy annotations"](https://agda.readthedocs.io/en/v2.6.1/language/irrelevance.html#irrelevant-record-fields) and whether they serve as some form of "term abstractification" (i.e. blocking the term normalization)
  - does this work with `--cubical`? what is its intention?
- use of `hProp`s
  - ~~checkout `Cubical.Structures.Poset`~~
  - provide a Σ-theory similar to `CommRingΣTheory` with axioms and structure
