
## general TODOs

- make use of .lagda.md for the parts that literally follow Booij's thesis
- check out `abstract` for performance
  - also, likely due to [#1646](https://github.com/agda/agda/issues/1646) we might flatten-out the module hierarchy for better performance
- merge the notes with Hit.agda
- use equivalences intstead of `lemma` and `lemma-back`
- can we use `preserves` and `reflects` instead of `lemma` and `lemma-back`?
  - "f preserves P: P A ⇒ P (f A)"
  - "f reflects  P: P (f A) ⇒ P A"
- name the "items"
- check whether this `rinv` `linv` `lemmaʳ` `lemmaˡ` is the way its done in the standard library
- is `+-<-extensional` the right name for `∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)`?
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
- use `hProp`s
  - ~~checkout `Cubical.Structures.Poset`~~
  - apply the "hProp-record-idiom" to all the definitions and the hierarchy
  - provide a Σ-theory similar to `CommRingΣTheory` with axioms and structure
- get the absolute value function `abs` into the number hierarchy
- get the square root function `sqrt` into the number hierarchy
- complete all necessary axioms in the number hierarchy
  - then divide into necessary axioms and derivable theorems
    - and try to proof the theorems
- case-splitting for `⊔` would be great instead of using `⊔-elim` all the time .. I came up with
  ```agda
  ⊎-implies-⊔ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ') → [ P ] ⊎ [ Q ] → [ P ⊔ Q ]
  ⊎-implies-⊔ P Q (inl x) = inlᵖ x
  ⊎-implies-⊔ P Q (inr x) = inrᵖ x

  -- NOTE: need to explcitly state the props `P` and `Q`, as well as the returned prop `R z`
  --       to make agda resolving all the metas
  case[_⊔_]_return_of_ : ∀ {ℓ ℓ'} (P : hProp ℓ) (Q : hProp ℓ')
                    → (z : [ P ⊔ Q ])
                    → (R : [ P ⊔ Q ] → hProp ℓ'')
                    → (S : (x : [ P ] ⊎ [ Q ]) → [ R (⊎-implies-⊔ P Q x) ] )
                    → [ R z ]
  case[_⊔_]_return_of_ P Q z R S = ⊔-elim P Q R (λ p → S (inl p)) (λ q → S (inr q)) z
  ```
  - or can we even have something like `⊔⊎-iso : (P : hProp ℓ) (Q : hProp ℓ') → Iso ([ P ⊔ Q ]) ([ P ] ⊎ [ Q ])` ?
