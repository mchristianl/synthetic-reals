
## general TODOs

- make use of .lagda.md for the parts that literally follow Booij's thesis
- check out `abstract` for performance
  - also, likely due to [#1646](https://github.com/agda/agda/issues/1646) we might flatten-out the module hierarchy for better performance
- merge the notes with Hit.agda
- use equivalences intstead of `lemma` and `lemma-back`
- can we use `preserves` and `reflects` instead of `lemma` and `lemma-back`?
  "f preserves P: P A ⇒ P (f A)"
  "f reflects  P: P (f A) ⇒ P A"
- name the "items"
- check whether this `rinv` `linv` `lemmaʳ` `lemmaˡ` is the way its done in the standard library
- is `+-<-extensional` the right name for `∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)`?
- in `Relation.Binary.Structures` we can also find `IsStrictPartialOrder`
  also see in `Data.Nat.Properties` the definition of `Structures` and `Bundles`
  - here, under `Structures` we find the `IsX` records, where under `Bundles` there is the corresponding `X` record
  - the cubical standard library uses `Cubical.Data.Nat` and `Cubical.Data.Nat.Order`
  - there is a recent email on the agda mailing list from Arjen Rouvoet (10.08.20, 18:27)
    > The problem you encounter is wellknown under the name 'the (un)bundling problem':
    > i.e., the problem of choosing which fields should be parameters, and which should be fields.
    > The problem is hard, in the sense that every permutation you can think of has applications.
    > The Agda standard library chooses to do what most other languages have done previously: i.e., provide a unbundled IsStructure, and a bundled Structure.
