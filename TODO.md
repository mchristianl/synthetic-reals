
## general TODOs

- separate personal notes from the code into it's own NOTES.md
- make use of .lagda.md for the parts that literally follow Booij's thesis
- put Lemmas in appropriate modules
- check out `abstract` for performance
- merge the notes with Hit.agda
- use equivalences intstead of `lemma` and `lemma-back`
- can we use `preserves` and `reflects` instead of `lemma` and `lemma-back`?
  "f preserves P: P A ⇒ P (f A)"
  "f reflects  P: P (f A) ⇒ P A"
- name the "items"
- check whether this `rinv` `linv` `lemmaʳ` `lemmaˡ` is the way its done in the standard library
- is `+-<-extensional` the right name for `∀ w x y z → (x + y) < (z + w) → (x < z) ⊎ (y < w)`?
