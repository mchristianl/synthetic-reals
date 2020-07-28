4.1  Algebraic structure of numbers

Fields have the property that nonzero numbers have a multiplicative inverse, or more precisely, that
  (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

Remark 4.1.1.
If we require the collection of numbers to form a set in the sense of Definition 2.5.4, and satisfy the ring axioms, then multiplicative inverses are unique, so that the above is equivalent to the proposition
  (Π x : F) x ≠ 0 ⇒ (Σ y : F) x · y = 1.

Definition 4.1.2.
A classical fieldis a set F with points 0, 1 : F, operations +, · : F → F → F, which is a commutative ring with unit, such that
  (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

Remark 4.1.3.
As in the classical case, by proving that additive and multiplicative inverses are unique, we also obtain the negation and division operations.

For the reals, the assumption x ≠ 0 does not give us any information allowing us to bound x away from 0, which we would like in order to compute multiplicative inverses.
Hence, we give a variation on the denition of fields in which the underlying set comes equipped with an apartness relation #, which satises x # y ⇒ x ≠ y, although the converse implication may not hold.
This apartness relation allows us to make appropriate error bounds and compute multiplicative inverses based on the assumption x # 0.

Definition 4.1.4.
- An apartness relation, denoted by #, is an irreflexive symmetric cotransitive relation.
- A strict partial order, denoted by <, is an irreflexive transitive cotransitive relation.

Definition 4.1.5.
A constructive field is a set F with points 0, 1 : F, binary operations +, · : F → F → F, and a binary relation # such that
1. (F, 0, 1, +, ·) is a commutative ring with unit;
2. x : F has a multiplicative inverse iff x # 0;
3. + is #-extensional, that is, for all w, x, y, z : F
   w + x # y + z ⇒ w # y ∨ x # z.

Lemma 4.1.6.
For a constructive field (F, 0, 1, +, ·, #), the following hold.
1. 1 # 0.
2. Addition + is #-compatible in the sense that for all x, y, z : F
   x # y ⇔ x + z # y + z.
3. Multiplication · is #-extensional in the sense that for all w, x, y, z : F
   w · x # y · z ⇒ w # y ∨ x # z.

Lemma 4.1.7.
Given a strict partial order < on a set X:
1. we have an apartness relation defined by
   x # y := (x < y) ∨ (y < x), and
2. we have a preorder defined by
   x ≤ y := ¬(y < x).

Definition 4.1.8.
Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
  z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
and max computes least upper bounds in the sense that for every x, y, z : A, we have
  max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.

Remark 4.1.9.
1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that for every x and y, min(x,y) = x ∨ min(x,y) = y. However, we can characterize min as
  z < min(x,y) ⇔ z < x ∨ z < y
  and similarly for max, see Lemma 6.7.1.
2. In a partial order, for two fixed elements a and b, all joins and meets of a, b are equal, so that Lemma 2.6.20 the type of joins and the type of meets are propositions. Hence, providing the maps min and max as in the above definition is equivalent to the showing the existenceof all binary joins and meets.

The following definition is modified from on The Univalent Foundations Program [89, Definition 11.2.7].

Definition 4.1.10.
An ordered field is a set F together with constants 0, 1, operations +, ·, min, max, and a binary relation < such that:
1. (F, 0, 1, +, ·) is a commutative ring with unit;
2. < is a strict order;
3. x : F has a multiplicative inverse iff x # 0, recalling that # is defined as in Lemma 4.1.7;
4. ≤, as in Lemma 4.1.7, is antisymmetric, so that (F, ≤) is a partial order;
5. (F, ≤, min, max) is a lattice.
6. for all x, y, z, w : F:
   x + y < z + w ⇒ x < z ∨ y < w, (†)
   0 < z ∧ x < y ⇒ x z < y z.     (∗)
Our notion of ordered fields coincides with The Univalent Foundations Program [89, Definition 11.2.7].

Lemma 4.1.11.
In the presence of the first five axioms of Definition 4.1.10, conditions (†) and (∗) are together equivalent to the condition that for all x, y, z : F,
 1. x ≤ y ⇔ ¬(y < x),
 2. x # y ⇔ (x < y) ∨ (y < x)
 3. x ≤ y ⇔ x + z ≤ y + z,
 4. x < y ⇔ x + z < y + z,
 5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
 6. x < y ≤ z ⇒ x < z,
 7. x ≤ y < z ⇒ x < z,
 8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
 9. 0 < z ⇒ (x < y ⇔ x z < y z),
10. 0 < 1.

Lemma 4.1.12.
An ordered field (F, 0, 1, +, ·, min, max, <) is a constructive field (F, 0, 1, +, ·, #).
