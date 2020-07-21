{-# OPTIONS --cubical --no-import-sorts #-}

module Hit where

-- open import Cubical.Core.Everything
open import Cubical.Foundations.Everything renaming (_⁻¹ to _⁻¹ᵖ)
-- open import Cubical.Foundations.Equiv.HalfAdjoint
-- open import Cubical.Data.Sigma.Properties

-- https://en.wikipedia.org/wiki/Inductive_type#Higher_inductive_types

-- private
--   ℓ : Level

_ : (A B : Type₀) → Type₁
_ = λ a b → a ≡ b

-- https://www.youtube.com/watch?v=AZ8wMIar-_c

-- List becomes a normal form of this
data FreeMonoid' (A : Type₀) : Type₀ where
  [_]' : A → FreeMonoid' A
  ε' : FreeMonoid' A
  _*'_ : FreeMonoid' A → FreeMonoid' A → FreeMonoid' A
  assoc' : ∀ x y z → x *' (y *' z) ≡ (x *' y) *' z


data List (A : Type) : Type where
  []  : List A
  _∷_ : A → List A → List A

-- debug fonts
-- see which fonts are "in effect" with
--  fc-match --verbose
-- https://wiki.archlinux.org/index.php/X_Logical_Font_Description
--   Two different font systems are used by X11:
--   - the older or core X Logical Font Description, XLFD,
--   - and the newer X FreeType, Xft, systems (see An Xft Tutorial for font names format).
-- https://keithp.com/~keithp/render/Xft.tutorial

-- λ-calculus
--   Cockx 2019 - Hack your type theory with rewrite rules
--     https://jesper.sikanda.be/posts/hack-your-type-theory.html
--   email thread from Georgi Lyubenov (24.03.20, 23:28 ff) about sized lambdas "How can I implement naive sized lambdas?"
--   email thread from Joey Eremondi (22.04.20, 06:07 ff) about variable binding "What do you use for variable binding in 2020?"

-- literate agda markdown -> latex
--   https://lists.chalmers.se/pipermail/agda/2019/011286.html
--   https://stackoverflow.com/questions/58339725/literate-agda-in-markdown-format-to-latex-via-pandoc
--   https://jesper.sikanda.be/posts/literate-agda.html
--   Jesper Cockx' mail from 09.07.19, 18:35

-- an example file/paper that shows how to use cubical:
--   /home/christianl/agda/cubical/Cubical/Papers/Synthetic.agda
--     Cubical synthetic homotopy theory
--     Mörtberg and Pujet, „Cubical synthetic homotopy theory“.
--     https://dl.acm.org/doi/abs/10.1145/3372885.3373825

-- the github repository recommends
--  Vezzosi 2019 - Cubical Agda: A Dependently Typed ProgrammingLanguage with Univalence and Higher Inductive Types
--  https://dl.acm.org/doi/pdf/10.1145/3341691

-- there is also the very comprehensive
--   https://arxiv.org/pdf/1911.00580.pdf
--   Martín Hötzel Escardó 2020 - Introduction to Univalent Foundations of Mathematics with Agda
--     clickable html version: https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html
--   https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#sns
--      A structure identity principle for a standard notion of structure


-- some useful, recent stuff from the mailing list:
-- https://ncatlab.org/nlab/show/archimedean+field
--   An archimedean field is an ordered field in which every element is bounded above by a natural number.
-- Q: why refl {x} and refl {_} {_} {x} behave differently according to context
-- A: (U. Norell 01.05.20, 23:08)
--   pattern reflpv x = refl {x = x}
--   you are not allowed to pattern match on datatype parameters, since they are not stored in the constructor. In a right-hand side you can give the parameters to guide the type checker, but they are thrown out during elaboration.
-- Andreas Nuyts 26.04.20, 22:34
--   a case in a pattern matching definition gets a light grey background when it doesn't hold as a definitional equation, typically because it is a fallthrough case and further matching of the arguments is necessary to establish that none of the prior cases apply
-- Q: what do I assume/not assume when using --cubical?
-- A: (Andreas Abel 24.04.20, 15:04) That is a long story.  One thing is that in --cubical, the identity type is a primitive (not a data), and you cannot match on refl.
-- https://agda.readthedocs.io/en/v2.6.1/tools/command-line-options.html?highlight=infective#consistency-checking-of-options-used
--   An   infective option is an option that if used in one module, must be used in all modules that depend on this module.
--   A  coinfective option is an option that if used in one module, must be used in all modules that this module depends on.
-- (Orestis Melkonian 22.12.19, 21:11) inspect MAlonzo haskell code's variable names with https://github.com/agda/agda-ghc-names
-- (James Wood 22.12.19, 21:28)
--   Note that record field names can also overlap if they are applied directly to a record value.
--   The theory behind this is in bidirectional type checking, and how a term having its type checked (rather than inferred) may be ambiguous without the information from the type.
--   The same mechanism allows λ to be reused for dimension abstraction in cubical Agda (because it is a constructor).
--   In short, overloading is fine in the following cases:
--   - Everything being overloaded is a constructor, and there is an obvious type to check the resulting construction against.
--   - Everything being overloaded is a field, and there is an obvious record type that the field is destructing.
--   Outside of these cases, overloading fails.
--   You might notice also that the agda2-infer-type command will usually fail to infer the type of a construction of which the head is an overloaded constructor.
--   This is because Agda really wants to check the construction, rather than inferring a type for it.
--   It just happens that when the constructor is not overloaded, it's easier to make progress, because that gives just enough to check the construction against.
-- Q: Copattern match in emacs
-- A: (James Wood 05.11.19, 22:41) If I understand the question correctly, it's the usual C-c C-c for case-splitting, but on an empty hole and followed immediately by RET, rather than entering a variable name. The intermediate prompt is “pattern variables to case (empty for split on result)”. It's splitting on the result that you want.
-- Constructor names can overlap; the right one will be chosen on usage depending on the expected type.
--   Note that other kind of names cannot overlap (e.g. definition names, etc..).

-- the cubical std-lib is described in a blog post from Andreas Mörtberg
--   https://homotopytypetheory.org/2018/12/06/cubical-agda/
--   isomorphisms are equivalences (i.e. have contractible fibers)
--   Hedberg’s theorem (types with decidable equality are sets)
--   The main things that the CCHM cubical type theory extends dependent type theory with are:
--   1. An interval pretype
--   2. Kan operations
--   3. Glue types
--   4. Cubical identity types

open import Cubical.Structures.CommRing
open import Cubical.Relation.Nullary.Base -- ¬_
open import Cubical.Relation.Binary.Base
-- open import Cubical.Data.Prod.Base renaming (_×_ to _×'_)
-- NOTE: Cubical.Core.Sigma uses Agda.Builtin.Sigma
-- open import Agda.Builtin.Sigma renaming (_×_ to _×ᵇ_)
open import Cubical.Data.Sum.Base
open import Cubical.Data.Sigma.Base -- Σ-types are defined in Core/Primitives as they are needed for Glue types.

-- PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
--
-- We have a variable name in `(λ i → A)` as a hint for case splitting.
--
-- Path : ∀ {ℓ} (A : Set ℓ) → A → A → Set ℓ
-- Path A a b = PathP (λ _ → A) a b
--
--  _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
--  _≡_ {A = A} = PathP (λ i → A)

-- Cubical.Foundations.Id 
--
-- transport : ∀ (B : A → Type ℓ') {x y : A} → x ≡ y → B x → B y
-- transport B {x} p b = J (λ y p → B y) b p
-- 
-- _⁻¹ : {x y : A} → x ≡ y → y ≡ x
-- _⁻¹ {x = x} p = J (λ z _ → z ≡ x) refl p
-- 
-- ap : ∀ {B : Type ℓ'} (f : A → B) → ∀ {x y : A} → x ≡ y → f x ≡ f y
-- ap f {x} = J (λ z _ → f x ≡ f z) refl
-- 
-- _∙_ : ∀ {x y z : A} → x ≡ y → y ≡ z → x ≡ z
-- _∙_ {x = x} p = J (λ y _ → x ≡ y) p

refl1 : ∀ {ℓ} {A : Type ℓ} {x : A} → Path A x x
refl1 {x = x} = λ i → x

refl2 : ∀ {ℓ} {A : Type ℓ} {x : A} → PathP (λ _ → A) x x
refl2 {x = x} = λ i → x

refl3 : ∀{ℓ} {A : Type ℓ} {x : A} → PathP (λ _ → A) x x
refl3 {x = x} = λ _ → x

sym1 : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → y ≡ x
sym1 p = λ i → p (~ i)

cong1 : ∀ {ℓ} {A : Type ℓ} {x y : A} {B : A → Type ℓ}
        (f : (a : A) → B a)
        (p : x ≡ y)
        --------------------------------------------
      → PathP (λ i → B (p i)) (f x) (f y)
cong1 f p i = f (p i)

cong2 : ∀ {ℓ} {A : Type ℓ} {x y : A} {B : A → Type ℓ}
        (f : (a : A) → B a)
        (p : PathP (λ i → A      )    x     y )
        ----------------------------------------------
      → (    PathP (λ i → B (p i)) (f x) (f y))
cong2 f p i = f (p i)

-- see "Propositional truncation" https://homotopytypetheory.org/2018/12/06/cubical-agda for
--  data ∥_∥ {ℓ} (A : Set ℓ) : Set ℓ where
--    ∣_∣ : A → ∥ A ∥
--    squash : ∀ (x y : ∥ A ∥) → x ≡ y
-- see https://planetmath.org/37propositionaltruncation

open import Cubical.HITs.PropositionalTruncation -- for `|_|` and `squash`

test1 : {Carrier : Type} -> ∃[ x ∈ Carrier ] x ≡ x → Carrier
test1 ∣ x , x≡x ∣ = x
-- Goal: Carrier
-- ———— Boundary ——————————————————————————————————————————————
-- i = i0 ⊢ test1 x
-- i = i1 ⊢ test1 y
-- ———— Constraints ———————————————————————————————————————————
-- test1 x = ?0 (i = i0) : Carrier
-- test1 y = ?0 (i = i1) : Carrier
test1 (squash x y i) = {! test1 x!}

test2 : {A : Type} → (x y : A) → x ≡ y → A
-- test2 x y x≡y = {! x≡y!}
test2 x y p = p i0

-- test4 : I → Type
-- test4 i = {!!}

test5a : {A : Type} {P : A → Type} → (x y : A) → x ≡ y → P x → P y
test5a {A} {P} x y p px = transport (λ i → P (p i)) px 

test5b : {A : Type}
       → {P : A → Type}
       → (x y : A)
       → PathP (λ _ → A) x y -- x ≡ y
       → P x
       --------------------------
       → P y
test5b {A} {P} x y x≡y Px = transport {A = P x} Px≡Py Px where
  -- transport gives us `P x → P y`, but we need to feed it `P x ≡ P y`
  Px≡Py : P x ≡ P y
  Px≡Py = cong P x≡y
  -- this is almost what `isProp P` would give us
  --   isProp : ∀ {ℓ} → Type ℓ → Type ℓ
  --   isProp A = (x y : A) → x ≡ y
  -- but we need something like `∀(x y : A) → P x ≡ P y`
  --   well, no. `cong P x≡y` gives us `P x ≡ P y`
  -- it is different from non-cubical agda, where `x ≡ y` was sufficient, no matter what P is
  -- there, we could just pattern match on refl and "change" the goal to `P x` instead of `P y`
  -- well, in some sense we are already changing the goal as this approach could be "at the end" of a sequence of equational reasoning
  --   ... just without pattern matching

test5c : {A : Type}
       → {P : A → Type}
       → (x y : A)
       → PathP (λ _ → A) x y -- x ≡ y
       → P x
       --------------------------
       → P y
test5c {A} {P} x y x≡y Px = transport {A = P x} Px≡Py Px where
  -- once again, without `cong`
  Px≡Py : P x ≡ P y
  -- we need to build a path that is `P x` at i0 and `P y` at i1
  -- with `x≡y` we have given a path that is `x` at i0 and `y` at i1
  -- therefore `x≡y(i)` behaves in the correct way and we just plug this into `P`
  Px≡Py i = P (x≡y i)

-- the short version, collapsing all intermediates
test5f : ∀{ℓ ℓ'} {A : Type ℓ} {P : A → Type ℓ'} {x y : A} → (x ≡ y) → (P x) → P y
test5f {P = P} p px = transport (λ i → P (p i)) px

--primitive
--  transp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (a : A i0) → A i1

transport1 : ∀{ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport1 p a = transp (λ i → p i) i0 a

test5d : {A : Type} {P : A → Type} → (x y : A) → x ≡ y → P x → P y
test5d {A} {P} x y x≡y Px = transport (cong P x≡y) Px

module Utils where
  private
    variable
      ℓ ℓ' : Level
      A :                               Type ℓ
      B :      A                      → Type ℓ
      C : (a : A) →      B a          → Type ℓ
      D : (a : A) → (b : B a) → C a b → Type ℓ

  cong₁ : ∀ (f : (a : A) → B a)
       → {x : A} {y : A} (p : PathP (λ i → A) x y) -- (p : x ≡ y)
       ----------------------------------
       → PathP (λ i → B (p i)) (f x) (f y)
  cong₁ f p i = f (p i)
  {-# INLINE cong₁ #-}

  cong₂' : ∀ {F : (a : A) → (b : B a) → Type ℓ}
         → (f : (a : A) → (b : B a) → F a b)
         → {x : A    } {y : A    } (p : PathP (λ i → A            ) x y) -- (p : x ≡ y)
         → {u : B x  } {v : B y  } (q : PathP (λ i → B (p i)      ) u v) -- ? u ≡ v given x ≡ y ?
         ---------------------------------------------
         → PathP (λ i → F (p i) (q i)) (f x u) (f y v)
  cong₂' f p q i = f (p i) (q i)
  {-# INLINE cong₂' #-}

  cong₃ : ∀{F : (a : A) → (b : B a) → (c : C a b) → Type ℓ}
        →   (f : (a : A) → (b : B a) → (c : C a b) → F a b c)
        → {x : A    } {y : A    } (p : PathP (λ i → A            ) x y) -- (p : x ≡ y)
        → {u : B x  } {v : B y  } (q : PathP (λ i → B (p i)      ) u v) -- ? u ≡ v given x ≡ y ?
        → {m : C x u} {n : C y v} (r : PathP (λ i → C (p i) (q i)) m n) -- ? m ≡ n given x ≡ y and u ≡ v ?
        --------------------------------------------
        → PathP (λ i → F (p i) (q i) (r i)) (f x u m) (f y v n)
  cong₃ f p q r i = f (p i) (q i) (r i)
  {-# INLINE cong₃ #-}

  cong₄ : ∀{F : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → Type ℓ}
        →   (f : (a : A) → (b : B a) → (c : C a b) → (d : D a b c) → F a b c d)
        → {x : A      } {y : A      } (p : PathP (λ i → A                  ) x y) -- (p : x ≡ y)
        → {u : B x    } {v : B y    } (q : PathP (λ i → B (p i)            ) u v) -- ? u ≡ v given x ≡ y ?
        → {m : C x u  } {n : C y v  } (r : PathP (λ i → C (p i) (q i)      ) m n) -- ? m ≡ n given x ≡ y and u ≡ v ?
        → {k : D x u m} {l : D y v n} (s : PathP (λ i → D (p i) (q i) (r i)) k l) -- ? k ≡ l given x ≡ y and u ≡ v and m ≡ n?
        --------------------------------------------
        → PathP (λ i → F (p i) (q i) (r i) (s i)) (f x u m k) (f y v n l)
  cong₄ f p q r s i = f (p i) (q i) (r i) (s i)
  {-# INLINE cong₄ #-}

open Utils using (cong₃; cong₄)

-- slide 18 of http://www.cse.chalmers.se/~abela/esslli2016/talkESSLLI3.pdf
fullelim : (A : Type)
         → (C : (x y : A) → (p : x ≡ y) → Type)
         → (M N : A)
         → (P : M ≡ N)
         → (O : (z : A) → C z z refl)
         ------------------------
         → C M N P
fullelim A C M N P O = transport along (O M) where
  along : C M M refl ≡ C M N P
  -- the "obvious" idea would be to show equality on every argument
  -- and then use a brute force `cong₃` to apply these equalities
  along = cong₃ C (refl {x = M}) P refl≡P where
    -- the first two arguments are easy, and the hole of the third argument rewards us with a signature to implement:
    refl≡P : PathP (λ i → M ≡ (P i)) refl P
    -- here, we need to build a path that is refl on i0 and P on i1 just with the things we have given
    --    refl : ∀{ℓ} {A : Type ℓ} {x : A} x ≡ x
    --    refl {x = x} = λ _ → x
    --    _≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
    --    _≡_ {A = A} = PathP (λ i → A)
    -- therefore, we have
    --    refl : ∀{ℓ} {A : Type ℓ} {x : A} → PathP (λ i → A) M M
    --    refl {x = x} = λ _ → x
    --    P : PathP (λ i → A) M N
    -- Goal: M ≡ P i
    -- Goal: PathP (λ j → A) M (P i)
    refl≡P i = λ j → P (i ∧ j)
    -- I could not come up with the solution myself, but I was able to pick it off ...
    --   ... of `J` under "Kan operations" at https://homotopytypetheory.org/2018/12/06/cubical-agda/
    -- so, how does this work? These are the cases:
    --    i |  j | i∧j | P(i∧j) | λ j → P(i∧j) | λ i → λ j → P(i∧j)
    --   i0 | i0 |  i0  |  M : A | M≡M : M ≡ M   |  p : (M≡M) ≡ (M≡N)
    --   i0 | i1 |  i0  |  M : A |               |    which is "like"
    --   i1 | i0 |  i0  |  M : A | M≡N : M ≡ N   |  p :  refl ≡ P
    --   i1 | i1 |  i1  |  N : A |               |
    -- and indeed, they work out
    -- we could not write `refl ≡ P` but instead have `PathP _ refl P`

fullelim2 : (A : Type)
         → (C : (x y : A) → (p : x ≡ y) → Type)
         → (M N : A)
         → (P : M ≡ N)
         → (O : (z : A) → C z z refl)
         ------------------------
         → C M N P
-- we can unfold `transport` as in the blog post
--   transport : {A B : Type ℓ} → A ≡ B → A → B
--   transport p a = transp (λ i → p i) i0 a
fullelim2 A C M N P O = transp (λ i → along i) i0 (O M) where
  -- and we can directly "set up" the path without using `cong₃`
  along : C M M refl ≡ C M N P
  along i = C (refl {x = M} i) (P i) (λ j →  P (i ∧ j) )

--

-- see favonia: [Agda] Equational Reasoning
--   https://favonia.org/courses/hdtt2020/agda/agda-0305-eqreasoning.agda

-- Kraus 2013 - Generalizations of Hedberg’s Theorem
--   https://www.cs.bham.ac.uk/~mhe/papers/hedberg.pdf
--   Although the identity types in Martin-Löf type theory (MLTT) are defined byone constructor refl and by one eliminator J that matches the constructor, the statement that every identity type has at most one inhabitant is not provable [9].
--   Thus,uniqueness of identity proofs(UIP), or, equivalently, Streicher’s axiom K are principles that have to be assumed, and have often been assumed, as additional rules of MLTT.
--   ...
--   we  do  not  assume  the  principle  of  unique  identity  proofs.
--   However, certain types do satisfy it naturally, and such types are often called h-sets.
--   A sufficient condition for a type to be an h-set, given by Hedberg [8], isthat it has decidable propositional equality.
--   In Section 3, we analyze Hedberg’s original argument, which consists of two steps:
--   1.  A type X is an h-set iff for all x, y : X there is a constant map x = y → x = y.
--   2. If X has decidable equality then such constant endomaps exist
--   Decidable equality means that, for all x and y, we have (x = y) + (x ≠ y).
--   Thus, a natural weakening is ¬¬-separated equality, ¬¬(x = y) → x = y, which occurs often in constructive mathematics.
--   In this case we say that the type X is separated.
--   For example, going beyond MLTT, the reals and the Cantorspace in Bishop mathematics and topos theory are separated.
--   In MLTT, the Cantortype of functions from natural numbers to booleans is separated under the assumption of functional extensionality,
--     ∀ f g : X → Y, (∀ x : X, f x = g x) → f = g.
--   We observe that under functional extensionality, a separated type X is an h-set, because there is always a constant map x = y → x = y.
--   In order to obtain a further characterization of the notion of h-set, we consider truncations
--     (also known as bracket or squash types), written ‖X‖in accordance with recent HoTT notation.
--   The idea is to collapse all inhabitants of X so that ‖X‖ has at most one inhabitant.
--   We refer the reader to the technical development for a precise definition.
-- cites
--   Altenkirch 2012 - On h-Propositional Reflection and Hedberg’s Theorem
--   https://homotopytypetheory.org/2012/11/27/on-h-propositional-reflection-and-hedbergs-theorem/
-- Bracket-Type https://ncatlab.org/nlab/show/bracket+type
--   By contrast, in the paradigm that may be called propositions as some types, every proposition is a type, but not every type is a proposition.
--   The types which are propositions are generally those which “have at most one inhabitant” — in homotopy type theory this is called being of h-level 1 or being a (-1)-type.
--   ...
--   For A a type, the support of A denoted supp(A) or isInhab(A) or τ₋₁ A or ‖A‖₋₁ or ‖A‖ or, lastly, [A],
--     is the higher inductive type defined by the two constructors
--       a : A ⊢ isinhab(a) : supp(A)
--       x : supp(A), y : supp(A) ⊢ inpath(x,y) : (x = y),
--   where in the last sequent on the right we have the identity type.

-- https://github.com/agda/cubical/issues/286
-- It could also be a good idea to axiomatize the notion of a Caucy-complete Archimedean ordered field, as in Auke Booij's thesis, and show that Dedekind reals are an instance. The HoTT reals are then another instance. (Can cubical Agda handle the HoTT reals as a HIIT yet?)

-- https://www.cs.bham.ac.uk/~abb538/thesis-first_submission.pdf
-- Booij 2020 - Analysis in Univalent Type Theory

-- 4.1  Algebraic structure of numbers
-- 
-- Fields have the property that nonzero numbers have a multiplicative inverse, or more precisely, that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.
-- 
-- Remark 4.1.1.
-- If we require the collection of numbers to form a set in the sense of Definition 2.5.4, and satisfy the ring axioms, then multiplicative inverses are unique, so that the above is equivalent to the proposition
--   (Π x : F) x ≠ 0 ⇒ (Σ y : F) x · y = 1.
-- 
-- Definition 4.1.2.
-- A classical field is a set F with points 0, 1 : F, operations +, · : F → F → F, which is a commutative ring with unit, such that
--   (∀ x : F) x ≠ 0 ⇒ (∃ y : F) x · y = 1.

private
  variable
    ℓ ℓ' ℓ'' : Level

module ClassicalFieldModule where -- NOTE: one might want to put this into another file to omit the name-clashing
  record IsClassicalField {F : Type ℓ}
                          (0f : F) (1f : F) (_+_ : F → F → F) (_·_ : F → F → F) (-_ : F → F) (_⁻¹ᶠ : (x : F) → {{¬(x ≡ 0f)}} → F) : Type ℓ where
    constructor isclassicalfield

    field
      isCommRing : IsCommRing 0f 1f _+_ _·_ -_
      ·-rinv : (x : F) → (p : ¬(x ≡ 0f)) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
      ·-linv : (x : F) → (p : ¬(x ≡ 0f)) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f

    open IsCommRing {0r = 0f} {1r = 1f} isCommRing public

  record ClassicalField : Type (ℓ-suc ℓ) where
    field
      Carrier : Type ℓ
      0f   : Carrier
      1f   : Carrier
      _+_  : Carrier → Carrier → Carrier
      _·_  : Carrier → Carrier → Carrier
      -_   : Carrier → Carrier
      _⁻¹ᶠ : (x : Carrier) → {{¬(x ≡ 0f)}} → Carrier
      isClassicalField : IsClassicalField 0f 1f _+_ _·_ -_ _⁻¹ᶠ

    infix  9 _⁻¹ᶠ
    infix  8 -_
    infixl 7 _·_
    infixl 6 _+_

    open IsClassicalField isClassicalField public

-- Remark 4.1.3.
-- As in the classical case, by proving that additive and multiplicative inverses are unique, we also obtain the negation and division operations.
-- 
-- For the reals, the assumption x ≠ 0 does not give us any information allowing us to bound x away from 0, which we would like in order to compute multiplicative inverses.
-- Hence, we give a variation on the denition of fields in which the underlying set comes equipped with an apartness relation #, which satises x # y ⇒ x ≠ y, although the converse implication may not hold.
-- This apartness relation allows us to make appropriate error bounds and compute multiplicative inverses based on the assumption x # 0.
-- 
-- Definition 4.1.4.
-- - An apartness relation, denoted by #, is an irreflexive symmetric cotransitive relation.
-- - A strict partial order, denoted by <, is an irreflexive transitive cotransitive relation.

IsIrrefl : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsIrrefl {A = A} R = (a b : A) → R a b → ¬(R b a)

IsCotrans : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
IsCotrans {A = A} R = (a b : A) → R a b → (∀(x : A) → (R a x) ⊎ (R x b))

-- NOTE: these `IsX` definitions are in the style of the standard library and do not make `a` and `b` to be implicit arguments
--   when using them, we can just use `_` as in `isIrrefl _ _ a#b`

-- NOTE: module parameters "add" to the contained function's arguments
--   see https://agda.readthedocs.io/en/v2.6.0.1/language/module-system.html#parameterised-modules

-- IsApartnessRel : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
-- IsApartnessRel R = IsIrrefl R × BinaryRelation.isSym R × IsCotrans R

record IsApartnessRel {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isIrrefl  : IsIrrefl R
    isSym     : BinaryRelation.isSym R
    isCotrans : IsCotrans R

-- IsStrictPartialOrder : {ℓ ℓ' : Level} {A : Type ℓ} → (R : Rel A A ℓ') → Type (ℓ-max ℓ ℓ')
-- IsStrictPartialOrder R = IsIrrefl R × BinaryRelation.isTrans R × IsCotrans R

record IsStrictPartialOrder {ℓ ℓ' : Level} {A : Type ℓ} (R : Rel A A ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    isIrrefl  : IsIrrefl R
    isTrans   : BinaryRelation.isTrans R
    isCotrans : IsCotrans R

-- Definition 4.1.5.
-- A constructive field is a set F with points 0, 1 : F, binary operations +, · : F → F → F, and a binary relation # such that
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. x : F has a multiplicative inverse iff x # 0;
-- 3. + is #-extensional, that is, for all w, x, y, z : F
--    w + x # y + z ⇒ w # y ∨ x # z.

{- NOTE: about naming in the standard library
with `isCommRing : IsCommRing 0f 1f _+_ _·_ -_` we import
  is-set        : (x y : Carrier) (x₁ y₁ : x ≡ y) → x₁ ≡ y₁ -- NOTE: this is imported from +-isAbGroup and explicitly hidden from ·-isMonoid
  isCommRing    : IsCommRing 0f 1f _+_ _·_ -_
  isRing        : IsRing 0f 1f _+_ _·_ -_
  +-isAbGroup   : IsAbGroup 0f _+_ -_
  +-assoc       : (x y z : Carrier) → x + (y + z) ≡ x + y + z
  +-identity    : (x : Carrier) → (x + 0f ≡ x) × (0f + x ≡ x)
  +-rid         : (x : Carrier) → x + 0f ≡ x
  +-lid         : (x : Carrier) → 0f + x ≡ x
  +-inv         : (x : Carrier) → (x + - x ≡ 0f) × (- x + x ≡ 0f)
  +-linv        : (x : Carrier) → - x + x ≡ 0f
  +-rinv        : (x : Carrier) → x + - x ≡ 0f
  +-comm        : (x y : Carrier) → x + y ≡ y + x
  +-isSemigroup : IsSemigroup _+_
  +-isMonoid    : IsMonoid 0f _+_
  +-isGroup     : IsGroup 0f _+_ -_
  ·-isSemigroup : IsSemigroup _·_
  ·-isMonoid    : IsMonoid 1f _·_
  ·-comm        : (x y : Carrier) → x · y ≡ y · x
  ·-assoc       : (x y z : Carrier) → x + (y + z) ≡ x + y + z
  ·-identity    : (x : Carrier) → (x · 1f ≡ x) × (1f · x ≡ x)
  ·-lid         : (x : Carrier) → 1f · x ≡ x
  ·-rid         : (x : Carrier) → x · 1f ≡ x
  dist          : (x y z : Carrier) → (x · (y + z) ≡ x · y + x · z) × ((x + y) · z ≡ x · z + y · z)
  ·-rdist-+     : (x y z : Carrier) → x · (y + z) ≡ x · y + x · z
  ·-ldist-+     : (x y z : Carrier) → (x + y) · z ≡ x · z + y · z
there is
  module GroupLemmas (G : Group {ℓ}) where
  record MonoidEquiv (M N : Monoid {ℓ}) : Type ℓ where
  module SemigroupΣTheory {ℓ} where
  module CommRingΣTheory {ℓ} where
  module MonoidΣTheory {ℓ} where
  module MonoidTheory {ℓ} (M' : Monoid {ℓ}) where
  module GroupΣTheory {ℓ} where
  module AbGroupΣTheory {ℓ} where
  module RingΣTheory {ℓ} where
  module Theory (R' : Ring {ℓ}) where
  module PosetReasoning (P : Poset ℓ₀ ℓ₁) where
there is a syntax for https://agda.readthedocs.io/en/latest/language/module-system.html?highlight=module#parameterised-modules
  module SortNat = Sort Nat leqNat
the non-cubical standard library has a lot of machinery that is missing in the cubical-stdlib
  module Function.Base where
    -- Binary application
    _⟨_⟩_ : A → (A → B → C) → B → C
    x ⟨ f ⟩ y = f x y
    -- Composition of a binary function with a unary function
    _on_ : (B → B → C) → (A → B) → (A → A → C)
    _*_ on f = λ x y → f x * f y
    -- Flipped application (aka pipe-forward)
    _|>_ : ∀ {A : Set a} {B : A → Set b} → (a : A) → (∀ a → B a) → B a
    -- Construct an element of the given type by instance search.
    it : {A : Set a} → {{A}} → A
    it {{x}} = x
  module Relation.Binary.Core where
    infix 4 _⇒_ _⇔_ _=[_]⇒_
    -- Implication/containment - could also be written _⊆_.
    -- and corresponding notion of equivalence
    _⇒_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
    P ⇒ Q = ∀ {x y} → P x y → Q x y
    _⇔_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
    P ⇔ Q = P ⇒ Q × Q ⇒ P
    -- Generalised implication - if P ≡ Q it can be read as "f preserves P".
    _=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
    P =[ f ]⇒ Q = P ⇒ (Q on f)
    -- A synonym for _=[_]⇒_.
    _Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
    f Preserves P ⟶ Q = P =[ f ]⇒ Q
    -- A binary variant of _Preserves_⟶_.
    _Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
    _∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)
  module Algebra.Definitions
    Congruent₁ : Op₁ A → Set _
    Congruent₁ f = f Preserves _≈_ ⟶ _≈_
    Congruent₂ : Op₂ A → Set _
    Congruent₂ ∙ = ∙ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
    LeftCongruent : Op₂ A → Set _
    LeftCongruent _∙_ = ∀ {x} → (x ∙_) Preserves _≈_ ⟶ _≈_
    RightCongruent : Op₂ A → Set _
    RightCongruent _∙_ = ∀ {x} → (_∙ x) Preserves _≈_ ⟶ _≈_
the non-cubical standard library makes more use of unicode, e.g. in invˡ and invʳ
for the inverse, we have in the non-cubical standard library
  inverseˡ : LeftInverse ε _⁻¹ _∙_
  inverseˡ = proj₁ inverse
  inverseʳ : RightInverse ε _⁻¹ _∙_
  inverseʳ = proj₂ inverse
  uniqueˡ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → x ≈ (y ⁻¹)
  uniqueˡ-⁻¹ = Consequences.assoc+id+invʳ⇒invˡ-unique
                setoid ∙-cong assoc identity inverseʳ
  uniqueʳ-⁻¹ : ∀ x y → (x ∙ y) ≈ ε → y ≈ (x ⁻¹)
  uniqueʳ-⁻¹ = Consequences.assoc+id+invˡ⇒invʳ-unique
                setoid ∙-cong assoc identity inverseˡ
interestingly, this follows from just one field `inverse : Inverse ε _⁻¹ _∙_`
  there is `module Algebra.Consequences.Setoid` for such results ("consequences")
there are open pull requests which might have some more information about the "intended" style
  https://github.com/agda/cubical/pull/331
    Algebras and modules #331 
  https://github.com/agda/cubical/pull/365
    Mayer-Vietoris and some cohomology groups #365 
  https://github.com/agda/cubical/pull/325
    Denial field #325
    A denial field is a commutative ring where every non-zero element has an inverse. See #301 for a discussion of other notions of 'field' in constructive algebra.
    https://github.com/felixwellen/cubical/tree/denial-field
  https://github.com/agda/cubical/issues/301
    Add Field to Cubical.Structures #301 
    In the style of Ring, etc. from #284. I think it would be good to have this so we could show ℚ is a field.
  https://github.com/agda/cubical/pull/284
    Newstructures #284
    Adding some new structures (semigroups, groups, abelian groups and rngs) and a new folder of Algebra, in order to produce results about these new Algebraic structures.
  https://github.com/agda/cubical/commit/8cf91aeb49ebf26d4cf4e6795e8b56041e28c7a1
    Rewrite Group, AbGroup, Ring and CommRing to be records instead of nested Sigma types
  https://github.com/agda/cubical/pull/324
    Ideals and quotient rings #324 
    - define (left-, right- and two-sided) ideals
    - define quotient by a two-sided ideal
    - construct the ring structure on the quotient
-}

record IsConstructiveField {F : Type ℓ}
                           (0f : F) (1f : F) (_+_ : F → F → F) (_·_ : F → F → F) (-_ : F → F) (_#_ : Rel F F ℓ') (_⁻¹ᶠ : (x : F) → {{x # 0f}} → F) : Type (ℓ-max ℓ ℓ') where
  constructor isconstructivefield

  field
    isCommRing : IsCommRing 0f 1f _+_ _·_ -_
    ·-rinv     : (x : F) → (p : x # 0f) → x · (_⁻¹ᶠ x {{p}}) ≡ 1f
    ·-linv     : (x : F) → (p : x # 0f) → (_⁻¹ᶠ x {{p}}) · x ≡ 1f
    -- ·-inv      : (x : F) → (p : x # 0f) → x · (let instance p = p in (x ⁻¹ᶠ)) ≡ 1f -- this does also work
    -- ·-inv      : (x : F) → ({{p}} : x # 0f) → x · (x ⁻¹ᶠ) ≡ 1f -- this does not do the right thing
    -- ·-inv-back : (x : F) → ∃[ y ∈ F ] (x · y ≡ 1f) → x # 0f
    ·-inv-back : (x y : F) → (x · y ≡ 1f) → x # 0f × y # 0f
    +-#-extensional : (w x y z : F) → (w + x) # (y + z) → (w # y) ⊎ (x # z)
    isApartnessRel : IsApartnessRel _#_

  open IsCommRing {0r = 0f} {1r = 1f} isCommRing public
  open IsApartnessRel isApartnessRel public
    renaming
      ( isIrrefl  to #-irrefl
      ; isSym     to #-sym
      ; isCotrans to #-cotrans )

_ = {!!}

record ConstructiveField : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    Carrier : Type ℓ
    0f   : Carrier
    1f   : Carrier
    _+_  : Carrier → Carrier → Carrier
    _·_  : Carrier → Carrier → Carrier
    -_   : Carrier → Carrier
    _#_  : Rel Carrier Carrier ℓ'
    _⁻¹ᶠ : (x : Carrier) → {{x # 0f}} → Carrier
    isConstructiveField : IsConstructiveField 0f 1f _+_ _·_ -_ _#_ _⁻¹ᶠ
 
  infix  9 _⁻¹ᶠ
  infixl 7 _·_
  infix  6 -_
  infixl 5 _+_
  infixl 4 _#_

  open IsConstructiveField isConstructiveField public

open import Cubical.Data.Empty renaming (elim to ⊥-elim) -- `⊥` and `elim`

-- Lemma 4.1.6.
-- For a constructive field (F, 0, 1, +, ·, #), the following hold.
-- 1. 1 # 0.
-- 2. Addition + is #-compatible in the sense that for all x, y, z : F
--    x # y ⇔ x + z # y + z.
-- 3. Multiplication · is #-extensional in the sense that for all w, x, y, z : F
--    w · x # y · z ⇒ w # y ∨ x # z.
module Lemmas-4-6-1 {{F : ConstructiveField {ℓ} {ℓ'}}} where
  --open ConstructiveField {{...}} public -- creates additional `ConstructiveField.foo F` in the "Goal/Have-previews"
  open ConstructiveField F -- works
  
  open import Cubical.Structures.Ring
  -- NOTE: this also creates additional `Ring.Carrier (makeRing ...)` in the "Goal/Have-previews", except when using C-u C-u C-... then these get normalized fine
  --   can we do something with pragmas here? https://agda.readthedocs.io/en/latest/language/pragmas.html?highlight=INLINE#the-inline-and-noinline-pragmas
  --   or maybe with macros? https://github.com/alhassy/gentle-intro-to-reflection
  -- using this `R` makes it a little better
  R = (makeRing 0f 1f _+_ _·_ -_ is-set +-assoc +-rid +-rinv +-comm ·-assoc ·-rid ·-lid ·-rdist-+ ·-ldist-+)
  open Cubical.Structures.Ring.Theory R
  -- 0-rightNullifies

  -- open Ring {{...}} public

  {-
  module ReflectionTest where
    open import Data.Nat as Nat hiding (_⊓_)
    open import Data.List as List
    open import Data.Char as Char
    open import Data.String as String

    open import Reflection hiding (name; Type)
    open import Reflection.Term as Term public hiding (Type)
    test06 = (quoteTC 0-rightNullifies)

    test07 : _
    unquoteDef test07 = defineFun test07
      [ clause
        ( [] ) -- hidden arguments `{x}`
        ( [] ) -- visible arguments `{y}`
        (quoteTerm 0f) -- the "Term" at the right hand side of the `=`
      ]
    -- {-# INLINE test07 #-}
    -- {-# NOINLINE test07 #-}

    proof07 : test07 ≡ 0f
    proof07 = {!!}
  -}

  {-
  -- NOTE: it might be possible with --overlapping-instances to resolve this "Goal/Have-preview" issue
  --   but it is mentioned that this "might lead to an exponential slowdown in instance resolution and possibly (apparent) looping behaviour"
  --   also the OPTION pragma to apply --overlapping-instances can only be set per file (and not per module)
  --   so it might be a good idea to have a separate "Theory.agda" or "Properties.agda" (as it is called in the standard library)
  -- well, in a test with --overlapping instances, I got the issue that -_ is defined multiple times
  --   to be fair, the result we have implemented might fit better in a more general Ring context
  -- so one might think about this and until then, I guess, the best solution is to just omit multiple instances

  module InstanceTest where
    -- taken from https://agda.readthedocs.io/en/latest/language/instance-arguments.html#defining-type-classes
    -- open import Algebra
    open import Agda.Builtin.Nat
    open import Data.List renaming (List to BList)

    record Monoid {a} (A : Type a) : Type a where
      field
        mempty : A
        _<>_   : A → A → A
    open Monoid {{...}} public

    instance
      ListMonoid : ∀ {a} {A : Type a} → Monoid (BList A)
      -- normal: provide "implementation" in a single term
      --   ListMonoid = record { mempty = []; _<>_ = _++_ }
      -- with copatterns: provide "implementation" with patterns
      mempty {{ListMonoid}} = []
      _<>_   {{ListMonoid}} xs ys = xs ++ ys

    mconcat : ∀ {a} {A : Type a} → {{Monoid A}} → BList A → A
    mconcat [] = mempty
    mconcat (x ∷ xs) = x <> mconcat xs

    sum1 : BList Nat → Nat
    sum1 xs =
      let instance -- NOTE: IMPORTANT: the instance-block needs to be more indented (!) than the `instance` keyword
            NatMonoid : Monoid Nat
            NatMonoid = record { mempty = 0; _<>_ = Agda.Builtin.Nat._+_ }
      in mconcat xs

  itest2 =
    let
      instance
        rr = R
    in {! 0-rightNullifies!}

  -- To restrict an instance to the current module, you can mark it as private. For instance,
  --    https://agda.readthedocs.io/en/latest/language/instance-arguments.html#restricting-instance-search
  -}

  {-
  https://agda.readthedocs.io/en/latest/language/abstract-definitions.html
    Abstract definitions
    Definitions can be marked as abstract, for the purpose of hiding implementation details, or to speed up type-checking of other parts. In essence, abstract definitions behave like postulates, thus, do not reduce/compute. For instance, proofs whose content does not matter could be marked abstract, to prevent Agda from unfolding them (which might slow down type-checking).
  -}

  -- anonymous modules `module _ params where` automatically open themselves
  --   they are not well documented but there is this usage example
  --     Anonymous modules or sections #735 
  --     https://github.com/agda/agda/issues/735
  --       I often want to use something like sections in Coq. I usually use parametrized modules but this has at least two issues that Coq does not have:
  --       1) I need to give a name to the module, and there is often no meaningful name  to be given
  --       2) It exports the module, so I cannot define a module in another file with the  same name
  --       the following code
  --         module _ params where
  --           declarations
  --       would be translated to:
  --         private
  --           module Fresh params where
  --             declarations
  --         open Fresh public
  --       where Fresh is a new name.
  --     NOTE: this gives a hint on the use of "sections" in mathematical writing
  --       it suggests, that these introduce variable-but-fixed parameter dependencies to all definitions (in the way the `variable` keyword does)
  --       the difference between an anonymous module and a variable seems to be that the module adds all parameters, where `variable` only adds parameters when used
  --       also, in the module we have more flexibility with opening other modules and hiding names with the `private` keyword, etc.
  --     and there is
  --       https://github.com/agda/agda/issues/1145
  --       Allow multiple layout keywords on the same line #1145 

  -- NOTE: IMPORTANT: when in a hole, with C-c C-o one can list "module contents"
  --   if given `F` here, we can see the contents of F
  --   I guess, since every inherited member is included with `open ... public`,
  --     we can continue with just `isConstructiveField`
  --     and even `isCommRing`
  --     and even `isRing`
  --   this greatly helps to investigate available

  {-
  test3 : ∃[ x ∈ Carrier ] x · x ≡ x → Carrier
  test3 ∥_∥.∣ Σx-x·x≡x ∣ = {!!}
  --test ∥_∥.∣ x , x·x≡x ∣ = x
  test3 (∥_∥.squash Σx-x·x≡x₁ Σx-x·x≡x₂ i) = {!!}

  test3b : {A : Type} → ∃[ x ∈ A ] ∃[ y ∈ A ] x ≡ y → A
  test3b ∥_∥.∣ fst₁ , ∥_∥.∣ fst₂ , snd₁ ∣ ∣ = {!!}
  test3b ∥_∥.∣ fst₁ , ∥_∥.squash snd₁ ∥_∥.∣ x ∣ i ∣ = {!!}
  test3b ∥_∥.∣ fst₁ , ∥_∥.squash snd₁ (∥_∥.squash snd₂ ∥_∥.∣ x ∣ i₁) i ∣ = {!!}
  test3b ∥_∥.∣ fst₁ , ∥_∥.squash snd₁ (∥_∥.squash snd₂ (∥_∥.squash snd₃ snd₄ i₂) i₁) i ∣ = {!!}
  test3b (∥_∥.squash ∥_∥.∣ x ∣ ∥_∥.∣ x₁ ∣ i) = {!!}
  test3b (∥_∥.squash ∥_∥.∣ x ∣ (∥_∥.squash x₁ x₂ i₁) i) = {!!}
  test3b (∥_∥.squash (∥_∥.squash x x₂ i₁) x₁ i) = {!!}
  -}

  -- ∃ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  -- ∃ A B = ∥ Σ A B ∥
  -- infix 2 ∃-syntax
  -- ∃-syntax : ∀ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') → Type (ℓ-max ℓ ℓ')
  -- ∃-syntax = ∃
  -- syntax ∃-syntax A (λ x → B) = ∃[ x ∈ A ] B

  -- Lemma 4.1.6.1
  1f#0f : 1f # 0f
  1f#0f with ·-identity 1f
  -- 1f#0f | 1·1≡1 , _ = ·-inv-back 1f ∣ (1f , 1·1≡1) ∣ -- need additional ∣_∣ resp. \|_\| around the tuple
  1f#0f | 1·1≡1 , _ = fst (·-inv-back _ _ 1·1≡1)

  _ = Cubical.Data.Sigma.Base._×_ -- fst and snd

  a+b-b≡a : ∀ a b → a ≡ (a + b) - b
  -- NOTE: about workflow
  --   one can investigate some single term in the hole (C-c C-.), but not a second one
  --   therefore, we can move a term temporarily into a let-clause and work on another term in the hole
  --   ... is there equational reasoning in --cubical ?
  -- NOTE: Yes! it is in Cubical.Foundations.Id
  a+b-b≡a a b = let P = sym (fst (+-inv b))
                    Q = sym (fst (+-identity a))
                    R = transport (λ i → a ≡ a + P i) Q
                    S = transport (λ i → a ≡ (+-assoc a b (- b)) i ) R
                in S

  +-preserves-≡ : ∀{a b} → ∀ c → a ≡ b → a + c ≡ b + c
  +-preserves-≡ c a≡b i = a≡b i + c

  +-preserves-≡-l : ∀{a b} → ∀ c → a ≡ b → c + a ≡ c + b
  +-preserves-≡-l c a≡b i = c + a≡b i

  a+b≡0→a≡-b : ∀{a b} → a + b ≡ 0f → a ≡ - b
  a+b≡0→a≡-b {a} {b} a+b≡0 = transport
    (λ i →
      let RHS = snd (+-identity (- b))
          LHS₁ : a + (b + - b) ≡ a + 0f
          LHS₁ = +-preserves-≡-l a (fst (+-inv b))
          LHS₂ : (a + b) - b ≡ a
          LHS₂ = transport (λ j →  (+-assoc a b (- b)) j ≡ fst (+-identity a) j) LHS₁
          in  LHS₂ i ≡ RHS i  
    ) (+-preserves-≡ (- b) a+b≡0)

  a·-b≡-a·b : ∀ a b → a · (- b) ≡ - a · b
  a·-b≡-a·b a b =
    let P : a · 0f ≡ 0f
        P = 0-rightNullifies a
        Q : a · (- b + b) ≡ 0f
        Q = transport (λ i →  a · snd (+-inv b) (~ i) ≡ 0f) P
        R : a · (- b) + a · b ≡ 0f
        R = transport (λ i → ·-rdist-+ a (- b) b i ≡ 0f) Q
    in a+b≡0→a≡-b R

  a·b-a·c≡a·[b-c] : ∀ a b c → a · b - a · c ≡ a · (b - c)
  a·b-a·c≡a·[b-c] a b c =
    let P : a · b + a · (- c) ≡ a · (b + - c)
        P = sym (·-rdist-+ a b (- c))
        Q : a · b - a · c ≡ a · (b + - c)
        Q = transport (λ i →  a · b + a·-b≡-a·b a c i ≡ a · (b + - c) ) P
    in  Q  

  -- Lemma 4.1.6.2
  --   For #-compatibility of +, suppose x # y, that is, (x +z) −z # (y +z) −z.
  --   Then #-extensionality gives (x + z # y + z) ∨ (−z # −z), where the latter case is excluded by irreflexivity of #.
  +-#-compatible : ∀(x y z : Carrier) → x # y → x + z # y + z
  +-#-compatible x y z x#y with
    let P = transport (λ i →  a+b-b≡a x z i # a+b-b≡a y z i ) x#y 
    in  +-#-extensional _ _ _ _ P
  ... | inl x+z#y+z = x+z#y+z
  ... | inr  -z#-z  = ⊥-elim (#-irrefl _ _ -z#-z -z#-z) 

  -- The other direction is similar.
  +-#-compatible-inv : ∀(x y z : Carrier) → x + z # y + z → x # y
  +-#-compatible-inv _ _ _ x+z#y+z with +-#-extensional _ _ _ _ x+z#y+z
  ... | inl x#y = x#y
  ... | inr z#z = ⊥-elim (#-irrefl _ _ z#z z#z)

  -- _ = {!!} ≃⟨ {!!} ⟩ {!!} ■
  -- open import 
  -- _ = {!!} ≡[ i ]⟨ {!!} ⟩ {!!} ∎

  --_≡⟨_⟩_ : (x : A) → x ≡ y → y ≡ z → x ≡ z
  --_ ≡⟨ x≡y ⟩ y≡z = x≡y ∙ y≡z

  -- for a list of unicode symbols in agda, see https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html
  infix  3 _◼
  infixr 2 _⇒⟨_⟩_

  _⇒⟨_⟩_ : ∀{ℓ ℓ' ℓ''} {Q : Type ℓ'} {R : Type ℓ''} → (P : Type ℓ) → (P → Q) → (Q → R) → (P → R)
  _ ⇒⟨ pq ⟩ qr = qr ∘ pq

  _◼ : ∀{ℓ} (A : Type ℓ) → A → A
  _ ◼ = λ x → x

  f : Carrier → Carrier
  f x with +-inv x
  ... | fst₁ , snd₁ = {!!}

  -- see https://agda.readthedocs.io/en/latest/language/instance-arguments.html
  it : ∀ {a} {A : Type a} → {{A}} → A
  it {{x}} = x -- instance search

  -- Lemma 4.1.6.3
  --   TODO: there is equational resoning in Cubical.Foundations.Id, use this
  --     P = _ ≡⟨ _ ⟩ _ ∎
  --     P = _ ≡[ i ] _ ∎
  --       syntax ≡⟨⟩-syntax x (λ i → B) y = x ≡[ i ]⟨ B ⟩ y
  --   in general this module offers a lot of useful equational machinery
  --     it already makes use of path concatenation with ∙ and ∙∙
  --   there is also Cubical.Foundations.Equiv
  --     P = _ ≃⟨ _ ⟩ _ ■
  ·-#-extensional-case1 : ∀(w x y z : Carrier) → w · x # y · z → w · x # w · z → x # z
  ·-#-extensional-case1 w x y z w·x#y·z w·x#w·z =
    let P : w · x + - w · x # w · z + - w · x
        P =   +-#-compatible _ _ (- (w · x)) w·x#w·z
        Q : 0f # w · (z + - x)
        Q =   transport (λ i →  (fst (+-inv (w · x)) i) # a·b-a·c≡a·[b-c] w z x i) P
        instance -- NOTE: this allows to use ⁻¹ᶠ without an instance argument
          q = #-sym _ _ Q
        -- see https://agda.readthedocs.io/en/latest/language/instance-arguments.html
        it : ∀ {a} {A : Type a} → {{A}} → A
        it {{x}} = x -- instance search
        R : w · (z - x) · (w · (z - x)) ⁻¹ᶠ ≡ 1f
        R =   ·-rinv (w · (z - x)) it -- (#-sym _ _ Q)
        S : (z + - x) · w · (w · (z + - x)) ⁻¹ᶠ ≡ 1f
        S =   transport (λ i → ·-comm w (z - x) i · (w · (z - x)) ⁻¹ᶠ ≡ 1f) R
        T : (z + - x) · (w · (w · (z + - x)) ⁻¹ᶠ) ≡ 1f
        T =   transport (λ i → ·-assoc (z + - x) w ((w · (z + - x)) ⁻¹ᶠ) (~ i) ≡ 1f) S
        U : z - x # 0f
        U =   fst (·-inv-back _ _ T)
        V : z - x + x # 0f + x
        V = (+-#-compatible _ _ x) (fst (·-inv-back _ _ T)) -- (+-#-compatible _ _ x U)
        -- workflow:
        --   start with `transport (λ i → z - x + x # 0f + x) V` in the hole (i.e. a constant transport)
        --   and then fiddle with the path and look what comes out
        W : z + (- x + x) # x
        W =   transport (λ i → +-assoc z (- x) x (~ i) # snd (+-identity x) i) V
        X : z + 0f # x
        X =   transport (λ i → z + snd (+-inv x) i # x) W
    in (#-sym _ _ (transport (λ i → fst (+-identity z) i # x) X))
  ·-#-extensional : ∀(w x y z : Carrier) → w · x # y · z → (w # y) ⊎ (x # z)
  ·-#-extensional w x y z w·x#y·z with #-cotrans _ _ w·x#y·z (w · z)
  ... | inl w·x#w·z =    inr (·-#-extensional-case1 w x y z w·x#y·z w·x#w·z) -- first case
  ... | inr w·z#y·z = let z·w≡z·y = (transport (λ i → ·-comm w z i # ·-comm y z i) w·z#y·z)
                      in inl (·-#-extensional-case1 _ _ _ _ z·w≡z·y z·w≡z·y) -- second case reduced to first case

  -- for an example to use equational reasoning in this topic, see https://github.com/felixwellen/cubical/blob/field/Cubical/Structures/Field.agda
  -- we do not do equational reasoning here but "implicational" reasoning instead
  -- the special syntax should make it more readable and omit giving names to every intermediate step
  -- but giving names to intermediates in a `let` or `where` clause might just be the way it's done
  --   c.f. with more elaborate proofs e.g. in https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#combining-structures
  -- also see the elaborate proof in https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#381519
  --   which uses equational reasoning, but still names the single steps i, ii, iii, iv, v, vi, ... and resolves them in a `where` clause
  -- also see https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#391417
  -- "We consider rings without unit, called rngs, and with unit, called rings."
  -- this work of Martín Escardó was prepared for the
  --   Midlands Graduate School in the Foundations of Computing Science (University of Birmingham, UK, 14 - 18 April, 2019)
  --     http://events.cs.bham.ac.uk/mgs2019/
  --   Introductory Courses:
  --   - Lambda Calculus (course notes)               by Venanzio Capretta (University of Nottingham)
  --   - Category Theory (course notes)               by Thorsten Altenkirch (University of Nottingham)
  --   - Univalent Type Theory in Agda (course notes) by Martín Escardó (University of Birmingham)

  ·-#-extensional-case1' : ∀(w x y z : Carrier) → w · x # y · z → w · x # w · z → x # z
  ·-#-extensional-case1' w x y z w·x#y·z w·x#w·z =
    let
      instance -- this allows to use ⁻¹ᶠ without an instance argument
        w·[z-x]#0f =
          ( w · x         # w ·  z         ⇒⟨ +-#-compatible _ _ (- (w · x)) ⟩
            w · x - w · x # w ·  z - w · x ⇒⟨ transport (λ i →  (fst (+-inv (w · x)) i) # a·b-a·c≡a·[b-c] w z x i) ⟩
                       0f # w · (z - x)    ⇒⟨ #-sym _ _ ⟩
            w ·   (z - x) # 0f             ◼) w·x#w·z
    in (     w  · (z - x) # 0f                      ⇒⟨ (λ _ → ·-rinv (w · (z - x)) it ) ⟩  -- NOTE: "plugging in" the instance did not work, ∴ `it`
             w  · (z - x) · (w · (z - x)) ⁻¹ᶠ  ≡ 1f ⇒⟨ transport (λ i → ·-comm w (z - x) i · (w · (z - x)) ⁻¹ᶠ ≡ 1f) ⟩
        (z - x) ·  w      · (w · (z - x)) ⁻¹ᶠ  ≡ 1f ⇒⟨ transport (λ i → ·-assoc (z - x) w ((w · (z - x)) ⁻¹ᶠ) (~ i) ≡ 1f) ⟩
        (z - x) · (w      · (w · (z - x)) ⁻¹ᶠ) ≡ 1f ⇒⟨ fst ∘ (·-inv-back _ _)  ⟩
           z    - x       # 0f                      ⇒⟨ +-#-compatible _ _ x ⟩
          (z    - x) + x  # 0f + x                  ⇒⟨ transport (λ i → +-assoc z (- x) x (~ i) # snd (+-identity x) i) ⟩
           z + (- x  + x) #      x                  ⇒⟨ transport (λ i → z + snd (+-inv x) i # x) ⟩
           z +      0f    # x                       ⇒⟨ transport (λ i → fst (+-identity z) i # x) ⟩
           z              # x                       ⇒⟨ #-sym _ _ ⟩
           x              # z                       ◼) it -- conceptually we would plug `w·[z-x]#0f` in, but this breaks the very first step

-- 
-- Lemma 4.1.7.
-- Given a strict partial order < on a set X:
-- 1. we have an apartness relation defined by
--    x # y := (x < y) ∨ (y < x), and
-- 2. we have a preorder defined by
--    x ≤ y := ¬(y < x).
-- 
-- Definition 4.1.8.
-- Let (A, ≤) be a partial order, and let min, max : A → A → A be binary operators on A. We say that (A, ≤, min, max) is a lattice if min computes greatest lower bounds in the sense that for every x, y, z : A, we have
--   z ≤ min(x,y) ⇔ z ≤ x ∧ z ≤ y,
-- and max computes least upper bounds in the sense that for every x, y, z : A, we have
--   max(x,y) ≤ z ⇔ x ≤ z ∧ y ≤ z.
-- 
-- Remark 4.1.9.
-- 1. From the fact that (A, ≤, min, max) is a lattice, it does not follow that for every x and y, min(x,y) = x ∨ min(x,y) = y. However, we can characterize min as
--   z < min(x,y) ⇔ z < x ∨ z < y
--   and similarly for max, see Lemma 6.7.1.
-- 2. In a partial order, for two fixed elements a and b, all joins and meets of a, b are equal, so that Lemma 2.6.20 the type of joins and the type of meets are propositions. Hence, providing the maps min and max as in the above definition is equivalent to the showing the existenceof all binary joins and meets.
-- 
-- The following definition is modified from on The Univalent Foundations Program [89, Definition 11.2.7].
-- 
-- Definition 4.1.10.
-- An ordered field is a set F together with constants 0, 1, operations +, ·, min, max, and a binary relation < such that:
-- 1. (F, 0, 1, +, ·) is a commutative ring with unit;
-- 2. < is a strict order;
-- 3. x : F has a multiplicative inverse iff x # 0, recalling that # is defined as in Lemma 4.1.7;
-- 4. ≤, as in Lemma 4.1.7, is antisymmetric, so that (F, ≤) is a partial order;
-- 5. (F, ≤, min, max) is a lattice.
-- 6. for all x, y, z, w : F:
--    x + y < z + w ⇒ x < z ∨ y < w, (†)
--    0 < z ∧ x < y ⇒ x z < y z.     (∗)
-- Our notion of ordered fields coincides with The Univalent Foundations Program [89, Definition 11.2.7].
-- 
-- Lemma 4.1.11.
-- In the presence of the first five axioms of Definition 4.1.10, conditions (†) and (∗) are together equivalent to the condition that for all x, y, z : F,
--  1. x ≤ y ⇔ ¬(y < x),
--  2. x # y ⇔ (x < y) ∨ (y < x)
--  3. x ≤ y ⇔ x + z ≤ y + z,
--  4. x < y ⇔ x + z < y + z,
--  5. 0 < x + y ⇒ 0 < x ∨ 0 < y,
--  6. x < y ≤ z ⇒ x < z,
--  7. x ≤ y < z ⇒ x < z,
--  8. x ≤ y ∧ 0 ≤ z ⇒ x z ≤ y z,
--  9. 0 < z ⇒ (x < y ⇔ x z < y z),
-- 10. 0 < 1.


-- we have in cubical
--   import Cubical.HITs.Rationals.HITQ
--     ℚ as a higher inductive type
--   import Cubical.HITs.Rationals.QuoQ
--     ℚ as a set quotient of ℤ × ℕ₊₁ (as in the HoTT book)
--   import Cubical.HITs.Rationals.SigmaQ
--     ℚ as the set of coprime pairs in ℤ × ℕ₊₁
