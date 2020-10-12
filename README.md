

This is an attempt to make use of [Booij 2020 - Analysis in Univalent Type Theory](https://abooij.blogspot.com/p/phd-thesis.html) to get a _cauchy-complete archimedean field_ into `--cubical` Agda as [suggested in a Github issue](https://github.com/agda/cubical/issues/286). I am quite verbosely copying from [chapter 4](chapter-4-1.md) of Booij's thesis.

[UPDATE (12.10.2020): the "main" file is currently broken. There is [Number.Instances.QuoQ](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.QuoQ.Instance.html) instead.]

~~The main file is [SyntheticReals.agda](agda/SyntheticReals.agda) that is also [rendered in clickable html](https://mchristianl.github.io/synthetic-reals/html/SyntheticReals.html) and [a literate agda version](https://mchristianl.github.io/synthetic-reals/html/) is in the making.~~

## NEWS / current development status

### 12.10.2020

there are now instance proofs to replace the postulates
- [Cubical.Data.Nat](https://mchristianl.github.io/synthetic-reals/html/Cubical.Data.Nat.html) being an instance of a [LinearlyOrderedCommSemiring](https://mchristianl.github.io/synthetic-reals/html/Number.Bundles2.html#LinearlyOrderedCommSemiring) in [Number.Instances.Nat](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.Nat.html#bundle)
- [Cubical.Data.Int](https://mchristianl.github.io/synthetic-reals/html/Cubical.Data.Int.html) being an instance of a [LinearlyOrderedCommRing](https://mchristianl.github.io/synthetic-reals/html/Number.Bundles2.html#LinearlyOrderedCommRing) in [Number.Instances.Int](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.Int.html#ℤbundle)
- ~~[Cubical.HITs.Ints.QuoInt](https://mchristianl.github.io/synthetic-reals/html/Cubical.HITs.Ints.QuoInt.html) being an instance of a [LinearlyOrderedCommRing](https://mchristianl.github.io/synthetic-reals/html/Number.Bundles2.html#LinearlyOrderedCommRing) in [Number.Instances.QuoIntUnfinished](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.QuoIntUnfinished.html)~~
  - I could not obtain all necessary properties, but with a hint from Anders Mörtberg, I was able to proof the `LinearlyOrderedCommRing`-structure of `Int` equal to the `LinearlyOrderedCommRing`-structure of `QuoInt`
  - therefore, there is an instance proof of `Cubical.HITs.Ints.QuoInt` being an instance of a `LinearlyOrderedCommRing` in [Number.Instances.QuoIntFromInt](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.QuoIntFromInt.html#bundle)
  - [Cubical.HITs.Ints.QuoInt](https://mchristianl.github.io/synthetic-reals/html/Cubical.HITs.Ints.QuoInt.html) being an instance of a [LinearlyOrderedCommRing](https://mchristianl.github.io/synthetic-reals/html/Number.Bundles2.html#LinearlyOrderedCommRing) and more properties in [Number.Instances.QuoInt](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.QuoInt.html)
- and finally, there is [Cubical.HITs.Rationals.QuoQ](https://mchristianl.github.io/synthetic-reals/html/Cubical.HITs.Rationals.QuoQ.html) being an instance of a [LinearlyOrderedField](https://mchristianl.github.io/synthetic-reals/html/Number.Bundles2.html#LinearlyOrderedField) in [Number.Instances.QuoQ](https://mchristianl.github.io/synthetic-reals/html/Number.Instances.QuoQ.Instance.html#ℚbundle)

to make the usage a bit more convenient, there are little "preludes" with renamed properties for
- [Number.Prelude.Nat](https://mchristianl.github.io/synthetic-reals/html/Number.Prelude.Nat.html)
- [Number.Prelude.Int](https://mchristianl.github.io/synthetic-reals/html/Number.Prelude.Int.html) (although this should not be used because `QuoInt` is preferred)
- [Number.Prelude.QuoInt](https://mchristianl.github.io/synthetic-reals/html/Number.Prelude.QuoInt.html)
- (`Number.Prelude.QuoQ` comes next)

## developments on-top of real numbers

[UPDATE (12.10.2020): this remains valid but it is currently broken as the supporting layer is being rewritten]

Not all necessary machinery is already available in the cubical standard library. Nonetheless, we provide `record`s for several number types that are [backed by postulates](https://mchristianl.github.io/synthetic-reals/html/Number.Postulates.html) [UPDATE (12.10.2020): we have some "real" instance proofs now]. Ideally these postulates will be replaced by actual implementations from the standard library when they are available.

Considered number types are ℕ, ℤ, ℚ, ℝ and ℂ. Their operations are abbreviated with a superscript:
- operations on ℕ are abbreviated with `ⁿ`, e.g. `_<ⁿ_`
- operations on ℤ are abbreviated with `ᶻ`, e.g. `_<ᶻ_`
- operations on ℚ are abbreviated with `ᶠ`, e.g. `_<ᶠ_`
- operations on ℝ are abbreviated with `ʳ`, e.g. `_<ʳ_`
- operations on ℂ are abbreviated with `ᶜ`, e.g. `_<ᶜ_`

Additional naming occurs for:
- operations on types are annotated with `ᵗ` when types are not the "default", e.g. `_ᵗ⇒_` mapping a type and an hProp into an hProp
- operations on sets and hProps of sets are annotated with `ˢ` when sets are not the "default", e.g. `[_]_≡ˢ_` as an alternative to `_≡ₚ_`
- operations on hProps and instance of hProps are annotated with `ᵖ`, e.g. `isIrreflᵖ`
- homogeneous variants are annotated with `ʰ`, inhomogeneous variants are annotated  with `ⁱ` or not annotated at all (inhomogeneous being the "default")
- implicit or instance variants are also annotated with `ⁱ`
- other naming scheme ideas are
  - `f-preserves-R`, `f-reflects-R`, `P-implies-Q`, `[P⇒¬Q]-implies-[Q⇒¬P]`, `P+Q+R-implies-A+B`, `P-≡-Q`, `P+Q+R-≡-A+B`, `P-⇔-Q`
  - where `P`, `Q`, `R`, `A` and `B` are "short names" (e.g. "irrefl") which have the type `[ isIrreflᵖ _<_ ]`
  - although somehow `[P⇒¬Q]⇔[Q⇒¬P]` for `P` and `Q` being just "P" and "Q" seems also appropriate
  - e.g. `irrefl+tight-implies-¬#-≡-≡ᵖ : [ isIrreflᵖ _#_ ] → [ isTightᵖ''' _#_ ] → ∀ a b → ¬ᵖ (a # b) ≡ (a ≡ₚ b)`

The general idea is to attach subtype properties to a number. [We have](https://mchristianl.github.io/synthetic-reals/html/Summary.html) the following common number types:

```agda
iso00 : [ℕ]   ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] Unit
iso01 : [ℕ⁺⁻] ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] x  #ⁿ 0ⁿ
iso02 : [ℕ₀⁺] ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] 0ⁿ ≤ⁿ x
iso03 : [ℕ⁺]  ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] 0ⁿ <ⁿ x
iso04 : [ℕ₀⁻] ≅ Σ[ x ∈ Cubical.Data.Nat.ℕ ] x  ≤ⁿ 0ⁿ
iso05 : [ℤ]   ≅ Σ[ x ∈ ℤ.Carrier          ] Lift {j = ℤℓ'} Unit
iso06 : [ℤ⁺⁻] ≅ Σ[ x ∈ ℤ.Carrier          ] x  #ᶻ 0ᶻ
iso07 : [ℤ₀⁺] ≅ Σ[ x ∈ ℤ.Carrier          ] 0ᶻ ≤ᶻ x
iso08 : [ℤ⁺]  ≅ Σ[ x ∈ ℤ.Carrier          ] 0ᶻ <ᶻ x
iso09 : [ℤ⁻]  ≅ Σ[ x ∈ ℤ.Carrier          ] x  <ᶻ 0ᶻ
iso10 : [ℤ₀⁻] ≅ Σ[ x ∈ ℤ.Carrier          ] x  ≤ᶻ 0ᶻ
iso11 : [ℚ]   ≅ Σ[ x ∈ ℚ.Carrier          ] Lift {j = ℚℓ'} Unit
iso12 : [ℚ⁺⁻] ≅ Σ[ x ∈ ℚ.Carrier          ] x  #ᶠ 0ᶠ
iso13 : [ℚ₀⁺] ≅ Σ[ x ∈ ℚ.Carrier          ] 0ᶠ ≤ᶠ x
iso14 : [ℚ⁺]  ≅ Σ[ x ∈ ℚ.Carrier          ] 0ᶠ <ᶠ x
iso15 : [ℚ⁻]  ≅ Σ[ x ∈ ℚ.Carrier          ] x  <ᶠ 0ᶠ
iso16 : [ℚ₀⁻] ≅ Σ[ x ∈ ℚ.Carrier          ] x  ≤ᶠ 0ᶠ
iso17 : [ℝ]   ≅ Σ[ x ∈ ℝ.Carrier          ] Lift {j = ℝℓ'} Unit
iso18 : [ℝ⁺⁻] ≅ Σ[ x ∈ ℝ.Carrier          ] x  #ʳ 0ʳ
iso19 : [ℝ₀⁺] ≅ Σ[ x ∈ ℝ.Carrier          ] 0ʳ ≤ʳ x
iso20 : [ℝ⁺]  ≅ Σ[ x ∈ ℝ.Carrier          ] 0ʳ <ʳ x
iso21 : [ℝ⁻]  ≅ Σ[ x ∈ ℝ.Carrier          ] x  <ʳ 0ʳ
iso22 : [ℝ₀⁻] ≅ Σ[ x ∈ ℝ.Carrier          ] x  ≤ʳ 0ʳ
iso23 : [ℂ]   ≅ Σ[ x ∈ ℂ.Carrier          ] Lift {j = ℂℓ'} Unit
iso24 : [ℂ⁺⁻] ≅ Σ[ x ∈ ℂ.Carrier          ] x  #ᶜ 0ᶜ
```

Here, all `[…]` types are abbreviations for one single `Number` type family

```agda
data Number (p : NumberProp) : Type (NumberLevel (fst p)) where
  _,,_ : (x : NumberKindInterpretation (fst p))
       → PositivityLevelInterpretation (fst p) (snd p) x
       → Number p
```

This allows to define the operations `_+_`, `-_`, `_·_`, `_⁻¹`, `_<_`, `_≤_`, `_#_`, `min`, `max` and `abs` [on a general `Number` type family](https://mchristianl.github.io/synthetic-reals/html/Number.Base.html) in a way that it makes use of the specific operations for the underlying, concrete number type. The special behavior of these operations is given [by tables](https://mchristianl.github.io/synthetic-reals/html/Number.Operations.Specification.html)

```agda
test201 : [ℕ⁺] → [ℝ₀⁺] → [ℝ]
-- As-patterns (or @-patterns) go well with resolving things in our approach
test201 n@(nn ,, np) r@(rn ,, rp) = let
-- generic operations are provided
-- q : [ℕ⁺]
-- z : [ℝ₀⁺]
   q = n + n
   z = r + r

-- we can project-out the underlying number of a `Number` with `num`
-- zʳ : ℝ
   zʳ = num z

-- and we can project-out the property of a `Number` with `prp`
-- zp : 0ʳ ≤ʳ (rn +ʳ rn)
   zp = prp z

-- since the generic `_+_` makes use of `_+ʳ_` on ℝ, we get definitional equality
   _ : zʳ ≡ rn +ʳ rn
   _ = refl

-- we can turn a generic number into a Σ pair with `pop`
-- qʳ   : ℕ₀
-- qʳ   = nn +ⁿ nn
-- qp   : 0ⁿ <ⁿ (nn +ⁿ nn)
-- qp   = +-<-<-implies-<ʳ nn nn np np
   (qʳ , qp) = pop q

-- and we can create a number with `_,,_`
-- this needs some type annotation for help
   q' : typeOf q
   q' = qʳ ,, qp

-- r is nonnegative from [ℝ₀⁺], [1ʳ] is positive from [ℝ⁺]
-- and _+_ makes use of the fact that "positive + nonnegative = positive"
-- y : [ℝ⁺]
-- y = (rn +ʳ 1ʳ) ,, +-≤-<-implies-<ʳ rn 1ʳ rp 0<1
   y =  r + [1ʳ]

-- _+_ automatically coerces n from ℕ⁺ to ℝ⁺
-- and uses the fact that "positive + nonnegative = positive"
-- n+r : [ℝ⁺]
-- n+r = (ℕ↪ℝ nn +ʳ rn) ,, +-<-≤-implies-<ʳ (ℕ↪ℝ nn) rn (coerce-ℕ↪ℝ (nn ,, np)) rp
   n+r = n + r

-- generic relations like _<_ also make use of their underlying relations
-- and therefore we also get definitional equality, no matter how the relation is stated
   pp   : [1ʳ] <      (r  + [1ʳ])
   pp   = {!!}
   pp'  :  1ʳ  <ʳ num (r  + [1ʳ])
   pp'  = {!!}
   pp'' :  1ʳ  <ʳ     (rn +ʳ 1ʳ )
   pp'' = {!!}
   _ : (pp ≡ pp') × (pp ≡ pp'')
   _ = refl , refl
   in {!!}
```

The coercions rely on inclusions between ℕ, ℤ, ℚ, ℝ and ℂ [UPDATE (12.10.2020): this approach is going to change]

```agda
ℕ↪ℤ : ℕ → ℤ
ℕ↪ℚ : ℕ → ℚ
ℕ↪ℂ : ℕ → ℂ
ℕ↪ℝ : ℕ → ℝ
ℤ↪ℚ : ℤ → ℚ
ℤ↪ℝ : ℤ → ℝ
ℤ↪ℂ : ℤ → ℂ
ℚ↪ℝ : ℚ → ℝ
ℚ↪ℂ : ℚ → ℂ
ℝ↪ℂ : ℝ → ℂ

ℕ↪ℤinc : IsROrderedCommSemiringInclusion ℕ.bundle                       (record { ℤ.Bundle ℤ.bundle }) ℕ↪ℤ
ℕ↪ℚinc : IsROrderedCommSemiringInclusion ℕ.bundle                       (record { ℚ.Bundle ℚ.bundle }) ℕ↪ℚ
ℕ↪ℂinc : Isℕ↪ℂ                           ℕ.bundle                       ℂ.bundle                       ℕ↪ℂ
ℕ↪ℝinc : IsROrderedCommSemiringInclusion ℕ.bundle                       (record { ℝ.Bundle ℝ.bundle }) ℕ↪ℝ
ℤ↪ℚinc : IsROrderedCommRingInclusion     ℤ.bundle                       (record { ℚ.Bundle ℚ.bundle }) ℤ↪ℚ
ℤ↪ℝinc : IsROrderedCommRingInclusion     ℤ.bundle                       (record { ℝ.Bundle ℝ.bundle }) ℤ↪ℝ
ℤ↪ℂinc : Isℤ↪ℂ                           ℤ.bundle                       ℂ.bundle                       ℤ↪ℂ
ℚ↪ℝinc : IsROrderedFieldInclusion        ℚ.bundle                       (record { ℝ.Bundle ℝ.bundle }) ℚ↪ℝ
ℚ↪ℂinc : IsRFieldInclusion               (record { ℚ.Bundle ℚ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℚ↪ℂ
ℝ↪ℂinc : IsRFieldInclusion               (record { ℝ.Bundle ℝ.bundle }) (record { ℂ.Bundle ℂ.bundle }) ℝ↪ℂ
```
