/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneANT.Ch6FermatThm
import NumberFieldKB.MilneANT.Ch8Unconditional
import NumberFieldKB.MilneANT.Ch7Ostrowski

/-!
# Headline statements of NumberFieldKB 0.2.1: Milne, Algebraic Number Theory, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Milne, *Algebraic Number Theory* -/

open NumberField Polynomial in
/-- **Kummer's theorem** (Milne, *Algebraic Number Theory*, Theorem 6.8): if $p$ is an odd prime that does not divide
the class number of $\mathbb Q(\zeta_p)$, then $x^p + y^p = z^p$ has no solution in integers with $p \nmid xyz$. -/
theorem kummer_regular (p : ℕ) [Fact p.Prime] (hodd : p ≠ 2)
    (hreg : ¬ p ∣ classNumber (CyclotomicField p ℚ)) :
    ¬ ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧ ¬ (p : ℤ) ∣ x * y * z :=
  NumberFieldKB.MilneANT.theorem_6_8 p hodd hreg

open NumberField IsDedekindDomain Polynomial UniqueFactorizationMonoid in
open scoped Classical in
open NumberFieldKB.MilneANT in
/-- **Dedekind's theorem** (Milne, *Algebraic Number Theory*, Theorem 8.23): let $f$ be a monic polynomial over the
ring of integers of a number field $K$ and $\mathfrak p$ a prime such that $f$ is squarefree modulo $\mathfrak p$.
Then some element of the Galois group of $f$ over $K$, acting on the roots of $f$, has as cycle type the multiset of
the degrees of the irreducible factors of $f$ modulo $\mathfrak p$. -/
theorem dedekind_factorizationType {K : Type} [Field K] [NumberField K] (f : (𝓞 K)[X]) (hf : f.Monic)
    (𝔭 : HeightOneSpectrum (𝓞 K))
    (hsq : Squarefree (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))) :
    ∃ σ : (f.map (algebraMap (𝓞 K) K)).Gal,
      (galPerm (f.map (algebraMap (𝓞 K) K)) σ).partition.parts =
        (normalizedFactors (f.map (algebraMap (𝓞 K) 𝔭.asIdeal.ResidueField))).map natDegree :=
  NumberFieldKB.MilneANT.thm_8_23' f hf 𝔭 hsq

open NumberField in
open NumberFieldKB.MilneANT in
/-- **The places of a number field** (Milne, *Algebraic Number Theory*, Theorem 7.14): every nontrivial absolute value
on a number field $K$ is equivalent to exactly one of the absolute values attached to a nonzero prime ideal, a real
embedding, or a conjugate pair of complex embeddings. In Lean: the map from Mathlib's finite and infinite places to the
equivalence classes of nontrivial absolute values on $K$ (`MilnePlace K`) is a bijection. -/
theorem ostrowski_numberField (K : Type) [Field K] [NumberField K] : Function.Bijective (placeOf K) :=
  NumberFieldKB.MilneANT.thm_7_14_unconditional K

end NumberFieldKB.Headlines
