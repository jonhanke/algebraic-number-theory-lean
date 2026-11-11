/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneANT.Ch6FermatThm
import NumberFieldKB.MilneANT.Ch8Unconditional
import NumberFieldKB.MilneANT.Ch7Ostrowski

/-!
# Headline statements of NumberFieldKB 0.2.1: Milne, Algebraic Number Theory

The main results of the library, one theorem each, with every proof a deliberate `sorry`: to check what is claimed,
read this file. `Solution.lean` proves the same statements from the library, and `lake comparator` (configured by
`comparator.json`) checks that each proved statement is exactly the one here and uses only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

Each statement is the library's statement, copied, except where its docstring says otherwise: a named statement in the
conclusion (a `Prop` structure of the library) is unfolded, and where the library defines a continuation by cases the
headline states the existence of a continuation with the stated properties. The statements were not yet reviewed by a
human (see the README).

## Definitions used

Besides Mathlib, the statements use these definitions of the library (and of the quadratic-forms library it builds
on); a reader checking a statement should check these too:

* `NumberFieldKB.MilneANT.galPerm`
* `NumberFieldKB.MilneANT.placeOf`
* `NumberFieldKB.MilneANT.MilnePlace`
* `NumberFieldKB.MilneANT.placeAbv`
* `NumberFieldKB.WeilBNT.chiA`
* `NumberFieldKB.WeilBNT.chiInf`
* `NumberFieldKB.WeilBNT.chiFin`
* `NumberFieldKB.WeilBNT.omega`
* `NumberField.IdeleGroup.principalSubgroup`
* `NumberFieldKB.WeilBNT.FF.IsConstantField`
* `NumberFieldKB.WeilBNT.FF.genus`
* `NumberFieldKB.WeilBNT.FF.ClassGroup0`
* `NumberFieldKB.WeilBNT.FF.zetaSeries`
* `NumberFieldKB.WeilBNT.FF.FFHeckeCharacter`
* `NumberFieldKB.WeilBNT.FF.FFHeckeCharacter.conductor`
* `NumberFieldKB.WeilBNT.FF.FFHeckeCharacter.lSeriesF`
* `NumberFieldKB.SchwartzBruhat`
* `NumberFieldKB.SchwartzBruhat.fourier`
* `NumberFieldKB.HeckeCharacter`
* `NumberFieldKB.HeckeCharacter.shift`
* `NumberFieldKB.globalZeta`
* `QuadFormsKB.Tamagawa.Measure.Weil.Adeles`
* `NumberFieldKB.HeckeCharacter.normPow`
* `NumberFieldKB.HeckeL.completedHeckeL`
* `NumberFieldKB.HeckeL.condDisc`
* `NumberFieldKB.HeckeL.gammaInf`
* `NumberFieldKB.HeckeL.heckeL`
* `NumberFieldKB.HeckeL.IsPoleFree`
* `NumberFieldKB.HeckeL.rootNumber`
* `NumberFieldKB.HeckeCharacter.IsUnitary`
* `NumberFieldKB.Pontryagin.IsDualMeasure`
* `NumberFieldKB.WeilBNT.AbstractFourier.IsAdmissible`
* `NumberFieldKB.WeilBNT.AbstractFourier.fourierLCA`
* `NumberFieldKB.Pontryagin.annihilator`
* `NumberFieldKB.ModularCurves.X0`
* `NumberFieldKB.MilneEC.IsGenus`
* `NumberFieldKB.MilneEC.genus`
* `NumberFieldKB.MilneEC.Divisor.ell`
* `NumberFieldKB.MilneEC.V.evalJJN`
* `NumberFieldKB.MilneEC.V.jFun`
* `NumberFieldKB.MilneEC.V.jN`
* `NumberFieldKB.MilneEC.V.IsModularFunction`
* `NumberFieldKB.MilneEC.V.IsMeromorphicOnUpperHalfPlane`
* `NumberFieldKB.MilneEC.V.IsMeromorphicAtImInfty`
* `NumberFieldKB.MilneEC.V.g4`
* `NumberFieldKB.MilneEC.V.g6`
* `NumberFieldKB.MilneEC.V.discr`
* `NumberFieldKB.MilneCFT.Ch4.BrauerGroup`
* `NumberFieldKB.MilneCFT.Ch4.BrauerGroup.mk`
* `NumberFieldKB.MilneCFT.LocalCFT.FiniteAbelianExt`
* `NumberFieldKB.MilneCFT.LocalCFT.ltTower`
* `NumberFieldKB.MilneCFT.LocalCFT.ltField`
* `NumberFieldKB.MilneCFT.LocalCFT.unramifiedClosure`
* `NumberFieldKB.MilneCFT.Ch8.cubicAffineCount`
* `NumberFieldKB.MilneCFT.Modulus`
* `NumberFieldKB.MilneCFT.RayClassGroup`
* `NumberFieldKB.MilneCFT.weberLSeries`
* `NumberFieldKB.MilneCFT.idealRayClass`
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
  sorry

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
  sorry

open NumberField in
open NumberFieldKB.MilneANT in
/-- **The places of a number field** (Milne, *Algebraic Number Theory*, Theorem 7.14): every nontrivial absolute value
on a number field $K$ is equivalent to exactly one of the absolute values attached to a nonzero prime ideal, a real
embedding, or a conjugate pair of complex embeddings. In Lean: the map from Mathlib's finite and infinite places to the
equivalence classes of nontrivial absolute values on $K$ (`MilnePlace K`) is a bijection. -/
theorem ostrowski_numberField (K : Type) [Field K] [NumberField K] : Function.Bijective (placeOf K) :=
  sorry

end NumberFieldKB.Headlines
