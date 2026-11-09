/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangUncond
import NumberFieldKB.MilneCFT.Ch8.GaussCubicUncond
import NumberFieldKB.MilneCFT.Ch5LSeriesExtends

/-!
# Headline statements of NumberFieldKB 0.2.0: Milne, Class Field Theory

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
* `NumberFieldKB.MilneCFT.LocalCFT.ltField`
* `NumberFieldKB.MilneCFT.Ch8.cubicAffineCount`
* `NumberFieldKB.MilneCFT.Modulus`
* `NumberFieldKB.MilneCFT.RayClassGroup`
* `NumberFieldKB.MilneCFT.weberLSeries`
* `NumberFieldKB.MilneCFT.idealRayClass`
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Milne, *Class Field Theory* -/

open NumberField IsDedekindDomain in
/-- **The Grunwald–Wang theorem** (Milne, *Class Field Theory*, Chapter VIII, Theorem 2.4): let $K$ be a number field,
$S$ a finite set of finite places and $T$ a finite set of infinite places, and for each $v \in S \cup T$ let
$\chi_v$ be a continuous character of finite order of $K_v^\times$; let $n$ be the least common multiple of their
orders. There is a continuous character $\psi$ of the idele class group $C_K$ whose restriction to $K_v^\times$ is
$\chi_v$ for all $v \in S \cup T$, and $\psi$ can be chosen of order exactly $n$ unless $2^t \mid n$ for some $t$
with $K(\zeta_{2^t})/K$ not cyclic (Wang's special case). (The library's named statement `Theorem2_4`, unfolded.) -/
theorem grunwaldWang {K : Type} [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) (T : Finset (InfinitePlace K))
    (χ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (χ' : ∀ w : InfinitePlace K, w.Completionˣ →* ℂˣ)
    (hχ : ∀ v ∈ S, Continuous (χ v) ∧ IsOfFinOrder (χ v)) (hχ' : ∀ w ∈ T, Continuous (χ' w) ∧ IsOfFinOrder (χ' w))
    (n : ℕ) (hn : ∀ v ∈ S, orderOf (χ v) ∣ n) (hn' : ∀ w ∈ T, orderOf (χ' w) ∣ n)
    (hlcm : ∀ m : ℕ, (∀ v ∈ S, orderOf (χ v) ∣ m) → (∀ w ∈ T, orderOf (χ' w) ∣ m) → n ∣ m) :
    ∃ ψ : IdeleClassGroup (𝓞 K) K →* ℂˣ, Continuous ψ ∧
      (∀ v ∈ S, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofAdicCompletion (𝓞 K) K v)) = χ v) ∧
      (∀ w ∈ T, ψ.comp ((QuotientGroup.mk' _).comp (IdeleGroup.ofCompletion (𝓞 K) K w)) = χ' w) ∧
      ((∀ t : ℕ, 2 ^ t ∣ n →
          IsCyclic (CyclotomicField (2 ^ t) K ≃ₐ[K] CyclotomicField (2 ^ t) K)) → orderOf ψ = n) :=
  sorry

open NumberFieldKB.MilneCFT.Ch8 in
/-- **A theorem of Gauss** (Milne, *Class Field Theory*, Chapter VIII, §10; Silverman–Tate IV.2): let $N_p$ be the
number of points of the projective curve $X^3 + Y^3 + Z^3 = 0$ over $\mathbb F_p$, so that the number of nonzero
solutions in $\mathbb F_p^3$ (`cubicAffineCount p`) is $(p-1)N_p$. If $p \not\equiv 1 \pmod 3$ then $N_p = p + 1$;
if $p \equiv 1 \pmod 3$ then $N_p = p + 1 + A$, where $A$ is the unique integer $\equiv 1 \pmod 3$ with
$4p = A^2 + 27B^2$ for some integer $B$. (The library's named statement `GaussCubicCount`, unfolded.) -/
theorem gauss_cubicCurve_count (p : ℕ) [Fact p.Prime] :
    (p % 3 ≠ 1 → cubicAffineCount p = (p - 1) * (p + 1)) ∧
    (p % 3 = 1 → ∃ A B : ℤ, A % 3 = 1 ∧ 4 * p = A ^ 2 + 27 * B ^ 2 ∧
      (cubicAffineCount p : ℤ) = (p - 1) * (p + 1 + A) ∧
      ∀ A' B' : ℤ, A' % 3 = 1 → 4 * p = A' ^ 2 + 27 * B' ^ 2 → A' = A) :=
  sorry

open NumberField in
open NumberFieldKB.MilneCFT in
/-- **Weber $L$-series** (Milne, *Class Field Theory*, Chapter V, Theorem 2.4(b), in the corrected form: the book says
"converges for $\mathrm{Re}(s) > 0$", which fails in general for $[K:\mathbb Q] \ge 2$; the author of this library
confirmed "extends" as the intended reading): for a modulus $\mathfrak m$ of a number field $K$ and a nontrivial
character $\chi$ of the ray class group $C_\mathfrak m$, the series
$L(s,\chi) = \sum_{(\mathfrak a,\mathfrak m_0) = 1}\chi(\mathfrak a)N\mathfrak a^{-s}$ (`weberLSeries`) extends to a
holomorphic function on $\mathrm{Re}(s) > 0$ whose value at $s = 1$ is nonzero. (The library's named statement
`Theorem2_4bExtends`, unfolded; proved from the Hecke $L$-function of the attached Hecke character of finite order.) -/
theorem weberL_continuation {K : Type} [Field K] [NumberField K] (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (hχ : χ ≠ 1) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L {s : ℂ | 0 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → L s = weberLSeries m χ s) ∧ L 1 ≠ 0 :=
  sorry

end NumberFieldKB.Headlines
