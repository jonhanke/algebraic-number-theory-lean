/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.WeilBNT.AdeleSelfDuality
import NumberFieldKB.WeilBNT.AdeleAnnihilator
import NumberFieldKB.WeilBNT.IdeleClassFiniteness
import NumberFieldKB.WeilBNT.FunctionField.ZetaFinal
import NumberFieldKB.WeilBNT.FunctionField.HeckeRamFE

/-!
# Headline statements of NumberFieldKB 0.2.0: Weil, Basic Number Theory

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

/-! ## Weil, *Basic Number Theory*: number fields -/

open IsDedekindDomain NumberField in
open NumberFieldKB.WeilBNT in
/-- **Self-duality of the adeles** (Weil, *Basic Number Theory*, Chapter IV, §2, Theorem 3, for $E = K$): let $\chi$ be
the standard character of $\mathbb A_K$ (`chiA K`, trivial on $K$). Every continuous character $\psi$ of the additive
group $\mathbb A_K$ is $x \mapsto \chi(ax)$ for a unique $a \in \mathbb A_K$; and $\chi(a\xi) = 1$ for every $\xi \in K$ if
and only if $a \in K$ (the annihilator of $K$ is $K$). -/
theorem adeles_selfDual (K : Type) [Field K] [NumberField K] :
    (∀ ψ : AddChar (AdeleRing (𝓞 K) K) Circle, Continuous ψ →
      ∃! a : AdeleRing (𝓞 K) K, ∀ x, ψ x = chiA K (a * x)) ∧
    ∀ a : AdeleRing (𝓞 K) K,
      ((∀ ξ : K, chiA K (a * algebraMap K (AdeleRing (𝓞 K) K) ξ) = 1) ↔
        a ∈ Set.range (algebraMap K (AdeleRing (𝓞 K) K))) :=
  sorry

open IsDedekindDomain NumberField in
open NumberFieldKB.WeilBNT in
/-- **Weil, *Basic Number Theory*, Chapter IV, §4, Theorem 7** (number fields): for every set $S$ of finite primes of $K$,
with $P$ the set of the infinite places and $S$, the group $\mathbb A_K^\times / K^\times\,\Omega(P)$ is finite, where
$\Omega(P)$ (`omega K S`) is the group of ideles that are units at every finite prime outside $S$. For $S = \emptyset$
this is the finiteness of the class number. -/
theorem idele_classes_finite (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    Finite (IdeleGroup (𝓞 K) K ⧸ (IdeleGroup.principalSubgroup (𝓞 K) K ⊔ omega K S)) :=
  sorry

/-! ## Weil, *Basic Number Theory*: function fields -/

open scoped Polynomial in
open NumberFieldKB.WeilBNT.FF in
open Divisor Rep in
/-- **The zeta function of a function field** (Weil, *Basic Number Theory*, Chapter VII, §6, Theorem 4): let $k$ be a
function field of one variable with field of constants $\mathbb F_q$, of genus $g$, and $Z(u) = \sum_{\mathfrak a \ge 0}
u^{\deg \mathfrak a}$ (so $\zeta_k(s) = Z(q^{-s})$). Then $Z(u)(1 - u)(1 - qu) = P(u)$ with $P \in \mathbb Z[u]$ of
degree $2g$, $P(0) = 1$, $P(1) = h$ the number of divisor classes of degree $0$, and $P(u) = q^g u^{2g} P(1/qu)$ (stated
on the coefficients). -/
theorem zeta_functionField {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
    [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k] (hc : IsConstantField Fq k) :
    ∃ P : ℤ[X], P.natDegree = 2 * genus Fq k ∧ P.eval 0 = 1 ∧
      P.eval 1 = Nat.card (ClassGroup0 Fq k) ∧
      zetaSeries Fq k * ((1 - PowerSeries.X) * (1 - (Nat.card Fq : PowerSeries ℤ) * PowerSeries.X)) =
        (P : PowerSeries ℤ) ∧
      ∀ i ≤ 2 * genus Fq k,
        P.coeff (2 * genus Fq k - i) * (Nat.card Fq : ℤ) ^ i = (Nat.card Fq : ℤ) ^ genus Fq k * P.coeff i :=
  sorry

open NumberFieldKB.WeilBNT.FF in
/-- **Hecke $L$-functions of a function field** (Weil, *Basic Number Theory*, Chapter VII, §7, Theorem 6, ramified case):
for a quasicharacter $\omega$ of the idele class group of a function field $k$ with field of constants $\mathbb F_q$,
with conductor $\mathfrak f \ne 0$, the series $L(u, \omega)$ is a polynomial in $u$ of degree exactly
$2g - 2 + \deg \mathfrak f$. -/
theorem heckeL_functionField_polynomial {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
    [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]
    (ω : FFHeckeCharacter Fq k) (hc : IsConstantField Fq k) (hf : ω.conductor ≠ 0) :
    ∃ P : Polynomial ℂ, (P.natDegree : ℤ) = 2 * (genus Fq k : ℤ) - 2 + Divisor.deg ω.conductor ∧
      (P : PowerSeries ℂ) = ω.lSeriesF :=
  sorry

end NumberFieldKB.Headlines
