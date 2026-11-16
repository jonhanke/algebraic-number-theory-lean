/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.MilneEC.Ch1Bezout
import NumberFieldKB.MilneEC.Ch1Assoc
import NumberFieldKB.MilneEC.Ch4TwoDescent
import NumberFieldKB.MilneEC.Ch4Example57
import NumberFieldKB.MilneEC.Ch4bLangUnconditional
import NumberFieldKB.MilneEC.Ch4BSD

/-!
# Headline statements of NumberFieldKB 0.3.0: Milne, Elliptic Curves

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
* `NumberFieldKB.MilneEC.IsProjectivePlaneCurve`
* `NumberFieldKB.MilneEC.NoCommonComponent`
* `NumberFieldKB.MilneEC.projectivePoints`
* `NumberFieldKB.MilneEC.projIntersectionNumber`
* `NumberFieldKB.MilneEC.curveDegree`
* `NumberFieldKB.MilneEC.IsNonsingularCubic`
* `NumberFieldKB.MilneEC.CurvePoints`
* `NumberFieldKB.MilneEC.chordAdd`
* `NumberFieldKB.MilneEC.thirdPoint`
* `NumberFieldKB.MilneEC.cubicCurve`
* `NumberFieldKB.MilneEC.cubicDisc`
* `NumberFieldKB.MilneEC.rank`
* `NumberFieldKB.MilneEC.ContH1`
* `NumberFieldKB.MilneEC.contCocycles`
* `NumberFieldKB.MilneEC.contCoboundaries`
* `NumberFieldKB.MilneEC.Conjecture10_5Corrected`
* `NumberFieldKB.MilneEC.milneBSDConstant`
* `NumberFieldKB.MilneEC.realPeriodOf`
* `NumberFieldKB.MilneEC.tamagawaProductBad`
* `NumberFieldKB.MilneEC.neronTateBilin`
* `NumberFieldKB.MilneEC.IsMinimalOverRat`
* `NumberFieldKB.MilneEC.ShaComparison`
* `NumberFieldKB.MilneEC.PeriodComparison`
* `NumberFieldKB.MilneEC.TamagawaComparison`
* `NumberFieldKB.FormalConjectures.StrongBSD`
* `NumberFieldKB.FormalConjectures.bsdQuotient`
* `NumberFieldKB.FormalConjectures.HasMeromorphicContinuation`
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Milne, *Elliptic Curves* -/

open MvPolynomial in
open scoped LinearAlgebra.Projectivization in
open NumberFieldKB.MilneEC in
/-- **Bézout's theorem** (Milne, *Elliptic Curves*, Theorem I.1.18): two projective plane curves $F$, $G$ over a
field $k$ with no common component meet in finitely many points of $\mathbb P^2(k^{\mathrm{al}})$, and the sum of
the intersection numbers at these points is $\deg F \cdot \deg G$. (The library's named statement `Thm1_18`,
unfolded; proved by Fulton's dimension count, *Algebraic Curves*, Chapter 5.) -/
theorem bezout (k : Type) [Field k] (F G : MvPolynomial (Fin 3) k)
    (hF : IsProjectivePlaneCurve F) (hG : IsProjectivePlaneCurve G) (hFG : NoCommonComponent F G) :
    ∃ S : Finset (ℙ (AlgebraicClosure k) (Fin 3 → AlgebraicClosure k)),
      (S : Set _) = projectivePoints F (AlgebraicClosure k) ∩ projectivePoints G (AlgebraicClosure k) ∧
      ∑ P ∈ S, projIntersectionNumber F G P = curveDegree F * curveDegree G :=
  sorry

open MvPolynomial in
open scoped LinearAlgebra.Projectivization in
open NumberFieldKB.MilneEC in
/-- **The group law on a plane cubic** (Milne, *Elliptic Curves*, Theorem I.3.1): for a nonsingular projective plane
cubic $C$ over a perfect field $k$ and a point $O \in C(k)$, the chord-tangent addition (the third point of the line
through $O$ and the third point of the line through $P$ and $Q$) is associative. The cubic need not be in Weierstrass
form. (The library's named statement `Thm3_1`, unfolded; proved by Fulton's argument from Bézout's theorem and the
nine-point lemma with multiplicities.) -/
theorem chordTangent_assoc (k : Type) [Field k] [PerfectField k] (F : MvPolynomial (Fin 3) k)
    (hF : IsNonsingularCubic F) (O P Q R : CurvePoints F) :
    chordAdd hF O (chordAdd hF O P Q) R = chordAdd hF O P (chordAdd hF O Q R) :=
  sorry

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Proposition IV.5.5** (Milne, *Elliptic Curves*), with Mordell's theorem for these curves: for distinct integers
$\alpha, \beta, \gamma$ and $E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ over $\mathbb Q$, the group
$E(\mathbb Q)$ is finitely generated and its rank is at most twice the number of primes dividing $2\Delta$,
$\Delta = (\alpha - \beta)^2(\beta - \gamma)^2(\gamma - \alpha)^2$. Proved by Milne's explicit descent: the map
$x - T$ of Remark IV.3.7 makes $E(\mathbb Q)/2E(\mathbb Q)$ finite, and the canonical height gives finite generation;
no Selmer group is used. (`rank` is `Module.finrank ℤ` of the group of rational points.) -/
theorem rank_bound_twoDescent (α β γ : ℤ) (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    AddGroup.FG (cubicCurve α β γ).toAffine.Point ∧
      rank (cubicCurve α β γ) ≤ 2 * (2 * cubicDisc α β γ).natAbs.primeFactors.card :=
  sorry

/-- **Example IV.5.7** (Milne, *Elliptic Curves*): for $E : Y^2 = X^3 - X$ over $\mathbb Q$,
$E(\mathbb Q) \cong (\mathbb Z/2\mathbb Z)^2$ (the points $O$, $(0,0)$, $(\pm1,0)$); in particular the rank is $0$.
Proved by Milne's explicit 2-descent (the map $x - T$ of Remark IV.3.7 and the bound of Proposition IV.5.6) and
reduction modulo 3. The curve is Mathlib's Weierstrass curve with $a_4 = -1$ and the other coefficients $0$. -/
theorem points_x3_sub_x : Nonempty ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).toAffine.Point ≃+ ZMod 2 × ZMod 2) :=
  sorry

/-- **$1$ is not a congruent number** (Milne, *Elliptic Curves*, Introduction, with Example IV.5.7): there is no right
triangle with rational sides and area $1$. A triangle gives a rational point of $Y^2 = X^3 - X$ with $Y \ne 0$,
which Example IV.5.7 excludes. -/
theorem one_not_congruent : ¬ ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ x * y / 2 = 1 :=
  sorry

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Lang's theorem for elliptic curves** (Milne, *Elliptic Curves*, Proposition IV.9.2): for an elliptic curve $E$
over a finite field $k$, $H^1(k, E) = 0$, where $H^1$ is the group of continuous crossed homomorphisms of the absolute
Galois group $\mathrm{Gal}(k^{\mathrm{al}}/k)$ into $E(k^{\mathrm{al}})$ modulo the principal ones (`ContH1`).
Milne reduces it to the surjectivity of $P \mapsto \varphi(P) - P$ ($\varphi$ the Frobenius map); here that
surjectivity is proved from the divisibility of $E(k^{\mathrm{al}})$ (Lemma IV.2.1, in every characteristic) by
counting on the finite groups $E(\mathbb F_{q^m})$, instead of Milne's appeal to Proposition I.4.23. -/
theorem lang_H1_eq_zero (k : Type) [Field k] [Fintype k] (W : WeierstrassCurve k) [W.IsElliptic]
    (c : ContH1 (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (W.toAffine.baseChange (AlgebraicClosure k)).Point) :
    c = 0 :=
  sorry

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 against Formal Conjectures** (conditional on three named comparison statements; no
conjecture is assumed): for an elliptic curve $E$ over $\mathbb Q$ given by a minimal equation, Milne's form of the
conjecture of Birch and Swinnerton-Dyer, with the height pairing normalized as in the standard regulator
(`Conjecture10_5Corrected`: Milne's printed constant divided by $2^r$; as printed, Milne's pairing is twice the
standard one), is equivalent to Formal Conjectures' `StrongBSD`. The named inputs, not proved here: the two
formalizations of the Tate–Shafarevich group are isomorphic (`ShaComparison`), Milne's period $\Omega$ is Formal
Conjectures' global period for a minimal equation (`PeriodComparison`), and Milne's product of the Tamagawa numbers
at the bad primes is Formal Conjectures' Tamagawa product (`TamagawaComparison`). The finite generation of
$E(\mathbb Q)$ (Mordell's theorem) is an instance argument, as in Formal Conjectures. -/
theorem bsd_milne_iff_strongBSD (E : WeierstrassCurve ℚ) [E.IsElliptic] [Module.Finite ℤ E.toAffine.Point]
    (hSha : ShaComparison) (hΩ : PeriodComparison) (hc : TamagawaComparison) (hmin : IsMinimalOverRat E) :
    Conjecture10_5Corrected E ↔ NumberFieldKB.FormalConjectures.StrongBSD E.toAffine :=
  sorry

end NumberFieldKB.Headlines
