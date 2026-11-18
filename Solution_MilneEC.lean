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
import NumberFieldKB.MilneEC.Ch4Prop81
import NumberFieldKB.MilneEC.Ch4LocalPeriodBad
import NumberFieldKB.MilneEC.Ch4LocalPeriodRemark
import NumberFieldKB.MilneEC.Ch3RealPeriod
import NumberFieldKB.MilneEC.Ch2MazurRealization
import NumberFieldKB.MilneEC.ShaComparison
import NumberFieldKB.MilneEC.LocalPointsPadic

/-!
# Headline statements of NumberFieldKB 0.4.1: Milne, Elliptic Curves, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
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
  NumberFieldKB.MilneEC.thm1_18.bezout k F G hF hG hFG

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
  NumberFieldKB.MilneEC.thm3_1.assoc k F hF O P Q R

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
  ⟨NumberFieldKB.MilneEC.fg_cubicCurve hαβ hβγ hγα,
      NumberFieldKB.MilneEC.prop_5_5_rank_unconditional hαβ hβγ hγα⟩

/-- **Example IV.5.7** (Milne, *Elliptic Curves*): for $E : Y^2 = X^3 - X$ over $\mathbb Q$,
$E(\mathbb Q) \cong (\mathbb Z/2\mathbb Z)^2$ (the points $O$, $(0,0)$, $(\pm1,0)$); in particular the rank is $0$.
Proved by Milne's explicit 2-descent (the map $x - T$ of Remark IV.3.7 and the bound of Proposition IV.5.6) and
reduction modulo 3. The curve is Mathlib's Weierstrass curve with $a_4 = -1$ and the other coefficients $0$. -/
theorem points_x3_sub_x : Nonempty ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).toAffine.Point ≃+ ZMod 2 × ZMod 2) :=
  by
    have h : NumberFieldKB.MilneEC.cubicCurve (-1) 0 1 = ⟨0, 0, 0, -1, 0⟩ := by
      simp only [NumberFieldKB.MilneEC.cubicCurve, WeierstrassCurve.mk.injEq]; norm_num
    rw [← h]
    exact NumberFieldKB.MilneEC.example_5_7_unconditional.2

/-- **$1$ is not a congruent number** (Milne, *Elliptic Curves*, Introduction, with Example IV.5.7): there is no right
triangle with rational sides and area $1$. A triangle gives a rational point of $Y^2 = X^3 - X$ with $Y \ne 0$,
which Example IV.5.7 excludes. -/
theorem one_not_congruent : ¬ ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 = z ^ 2 ∧ x * y / 2 = 1 :=
  fun ⟨x, y, z, hx, hy, hz, h, ha⟩ =>
    NumberFieldKB.MilneEC.not_isCongruentNumber_one ⟨x, y, z, hx, hy, hz, h, by rw [ha]; norm_num⟩

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
  NumberFieldKB.MilneEC.prop_9_2_unconditional k W c

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
  NumberFieldKB.MilneEC.conjecture10_5Corrected_iff_strongBSD E hSha hΩ hc hmin

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Propositions IV.8.1 and IV.8.2** (Milne, *Elliptic Curves*; Silverman, *The Arithmetic of Elliptic Curves*,
X.6.2): let $p \equiv 1 \pmod 8$ be a prime and $E : Y^2 = X^3 + pX$ over $\mathbb Q$. Then the $2$-Selmer group
$S^{(2)}(E/\mathbb Q)$ is isomorphic to $(\mathbb Z/2)^3$; if moreover $2$ is not a fourth power modulo $p$, then
$E(\mathbb Q)$ has rank $0$ and the $2$-torsion of the Tate–Shafarevich group, $Ш(E/\mathbb Q)[2]$, is isomorphic to
$(\mathbb Z/2)^2$. The Selmer and Tate–Shafarevich groups are Milne's: continuous classes in
$H^1(\operatorname{Gal}(\mathbb Q^{\mathrm{al}}/\mathbb Q), -)$ whose images in $H^1(\mathbb Q_v, E)$ vanish at every place
$v$, finite and infinite. Proved directly on the Galois-cohomological Selmer group, by Kummer theory for
$\mathbb Z/2$ and the local conditions at $2$, $p$ and $\infty$. (The library's statements are the fields of the
structures `Prop8_1` and `Prop8_2`, unfolded here; `rank` is `Module.finrank ℤ` of the group of rational points.) -/
theorem selmer_sha_x3_add_px (p : ℕ) (hp : p.Prime) (h8 : p % 8 = 1) :
    Nonempty (selmerGroup ℚ (curveP p) 2 ≃+ (Fin 3 → ZMod 2)) ∧
      ((¬ ∃ x : ZMod p, x ^ 4 = 2) →
        rank (curveP p) = 0 ∧ Nonempty (shaTwoTorsion (curveP p) ≃+ (Fin 2 → ZMod 2))) :=
  ⟨NumberFieldKB.MilneEC.prop_8_1.selmer p hp h8, fun h4 =>
      ⟨NumberFieldKB.MilneEC.prop_8_2.rank_eq_zero p hp h8 h4, NumberFieldKB.MilneEC.prop_8_2.sha_two p hp h8 h4⟩⟩

open MeasureTheory QuadFormsKB.Analysis in
open scoped ENNReal in
open NumberFieldKB.MilneEC.LocalPeriod in
/-- **The local measure of $E_0(\mathbb Q_p)$** (Milne, *Elliptic Curves*, Remark IV.10.6 (a), the step that does
not involve $c_p$): let $p$ be an odd prime and $W$ a minimal Weierstrass equation over $\mathbb Q_p$, with good,
multiplicative or additive reduction. Then $\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$, where
$\omega = dx/(2y + a_1x + a_3)$, $E_0(\mathbb Q_p)$ is the set of points with non-singular reduction and $N_p$ is the
number of non-singular points of the reduction over $\mathbb F_p$ (Mathlib's `Point` type of `W.reduction`, which
includes the point at infinity). The measure is read on the $x$-line: `omegaDensity W x` is the number of square
roots $\psi$ of $\Psi_2^2(x) = 4x^3 + b_2x^2 + 2b_4x + b_6$ in $\mathbb Q_p$ divided by $|\psi|_p$, `zeroComponentX W`
is the image of $E_0(\mathbb Q_p)$ under $x$, and `haarP p` is the Haar measure on $\mathbb Q_p$ with
$\operatorname{vol}(\mathbb Z_p) = 1$ (from quadratic-forms-lean). -/
theorem omega_measure_zeroComponent (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.IsMinimal ℤ_[p]] :
    ∫⁻ x in zeroComponentX W, omegaDensity W x ∂haarP p =
      (Nat.card (W.reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p :=
  NumberFieldKB.MilneEC.LocalPeriod.omegaVolume_zeroComponent hp2 W

open MeasureTheory QuadFormsKB.Analysis in
open scoped ENNReal in
open NumberFieldKB.MilneEC.LocalPeriod in
/-- **The local Tamagawa measure at good reduction** (Milne, *Elliptic Curves*, Remark IV.10.6 (a)): for an odd
prime $p$ and a Weierstrass equation $W$ over $\mathbb Q_p$ with good reduction (Mathlib's `HasGoodReduction`, which
includes minimality), $\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$, with $c_p$ the local Tamagawa number of Formal
Conjectures (`tamagawaNumber`, the number of translates of $E_0(\mathbb Q_p)$; here $c_p = 1$) and
$N_p = \#\tilde E(\mathbb F_p)$. The measure `omegaVolume W` is the integral of `omegaDensity W` over $\mathbb Q_p$ for
the Haar measure with $\operatorname{vol}(\mathbb Z_p) = 1$ (see `omega_measure_zeroComponent`). -/
theorem omega_measure_goodReduction (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.HasGoodReduction ℤ_[p]] :
    omegaVolume W = (NumberFieldKB.FormalConjectures.tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective :
      ℝ≥0∞) * Nat.card (W.reduction ℤ_[p]).toAffine.Point / p :=
  NumberFieldKB.MilneEC.LocalPeriod.remark_10_6_a_good_cp hp2 W

open NumberFieldKB.MilneEC.III in
/-- **The real period through the uniformization** (Milne, *Elliptic Curves*, the period $\Omega$ of Conjecture
IV.10.5, through Chapter III): for every elliptic curve $W$ over $\mathbb R$ there is a lattice $\Lambda$ with real
invariants $g_2, g_3$ (Mathlib's `PeriodPair`) and a change of variables with $u = 1$ taking $W$ to
$E(\Lambda) : y^2 = x^3 - \tfrac{g_2}4x - \tfrac{g_3}4$; for it, the real period of Formal Conjectures,
$\Omega(W) = \int_{E(\mathbb R)}|\omega| = 2\int_{\mathbb R}dx/\sqrt{\Psi_2^2(x)}$, equals the number of connected
components of $E(\mathbb R)$ (2 if $\Delta > 0$, else 1) times the least positive real element of $\Lambda$. Proved
by the substitution $x = \wp(t)$. -/
theorem realPeriod_eq_latticePeriod (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    ∃ L : PeriodPair, HasRealInvariants L ∧
      ∃ C : WeierstrassCurve.VariableChange ℝ, C.u = 1 ∧ C • W = realCurveOf L ∧
        NumberFieldKB.FormalConjectures.realPeriod W = realComponentCount W * leastRealPeriod L :=
  NumberFieldKB.MilneEC.III.rp1_real_period W

/-- **Mazur's list is attained** (Milne, *Elliptic Curves*, Remark II.5.11, the realization half; Mazur's theorem,
the other half, is not formalized): each of the groups $\mathbb Z/m$ ($1 \le m \le 10$ or $m = 12$) and
$\mathbb Z/2 \times \mathbb Z/2m$ ($1 \le m \le 4$) is the torsion subgroup of $E(\mathbb Q)$ for an explicit
elliptic curve $E$ over $\mathbb Q$. For each curve the torsion is computed by exhibiting points of the right orders
and bounding the torsion by reduction modulo a prime of good reduction. -/
theorem mazur_torsion_realized :
    (∀ m : ℕ, (1 ≤ m ∧ m ≤ 10 ∨ m = 12) → ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod m)) ∧
      ∀ m : ℕ, 1 ≤ m ∧ m ≤ 4 → ∃ W : WeierstrassCurve ℚ, W.IsElliptic ∧
        Nonempty (AddCommGroup.torsion W.toAffine.Point ≃+ ZMod 2 × ZMod (2 * m)) :=
  NumberFieldKB.MilneEC.II.mazur_groups_realized

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 against Formal Conjectures, over $\mathbb Q$** (conditional on one named local
statement; no conjecture is assumed): for an elliptic curve $E$ over $\mathbb Q$ given by a minimal equation,
Milne's form of the conjecture of Birch and Swinnerton-Dyer with the standard normalization of the height pairing
(`Conjecture10_5Corrected`) is equivalent to Formal Conjectures' `StrongBSD`. Unlike `bsd_milne_iff_strongBSD`, the
finite generation of $E(\mathbb Q)$ is the library's Mordell–Weil theorem over $\mathbb Q$ (`mordell_weil_rat`, by
Milne's descent), not an instance argument; the period and Tamagawa comparisons are proved; and the comparison of the
two Tate–Shafarevich groups is proved from one named input, `LocalPointsInjective`: at every place $v$ of
$\mathbb Q$, a continuous class of $\operatorname{Gal}(\bar{\mathbb Q}_v/\mathbb Q_v)$ with values in
$E(\bar{\mathbb Q})$ that becomes trivial in $E(\bar{\mathbb Q}_v)$ is trivial (Milne, *Arithmetic Duality
Theorems*, Remark I.3.10, by Greenberg approximation at the finite places). -/
theorem bsd_milne_iff_strongBSD_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] (hloc : LocalPointsInjective) (hmin : IsMinimalOverRat E) :
    haveI := NumberFieldKB.MilneEC.mordell_weil_rat E
    Conjecture10_5Corrected E ↔ NumberFieldKB.FormalConjectures.StrongBSD E.toAffine :=
  NumberFieldKB.MilneEC.conjecture10_5Corrected_iff_strongBSD_of_localPointsInjective E hloc hmin

open MeasureTheory QuadFormsKB.Analysis in
open scoped ENNReal in
open NumberFieldKB.MilneEC.LocalPeriod in
/-- **The local Tamagawa measure at every reduction type** (Milne, *Elliptic Curves*, Remark IV.10.6 (a);
conditional on one named input): for an odd prime $p$ and a minimal equation $W$ of an elliptic curve over
$\mathbb Q_p$, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$, with $c_p$ Formal Conjectures' local Tamagawa number
and $N_p$ the number of non-singular points of the reduction. The named input `ZeroComponentIndex` is Milne's first
step, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p\int_{E_0(\mathbb Q_p)}|\omega|_p$ ($|\omega|_p$ is invariant under
translation and $E(\mathbb Q_p)$ is the union of $c_p$ translates of $E_0(\mathbb Q_p)$); the second step,
$\int_{E_0(\mathbb Q_p)}|\omega|_p = N_p/p$, is the unconditional headline `omega_measure_zeroComponent`. -/
theorem omega_measure_of_zeroComponentIndex (hI : ZeroComponentIndex) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [W.IsElliptic] [W.IsMinimal ℤ_[p]] :
    omegaVolume W = (NumberFieldKB.FormalConjectures.tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective :
      ℝ≥0∞) * Nat.card (W.reduction ℤ_[p]).toAffine.Point / p :=
  NumberFieldKB.MilneEC.LocalPeriod.remark_10_6_a_of_index hI hp2 W

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 against Formal Conjectures, with no named input** (no conjecture is assumed): for
every elliptic curve $E$ over $\mathbb Q$ given by a minimal equation, Milne's form of the conjecture of Birch and
Swinnerton-Dyer with the standard normalization of the height pairing (`Conjecture10_5Corrected`: Milne's printed
constant divided by $2^r$) is equivalent to Formal Conjectures' `StrongBSD`. The finite generation of $E(\mathbb Q)$
is the library's Mordell–Weil theorem over $\mathbb Q$ (`mordell_weil_rat`); the comparisons of the periods, of the
Tamagawa products and of the two Tate–Shafarevich groups are all proved (the last one is the headline
`sha_milne_equiv_formalConjectures`). The statement is that of `bsd_milne_iff_strongBSD_rat` without its hypothesis
`LocalPointsInjective`, which is now the headline `localPoints_injective_rat`. -/
theorem bsd_milne_iff_strongBSD_unconditional (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmin : IsMinimalOverRat E) :
    haveI := NumberFieldKB.MilneEC.mordell_weil_rat E
    Conjecture10_5Corrected E ↔ NumberFieldKB.FormalConjectures.StrongBSD E.toAffine :=
  NumberFieldKB.MilneEC.conjecture10_5Corrected_iff_strongBSD_unconditional E hmin

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 as printed, in rank $0$** (no named input; no conjecture is assumed): for an
elliptic curve $E$ over $\mathbb Q$ given by a minimal equation and with $E(\mathbb Q)$ of rank $0$, Milne's
Conjecture IV.10.5 exactly as printed (`Conjecture10_5`) is equivalent to Formal Conjectures' `StrongBSD`. In rank $0$
the height pairing does not enter the constant, so the factor $2^r$ of `bsd_milne_iff_strongBSD_unconditional` is $1$.
The rank is `Module.finrank ℤ` of $E(\mathbb Q)$, finitely generated by `mordell_weil_rat`. -/
theorem bsd_milne_printed_iff_strongBSD_rank_zero (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmin : IsMinimalOverRat E) :
    haveI := NumberFieldKB.MilneEC.mordell_weil_rat E
    rank E = 0 → (Conjecture10_5 E ↔ NumberFieldKB.FormalConjectures.StrongBSD E.toAffine) :=
  NumberFieldKB.MilneEC.conjecture10_5_iff_strongBSD_of_rank_eq_zero_unconditional E hmin

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **Milne's Conjecture IV.10.5 as printed is off by $2^r$ in positive rank** (no named input; no conjecture is
assumed): for an elliptic curve $E$ over $\mathbb Q$ given by a minimal equation and with $E(\mathbb Q)$ of rank
$r > 0$, Formal Conjectures' `StrongBSD` implies that Milne's Conjecture IV.10.5 as printed (`Conjecture10_5`) is
false. As printed, Milne's height pairing is twice the standard one, so the printed constant is $2^r$ times the
standard one; the corrected form is `bsd_milne_iff_strongBSD_unconditional`. -/
theorem strongBSD_refutes_milne_printed_positive_rank (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmin : IsMinimalOverRat E) :
    haveI := NumberFieldKB.MilneEC.mordell_weil_rat E
    0 < rank E → NumberFieldKB.FormalConjectures.StrongBSD E.toAffine → ¬ Conjecture10_5 E :=
  NumberFieldKB.MilneEC.not_conjecture10_5_of_strongBSD_unconditional E hmin

open WeierstrassCurve in
open NumberFieldKB.MilneEC in
/-- **The Tate–Shafarevich groups agree** (the named statement `ShaComparison` of release 0.4.0, unfolded and now
proved): for every elliptic curve $E$ over $\mathbb Q$, Milne's $Ш(E/\mathbb Q)$ (`tateShafarevich ℚ E`: continuous
classes in $H^1(\operatorname{Gal}(\bar{\mathbb Q}/\mathbb Q), E(\bar{\mathbb Q}))$ whose image in
$H^1(\operatorname{Gal}(\bar{\mathbb Q}_v/\mathbb Q_v), E(\bar{\mathbb Q}_v))$ vanishes at every place $v$) is
isomorphic to Formal Conjectures' (continuous cohomology of the discrete module $E(\bar{\mathbb Q})$, with the local
condition taken in the same module $E(\bar{\mathbb Q})$). The two local conditions agree by local injectivity
(`localPoints_injective_rat`). -/
theorem sha_milne_equiv_formalConjectures (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    Nonempty (tateShafarevich ℚ E ≃+ NumberFieldKB.FormalConjectures.tateShafarevich E.toAffine) :=
  NumberFieldKB.MilneEC.shaComparison.equiv E

open NumberField IsDedekindDomain NumberFieldKB.MilneEC in
attribute [-instance] DivisionRing.toRatAlgebra in
/-- **Local injectivity at every place of $\mathbb Q$** (the named statement `LocalPointsInjective` of release
0.4.0, unfolded and now proved; Milne, *Arithmetic Duality Theorems*, Remark I.3.10): for every elliptic curve $E$ over
$\mathbb Q$ and every place $v$ of $\mathbb Q$ (every finite place, as the adic completion, and the infinite place), a
continuous crossed homomorphism of $\operatorname{Gal}(\bar{\mathbb Q}_v/\mathbb Q_v)$ into $E(\bar{\mathbb Q})$
whose image in $E(\bar{\mathbb Q}_v)$ is principal is itself principal (`LocalPointsInjectiveAt`). Proved from Kummer
approximation (`kummer_approx_padic` at the finite places; at the real place, halving of points with large $x$ and
density of the algebraic points), not from Greenberg approximation. The statement is read with the algebra structure
of $\mathbb Q$ on each completion that the completion carries (`attribute [-instance] DivisionRing.toRatAlgebra`, as in
the library); any two $\mathbb Q$-algebra structures on a ring are equal, so this only fixes which term is written. -/
theorem localPoints_injective_rat (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), LocalPointsInjectiveAt E (v.adicCompletion ℚ)) ∧
      ∀ w : InfinitePlace ℚ, LocalPointsInjectiveAt E w.Completion :=
  NumberFieldKB.MilneEC.localPointsInjective.holds E

open NumberField IsDedekindDomain NumberFieldKB.MilneEC in
attribute [-instance] DivisionRing.toRatAlgebra in
/-- **Kummer approximation at the finite places of $\mathbb Q$** (the named statement `FiniteKummerPrime`, unfolded
and now proved): for every elliptic curve $E$ over $\mathbb Q$, every finite place $v$ of $\mathbb Q$ (every prime
$p$, including $p = 2$) and every prime $\ell$, every point $R$ of $E(\mathbb Q_v)$ is $\ell S + T$ in
$E(\bar{\mathbb Q}_v)$, with $S \in E(\mathbb Q_v)$ and $T$ a point with coordinates in $\bar{\mathbb Q}$
(`KummerApprox`). Proved by Hensel's lemma on the reflected division polynomials (multiplication by $m \ne 0$ is onto
the points with $\lVert x\rVert > \lVert m\rVert^{-4}$, as in Milne's Corollary II.4.2, with no formal group) and the
density of the algebraic points. The algebra structure of $\mathbb Q$ on the completion is read as in
`localPoints_injective_rat`. -/
theorem kummer_approx_padic (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : HeightOneSpectrum (𝓞 ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    KummerApprox E (v.adicCompletion ℚ) ℓ :=
  NumberFieldKB.MilneEC.finiteKummerPrime.holds E v ℓ hℓ

end NumberFieldKB.Headlines
