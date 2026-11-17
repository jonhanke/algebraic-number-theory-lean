import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch4BSD
import NumberFieldKB.MilneEC.Ch5bModularity

/-!
# Tate's algorithm and Ogg's formula, cited from Tau Ceti

Not numbered items of Milne, *Elliptic Curves*: they supply the local invariants $c_p$ and $N$ of Conjectures
IV.10.3 and IV.10.5, pdf pp. 172–173. Called TA1 and TA2 below.

Tau Ceti (`TauCetiProject/TauCeti`, main `f11cb6ac` and later) proves both:

* `WeierstrassCurve.tamagawaNumber_eq_tateLocalIndex` (`AlgebraicGeometry/EllipticCurve/Tamagawa/Local.lean`): if
  Tate's algorithm stops at the Kodaira symbol $s$ on an integral equation, the local Tamagawa number is
  `tateLocalIndex` $s$, the value in the table of Silverman, *Advanced Topics*, IV.9 ($1$ at $I_0$, $II$, $II^*$;
  $2$ at $III$, $III^*$; $n$ or $\gcd(2, n)$ at $I_n$, split or not; $1$ or $3$ at $IV$, $IV^*$; $1 + $ the number of
  roots of the residue cubic at $I_0^*$; $2$ or $4$ at $I_n^*$); with `exists_isTateTerminal_reductionSymbol` (the
  algorithm stops) and `reductionSymbol_eq_I_of_hasMultiplicativeReduction`;
* `WeierstrassCurve.algorithmicOggExponent` and `algorithmicConductor`
  (`TateAlgorithm/Reduction/{Curve,Conductor}.lean`): Tau Ceti *defines* the conductor exponent by Ogg's formula
  $f_p = \operatorname{ord}_p\Delta_{\min} - m_p + 1$, $m_p$ the number of components of the Kodaira symbol, and
  proves `algorithmicOggExponent_eq_zero_iff` (good), `_eq_one_iff` (multiplicative),
  `two_le_algorithmicOggExponent_iff` (additive) and `algorithmicOggExponent_le_localMinimalDiscriminantValuation`.

**Not ported.** The import closure of `TateAlgorithm.Reduction.Conductor`, `TateAlgorithm.LocalIndex` and
`Tamagawa.Local` is 332 files, 195 of them new here, and needs Mathlib master (`AdicValuation.Completion`,
`Ramification`, `QuadraticAlgebra`), absent from the pinned v4.35.0. So TA1 and
TA2 are **named inputs** (structures, not definitionally equal to anything proved here).
Tate's algorithm itself (its steps and stopping symbol) is not definable here without the port, so
TA1 records the *table of values* of $c_p$ that `tamagawaNumber_eq_tateLocalIndex` gives, and TA2 the *properties*
of Ogg's exponent that Tau Ceti proves, with Milne's `Vb.IsConductorOf` satisfied by $\prod_p p^{f_p}$. They become
proofs after the Mathlib bump.
-/

namespace NumberFieldKB.MilneEC

open WeierstrassCurve

/-- The valuation $\operatorname{ord}_p(\Delta_{\min})$ of the discriminant of a minimal model of $E$ over
$\mathbb Q_p$. -/
noncomputable def ordMinimalDiscriminant (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime] : ℤ :=
  Padic.valuation ((E.baseChange ℚ_[p]).minimal ℤ_[p]).Δ

/-- **TA1: Tate's algorithm computes $c_p$** (named input citing Tau Ceti
`WeierstrassCurve.tamagawaNumber_eq_tateLocalIndex`, not ported; Silverman, *Advanced Topics*, IV.9, Table 4.1). For an
elliptic curve over $\mathbb Q$ and a prime $p$, Milne's $c_p$ (`tamagawaNumberAt`, Formal Conjectures' local
Tamagawa number of the minimal model over $\mathbb Z_p$) is:
* $1$ at good reduction ($I_0$);
* $\operatorname{ord}_p\Delta_{\min}$ at split multiplicative reduction ($I_n$, split, $c_p = n$);
* $\gcd(2, \operatorname{ord}_p\Delta_{\min})$ at nonsplit multiplicative reduction ($I_n$, nonsplit);
* one of $1, 2, 3, 4$ at additive reduction (every other Kodaira symbol). -/
@[kb "milne2006ec" "Ch. IV, §10, the Tamagawa numbers c_p of Conjecture 10.5 (Tate's algorithm), pdf p. 173"]
structure TateAlgorithmTamagawa : Prop where
  good : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime],
    Vb.HasGoodReductionAt E p → tamagawaNumberAt E p = 1
  split : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime],
    ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasSplitMultiplicativeReduction ℤ_[p] →
      (tamagawaNumberAt E p : ℤ) = ordMinimalDiscriminant E p
  nonsplit : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime],
    Vb.HasMultiplicativeReductionAt E p →
      ¬ ((E.baseChange ℚ_[p]).minimal ℤ_[p]).HasSplitMultiplicativeReduction ℤ_[p] →
        (tamagawaNumberAt E p : ℤ) = Int.gcd 2 (ordMinimalDiscriminant E p)
  additive : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime],
    Vb.HasAdditiveReductionAt E p → tamagawaNumberAt E p ∈ ({1, 2, 3, 4} : Finset ℕ)

/-- **TA2: the conductor exponent by Ogg's formula** (named input citing Tau Ceti
`WeierstrassCurve.algorithmicOggExponent` and `algorithmicConductor`, not ported). For an elliptic curve over
$\mathbb Q$ there are exponents $f_p$ (Tau Ceti's $\operatorname{ord}_p\Delta_{\min} - m_p + 1$) with $f_p = 0$
exactly at good reduction, $f_p = 1$ exactly at multiplicative reduction, $f_p \ge 2$ exactly at additive reduction,
$f_p \le \operatorname{ord}_p\Delta_{\min}$, $f_p = 2$ at additive reduction when $p \ge 5$ (tame reduction; this
clause is in the literature, Ogg 1967 with Saito 1988, not in Tau Ceti), and $N = \prod_p p^{f_p}$ satisfies
Milne's description of the conductor (`Vb.IsConductorOf`). This names the $N$ of Conjecture 10.3;
the exponents at $2$ and $3$ are pinned down only by Ogg's formula itself, whose component count
$m_p$ needs Tate's algorithm. -/
@[kb "milne2006ec" "Ch. IV, §10, the conductor N of Conjecture 10.3 (Ogg's formula), pdf p. 172"]
structure OggConductor : Prop where
  exists_exponent : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ f : ℕ → ℕ,
    (∀ (p : ℕ) [Fact p.Prime],
      (f p = 0 ↔ Vb.HasGoodReductionAt E p) ∧
      (f p = 1 ↔ Vb.HasMultiplicativeReductionAt E p) ∧
      (2 ≤ f p ↔ Vb.HasAdditiveReductionAt E p) ∧
      (f p : ℤ) ≤ ordMinimalDiscriminant E p ∧
      (5 ≤ p → Vb.HasAdditiveReductionAt E p → f p = 2)) ∧
    Vb.IsConductorOf E (∏ᶠ p : Nat.Primes, (p : ℕ) ^ f p)

end NumberFieldKB.MilneEC
