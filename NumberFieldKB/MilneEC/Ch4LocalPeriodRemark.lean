import NumberFieldKB.MilneEC.Ch4LocalPeriodTwo

/-!
# Milne, *Elliptic Curves*, Remark IV.10.6 (a), (c) from Milne's translation step

Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Remark 10.6, pdf p. 173.
The named statement `Remark10_6` (Ch4LocalPeriod.lean) asks, for every prime and every minimal
equation, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$ (a) and $= c_p L_p(E, 1)^{-1}$ (c).

## Proved here (no named input)
* `remark_10_6_a_good_cp`: (a) at good reduction, $p$ odd, **with the factor $c_p$**.
* `ofReal_localFactorInvAtOne`: $L_p(E, 1)^{-1} = N_p/p$ for every reduction type, $p$ odd (from the point counts
  $N_p = p - 1$, $p + 1$, $p$ of Ch4LocalPeriodCount.lean).
* `remark_10_6_c_of_a`: so (c) follows from (a) at every odd prime.

## Named inputs and what follows
* `ZeroComponentIndex` (Milne's step 1): $\int_{E(\mathbb Q_p)}|\omega|_p = c_p\int_{E_0(\mathbb Q_p)}|\omega|_p$,
  i.e. translation invariance of $|\omega|_p$ and $[E(\mathbb Q_p) : E_0(\mathbb Q_p)] = c_p$.
* `ZeroComponentVolumeTwo` (Milne's step 2 at $p = 2$; proved for $p$ odd as `omegaVolume_zeroComponent`).
* `PointCountTwo` ($N_2 = 1, 3, 2$ at split, non-split, additive reduction): now proved, `pointCountTwo`.
* `remark_10_6_a_of_index` ($p$ odd) and `remark10_6_of`: `Remark10_6` from the first two.
* `NodeDiscVolume` (the residue disc of the node at multiplicative reduction, $p$ odd) and
  `tamagawaNumber_of_split`, `tamagawaNumber_of_nonsplit`: $c_p = \operatorname{ord}_p\Delta$ (split) and
  $c_p = \gcd(2, \operatorname{ord}_p\Delta)$ (non-split) from `ZeroComponentIndex` and `NodeDiscVolume`, without
  Tate's algorithm.
-/

open MeasureTheory QuadFormsKB.Analysis Polynomial
open scoped ENNReal

namespace NumberFieldKB.MilneEC.LocalPeriod

open FormalConjectures

/-! ## Named inputs -/

/-- **Milne's step 1** (named input; Milne, Remark IV.10.6, pdf p. 173): for a minimal equation of an elliptic
curve over $\mathbb Q_p$, $\int_{E(\mathbb Q_p)}|\omega|_p = c_p\int_{E_0(\mathbb Q_p)}|\omega|_p$, with $c_p$ Formal
Conjectures' `tamagawaNumber` (the number of translates of $E_0(\mathbb Q_p)$) and $E_0(\mathbb Q_p)$ read on the
$x$-line through `zeroComponentX` (`mem_nonsingularReduction_iff_mem_zeroComponentX`). Milne's proof: $|\omega|_p$
is invariant under translation by $E(\mathbb Q_p)$ since $\omega$ is an invariant differential, and $E(\mathbb Q_p)$ is
the disjoint union of $c_p$ translates of the subgroup $E_0(\mathbb Q_p)$. Neither the invariance (which needs the
measure on the $p$-adic manifold $E(\mathbb Q_p)$) nor the subgroup property of $E_0$ is available here. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), vol E(Q_p) = c_p vol E_0(Q_p) (named input), pdf p. 173"]
structure ZeroComponentIndex : Prop where
  index : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] [W.IsMinimal ℤ_[p]],
    omegaVolume W = (tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
      ∫⁻ x in zeroComponentX W, omegaDensity W x ∂haarP p

/-- **Milne's step 2 at $p = 2$** (named input; proved for $p$ odd as `omegaVolume_zeroComponent`):
$\int_{E_0(\mathbb Q_2)}|\omega|_2 = N_2/2$ on a minimal equation. At $p = 2$ the $x$-line density is not locally
constant on the discs where $2y + a_1x + a_3$ vanishes modulo $2$; the computation needs the $y$-chart there. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), vol E_0(Q_2) = N_2/2 (named input), pdf p. 173"]
structure ZeroComponentVolumeTwo : Prop where
  volume : ∀ (W : WeierstrassCurve ℚ_[2]) [W.IsElliptic] [W.IsMinimal ℤ_[2]],
    ∫⁻ x in zeroComponentX W, omegaDensity W x ∂haarP 2 =
      (Nat.card (W.reduction ℤ_[2]).toAffine.Point : ℝ≥0∞) / 2

/-- **Non-singular points of a singular cubic over $\mathbb F_2$**: $N_2 = 1$, $3$, $2$ at split multiplicative,
non-split multiplicative and additive reduction (proved: `pointCountTwo`, by enumeration in Ch4LocalPeriodTwo.lean;
for $p$ odd see `card_reduction_of_split`, `card_reduction_of_nonsplit`, `card_reduction_of_additive`). -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (c), N_2 at bad reduction, pdf p. 173"]
structure PointCountTwo : Prop where
  split : ∀ (W : WeierstrassCurve ℚ_[2]) [W.HasSplitMultiplicativeReduction ℤ_[2]],
    Nat.card (W.reduction ℤ_[2]).toAffine.Point = 1
  nonsplit : ∀ (W : WeierstrassCurve ℚ_[2]) [W.HasMultiplicativeReduction ℤ_[2]],
    ¬ W.HasSplitMultiplicativeReduction ℤ_[2] → Nat.card (W.reduction ℤ_[2]).toAffine.Point = 3
  additive : ∀ (W : WeierstrassCurve ℚ_[2]) [W.HasAdditiveReduction ℤ_[2]],
    Nat.card (W.reduction ℤ_[2]).toAffine.Point = 2

/-- **$N_2$ at bad reduction** (Milne, Remark IV.10.6 (c), pdf p. 173). -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (c), N_2 = 1, 3, 2 at bad reduction, pdf p. 173"]
theorem pointCountTwo : PointCountTwo :=
  ⟨fun W _ => card_reduction_two_of_split W, fun W _ hns => card_reduction_two_of_nonsplit W hns,
    fun W _ => card_reduction_two_of_additive W⟩

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Remark 10.6 (a) at good reduction with the factor $c_p$ -/

/-- **Milne, Remark IV.10.6 (a), good reduction, $p$ odd, with $c_p$** (pdf p. 173):
$\int_{E(\mathbb Q_p)}|\omega|_p = c_p N_p/p$, $c_p = 1$ (`Tamagawa.tamagawaNumber_eq_one_of_hasGoodReduction`). -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), ∫|ω| = c_p N_p / p (good reduction, p odd), pdf p. 173"]
theorem remark_10_6_a_good_cp (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) [W.HasGoodReduction ℤ_[p]] :
    omegaVolume W = (tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
      Nat.card (W.reduction ℤ_[p]).toAffine.Point / p := by
  rw [Tamagawa.tamagawaNumber_eq_one_of_hasGoodReduction (R := ℤ_[p]) W, Nat.cast_one, one_mul]
  exact remark_10_6_a_good hp2 W

/-! ## $L_p(E, 1)^{-1} = N_p/p$ -/

lemma natCard_residueField' : Nat.card (IsLocalRing.ResidueField ℤ_[p]) = p := by
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]

/-- $L_p(E, 1)^{-1} = N_p/p$ on the minimal model, given the point counts at bad reduction. -/
lemma ofReal_localFactorInvAtOne_of (W : WeierstrassCurve ℚ_[p])
    (hs : (W.minimal ℤ_[p]).HasSplitMultiplicativeReduction ℤ_[p] →
      Nat.card ((W.minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point = p - 1)
    (hn : (W.minimal ℤ_[p]).HasMultiplicativeReduction ℤ_[p] →
      ¬ (W.minimal ℤ_[p]).HasSplitMultiplicativeReduction ℤ_[p] →
      Nat.card ((W.minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point = p + 1)
    (ha : (W.minimal ℤ_[p]).HasAdditiveReduction ℤ_[p] →
      Nat.card ((W.minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point = p) :
    ENNReal.ofReal (localFactorInvAtOne W) =
      (Nat.card ((W.minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p := by
  classical
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hdiv : ∀ n : ℕ, ENNReal.ofReal ((n : ℝ) / p) = (n : ℝ≥0∞) / p := by
    intro n
    rw [ENNReal.ofReal_div_of_pos hP, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  unfold localFactorInvAtOne WeierstrassCurve.localPolynomial
  simp only [natCard_residueField']
  split_ifs with hg hsp hm
  · generalize Nat.card (WeierstrassCurve.reduction ℤ_[p] (W.minimal ℤ_[p])).toAffine.Point = N
    rw [← hdiv]
    congr 1
    simp
    field_simp
    ring
  · rw [hs hsp, ← hdiv]
    congr 1
    simp
    rw [Nat.cast_sub hp1]
    field_simp
    simp
  · rw [hn hm hsp, ← hdiv]
    congr 1
    simp
    field_simp
  · have hadd : (W.minimal ℤ_[p]).HasAdditiveReduction ℤ_[p] := by
      rcases WeierstrassCurve.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction
        (R := ℤ_[p]) (W := W.minimal ℤ_[p]) with h | h | h
      · exact absurd h hg
      · exact absurd h hm
      · exact h
    rw [ha hadd, ← hdiv]
    congr 1
    simp

/-- **$L_p(E, 1)^{-1} = N_p/p$ for every reduction type, $p$ odd** (Milne, Remark IV.10.6 (c), pdf p. 173), with
Mathlib's `localPolynomial` ($1 - a_pT + pT^2$, $1 - T$, $1 + T$, $1$). -/
theorem ofReal_localFactorInvAtOne (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p]) :
    ENNReal.ofReal (localFactorInvAtOne W) =
      (Nat.card ((W.minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point : ℝ≥0∞) / p :=
  ofReal_localFactorInvAtOne_of W (fun _ => card_reduction_of_split hp2 _)
    (fun _ hns => card_reduction_of_nonsplit hp2 _ hns) (fun _ => card_reduction_of_additive hp2 _)

-- local: Tau Ceti declares the general instance `WeierstrassCurve.isElliptic_minimal`
local instance (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] : (W.minimal ℤ_[p]).IsElliptic := by
  unfold WeierstrassCurve.minimal; infer_instance

/-- **(a) implies (c)** at an odd prime: if $\int_{E(\mathbb Q_p)}|\omega|_p = c_pN_p/p$ on the minimal model then
$\int_{E(\mathbb Q_p)}|\omega|_p = c_pL_p(E, 1)^{-1}$. -/
theorem remark_10_6_c_of_a (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    (ha : omegaVolume (W.minimal ℤ_[p]) =
      (tamagawaNumber ℚ_[p] ((W.minimal ℤ_[p]).integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
        Nat.card ((W.minimal ℤ_[p]).reduction ℤ_[p]).toAffine.Point / p) :
    omegaVolume (W.minimal ℤ_[p]) =
      (tamagawaNumber ℚ_[p] ((W.minimal ℤ_[p]).integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
        ENNReal.ofReal (localFactorInvAtOne W) := by
  rw [ha, ofReal_localFactorInvAtOne hp2, mul_div_assoc]

/-! ## Remark 10.6 from the named inputs -/

/-- **Remark 10.6 (a) at an odd prime, every reduction type**, from Milne's step 1 (`ZeroComponentIndex`); step 2
is `omegaVolume_zeroComponent`. -/
theorem remark_10_6_a_of_index (hI : ZeroComponentIndex) (hp2 : p ≠ 2) (W : WeierstrassCurve ℚ_[p])
    [W.IsElliptic] [W.IsMinimal ℤ_[p]] :
    omegaVolume W = (tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
      Nat.card (W.reduction ℤ_[p]).toAffine.Point / p := by
  rw [hI.index p W, omegaVolume_zeroComponent hp2 W, mul_div_assoc]

/-- **Milne, Remark IV.10.6 (a), (c)** (pdf p. 173) from Milne's step 1 and the measure of $E_0(\mathbb Q_2)$. -/
@[kb "milne2006ec" "Ch. IV, Remark 10.6 (a), (c), from the named inputs, pdf p. 173"]
theorem remark10_6_of (hI : ZeroComponentIndex) (h2 : ZeroComponentVolumeTwo) :
    Remark10_6 := by
  have ha : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] [W.IsMinimal ℤ_[p]],
      omegaVolume W = (tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℝ≥0∞) *
        Nat.card (W.reduction ℤ_[p]).toAffine.Point / p := by
    intro p _ W _ _
    by_cases hp2 : p = 2
    · subst hp2
      rw [hI.index 2 W, h2.volume W, mul_div_assoc]
      norm_num
    · exact remark_10_6_a_of_index hI hp2 W
  refine ⟨ha, ?_⟩
  have hc2 := pointCountTwo
  intro p _ W _
  by_cases hp2 : p = 2
  · subst hp2
    rw [ha 2 (W.minimal ℤ_[2]), ofReal_localFactorInvAtOne_of W (fun _ => hc2.split _)
      (fun _ hns => hc2.nonsplit _ hns) (fun _ => hc2.additive _), mul_div_assoc]
  · exact remark_10_6_c_of_a hp2 W (ha p (W.minimal ℤ_[p]))

/-! ## $c_p$ at multiplicative reduction from the node disc -/

/-- **The residue disc of the node** (named input, $p$ odd): on a minimal equation with multiplicative reduction,
the complement of $E_0(\mathbb Q_p)$ on the $x$-line (the disc $x_0 + p\mathbb Z_p$ over the node) has measure
$(n - 1)(p - 1)/p$ at split reduction and $(\gcd(2, n) - 1)(p + 1)/p$ at non-split reduction,
$n = \operatorname{ord}_p\Delta$. This is an explicit one-variable integral: $\Psi_2^2 = u(x)\,((x - c)^2 - D)$ on the
disc with $u$ a unit of constant square class $s$, $\operatorname{ord}_p D = n$, and the shells
$|x - c|_p = p^{-k}$, $2k < n$, each give $2(1 - p^{-1})$ when $s$ is a square and $0$ otherwise; when $n$ is even the
centre $|x - c|_p \le p^{-n/2}$ gives the affine conic count $(p - \chi(s))/p$. -/
@[kb "milne2006ec" "Ch. IV, §10, c_p at multiplicative reduction: the node disc (named input), pdf p. 173"]
structure NodeDiscVolume : Prop where
  split : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic]
    [W.HasSplitMultiplicativeReduction ℤ_[p]],
    ∫⁻ x in (zeroComponentX W)ᶜ, omegaDensity W x ∂haarP p =
      (((Padic.valuation W.Δ).toNat - 1 : ℕ) : ℝ≥0∞) * ((p - 1 : ℕ) : ℝ≥0∞) / p
  nonsplit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic]
    [W.HasMultiplicativeReduction ℤ_[p]], ¬ W.HasSplitMultiplicativeReduction ℤ_[p] →
    ∫⁻ x in (zeroComponentX W)ᶜ, omegaDensity W x ∂haarP p =
      ((Int.gcd 2 (Padic.valuation W.Δ) - 1 : ℕ) : ℝ≥0∞) * ((p + 1 : ℕ) : ℝ≥0∞) / p

lemma measurableSet_zeroComponentX (W : WeierstrassCurve ℚ_[p]) [W.IsIntegral ℤ_[p]] :
    MeasurableSet (zeroComponentX W) := by
  classical
  rw [zeroComponentX_eq]
  refine MeasurableSet.union (measurableSet_lt measurable_const measurable_norm) (MeasurableSet.iUnion ?_)
  intro j
  split_ifs
  · exact Metric.isClosed_closedBall.measurableSet
  · exact MeasurableSet.empty

/-- At bad reduction $\operatorname{ord}_p\Delta \ge 1$. -/
lemma one_le_valuation_Δ (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] [W.IsMinimal ℤ_[p]]
    (hW : W.HasMultiplicativeReduction ℤ_[p] ∨ W.HasAdditiveReduction ℤ_[p]) : 1 ≤ Padic.valuation W.Δ := by
  have h0 : PadicInt.toZMod (W.integralModel ℤ_[p]).Δ = 0 := by
    rw [← reductionZMod_Δ]; exact reductionZMod_Δ_eq_zero W hW
  have hlt : ‖(W.integralModel ℤ_[p]).Δ‖ < 1 := (norm_lt_one_iff_toZMod _).mpr h0
  have hΔ : W.Δ = ((W.integralModel ℤ_[p]).Δ : ℚ_[p]) :=
    (WeierstrassCurve.integralModel_Δ_eq ℤ_[p] W).symm
  have hne : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  have hn := Padic.norm_eq_zpow_neg_valuation hne
  rw [hΔ] at hn hne
  rw [hΔ]
  have hlt' : ‖((W.integralModel ℤ_[p]).Δ : ℚ_[p])‖ < 1 := hlt
  rw [hn] at hlt'
  by_contra hv
  push Not at hv
  have : (1 : ℝ) ≤ (p : ℝ) ^ (-Padic.valuation ((W.integralModel ℤ_[p]).Δ : ℚ_[p])) :=
    one_le_zpow₀ (by exact_mod_cast hp.out.one_lt.le) (by omega)
  linarith

/-- The cancellation step: $c\,V_0 = V_0 + (m - 1)V_0$ with $0 < V_0 < \infty$ and $m \ge 1$ gives $c = m$. -/
lemma cancel_index {c m N : ℕ} (hm : 1 ≤ m) (hN : 0 < N)
    (h : (c : ℝ≥0∞) * ((N : ℝ≥0∞) / p) = (N : ℝ≥0∞) / p + ((m - 1 : ℕ) : ℝ≥0∞) * (N : ℝ≥0∞) / p) :
    c = m := by
  have hV0 : (N : ℝ≥0∞) / p ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, hN.ne']
  have hVt : (N : ℝ≥0∞) / p ≠ ⊤ := by
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top N) (by exact_mod_cast hp.out.ne_zero)
  rw [mul_div_assoc, ← one_add_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_cancel' hm] at h
  exact_mod_cast (ENNReal.mul_left_inj hV0 hVt).mp h

/-- **$c_p = \operatorname{ord}_p\Delta$ at split multiplicative reduction** ($p$ odd), from Milne's step 1 and the
node disc, without Tate's algorithm. -/
@[kb "milne2006ec" "Ch. IV, §10, c_p = ord Δ at split multiplicative reduction, pdf p. 173"]
theorem tamagawaNumber_of_split (hI : ZeroComponentIndex) (hD : NodeDiscVolume) (hp2 : p ≠ 2)
    (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] [hs : W.HasSplitMultiplicativeReduction ℤ_[p]] :
    (tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℤ) = Padic.valuation W.Δ := by
  have hv := one_le_valuation_Δ W (Or.inl hs.toHasMultiplicativeReduction)
  have h := hI.index p W
  unfold omegaVolume at h
  rw [← lintegral_add_compl (μ := haarP p) (omegaDensity W) (measurableSet_zeroComponentX W),
    omegaVolume_zeroComponent hp2 W,
    hD.split p hp2 W, card_reduction_of_split hp2 W] at h
  have hp3 : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  have := cancel_index (by omega) (by omega) h.symm
  rw [this]
  omega

/-- **$c_p = \gcd(2, \operatorname{ord}_p\Delta)$ at non-split multiplicative reduction** ($p$ odd), from Milne's
step 1 and the node disc, without Tate's algorithm. -/
@[kb "milne2006ec" "Ch. IV, §10, c_p = gcd(2, ord Δ) at nonsplit multiplicative reduction, pdf p. 173"]
theorem tamagawaNumber_of_nonsplit (hI : ZeroComponentIndex) (hD : NodeDiscVolume) (hp2 : p ≠ 2)
    (W : WeierstrassCurve ℚ_[p]) [W.IsElliptic] [hm : W.HasMultiplicativeReduction ℤ_[p]]
    (hns : ¬ W.HasSplitMultiplicativeReduction ℤ_[p]) :
    (tamagawaNumber ℚ_[p] (W.integralModel ℤ_[p]).toProjective : ℤ) = Int.gcd 2 (Padic.valuation W.Δ) := by
  have h := hI.index p W
  unfold omegaVolume at h
  rw [← lintegral_add_compl (μ := haarP p) (omegaDensity W) (measurableSet_zeroComponentX W),
    omegaVolume_zeroComponent hp2 W,
    hD.nonsplit p hp2 W hns, card_reduction_of_nonsplit hp2 W hns] at h
  have hg : 1 ≤ Int.gcd 2 (Padic.valuation W.Δ) := Int.gcd_pos_of_ne_zero_left _ (by norm_num)
  have := cancel_index hg (by omega) h.symm
  rw [this]

end NumberFieldKB.MilneEC.LocalPeriod
