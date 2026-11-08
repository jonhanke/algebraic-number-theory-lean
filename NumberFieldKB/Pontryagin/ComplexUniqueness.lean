import NumberFieldKB.Pontryagin.FourierInversion

/-!
# Uniqueness for complex densities on the dual group, given Bochner

$H$ is a locally compact commutative group, $H^*$ its dual. Bochner's uniqueness half (`BochnerTheorem.ext`) is
for finite positive inner regular measures; here it is extended to a complex density.

* **`measureReal_eq_setIntegral_of_fourierStieltjes`**: if $\nu$ is a finite inner regular measure on $H^*$, $\rho$ a
  measure on $H^*$ inner regular on sets of finite measure, and $h$ a bounded measurable $\rho$-integrable complex
  function with $\int\chi(x)\,d\nu(\chi)=\int\chi(x)h(\chi)\,d\rho(\chi)$ for all $x\in H$, then
  $\nu(A)=\int_Ah\,d\rho$ for every measurable $A$.

Proof: write $h=h_1-h_2+i(h_3-h_4)$ with $h_k\ge0$ (positive and negative parts of the real and imaginary parts), and
$Q_k=h_k\rho$. Then $\hat\nu+\hat Q_2-\hat Q_1=i(\hat Q_3-\hat Q_4)$; both sides are Hermitian
($\overline{\hat Q(x)}=\hat Q(x^{-1})$), which forces both to vanish, so $\nu+Q_2=Q_1$ and $Q_3=Q_4$ by Bochner's
uniqueness (Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Theorem 4.33, the uniqueness argument).
-/

open MeasureTheory Topology Filter ComplexConjugate

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [MeasurableSpace (PontryaginDual H)] [BorelSpace (PontryaginDual H)]

/-- Evaluation of characters at a point is measurable. -/
lemma measurable_eval_char (x : H) : Measurable fun ω : PontryaginDual H => ((ω x : Circle) : ℂ) :=
by
  have hc : Continuous fun ω : PontryaginDual H => ((ω x : Circle) : ℂ) :=
    continuous_subtype_val.comp ((continuous_eval_const (F := C(H, Circle)) x).comp
      (ContinuousMonoidHom.isInducing_toContinuousMap H Circle).continuous)
  exact hc.measurable

/-- The transform of any measure on the dual is Hermitian. -/
lemma conj_fs (Q : Measure (PontryaginDual H)) (y : H) :
    conj (fourierStieltjes Q y) = fourierStieltjes Q y⁻¹ := by
  unfold fourierStieltjes
  rw [← integral_conj]
  congr 1 with ξ
  rw [map_inv, Circle.coe_inv_eq_conj]

/-- Transform of a measure with `NNReal` density. -/
lemma fs_wd (ρ : Measure (PontryaginDual H)) {r : PontryaginDual H → NNReal} (hr : Measurable r) (x : H) :
    fourierStieltjes (ρ.withDensity fun ξ => (r ξ : ENNReal)) x =
      ∫ ξ, ((r ξ : ℝ) : ℂ) * ((ξ x : Circle) : ℂ) ∂ρ := by
  unfold fourierStieltjes
  rw [integral_withDensity_eq_integral_smul hr]
  rfl

/-- A density bounded by `‖h‖` gives a finite inner regular measure. -/
lemma withDensity_fin_ir (ρ : Measure (PontryaginDual H)) [ρ.InnerRegularCompactLTTop]
    {h : PontryaginDual H → ℂ} {C : ℝ} (hC : ∀ ω, ‖h ω‖ ≤ C) (hi : Integrable h ρ)
    {q : PontryaginDual H → NNReal} (hq : Measurable q) (hqh : ∀ ω, (q ω : ℝ) ≤ ‖h ω‖) :
    IsFiniteMeasure (ρ.withDensity fun ω => (q ω : ENNReal)) ∧
      (ρ.withDensity fun ω => (q ω : ENNReal)).InnerRegular := by
  have hfin : ∫⁻ ω, (q ω : ENNReal) ∂ρ ≠ ⊤ := by
    refine ne_top_of_le_ne_top hi.hasFiniteIntegral.ne (lintegral_mono fun ω => ?_)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hqh ω)
  refine ⟨isFiniteMeasure_withDensity hfin, innerRegular_withDensity ρ
    (measurable_coe_nnreal_ennreal.comp hq) (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun ω => ?_) hfin⟩
  rw [← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal ((hqh ω).trans (hC ω))

/-- Integrability of a bounded density. -/
lemma integrable_density (ρ : Measure (PontryaginDual H)) {h : PontryaginDual H → ℂ} (hi : Integrable h ρ)
    {q : PontryaginDual H → NNReal} (hq : Measurable q) (hqh : ∀ ω, (q ω : ℝ) ≤ ‖h ω‖) :
    Integrable (fun ω => (q ω : ℝ)) ρ :=
  Integrable.mono' hi.norm hq.coe_nnreal_real.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [NNReal.norm_eq]; exact hqh ω)

/-- Integrability of density times character. -/
lemma integrable_density_char (ρ : Measure (PontryaginDual H)) {h : PontryaginDual H → ℂ}
    (hi : Integrable h ρ) {q : PontryaginDual H → NNReal} (hq : Measurable q)
    (hqh : ∀ ω, (q ω : ℝ) ≤ ‖h ω‖) (x : H) :
    Integrable (fun ω => ((q ω : ℝ) : ℂ) * ((ω x : Circle) : ℂ)) ρ :=
  Integrable.mono' (integrable_density ρ hi hq hqh)
    ((Complex.measurable_ofReal.comp hq.coe_nnreal_real).mul (measurable_eval_char x)).aestronglyMeasurable
    (ae_of_all _ fun ω => by simp)

/-- Real measure of a set for a measure with density. -/
lemma real_withDensity (ρ : Measure (PontryaginDual H)) {q : PontryaginDual H → NNReal} (hq : Measurable q)
    {A : Set (PontryaginDual H)} (hA : MeasurableSet A) :
    (ρ.withDensity fun ω => (q ω : ENNReal)).real A = ∫ ω in A, (q ω : ℝ) ∂ρ := by
  rw [Measure.real, withDensity_apply _ hA,
    integral_eq_lintegral_of_nonneg_ae (f := fun ω => (q ω : ℝ)) (ae_of_all _ fun ω => NNReal.coe_nonneg _)
      (hq.coe_nnreal_real.aestronglyMeasurable (μ := ρ.restrict A))]
  simp

/-- The uniqueness statement for an explicit decomposition of the density. -/
theorem uniqueness_aux (hB : BochnerTheorem.{u}) (ν ρ : Measure (PontryaginDual H)) [IsFiniteMeasure ν]
    [ν.InnerRegular] [ρ.InnerRegularCompactLTTop] {h : PontryaginDual H → ℂ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ ω, ‖h ω‖ ≤ C) (hi : Integrable h ρ)
    (hFS : ∀ x, fourierStieltjes ν x = ∫ ω, ((ω x : Circle) : ℂ) * h ω ∂ρ)
    {q1 q2 q3 q4 : PontryaginDual H → NNReal} (m1 : Measurable q1) (m2 : Measurable q2)
    (m3 : Measurable q3) (m4 : Measurable q4) (b1 : ∀ ω, (q1 ω : ℝ) ≤ ‖h ω‖) (b2 : ∀ ω, (q2 ω : ℝ) ≤ ‖h ω‖)
    (b3 : ∀ ω, (q3 ω : ℝ) ≤ ‖h ω‖) (b4 : ∀ ω, (q4 ω : ℝ) ≤ ‖h ω‖)
    (hdec : ∀ ω, h ω = ((q1 ω : ℝ) : ℂ) - ((q2 ω : ℝ) : ℂ) + (((q3 ω : ℝ) : ℂ) - ((q4 ω : ℝ) : ℂ)) * Complex.I)
    {A : Set (PontryaginDual H)} (hA : MeasurableSet A) :
    ((ν.real A : ℝ) : ℂ) = ∫ ω in A, h ω ∂ρ := by
  obtain ⟨f1, i1⟩ := withDensity_fin_ir ρ hC hi m1 b1
  obtain ⟨f2, i2⟩ := withDensity_fin_ir ρ hC hi m2 b2
  obtain ⟨f3, i3⟩ := withDensity_fin_ir ρ hC hi m3 b3
  obtain ⟨f4, i4⟩ := withDensity_fin_ir ρ hC hi m4 b4
  set Q1 := ρ.withDensity fun ω => (q1 ω : ENNReal) with hQ1
  set Q2 := ρ.withDensity fun ω => (q2 ω : ENNReal) with hQ2
  set Q3 := ρ.withDensity fun ω => (q3 ω : ENNReal) with hQ3
  set Q4 := ρ.withDensity fun ω => (q4 ω : ENNReal) with hQ4
  have hI : ∀ x, Integrable (fun ω => ((ω x : Circle) : ℂ) * h ω) ρ := fun x =>
    Integrable.mono' hi.norm ((measurable_eval_char x).mul hm).aestronglyMeasurable
      (ae_of_all _ fun ω => by simp)
  have hrel : ∀ x, fourierStieltjes ν x + fourierStieltjes Q2 x - fourierStieltjes Q1 x =
      Complex.I * (fourierStieltjes Q3 x - fourierStieltjes Q4 x) := by
    intro x
    have hs : Integrable (fun ω => ((ω x : Circle) : ℂ) * h ω + ((q2 ω : ℝ) : ℂ) * ((ω x : Circle) : ℂ)) ρ :=
      (hI x).add (integrable_density_char ρ hi m2 b2 x)
    rw [hFS, hQ1, hQ2, hQ3, hQ4, fs_wd ρ m1, fs_wd ρ m2, fs_wd ρ m3, fs_wd ρ m4,
      ← integral_add (hI x) (integrable_density_char ρ hi m2 b2 x),
      ← integral_sub hs (integrable_density_char ρ hi m1 b1 x),
      ← integral_sub (integrable_density_char ρ hi m3 b3 x) (integrable_density_char ρ hi m4 b4 x),
      ← integral_const_mul]
    congr 1 with ω
    linear_combination (((ω x : Circle) : ℂ)) * (hdec ω)
  have hc1 : ∀ x, conj (fourierStieltjes ν x + fourierStieltjes Q2 x - fourierStieltjes Q1 x) =
      fourierStieltjes ν x⁻¹ + fourierStieltjes Q2 x⁻¹ - fourierStieltjes Q1 x⁻¹ := by
    intro x; rw [map_sub, map_add, conj_fs, conj_fs, conj_fs]
  have hd2' : ∀ x, fourierStieltjes Q3 x⁻¹ - fourierStieltjes Q4 x⁻¹ = 0 := by
    intro x
    have h1 := hrel x⁻¹
    have h2 := congrArg conj (hrel x)
    rw [hc1, map_mul, Complex.conj_I, map_sub, conj_fs, conj_fs, h1] at h2
    have h3 : (2 * Complex.I) * (fourierStieltjes Q3 x⁻¹ - fourierStieltjes Q4 x⁻¹) = 0 := by
      linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (by simp)
  have hd2 : ∀ x, fourierStieltjes Q3 x - fourierStieltjes Q4 x = 0 := fun x => by simpa using hd2' x⁻¹
  have hd1 : ∀ x, fourierStieltjes ν x + fourierStieltjes Q2 x - fourierStieltjes Q1 x = 0 := fun x => by
    rw [hrel, hd2, mul_zero]
  have intE : ∀ (μ : Measure (PontryaginDual H)) [IsFiniteMeasure μ] (x : H),
      Integrable (fun ω : PontryaginDual H => ((ω x : Circle) : ℂ)) μ := fun μ _ x =>
    Integrable.of_bound (measurable_eval_char x).aestronglyMeasurable 1 (ae_of_all _ fun ω => by simp)
  have e1 : ν + Q2 = Q1 := hB.ext H (ν + Q2) Q1 inferInstance f1 inferInstance i1 (fun x => by
    have : fourierStieltjes (ν + Q2) x = fourierStieltjes ν x + fourierStieltjes Q2 x := by
      unfold fourierStieltjes
      exact integral_add_measure (intE ν x) (intE Q2 x)
    rw [this]; linear_combination hd1 x)
  have e2 : Q3 = Q4 := hB.ext H Q3 Q4 f3 f4 i3 i4 (fun x => by linear_combination hd2 x)
  have r1 : ν.real A + Q2.real A = Q1.real A := by
    have := congrArg (fun m : Measure (PontryaginDual H) => (m A).toReal) e1
    simp only [Measure.add_apply] at this
    rw [ENNReal.toReal_add (measure_ne_top ν A) (measure_ne_top Q2 A)] at this
    exact this
  have r2 : Q3.real A = Q4.real A := by rw [e2]
  have s1 : Q1.real A = ∫ ω in A, (q1 ω : ℝ) ∂ρ := real_withDensity ρ m1 hA
  have s2 : Q2.real A = ∫ ω in A, (q2 ω : ℝ) ∂ρ := real_withDensity ρ m2 hA
  have s3 : Q3.real A = ∫ ω in A, (q3 ω : ℝ) ∂ρ := real_withDensity ρ m3 hA
  have s4 : Q4.real A = ∫ ω in A, (q4 ω : ℝ) ∂ρ := real_withDensity ρ m4 hA
  have hiA : Integrable h (ρ.restrict A) := hi.restrict
  have hre := integral_re hiA
  have him := integral_im hiA
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hre him
  have dre : ∀ ω, (h ω).re = (q1 ω : ℝ) - q2 ω := fun ω => by simpa using congrArg Complex.re (hdec ω)
  have dim : ∀ ω, (h ω).im = (q3 ω : ℝ) - q4 ω := fun ω => by simpa using congrArg Complex.im (hdec ω)
  apply Complex.ext
  · rw [Complex.ofReal_re, ← hre]
    simp_rw [dre]
    rw [integral_sub (integrable_density ρ hi m1 b1).integrableOn (integrable_density ρ hi m2 b2).integrableOn]
    linarith
  · rw [Complex.ofReal_im, ← him]
    simp_rw [dim]
    rw [integral_sub (integrable_density ρ hi m3 b3).integrableOn (integrable_density ρ hi m4 b4).integrableOn]
    linarith

/-- Real-valued bound for the positive part of a bounded function. -/
lemma toNNReal_le_norm {h : PontryaginDual H → ℂ} {f : PontryaginDual H → ℝ} (hf : ∀ ω, |f ω| ≤ ‖h ω‖)
    (ω : PontryaginDual H) : (((f ω).toNNReal : NNReal) : ℝ) ≤ ‖h ω‖ := by
  rw [Real.coe_toNNReal']
  exact max_le ((le_abs_self _).trans (hf ω)) (norm_nonneg _)

/-- **Uniqueness for a complex density** (given Bochner). -/
theorem measureReal_eq_setIntegral_of_fourierStieltjes (hB : BochnerTheorem.{u}) {H : Type u} [CommGroup H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [MeasurableSpace (PontryaginDual H)]
    [BorelSpace (PontryaginDual H)] (ν ρ : Measure (PontryaginDual H)) [IsFiniteMeasure ν] [ν.InnerRegular]
    [ρ.InnerRegularCompactLTTop] {h : PontryaginDual H → ℂ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ ω, ‖h ω‖ ≤ C) (hi : Integrable h ρ)
    (hFS : ∀ x, fourierStieltjes ν x = ∫ ω, ((ω x : Circle) : ℂ) * h ω ∂ρ)
    {A : Set (PontryaginDual H)} (hA : MeasurableSet A) :
    ((ν.real A : ℝ) : ℂ) = ∫ ω in A, h ω ∂ρ := by
  have hre : ∀ ω, |(h ω).re| ≤ ‖h ω‖ := fun ω => Complex.abs_re_le_norm _
  have him : ∀ ω, |(h ω).im| ≤ ‖h ω‖ := fun ω => Complex.abs_im_le_norm _
  have hre' : ∀ ω, |-(h ω).re| ≤ ‖h ω‖ := fun ω => by rw [abs_neg]; exact hre ω
  have him' : ∀ ω, |-(h ω).im| ≤ ‖h ω‖ := fun ω => by rw [abs_neg]; exact him ω
  have mre : Measurable fun ω => (h ω).re := Complex.measurable_re.comp hm
  have mim : Measurable fun ω => (h ω).im := Complex.measurable_im.comp hm
  refine uniqueness_aux hB ν ρ hm hC hi hFS (q1 := fun ω => (h ω).re.toNNReal)
    (q2 := fun ω => (-(h ω).re).toNNReal) (q3 := fun ω => (h ω).im.toNNReal)
    (q4 := fun ω => (-(h ω).im).toNNReal) mre.real_toNNReal mre.neg.real_toNNReal mim.real_toNNReal
    mim.neg.real_toNNReal (toNNReal_le_norm hre) (toNNReal_le_norm hre') (toNNReal_le_norm him)
    (toNNReal_le_norm him') ?_ hA
  intro ω
  have e1 := max_zero_sub_max_neg_zero_eq_self (h ω).re
  have e2 := max_zero_sub_max_neg_zero_eq_self (h ω).im
  simp only [Real.coe_toNNReal']
  apply Complex.ext <;> simp <;> linarith

end NumberFieldKB.Pontryagin
