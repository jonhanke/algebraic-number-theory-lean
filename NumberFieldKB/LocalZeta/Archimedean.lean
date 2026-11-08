import NumberFieldKB.LocalZeta.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Local zeta integrals at the archimedean places: convergence

$K$ is $\mathbb R$ or $\mathbb C$, or more generally a nontrivially normed field which is a finite-dimensional real
normed space of dimension $d$, with an additive Haar measure $dx$ and modulus $|x|_K = \|x\|^d$ (for $\mathbb R$:
$|x|$; for $\mathbb C$: $|z|^2$).

* `Units.borelSpace`: Mathlib's measurable structure on $K^\times$ (pulled back from $K$) is the Borel one.
* **`integrable_zetaIntegrand_of_decay`**: if $f$ is continuous and bounded with $\|x\|^k|f(x)|$ bounded, $\chi$ is
  continuous with $|\chi| = |\cdot|_K^a$, and $0 < a + \operatorname{Re}s < k/d$, then $f(x)\chi(x)|x|_K^s$ is integrable
  for $d^\times x = |x|_K^{-1}dx$. Schwartz functions satisfy the hypothesis for every $k$
  (**`integrable_zetaIntegrand_schwartz`**), so $Z(f,\chi,s)$ converges absolutely for $\operatorname{Re}s > -a$.

The proof integrates in polar coordinates (Mathlib's `integrable_fun_norm_addHaar`): the integrand is dominated by
$r\mapsto r^{d(a+\operatorname{Re}s)-d}\min(C, C'r^{-k})$.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace NumberFieldKB.LocalZeta

noncomputable section

open QuadFormsKB.Tamagawa.Measure.Weil

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

/-- Mathlib's measurable structure on the units of a normed field (the pull-back along `Units.val`) is the Borel
structure of the units topology. -/
instance Units.borelSpace {K : Type*} [NontriviallyNormedField K] [MeasurableSpace K] [BorelSpace K] :
    BorelSpace Kˣ :=
  ⟨by
    have h1 : (Units.instMeasurableSpace : MeasurableSpace Kˣ) = MeasurableSpace.comap Units.val (borel K) := by
      rw [← BorelSpace.measurable_eq (α := K)]; rfl
    calc (Units.instMeasurableSpace : MeasurableSpace Kˣ) = MeasurableSpace.comap Units.val (borel K) := h1
      _ = @borel Kˣ (TopologicalSpace.induced Units.val inferInstance) := borel_comap.symm
      _ = borel Kˣ := by rw [← Units.isEmbedding_val₀.eq_induced]⟩

variable {K : Type*} [NontriviallyNormedField K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]
  [MeasurableSpace K] [BorelSpace K]

instance : LocallyCompactSpace K := by have := FiniteDimensional.proper ℝ K; infer_instance

instance : SecondCountableTopology K := by have := FiniteDimensional.proper ℝ K; infer_instance

/-- The radial majorant: integrable in polar coordinates. -/
theorem integrableOn_radial_majorant {d : ℕ} (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) {k : ℕ} (hk : (d : ℝ) * b < k)
    (C C' : ℝ) :
    IntegrableOn (fun y : ℝ => y ^ (d - 1) *
      (if y ≤ 1 then C * y ^ ((d : ℝ) * b - d) else C' * y ^ ((d : ℝ) * b - d - k))) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h : IntegrableOn (fun y : ℝ => C * y ^ ((d : ℝ) * b - 1)) (Ioc 0 1) := by
      refine (((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).mpr ?_).congr_set_ae Ioo_ae_eq_Ioc.symm).const_mul C
      have : (0 : ℝ) < d * b := mul_pos (by exact_mod_cast hd) hb
      linarith
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioc
    have hy0 : 0 < y := hy.1
    rw [ite_eq_left hy.2, ← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hy0, Nat.cast_sub hd, Nat.cast_one]
    ring_nf
  · have h : IntegrableOn (fun y : ℝ => C' * y ^ ((d : ℝ) * b - 1 - k)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C'
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : 0 < y := zero_lt_one.trans hy
    rw [ite_eq_right (not_le.mpr hy), ← Real.rpow_natCast, mul_left_comm, ← Real.rpow_add hy0, Nat.cast_sub hd,
      Nat.cast_one]
    ring_nf

/-- **Absolute convergence of archimedean local zeta integrals** under a decay hypothesis on $f$. -/
theorem integrable_zetaIntegrand_of_decay (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (hΔc : Continuous (distribHaarChar K : Kˣ → ℝ≥0))
    (hΔ : ∀ u : Kˣ, (distribHaarChar K u : ℝ) = ‖(u : K)‖ ^ Module.finrank ℝ K)
    {f : K → ℂ} (hf : Continuous f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {k : ℕ} {C' : ℝ}
    (hk : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ C') {χ : Kˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar K u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re)
    (hsk : (Module.finrank ℝ K : ℝ) * (a + s.re) < k) :
    Integrable (zetaIntegrand f χ s) (unitsHaar K μ) := by
  set d := Module.finrank ℝ K
  set b := a + s.re
  have hd : 1 ≤ d := Module.finrank_pos
  have : Nontrivial K := inferInstance
  refine ⟨?_, ?_⟩
  · refine (((hf.comp Units.continuous_val).mul (Units.continuous_val.comp hχc)).mul ?_).aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hΔc)).cpow continuous_const
      fun u => Complex.ofReal_mem_slitPlane.mpr (distribHaarChar_pos' u)
  -- the function on `K` to integrate
  set h : K → ℝ := fun x => ‖f x‖ * ‖x‖ ^ ((d : ℝ) * b - d)
  set G : ℝ → ℝ := fun y => if y ≤ 1 then C * y ^ ((d : ℝ) * b - d) else C' * y ^ ((d : ℝ) * b - d - k)
  have hGint : Integrable (fun x : K => G ‖x‖) μ := by
    rw [integrable_fun_norm_addHaar μ]
    refine (integrableOn_radial_majorant hd (show 0 < b from hs) hsk C C').congr_fun (fun y _ => ?_)
      measurableSet_Ioi
    simp only [G, smul_eq_mul]
    rfl
  have hh0 : ∀ x, 0 ≤ h x := fun x => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hhint : Integrable h μ := by
    refine hGint.mono' (hf.norm.measurable.mul (continuous_norm.measurable.pow_const _)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hh0 x)]
    simp only [h, G]
    split_ifs with hx
    · exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (norm_nonneg _) _)
    · have hx1 : 1 < ‖x‖ := lt_of_not_ge hx
      have hxpos : 0 < ‖x‖ := zero_lt_one.trans hx1
      have hfx : ‖f x‖ ≤ C' * (‖x‖ ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hxpos k), mul_comm]
        exact hk x
      calc ‖f x‖ * ‖x‖ ^ ((d : ℝ) * b - d) ≤ C' * (‖x‖ ^ k)⁻¹ * ‖x‖ ^ ((d : ℝ) * b - d) :=
            mul_le_mul_of_nonneg_right hfx (Real.rpow_nonneg (norm_nonneg _) _)
        _ = C' * ‖x‖ ^ ((d : ℝ) * b - d - k) := by
            rw [Real.rpow_sub hxpos ((d : ℝ) * b - d) k, Real.rpow_natCast]
            ring
  have hpt : ∀ u : Kˣ, ‖zetaIntegrand f χ s u‖ₑ =
      ENNReal.ofReal (h u) * (distribHaarChar K u : ℝ≥0∞) := by
    intro u
    have hpos := distribHaarChar_pos' u
    have hu : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
    rw [← ofReal_norm, zetaIntegrand, norm_mul, norm_mul, hχ, Complex.norm_cpow_eq_rpow_re_of_pos hpos,
      mul_assoc, ← Real.rpow_add hpos, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (hh0 _)]
    congr 1
    simp only [h]
    rw [mul_assoc]
    congr 1
    rw [hΔ, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_add hu]
    congr 1
    ring
  rw [HasFiniteIntegral]
  simp_rw [hpt]
  rw [lintegral_unitsHaar_mul_modulus hΔc μ (fun x => ENNReal.ofReal (h x))]
  have := hhint.hasFiniteIntegral
  rw [HasFiniteIntegral] at this
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) this
  rw [← ofReal_norm, Real.norm_of_nonneg (hh0 x)]

/-- **Absolute convergence of archimedean local zeta integrals of Schwartz functions**: for $f\in\mathcal S(K)$,
$\chi$ continuous with $|\chi| = |\cdot|_K^a$ and $\operatorname{Re}s > -a$, the integrand $f(x)\chi(x)|x|_K^s$ is integrable
for $d^\times x = |x|_K^{-1}dx$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4 [unverified locator] (ζ(f, c) converges for σ > 0)"]
theorem integrable_zetaIntegrand_schwartz (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (hΔc : Continuous (distribHaarChar K : Kˣ → ℝ≥0))
    (hΔ : ∀ u : Kˣ, (distribHaarChar K u : ℝ) = ‖(u : K)‖ ^ Module.finrank ℝ K)
    (f : SchwartzMap K ℂ) {χ : Kˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar K u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re) :
    Integrable (zetaIntegrand f χ s) (unitsHaar K μ) := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((Module.finrank ℝ K : ℝ) * (a + s.re))
  exact integrable_zetaIntegrand_of_decay μ hΔc hΔ f.continuous (SchwartzMap.norm_le_seminorm ℝ f)
    (SchwartzMap.norm_pow_mul_le_seminorm ℝ f k) hχc hχ hs hk

end

end NumberFieldKB.LocalZeta
