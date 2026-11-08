import NumberFieldKB.LocalZeta.Real
import QuadFormsKB.Analysis.WeilIndexInf
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Local zeta integrals at a complex place

On $\mathbb C$ we use QuadFormsKB's conventions at a complex place (`Analysis/WeilIndexInf.lean`): the character
$\psi_{\mathbb C}(z) = e(2\operatorname{Re}z) = e(\operatorname{Tr}_{\mathbb C/\mathbb R}z)$ (`psiC`), the self-dual measure
$dz = 2\,dx\,dy$ (`muC`), and the Fourier transform `fourierC` $\hat f(\eta) = 2\int f(z)e(2\operatorname{Re}(z\eta))\,dx\,dy$
(`fourier_muC_psiC`). The modulus is $|z|_{\mathbb C} = |z|^2$ (`distribHaarChar_complex`) and **Tate's multiplicative
measure** is $d^\times z = dz/|z|_{\mathbb C} = 2\,dx\,dy/|z|^2$ (`tateHaarC` = `unitsHaar ℂ muC`).

* **`zetaIntegral_gaussian_complex`**: $Z(e^{-2\pi|z|^2}, 1, s) = (2\pi)^{1-s}\Gamma(s) = \pi\,\Gamma_{\mathbb C}(s)$ for
  $\operatorname{Re}s > 0$, with Tate's measure. With the measure $d^\times z/\pi = 2\,dx\,dy/(\pi|z|^2)$ the value is
  Mathlib's $\Gamma_{\mathbb C}(s) = 2(2\pi)^{-s}\Gamma(s)$ (`zetaIntegral_gaussian_complex'`).
* **`zetaIntegral_fourierC_comm`**: the local functional equation for Schwartz functions ($|\chi| = |\cdot|_{\mathbb C}^a$,
  $0 < a + \operatorname{Re}s < 1$); `fourierC_schwartz`: $\hat f$ is a Schwartz function
  ($\hat f(\eta) = 2\,\mathcal F^{-1}f(2\bar\eta)$ in Mathlib's normalization).
* **`zetaIntegral_fourierC_one`**: $Z(\hat f, 1, 1-s) = \dfrac{\Gamma_{\mathbb C}(1-s)}{\Gamma_{\mathbb C}(s)}Z(f, 1, s)$
  ($0 < \operatorname{Re}s < 1$), using the self-dual Gaussian $e^{-2\pi|z|^2}$.

Source: Tate's thesis, Cassels–Fröhlich Ch. XV, §2.5 (the complex computation, $d^\times z = 2\,dx\,dy/|z|^2$)
[unverified locators].
-/

open MeasureTheory Filter Topology Set Complex
open scoped ENNReal NNReal FourierTransform Pointwise ComplexConjugate

namespace NumberFieldKB.LocalZeta

noncomputable section

open QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Analysis

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

/-! ### The modulus and Tate's measure on $\mathbb C^\times$ -/

/-- **The modulus of $\mathbb C$** is the square of the absolute value: $\Delta_{\mathbb C}(u) = |u|^2$. -/
theorem distribHaarChar_complex (u : ℂˣ) : (distribHaarChar ℂ u : ℝ) = ‖(u : ℂ)‖ ^ 2 := by
  set s : Set ℂ := Metric.ball 0 1
  have hs0 : (volume : Measure ℂ) s ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have hsT : (volume : Measure ℂ) s ≠ ⊤ := measure_ball_lt_top.ne
  have himg : u • s = LinearMap.mulLeft ℝ (u : ℂ) '' s := by
    ext x; simp [Set.mem_smul_set, Units.smul_def]
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ (u : ℂ)) = Complex.normSq u := by
    rw [← Algebra.norm_complex_apply, Algebra.norm_apply]; rfl
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (g := u) hs0 hsT
    (r := Real.toNNReal (‖(u : ℂ)‖ ^ 2)) (by
      rw [himg, Measure.addHaar_image_linearMap, hdet, abs_of_nonneg (Complex.normSq_nonneg _),
        ← Complex.sq_norm, ENNReal.ofReal])
  rw [this, Real.coe_toNNReal _ (sq_nonneg _)]

theorem distribHaarChar_complex' (u : ℂˣ) :
    (distribHaarChar ℂ u : ℝ) = ‖(u : ℂ)‖ ^ Module.finrank ℝ ℂ := by
  rw [distribHaarChar_complex, Complex.finrank_real_complex]

theorem continuous_distribHaarChar_complex : Continuous (distribHaarChar ℂ : ℂˣ → ℝ≥0) := by
  refine continuous_induced_rng.mpr ?_
  have : (fun u : ℂˣ => (distribHaarChar ℂ u : ℝ)) = fun u : ℂˣ => ‖(u : ℂ)‖ ^ 2 :=
    funext distribHaarChar_complex
  change Continuous fun u : ℂˣ => (distribHaarChar ℂ u : ℝ)
  rw [this]
  exact (continuous_norm.comp Units.continuous_val).pow 2

/-- **The self-dual measure on $\mathbb C$**: $dz = 2\,dx\,dy$ (for $\psi_{\mathbb C}$). -/
def muC : Measure ℂ := (2 : ℝ≥0) • (volume : Measure ℂ)

instance : muC.IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul _ two_ne_zero

instance : muC.Regular := by
  unfold muC
  exact Measure.Regular.smul (by simp)

/-- **Tate's multiplicative measure on $\mathbb C^\times$**: $d^\times z = dz/|z|_{\mathbb C} = 2\,dx\,dy/|z|^2$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (d^×z = 2 dx dy/|z|² at a complex place)"]
def tateHaarC : Measure ℂˣ := unitsHaar ℂ muC

instance : tateHaarC.IsHaarMeasure :=
  isHaarMeasure_unitsHaar isOpenEmbedding_units_val continuous_distribHaarChar_complex _

/-- Absolute convergence on $\mathbb C$ for Schwartz functions and $\operatorname{Re}s > -a$,
$|\chi| = |\cdot|_{\mathbb C}^a$. -/
theorem integrable_zetaIntegrand_complex (f : SchwartzMap ℂ ℂ) {χ : ℂˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar ℂ u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re) :
    Integrable (zetaIntegrand f χ s) tateHaarC :=
  integrable_zetaIntegrand_schwartz _ continuous_distribHaarChar_complex distribHaarChar_complex' f hχc hχ hs

/-! ### The Gaussian -/

/-- The self-dual Gaussian $e^{-2\pi|z|^2}$ on $\mathbb C$ (QuadFormsKB's `gaussianSchwartz`; it is `gaussC`). -/
def gaussCS : SchwartzMap ℂ ℂ := gaussianSchwartz (E := ℂ) (2 * Real.pi : ℂ) (by simp [Real.pi_pos])

theorem gaussCS_apply (z : ℂ) : gaussCS z = cexp (-(2 * Real.pi : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) := by
  rw [gaussCS, gaussianSchwartz_apply]

/-- On $\mathbb C$: $\int_{\mathbb C^\times}F(|u|)|u|_{\mathbb C}^s\,d^\times u = 4\pi\int_0^\infty F(r)r^{2s-1}\,dr$. -/
theorem integral_tateHaarC_radial (F : ℝ → ℂ) (s : ℂ) :
    ∫ u, F ‖(u : ℂ)‖ * ((distribHaarChar ℂ u : ℝ) : ℂ) ^ s ∂tateHaarC =
      4 * Real.pi * mellin F (2 * s) := by
  set h : ℂ → ℂ := fun x => F ‖x‖ * (((‖x‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1)
  have hpt : ∀ u : ℂˣ, F ‖(u : ℂ)‖ * ((distribHaarChar ℂ u : ℝ) : ℂ) ^ s =
      h u * ((distribHaarChar ℂ u : ℝ) : ℂ) := by
    intro u
    have hu : (((‖(u : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr u.ne_zero)
    simp only [h, distribHaarChar_complex]
    rw [mul_assoc, show (((‖(u : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1) * (((‖(u : ℂ)‖ ^ 2 : ℝ)) : ℂ) =
        (((‖(u : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ (s - 1) * (((‖(u : ℂ)‖ ^ 2 : ℝ)) : ℂ) ^ (1 : ℂ) by rw [cpow_one],
      ← cpow_add _ _ hu, sub_add_cancel]
  calc ∫ u, F ‖(u : ℂ)‖ * ((distribHaarChar ℂ u : ℝ) : ℂ) ^ s ∂tateHaarC
      = ∫ u, h u * ((distribHaarChar ℂ u : ℝ) : ℂ) ∂tateHaarC :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ x, h x ∂muC := integral_unitsHaar_mul_modulus continuous_distribHaarChar_complex muC h
    _ = 4 * Real.pi * mellin F (2 * s) := by
      rw [muC, integral_smul_nnreal_measure,
        integral_fun_norm_addHaar volume (fun r : ℝ => F r * (((r ^ 2 : ℝ)) : ℂ) ^ (s - 1))]
      simp only [Complex.finrank_real_complex, Measure.real, Complex.volume_ball, ENNReal.ofReal_one, one_pow,
        one_mul, mellin, smul_eq_mul, NNReal.smul_def, real_smul, nsmul_eq_mul]
      rw [ENNReal.coe_toReal, NNReal.coe_real_pi]
      have hI : ∫ y in Ioi (0 : ℝ), ((y ^ (2 - 1) : ℝ) : ℂ) * (F y * (((y ^ 2 : ℝ)) : ℂ) ^ (s - 1)) =
          ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (2 * s - 1) * F t := by
        refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
        have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
        have hsq : (((r ^ 2 : ℝ)) : ℂ) ^ (s - 1) = (r : ℂ) ^ (2 * s - 2) := by
          rw [show ((r ^ 2 : ℝ) : ℂ) = (r : ℂ) * (r : ℂ) by push_cast; ring,
            mul_cpow_ofReal_nonneg (le_of_lt hr) (le_of_lt hr), show 2 * s - 2 = (s - 1) + (s - 1) by ring,
            cpow_add _ _ hr0]
        rw [hsq, show (2 * s - 1) = (2 * s - 2) + 1 by ring, cpow_add _ _ hr0, cpow_one]
        norm_num
        ring
      rw [hI]
      push_cast
      ring

/-- **The complex Gaussian zeta integral** (Tate, Cassels–Fröhlich Ch. XV, §2.5): with Tate's
$d^\times z = 2\,dx\,dy/|z|^2$ and $\operatorname{Re}s > 0$,
$$Z(e^{-2\pi|z|^2}, 1, s) = \int_{\mathbb C^\times}e^{-2\pi|z|^2}|z|^{2s}\frac{2\,dx\,dy}{|z|^2}
= (2\pi)^{1-s}\Gamma(s) = \pi\,\Gamma_{\mathbb C}(s).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ζ(f, ‖·‖^s) = (2π)^{1−s}Γ(s) for f = e^{−2π|z|²})"]
theorem zetaIntegral_gaussian_complex {s : ℂ} (hs : 0 < s.re) :
    zetaIntegral tateHaarC gaussCS 1 s = Real.pi * Gammaℂ s := by
  have : zetaIntegral tateHaarC gaussCS 1 s =
      ∫ u, (fun r : ℝ => cexp (-((2 * Real.pi : ℝ) : ℂ) * ((r ^ 2 : ℝ) : ℂ))) ‖(u : ℂ)‖ *
        ((distribHaarChar ℂ u : ℝ) : ℂ) ^ s ∂tateHaarC := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [zetaIntegrand, gaussCS_apply, MonoidHom.one_apply, Units.val_one, mul_one]
    push_cast; ring_nf
  have hs2 : 0 < (2 * s).re := by simp; linarith
  rw [this, integral_tateHaarC_radial (fun r : ℝ => cexp (-((2 * Real.pi : ℝ) : ℂ) * ((r ^ 2 : ℝ) : ℂ))) s,
    mellin_gaussian (by positivity) hs2, Gammaℂ_def]
  rw [show 2 * s / 2 = s by ring, neg_div, show 2 * s / 2 = s by ring]
  push_cast
  ring

/-- The same computation for the measure $d^\times z/\pi = 2\,dx\,dy/(\pi|z|^2)$:
$Z(e^{-2\pi|z|^2}, 1, s) = \Gamma_{\mathbb C}(s) = 2(2\pi)^{-s}\Gamma(s)$. -/
theorem zetaIntegral_gaussian_complex' {s : ℂ} (hs : 0 < s.re) :
    zetaIntegral ((Real.pi⁻¹).toNNReal • tateHaarC) gaussCS 1 s = Gammaℂ s := by
  rw [zetaIntegral_smul_measure, zetaIntegral_gaussian_complex hs,
    Real.coe_toNNReal _ (inv_nonneg.mpr Real.pi_pos.le)]
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-! ### The local functional equation on $\mathbb C$ -/

/-- The trace $\operatorname{Tr}_{\mathbb C/\mathbb R}z = 2\operatorname{Re}z$, as an additive map. -/
def traceC : ℂ →+ ℝ := AddMonoidHom.mk' (fun z => 2 * z.re) (fun a b => by simp [mul_add])

/-- **The standard character at a complex place**: $\psi_{\mathbb C}(z) = e(2\operatorname{Re}z)$, the kernel of
QuadFormsKB's `fourierC`. -/
def psiC : AddChar ℂ Circle := Real.fourierChar.compAddMonoidHom traceC

theorem psiC_apply (z : ℂ) : psiC z = Real.fourierChar (2 * z.re) := rfl

theorem continuous_psiC : Continuous psiC :=
  Real.continuous_fourierChar.comp (continuous_const.mul Complex.continuous_re)

/-- QuadFormsKB's `fourierC` is the Fourier transform for $\psi_{\mathbb C}$ and the self-dual measure $2\,dx\,dy$. -/
theorem fourier_muC_psiC (f : ℂ → ℂ) : fourier muC psiC f = fourierC f := by
  funext η
  rw [fourier, muC, integral_smul_nnreal_measure, fourierC, NNReal.smul_def, real_smul]
  push_cast
  rfl

/-- The real-linear map $\eta\mapsto 2\bar\eta$. -/
def twoConj : ℂ ≃L[ℝ] ℂ :=
  Complex.conjCLE.trans (LinearEquiv.smulOfNeZero ℝ ℂ 2 two_ne_zero).toContinuousLinearEquiv

theorem twoConj_apply (η : ℂ) : twoConj η = 2 * conj η := by
  simp [twoConj, LinearEquiv.smulOfNeZero]
  rfl

/-- **The complex Fourier transform of a Schwartz function** as a Schwartz function:
$\hat f(\eta) = 2\,\mathcal F^{-1}f(2\bar\eta)$ with Mathlib's $\mathcal F^{-1}$ on the real inner product space $\mathbb C$. -/
def fourierCS (f : SchwartzMap ℂ ℂ) : SchwartzMap ℂ ℂ :=
  (2 : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ twoConj (𝓕⁻ f : SchwartzMap ℂ ℂ)

theorem coe_fourierCS (f : SchwartzMap ℂ ℂ) : ⇑(fourierCS f) = fourierC f := by
  funext η
  rw [fourierCS, smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq, fourierC, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_comm, twoConj_apply, Complex.inner]
  congr 3
  simp only [mul_re, mul_im, conj_re, conj_im, re_ofNat, im_ofNat]
  ring

theorem norm_inv_apply_complex {χ : ℂˣ →* ℂˣ} {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar ℂ u : ℝ) ^ a)
    (u : ℂˣ) : ‖((χ⁻¹ u : ℂˣ) : ℂ)‖ = (distribHaarChar ℂ u : ℝ) ^ (-a) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχ, Real.rpow_neg (NNReal.coe_nonneg _)]

theorem continuous_inv_char_complex {χ : ℂˣ →* ℂˣ} (hχc : Continuous χ) : Continuous (χ⁻¹ : ℂˣ →* ℂˣ) := by
  have : (χ⁻¹ : ℂˣ →* ℂˣ) = fun u => (χ u)⁻¹ := by funext u; rfl
  rw [this]; exact hχc.inv

/-- **Tate's local functional equation at a complex place**: for Schwartz functions $f, g$ on $\mathbb C$, $\chi$
continuous with $|\chi| = |\cdot|_{\mathbb C}^a$, and $0 < a + \operatorname{Re}s < 1$,
$$Z(f,\chi,s)\,Z(\hat g,\chi^{-1},1-s) = Z(g,\chi,s)\,Z(\hat f,\chi^{-1},1-s)$$
(QuadFormsKB's self-dual transform `fourierC`, Tate's $d^\times z = 2\,dx\,dy/|z|^2$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 [unverified locator] (the local functional equation)"]
theorem zetaIntegral_fourierC_comm (f g : SchwartzMap ℂ ℂ) {χ : ℂˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar ℂ u : ℝ) ^ a) {s : ℂ} (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    zetaIntegral tateHaarC f χ s * zetaIntegral tateHaarC (fourierC g) χ⁻¹ (1 - s) =
      zetaIntegral tateHaarC g χ s * zetaIntegral tateHaarC (fourierC f) χ⁻¹ (1 - s) := by
  have hs' : 0 < -a + (1 - s).re := by rw [sub_re, one_re]; linarith
  have hinv := continuous_inv_char_complex hχc
  have hnorm := norm_inv_apply_complex hχ
  have hf' : Integrable (zetaIntegrand (fourier muC psiC f) χ⁻¹ (1 - s)) tateHaarC := by
    have := integrable_zetaIntegrand_complex (fourierCS f) hinv hnorm hs'
    rwa [coe_fourierCS, ← fourier_muC_psiC] at this
  have hg' : Integrable (zetaIntegrand (fourier muC psiC g) χ⁻¹ (1 - s)) tateHaarC := by
    have := integrable_zetaIntegrand_complex (fourierCS g) hinv hnorm hs'
    rwa [coe_fourierCS, ← fourier_muC_psiC] at this
  have key := zetaIntegral_mul_fourier_comm continuous_distribHaarChar_complex muC psiC continuous_psiC χ s
    (f.integrable.smul_measure_nnreal) (g.integrable.smul_measure_nnreal)
    (integrable_zetaIntegrand_complex f hχc hχ hs0) (integrable_zetaIntegrand_complex g hχc hχ hs0) hf' hg'
  rwa [fourier_muC_psiC, fourier_muC_psiC] at key

/-- The Gaussian $e^{-2\pi|z|^2}$ is self-dual for `fourierC` (QuadFormsKB's `fourierC_chirp_real` at chirp $0$). -/
theorem fourierC_gaussCS : fourierC gaussCS = gaussCS := by
  funext η
  have h := fourierC_chirp_real 0 η
  have hfun : (fun w => chirpC (0 : ℝ) w * gaussC w) = ⇑gaussCS := by
    funext w
    simp [chirpC, gaussC, gaussCS_apply]
  rw [hfun] at h
  rw [h, gaussCS_apply]
  simp only [ofReal_zero, mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Real.sqrt_one, inv_one, Complex.ofReal_one, one_mul, div_one]
  congr 1
  push_cast
  ring

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero_of_re_pos hs)
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  left
  exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero

/-- **The complex gamma factor for the trivial character**: for every Schwartz function $f$ on $\mathbb C$ and
$0 < \operatorname{Re}s < 1$,
$$Z(\hat f, 1, 1-s) = \frac{\Gamma_{\mathbb C}(1-s)}{\Gamma_{\mathbb C}(s)}\,Z(f, 1, s).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(‖·‖^s) at a complex place)"]
theorem zetaIntegral_fourierC_one (f : SchwartzMap ℂ ℂ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaIntegral tateHaarC (fourierC f) 1 (1 - s) = Gammaℂ (1 - s) / Gammaℂ s * zetaIntegral tateHaarC f 1 s := by
  have hχ : ∀ u : ℂˣ, ‖((1 : ℂˣ →* ℂˣ) u : ℂ)‖ = (distribHaarChar ℂ u : ℝ) ^ (0 : ℝ) := fun u => by simp
  have h := zetaIntegral_fourierC_comm f gaussCS continuous_const hχ (by simpa using hs0) (by simpa using hs1)
  have hinv1 : (1 : ℂˣ →* ℂˣ)⁻¹ = 1 := by ext u; simp
  simp only [hinv1] at h
  have hs1' : 0 < (1 - s).re := by rw [sub_re, one_re]; linarith
  rw [fourierC_gaussCS, zetaIntegral_gaussian_complex hs1', zetaIntegral_gaussian_complex hs0] at h
  have hne : Gammaℂ s ≠ 0 := Gammaℂ_ne_zero_of_re_pos hs0
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  have h' : Real.pi * (zetaIntegral tateHaarC (fourierC f) 1 (1 - s) * Gammaℂ s) =
      Real.pi * (Gammaℂ (1 - s) * zetaIntegral tateHaarC f 1 s) := by
    linear_combination h.symm
  exact mul_left_cancel₀ hπ h'

end

end NumberFieldKB.LocalZeta
