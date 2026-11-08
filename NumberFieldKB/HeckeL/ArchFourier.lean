import NumberFieldKB.HeckeL.ArchGamma
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Fourier transforms of the archimedean test functions

With QuadFormsKB's conventions (`fourierR`: $\hat f(y) = \int f(x)e(xy)\,dx$ on $\mathbb R$; `fourierC`:
$\hat f(\eta) = 2\int f(z)e(2\operatorname{Re}(z\eta))\,dx\,dy$ on $\mathbb C$):

* **`fourierR_fRe`**: $\widehat{x^ee^{-\pi x^2}} = i^e\,y^ee^{-\pi y^2}$ for $e\in\{0,1\}$;
* **`fourierC_fCk`**: $\widehat{\bar z^ke^{-2\pi|z|^2}} = i^k\eta^ke^{-2\pi|\eta|^2}$ and
  $\widehat{z^ke^{-2\pi|z|^2}} = i^k\bar\eta^ke^{-2\pi|\eta|^2}$ ($k\ge0$), i.e. $\hat f_{k} = i^{|k|}f_{-k}$.

*Proofs.* On $\mathbb R$: $xe^{-\pi x^2} = -\frac1{2\pi}\frac{d}{dx}e^{-\pi x^2}$ and Mathlib's `Real.fourier_deriv`. On $\mathbb C$, by
induction on $k$: with $h = \bar z^kg$, $g = e^{-2\pi|z|^2}$, the Wirtinger combination
$\partial_1h - i\,\partial_ih = -4\pi\bar z^{k+1}g$ of directional derivatives, and Mathlib's `Real.fourier_fderiv`
($\mathcal F(\partial_eh)(w) = 2\pi i\langle w,e\rangle\mathcal Fh(w)$) gives
$\mathcal F(\bar z^{k+1}g)(w) = -\frac i2\bar w\,\mathcal F(\bar z^kg)(w)$; similarly with $\partial_1+i\,\partial_i$ for $z^k$.
-/

open MeasureTheory Filter Set Complex
open scoped ComplexConjugate FourierTransform Real InnerProductSpace

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

open QuadFormsKB.Analysis

/-! ### Fourier transforms and Mathlib's $\mathcal F$ -/

theorem fourierR_eq_fourier (f : ℝ → ℂ) (y : ℝ) : fourierR f y = 𝓕 f (-y) := by
  rw [fourierR_eq, Real.fourierInv_eq_fourier_neg]

theorem fourierC_eq_fourier (f : ℂ → ℂ) (η : ℂ) : fourierC f η = 2 * 𝓕 f (-(2 * conj η)) := by
  rw [← Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq, fourierC]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_comm, Complex.inner]
  congr 3
  simp only [mul_re, mul_im, conj_re, conj_im, re_ofNat, im_ofNat]
  ring

theorem integrable_fourierChar_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] {f : V → ℂ} (hf : Integrable f) (w : V) :
    Integrable (fun v => 𝐞 (-⟪v, w⟫_ℝ) • f v) := by
  refine hf.norm.mono' ?_ (Eventually.of_forall fun v => by rw [Circle.norm_smul])
  exact ((Real.continuous_fourierChar.comp (continuous_inner.comp
    (continuous_id.prodMk continuous_const)).neg).aestronglyMeasurable).smul hf.1

/-! ### The real place -/

theorem hasDerivAt_gaussR (x : ℝ) :
    HasDerivAt gaussR (-2 * π * x * gaussR x) x := by
  have h : HasDerivAt (fun z : ℂ => cexp (-π * z ^ 2)) (cexp (-π * (x : ℂ) ^ 2) * (-π * (2 * (x : ℂ)))) (x : ℂ) := by
    have h1 : HasDerivAt (fun z : ℂ => -π * z ^ 2) (-π * (2 * (x : ℂ))) (x : ℂ) := by
      simpa using ((hasDerivAt_pow 2 (x : ℂ)).const_mul (-π : ℂ))
    exact h1.cexp
  have h2 := h.comp_ofReal
  have hG : gaussR = fun y : ℝ => cexp (-π * (y : ℂ) ^ 2) := rfl
  rw [hG]
  convert h2 using 1
  ring

theorem deriv_gaussR : deriv gaussR = fun x => -2 * π * x * gaussR x :=
  funext fun x => (hasDerivAt_gaussR x).deriv

theorem fourier_gaussR (w : ℝ) : 𝓕 gaussR w = gaussR w := by
  have h := congrFun fourierR_gaussR (-w)
  rw [fourierR_eq_fourier, neg_neg] at h
  rw [h]
  simp [gaussR]

/-- **$\widehat{xe^{-\pi x^2}} = i\,ye^{-\pi y^2}$.** -/
theorem fourierR_fRe_one : fourierR (fRe 1) = fun y => I * fRe 1 y := by
  have hG : (gaussR : ℝ → ℂ) = (LocalZeta.gaussR : ℝ → ℂ) := (coe_gaussR_eq).symm
  have hint : Integrable gaussR := hG ▸ LocalZeta.gaussR.integrable
  have hdiff : Differentiable ℝ gaussR := hG ▸ LocalZeta.gaussR.differentiable
  have hderiv_int : Integrable (deriv gaussR) := by
    have : deriv gaussR = ⇑(SchwartzMap.derivCLM ℝ ℂ LocalZeta.gaussR) := by
      rw [hG]; funext x; exact (SchwartzMap.derivCLM_apply (𝕜 := ℝ) _ x).symm
    rw [this]
    exact (SchwartzMap.derivCLM ℝ ℂ LocalZeta.gaussR).integrable
  have hfd := Real.fourier_deriv hint hdiff hderiv_int
  have hfun : fRe 1 = fun x => (-(1 / (2 * π)) : ℂ) • deriv gaussR x := by
    funext x
    rw [deriv_gaussR, fRe, pow_one, smul_eq_mul]
    field_simp
  funext y
  rw [fourierR_eq_fourier]
  conv_lhs => rw [hfun, Real.fourier_eq]
  simp_rw [smul_comm _ (-(1 / (2 * π)) : ℂ), integral_smul]
  rw [← Real.fourier_eq, hfd]
  simp only [smul_eq_mul, fourier_gaussR]
  simp only [fRe, pow_one, gaussR]
  push_cast
  rw [neg_sq]
  field_simp

theorem fourierR_fRe_zero : fourierR (fRe 0) = fun y => I ^ 0 * fRe 0 y := by
  have : fRe 0 = gaussR := by funext x; simp [fRe]
  rw [this, fourierR_gaussR]
  funext y
  simp

/-- **$\widehat{x^ee^{-\pi x^2}} = i^e\,y^ee^{-\pi y^2}$** for $e\le1$. -/
theorem fourierR_fRe {e : ℕ} (he : e ≤ 1) : fourierR (fRe e) = fun y => I ^ e * fRe e y := by
  interval_cases e
  · exact fourierR_fRe_zero
  · rw [fourierR_fRe_one]; simp

/-! ### The complex place -/

theorem inner_one_right (z : ℂ) : ⟪z, (1 : ℂ)⟫_ℝ = z.re := by
  rw [Complex.inner]; simp

theorem inner_I_right (z : ℂ) : ⟪z, I⟫_ℝ = z.im := by
  rw [Complex.inner]; simp

theorem re_add_neg_I_mul_im (z : ℂ) : (z.re : ℂ) + -I * z.im = conj z := by
  apply Complex.ext <;> simp

theorem re_add_I_mul_im (z : ℂ) : (z.re : ℂ) + I * z.im = z := by
  apply Complex.ext <;> simp

theorem hasFDerivAt_gaussC (z : ℂ) :
    HasFDerivAt gaussC (cexp (-(2 * π : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)) •
      ((-(2 * π : ℂ)) • (Complex.ofRealCLM.comp (2 • innerSL ℝ z)))) z := by
  have h1 : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2) (2 • innerSL ℝ z) z := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 : HasFDerivAt (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ)) (Complex.ofRealCLM.comp (2 • innerSL ℝ z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h1
  exact (h2.const_mul (-(2 * π : ℂ))).cexp

/-- The directional derivative of $q(z)e^{-2\pi|z|^2}$, given that of $q$. -/
theorem hasFDerivAt_mul_gaussC {q : ℂ → ℂ} {q' : ℂ →L[ℝ] ℂ} {z : ℂ} (hq : HasFDerivAt q q' z) (e : ℂ) :
    fderiv ℝ (fun z => q z * gaussC z) z e =
      q z * (gaussC z * (-(2 * π : ℂ)) * (2 * ⟪z, e⟫_ℝ)) + gaussC z * q' e := by
  have h := hq.mul (hasFDerivAt_gaussC z)
  rw [show (fun z => q z * gaussC z) = q * gaussC from rfl, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, innerSL_apply_apply]
  rw [gaussC]
  push_cast
  ring

theorem hasFDerivAt_conj_pow (k : ℕ) (z : ℂ) :
    HasFDerivAt (fun z : ℂ => conj z ^ k) ((k • conj z ^ (k - 1)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.pow k

theorem hasFDerivAt_pow' (k : ℕ) (z : ℂ) :
    HasFDerivAt (fun z : ℂ => z ^ k) ((k • z ^ (k - 1)) • ContinuousLinearMap.id ℝ ℂ) z :=
  (hasFDerivAt_id z).pow k

/-- **Wirtinger**: $(\partial_1 - i\partial_i)(\bar z^kg) = -4\pi\bar z^{k+1}g$. -/
theorem wirtinger_conjPow (k : ℕ) (z : ℂ) :
    fderiv ℝ (fun z => conj z ^ k * gaussC z) z 1 + -I * fderiv ℝ (fun z => conj z ^ k * gaussC z) z I =
      -(4 * π : ℂ) * (conj z ^ (k + 1) * gaussC z) := by
  rw [hasFDerivAt_mul_gaussC (hasFDerivAt_conj_pow k z), hasFDerivAt_mul_gaussC (hasFDerivAt_conj_pow k z),
    inner_one_right, inner_I_right]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one,
    Complex.conj_I, nsmul_eq_mul, smul_eq_mul]
  have e2 := re_add_neg_I_mul_im z
  calc conj z ^ k * (gaussC z * -(2 * π : ℂ) * (2 * (z.re : ℂ))) + gaussC z * (k * conj z ^ (k - 1) * 1) +
        -I * (conj z ^ k * (gaussC z * -(2 * π : ℂ) * (2 * (z.im : ℂ))) + gaussC z * (k * conj z ^ (k - 1) * -I))
      = conj z ^ k * gaussC z * -(4 * π : ℂ) * ((z.re : ℂ) + -I * z.im) +
          gaussC z * k * conj z ^ (k - 1) * (1 + I * I) := by ring
    _ = _ := by rw [e2, Complex.I_mul_I]; ring

/-- **Wirtinger**: $(\partial_1 + i\partial_i)(z^kg) = -4\pi z^{k+1}g$. -/
theorem wirtinger_pow (k : ℕ) (z : ℂ) :
    fderiv ℝ (fun z => z ^ k * gaussC z) z 1 + I * fderiv ℝ (fun z => z ^ k * gaussC z) z I =
      -(4 * π : ℂ) * (z ^ (k + 1) * gaussC z) := by
  rw [hasFDerivAt_mul_gaussC (hasFDerivAt_pow' k z), hasFDerivAt_mul_gaussC (hasFDerivAt_pow' k z),
    inner_one_right, inner_I_right]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, nsmul_eq_mul, smul_eq_mul]
  have e2 := re_add_I_mul_im z
  calc z ^ k * (gaussC z * -(2 * π : ℂ) * (2 * (z.re : ℂ))) + gaussC z * (k * z ^ (k - 1) * 1) +
        I * (z ^ k * (gaussC z * -(2 * π : ℂ) * (2 * (z.im : ℂ))) + gaussC z * (k * z ^ (k - 1) * I))
      = z ^ k * gaussC z * -(4 * π : ℂ) * ((z.re : ℂ) + I * z.im) +
          gaussC z * k * z ^ (k - 1) * (1 + I * I) := by ring
    _ = _ := by rw [e2, Complex.I_mul_I]; ring

/-- **The Fourier transform of a Wirtinger combination**:
$\mathcal F\bigl(a(\partial_1h + c\,\partial_ih)\bigr)(w) = a\cdot2\pi i(\operatorname{Re}w + c\operatorname{Im}w)\,\mathcal Fh(w)$. -/
theorem fourier_fderiv_comb (h : SchwartzMap ℂ ℂ) (a c w : ℂ) :
    𝓕 (fun z => a * (fderiv ℝ h z 1 + c * fderiv ℝ h z I)) w =
      a * (2 * π * I * (w.re + c * w.im)) * 𝓕 (h : ℂ → ℂ) w := by
  have hint : Integrable h := h.integrable
  have hdiff : Differentiable ℝ h := h.differentiable
  have hfd : Integrable (fderiv ℝ h) := (SchwartzMap.fderivCLM ℝ ℂ ℂ h).integrable
  have key := Real.fourier_fderiv hint hdiff hfd
  have hdir : ∀ e : ℂ, 𝓕 (fun z => fderiv ℝ h z e) w = 2 * π * I * ⟪w, e⟫_ℝ * 𝓕 (h : ℂ → ℂ) w := fun e => by
    rw [← Real.fourier_continuousLinearMap_apply hfd, key]
    simp only [VectorFourier.fourierSMulRight_apply, ContinuousLinearMap.neg_apply, smul_eq_mul, Complex.real_smul]
    push_cast
    rw [show ((innerSL ℝ) w) e = ⟪w, e⟫_ℝ from rfl]
    ring
  have hA : Integrable (fun z => fderiv ℝ h z 1) := hfd.apply_continuousLinearMap 1
  have hB : Integrable (fun z => fderiv ℝ h z I) := hfd.apply_continuousLinearMap I
  have hlin : 𝓕 (fun z => a * (fderiv ℝ h z 1 + c * fderiv ℝ h z I)) w =
      a * (𝓕 (fun z => fderiv ℝ h z 1) w + c * 𝓕 (fun z => fderiv ℝ h z I) w) := by
    rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
    have hfun : (fun v : ℂ => 𝐞 (-⟪v, w⟫_ℝ) • (a * (fderiv ℝ h v 1 + c * fderiv ℝ h v I))) =
        fun v => a * (𝐞 (-⟪v, w⟫_ℝ) • fderiv ℝ h v 1) + (a * c) * (𝐞 (-⟪v, w⟫_ℝ) • fderiv ℝ h v I) := by
      funext v
      simp only [Circle.smul_def, smul_eq_mul]
      ring
    rw [hfun, integral_add ((integrable_fourierChar_smul hA w).const_mul a)
      ((integrable_fourierChar_smul hB w).const_mul (a * c)), integral_const_mul, integral_const_mul]
    ring
  rw [hlin, hdir, hdir, inner_one_right, inner_I_right]
  ring

theorem hasTemperateGrowth_conj_pow (k : ℕ) : (fun z : ℂ => conj z ^ k).HasTemperateGrowth :=
  ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasTemperateGrowth).pow k

theorem hasTemperateGrowth_pow' (k : ℕ) : (fun z : ℂ => z ^ k).HasTemperateGrowth :=
  ((ContinuousLinearMap.id ℝ ℂ).hasTemperateGrowth).pow k

/-- $\mathcal F(\bar z^kg)(w) = (-i/2)^k\bar w^k\mathcal Fg(w)$. -/
theorem fourier_conjPow_gaussC (k : ℕ) (w : ℂ) :
    𝓕 (fun z => conj z ^ k * gaussC z) w = (-(I / 2)) ^ k * conj w ^ k * 𝓕 gaussC w := by
  induction k with
  | zero => simp
  | succ k ih =>
    set hk : SchwartzMap ℂ ℂ := SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => conj z ^ k) LocalZeta.gaussCS
    have hk_apply : (hk : ℂ → ℂ) = fun z => conj z ^ k * gaussC z := by
      funext z
      rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_conj_pow k), smul_eq_mul, coe_gaussCS_eq]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hfun : (fun z => conj z ^ (k + 1) * gaussC z) =
        fun z => (-(1 / (4 * π)) : ℂ) * (fderiv ℝ hk z 1 + -I * fderiv ℝ hk z I) := by
      funext z
      rw [hk_apply, wirtinger_conjPow]
      field_simp
    rw [hfun, fourier_fderiv_comb, hk_apply, ih, re_add_neg_I_mul_im]
    field_simp
    ring

/-- $\mathcal F(z^kg)(w) = (-i/2)^kw^k\mathcal Fg(w)$. -/
theorem fourier_pow_gaussC (k : ℕ) (w : ℂ) :
    𝓕 (fun z => z ^ k * gaussC z) w = (-(I / 2)) ^ k * w ^ k * 𝓕 gaussC w := by
  induction k with
  | zero => simp
  | succ k ih =>
    set hk : SchwartzMap ℂ ℂ := SchwartzMap.smulLeftCLM ℂ (fun z : ℂ => z ^ k) LocalZeta.gaussCS
    have hk_apply : (hk : ℂ → ℂ) = fun z => z ^ k * gaussC z := by
      funext z
      rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_pow' k), smul_eq_mul, coe_gaussCS_eq]
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hfun : (fun z => z ^ (k + 1) * gaussC z) =
        fun z => (-(1 / (4 * π)) : ℂ) * (fderiv ℝ hk z 1 + I * fderiv ℝ hk z I) := by
      funext z
      rw [hk_apply, wirtinger_pow]
      field_simp
    rw [hfun, fourier_fderiv_comb, hk_apply, ih, re_add_I_mul_im]
    field_simp
    ring

theorem two_mul_fourier_gaussC (η : ℂ) : 2 * 𝓕 gaussC (-(2 * conj η)) = gaussC η := by
  rw [← fourierC_eq_fourier, fourierC_gaussC]

/-- **The Fourier transform of the complex test functions**: $\hat f_k = i^{|k|}f_{-k}$, i.e.
$\widehat{\bar z^ke^{-2\pi|z|^2}} = i^k\eta^ke^{-2\pi|\eta|^2}$ and $\widehat{z^ke^{-2\pi|z|^2}} = i^k\bar\eta^ke^{-2\pi|\eta|^2}$
($k\ge0$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (the test functions at a complex place)"]
theorem fourierC_fCk (k : ℤ) : fourierC (fCk k) = fun η => I ^ k.natAbs * fCk (-k) η := by
  funext η
  rw [fourierC_eq_fourier]
  have hg := two_mul_fourier_gaussC η
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hf : fCk k = fun z => z ^ k.natAbs * gaussC z := by
      funext z; simp only [fCk, qC, if_neg (show ¬ 0 ≤ k by omega)]
    have hf' : fCk (-k) η = conj η ^ k.natAbs * gaussC η := by
      simp only [fCk, qC, if_pos (show 0 ≤ -k by omega), Int.natAbs_neg]
    rw [hf, hf', fourier_pow_gaussC, ← hg, ← mul_pow,
      show (-(I / 2)) * (-(2 * conj η)) = I * conj η by ring, mul_pow]
    ring
  · subst hk
    have h0 : fCk 0 = gaussC := by funext z; simp [fCk, qC]
    rw [neg_zero, h0, hg]
    simp
  · have hf : fCk k = fun z => conj z ^ k.natAbs * gaussC z := by
      funext z; simp only [fCk, qC, if_pos hk.le]
    have hf' : fCk (-k) η = η ^ k.natAbs * gaussC η := by
      simp only [fCk, qC, if_neg (show ¬ 0 ≤ -k by omega), Int.natAbs_neg]
    rw [hf, hf', fourier_conjPow_gaussC, ← hg]
    simp only [map_mul, map_neg, map_ofNat, Complex.conj_conj]
    rw [← mul_pow, show (-(I / 2)) * (-(2 * η)) = I * η by ring, mul_pow]
    ring

end

end NumberFieldKB.HeckeL
