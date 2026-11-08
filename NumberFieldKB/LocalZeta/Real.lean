import NumberFieldKB.LocalZeta.Archimedean
import QuadFormsKB.Analysis.LocalFourier
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.MellinTransform

/-!
# Local zeta integrals at a real place

On $\mathbb R$: $dx$ is Lebesgue measure (self-dual for QuadFormsKB's character $\psi_\infty(x) = e^{2\pi ix}$, `psiR`, and
its Fourier transform `fourierR`), the modulus is $|x|$ (`distribHaarChar_real`), and Tate's multiplicative measure is
$d^\times x = dx/|x|$ (`tateHaarR` = QuadFormsKB's `unitsHaar ℝ volume`).

* **`zetaIntegral_gaussian_real`**: $Z(e^{-\pi x^2}, 1, s) = \pi^{-s/2}\Gamma(s/2) = \Gamma_{\mathbb R}(s)$ for
  $\operatorname{Re}s > 0$;
* **`zetaIntegral_mul_gaussian_sign`**: $Z(xe^{-\pi x^2}, \operatorname{sgn}, s) = \Gamma_{\mathbb R}(s+1)$;
* **`zetaIntegral_fourierR_comm`**: the local functional equation for Schwartz functions, for every continuous
  $\chi$ with $|\chi| = |\cdot|^a$ and $0 < a + \operatorname{Re}s < 1$;
* **`zetaIntegral_fourierR_one`**: for the trivial character,
  $Z(\hat f, 1, 1-s) = \dfrac{\Gamma_{\mathbb R}(1-s)}{\Gamma_{\mathbb R}(s)}Z(f, 1, s)$ ($0 < \operatorname{Re}s < 1$),
  using the self-dual Gaussian.

Source: Tate's thesis, Cassels–Fröhlich Ch. XV, §2.5 (the archimedean computations) [unverified locators].
-/

open MeasureTheory Filter Topology Set Complex
open scoped ENNReal NNReal FourierTransform Pointwise

namespace NumberFieldKB.LocalZeta

noncomputable section

open QuadFormsKB.Tamagawa.Measure.Weil QuadFormsKB.Analysis

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

/-! ### The Gaussian Mellin transform -/

/-- $\int_0^\infty e^{-cr^2}r^{s-1}\,dr = \tfrac12 c^{-s/2}\Gamma(s/2)$ for $c > 0$, $\operatorname{Re}s > 0$. -/
theorem mellin_gaussian {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun r : ℝ => cexp (-(c : ℂ) * ((r ^ 2 : ℝ) : ℂ))) s = (1 / 2 : ℂ) * (c : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
  set E : ℝ → ℂ := fun u => ((Real.exp (-u) : ℝ) : ℂ)
  set G : ℝ → ℂ := fun t => E (c * t)
  have hs2 : 0 < (s / 2).re := by rw [div_ofNat_re]; linarith
  calc mellin (fun r : ℝ => cexp (-(c : ℂ) * ((r ^ 2 : ℝ) : ℂ))) s = mellin (fun r : ℝ => G (r ^ (2 : ℝ))) s := by
        congr 1; funext r
        simp only [G, E, Real.rpow_two, ofReal_exp, ofReal_neg, ofReal_mul]
        ring_nf
    _ = |(2 : ℝ)|⁻¹ • mellin G (s / 2) := mellin_comp_rpow G s 2
    _ = |(2 : ℝ)|⁻¹ • ((c : ℂ) ^ (-(s / 2)) • mellin E (s / 2)) := by rw [mellin_comp_mul_left E (s / 2) hc]
    _ = (1 / 2 : ℂ) * (c : ℂ) ^ (-s / 2) * Gamma (s / 2) := by
        rw [show mellin E (s / 2) = GammaIntegral (s / 2) by rw [GammaIntegral_eq_mellin],
          ← Gamma_eq_integral hs2, abs_two, real_smul, smul_eq_mul, neg_div]
        push_cast
        ring

/-! ### The modulus and Tate's measure on $\mathbb R^\times$ -/

/-- **The modulus of $\mathbb R$** is the absolute value: $\Delta_{\mathbb R}(u) = |u|$. -/
theorem distribHaarChar_real (u : ℝˣ) : (distribHaarChar ℝ u : ℝ) = |(u : ℝ)| := by
  set s : Set ℝ := Metric.ball 0 1
  have hs0 : (volume : Measure ℝ) s ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have hsT : (volume : Measure ℝ) s ≠ ⊤ := measure_ball_lt_top.ne
  have himg : u • s = (u : ℝ) • s := by
    ext x; simp [Set.mem_smul_set, Units.smul_def]
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (g := u) hs0 hsT
    (r := Real.toNNReal |(u : ℝ)|) (by
      rw [himg, Measure.addHaar_smul, Module.finrank_self, pow_one, ENNReal.ofReal])
  rw [this, Real.coe_toNNReal _ (abs_nonneg _)]

theorem distribHaarChar_real' (u : ℝˣ) :
    (distribHaarChar ℝ u : ℝ) = ‖(u : ℝ)‖ ^ Module.finrank ℝ ℝ := by
  rw [distribHaarChar_real, Module.finrank_self, pow_one, Real.norm_eq_abs]

theorem continuous_distribHaarChar_real : Continuous (distribHaarChar ℝ : ℝˣ → ℝ≥0) := by
  refine continuous_induced_rng.mpr ?_
  have : (fun u : ℝˣ => (distribHaarChar ℝ u : ℝ)) = fun u : ℝˣ => |(u : ℝ)| := funext distribHaarChar_real
  change Continuous fun u : ℝˣ => (distribHaarChar ℝ u : ℝ)
  rw [this]
  exact continuous_abs.comp Units.continuous_val

/-- **Tate's multiplicative measure on $\mathbb R^\times$**: $d^\times x = dx/|x|$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (d^×x = dx/|x| at a real place)"]
def tateHaarR : Measure ℝˣ := unitsHaar ℝ (volume : Measure ℝ)

instance : tateHaarR.IsHaarMeasure :=
  isHaarMeasure_unitsHaar isOpenEmbedding_units_val continuous_distribHaarChar_real _

/-- Absolute convergence on $\mathbb R$ for Schwartz functions and $\operatorname{Re}s > -a$, $|\chi| = |\cdot|^a$. -/
theorem integrable_zetaIntegrand_real (f : SchwartzMap ℝ ℂ) {χ : ℝˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar ℝ u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re) :
    Integrable (zetaIntegrand f χ s) tateHaarR :=
  integrable_zetaIntegrand_schwartz _ continuous_distribHaarChar_real distribHaarChar_real' f hχc hχ hs

/-! ### Gaussian computations -/

/-- The self-dual Gaussian $e^{-\pi x^2}$ on $\mathbb R$, a Schwartz function (QuadFormsKB's `gaussianSchwartz`). -/
def gaussR : SchwartzMap ℝ ℂ := gaussianSchwartz (E := ℝ) (Real.pi : ℂ) (by simp [Real.pi_pos])

theorem gaussR_apply (x : ℝ) : gaussR x = cexp (-(Real.pi : ℂ) * ((x ^ 2 : ℝ) : ℂ)) := by
  rw [gaussR, gaussianSchwartz_apply, Real.norm_eq_abs, sq_abs]

/-- On $\mathbb R$: $\int_{\mathbb R^\times}F(|u|)|u|^s\,d^\times u = 2\int_0^\infty F(r)r^{s-1}\,dr$. -/
theorem integral_tateHaarR_radial (F : ℝ → ℂ) (s : ℂ) :
    ∫ u, F |(u : ℝ)| * ((distribHaarChar ℝ u : ℝ) : ℂ) ^ s ∂tateHaarR = 2 * mellin F s := by
  set h : ℝ → ℂ := fun x => F ‖x‖ * ((‖x‖ : ℝ) : ℂ) ^ (s - 1)
  have hpt : ∀ u : ℝˣ, F |(u : ℝ)| * ((distribHaarChar ℝ u : ℝ) : ℂ) ^ s =
      h u * ((distribHaarChar ℝ u : ℝ) : ℂ) := by
    intro u
    have hu : ((|(u : ℝ)| : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast abs_ne_zero.mpr u.ne_zero
    simp only [h, distribHaarChar_real, Real.norm_eq_abs]
    rw [mul_assoc, show ((|(u : ℝ)| : ℝ) : ℂ) ^ (s - 1) * ((|(u : ℝ)| : ℝ) : ℂ) =
        ((|(u : ℝ)| : ℝ) : ℂ) ^ (s - 1) * ((|(u : ℝ)| : ℝ) : ℂ) ^ (1 : ℂ) by rw [cpow_one],
      ← cpow_add _ _ hu, sub_add_cancel]
  calc ∫ u, F |(u : ℝ)| * ((distribHaarChar ℝ u : ℝ) : ℂ) ^ s ∂tateHaarR
      = ∫ u, h u * ((distribHaarChar ℝ u : ℝ) : ℂ) ∂tateHaarR :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = ∫ x, h x := integral_unitsHaar_mul_modulus continuous_distribHaarChar_real volume h
    _ = 2 * mellin F s := by
      rw [integral_fun_norm_addHaar volume (fun r : ℝ => F r * (r : ℂ) ^ (s - 1))]
      simp only [Module.finrank_self, tsub_self, pow_zero, one_smul, Measure.real, Real.volume_ball, mul_one,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), mellin, smul_eq_mul]
      rw [real_smul]
      push_cast
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      ring

/-- **The real Gaussian zeta integral** (Tate, Cassels–Fröhlich Ch. XV, §2.5): for $\operatorname{Re}s > 0$,
$$Z(e^{-\pi x^2}, 1, s) = \int_{\mathbb R^\times}e^{-\pi x^2}|x|^s\frac{dx}{|x|} = \pi^{-s/2}\Gamma(s/2) = \Gamma_{\mathbb R}(s).$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ζ(f, |·|^s) = π^{−s/2}Γ(s/2) for f = e^{−πx²})"]
theorem zetaIntegral_gaussian_real {s : ℂ} (hs : 0 < s.re) :
    zetaIntegral tateHaarR gaussR 1 s = Gammaℝ s := by
  have : zetaIntegral tateHaarR gaussR 1 s =
      ∫ u, (fun r : ℝ => cexp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ))) |(u : ℝ)| *
        ((distribHaarChar ℝ u : ℝ) : ℂ) ^ s ∂tateHaarR := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [zetaIntegrand, gaussR_apply, MonoidHom.one_apply, Units.val_one, mul_one, sq_abs]
  rw [this, integral_tateHaarR_radial (fun r : ℝ => cexp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ))) s,
    mellin_gaussian Real.pi_pos hs, Gammaℝ_def]
  ring

/-- **The sign character** of $\mathbb R^\times$. -/
def signChar : ℝˣ →* ℂˣ where
  toFun u := if 0 < (u : ℝ) then 1 else -1
  map_one' := by simp
  map_mul' u v := by
    have hu0 := u.ne_zero
    have hv0 := v.ne_zero
    simp only [Units.val_mul]
    by_cases hu : 0 < (u : ℝ) <;> by_cases hv : 0 < (v : ℝ)
    · simp [hu, hv, mul_pos hu hv]
    · have hv' : (v : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hv) hv0
      simp [hu, hv, (mul_neg_of_pos_of_neg hu hv').not_gt]
    · have hu' : (u : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hu) hu0
      simp [hu, hv, (mul_neg_of_neg_of_pos hu' hv).not_gt]
    · have hu' : (u : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hu) hu0
      have hv' : (v : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hv) hv0
      simp [hu, hv, mul_pos_of_neg_of_neg hu' hv']

theorem signChar_mul_self (u : ℝˣ) : ((signChar u : ℂˣ) : ℂ) * (u : ℝ) = |(u : ℝ)| := by
  simp only [signChar, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs with h
  · simp [abs_of_pos h]
  · have : (u : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp h) u.ne_zero
    simp [abs_of_neg this]

/-- **The real zeta integral with the sign character** (Tate, Cassels–Fröhlich Ch. XV, §2.5): for
$\operatorname{Re}s > -1$, $Z(xe^{-\pi x^2}, \operatorname{sgn}, s) = \pi^{-(s+1)/2}\Gamma((s+1)/2) = \Gamma_{\mathbb R}(s+1)$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (f = ξe^{−πξ²} for c = sgn·|·|^s)"]
theorem zetaIntegral_mul_gaussian_sign {s : ℂ} (hs : 0 < s.re + 1) :
    zetaIntegral tateHaarR (fun x => (x : ℂ) * gaussR x) signChar s = Gammaℝ (s + 1) := by
  have hs' : 0 < (s + 1).re := by rw [add_re, one_re]; exact hs
  rw [← zetaIntegral_gaussian_real hs']
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hu : ((|(u : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr u.ne_zero
  simp only [zetaIntegrand, MonoidHom.one_apply, Units.val_one, mul_one, distribHaarChar_real]
  rw [cpow_add _ _ hu, cpow_one, ← signChar_mul_self u]
  ring

/-! ### The local functional equation on $\mathbb R$ -/

theorem fourier_volume_psiR (f : ℝ → ℂ) : fourier volume psiR f = fourierR f := rfl

/-- The Fourier transform of a Schwartz function, as a Schwartz function (Mathlib's `𝓕⁻`, which is `fourierR`). -/
theorem coe_fourierInv_schwartz (f : SchwartzMap ℝ ℂ) : ⇑(𝓕⁻ f : SchwartzMap ℝ ℂ) = fourierR f := by
  rw [SchwartzMap.fourierInv_coe, fourierR_eq]

theorem norm_inv_apply_real {χ : ℝˣ →* ℂˣ} {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar ℝ u : ℝ) ^ a)
    (u : ℝˣ) : ‖((χ⁻¹ u : ℂˣ) : ℂ)‖ = (distribHaarChar ℝ u : ℝ) ^ (-a) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχ, Real.rpow_neg (NNReal.coe_nonneg _)]

theorem continuous_inv_char_real {χ : ℝˣ →* ℂˣ} (hχc : Continuous χ) : Continuous (χ⁻¹ : ℝˣ →* ℂˣ) := by
  have : (χ⁻¹ : ℝˣ →* ℂˣ) = fun u => (χ u)⁻¹ := by funext u; rfl
  rw [this]; exact hχc.inv

/-- **Tate's local functional equation at a real place**: for Schwartz functions $f, g$ on $\mathbb R$, $\chi$
continuous with $|\chi| = |\cdot|^a$, and $0 < a + \operatorname{Re}s < 1$,
$$Z(f,\chi,s)\,Z(\hat g,\chi^{-1},1-s) = Z(g,\chi,s)\,Z(\hat f,\chi^{-1},1-s)$$
(QuadFormsKB's self-dual transform `fourierR`, Tate's $d^\times x = dx/|x|$). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 [unverified locator] (the local functional equation)"]
theorem zetaIntegral_fourierR_comm (f g : SchwartzMap ℝ ℂ) {χ : ℝˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar ℝ u : ℝ) ^ a) {s : ℂ} (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    zetaIntegral tateHaarR f χ s * zetaIntegral tateHaarR (fourierR g) χ⁻¹ (1 - s) =
      zetaIntegral tateHaarR g χ s * zetaIntegral tateHaarR (fourierR f) χ⁻¹ (1 - s) := by
  have hs' : 0 < -a + (1 - s).re := by rw [sub_re, one_re]; linarith
  have hinv := continuous_inv_char_real hχc
  have hnorm := norm_inv_apply_real hχ
  have hf' : Integrable (zetaIntegrand (fourierR f) χ⁻¹ (1 - s)) tateHaarR := by
    have := integrable_zetaIntegrand_real (𝓕⁻ f : SchwartzMap ℝ ℂ) hinv hnorm hs'
    rwa [coe_fourierInv_schwartz] at this
  have hg' : Integrable (zetaIntegrand (fourierR g) χ⁻¹ (1 - s)) tateHaarR := by
    have := integrable_zetaIntegrand_real (𝓕⁻ g : SchwartzMap ℝ ℂ) hinv hnorm hs'
    rwa [coe_fourierInv_schwartz] at this
  exact zetaIntegral_mul_fourier_comm continuous_distribHaarChar_real (volume : Measure ℝ) psiR
    continuous_psiR χ s f.integrable g.integrable (integrable_zetaIntegrand_real f hχc hχ hs0)
    (integrable_zetaIntegrand_real g hχc hχ hs0) hf' hg'

/-- **The real gamma factor for the trivial character**: for every Schwartz function $f$ on $\mathbb R$ and
$0 < \operatorname{Re}s < 1$,
$$Z(\hat f, 1, 1-s) = \frac{\Gamma_{\mathbb R}(1-s)}{\Gamma_{\mathbb R}(s)}\,Z(f, 1, s)$$
(take $g = e^{-\pi x^2}$, which is self-dual, in `zetaIntegral_fourierR_comm`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ρ(|·|^s) = Γ_ℝ(1 − s)/Γ_ℝ(s) at a real place)"]
theorem zetaIntegral_fourierR_one (f : SchwartzMap ℝ ℂ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    zetaIntegral tateHaarR (fourierR f) 1 (1 - s) = Gammaℝ (1 - s) / Gammaℝ s * zetaIntegral tateHaarR f 1 s := by
  have hχ : ∀ u : ℝˣ, ‖((1 : ℝˣ →* ℂˣ) u : ℂ)‖ = (distribHaarChar ℝ u : ℝ) ^ (0 : ℝ) := fun u => by simp
  have h := zetaIntegral_fourierR_comm f gaussR continuous_const hχ (by simpa using hs0) (by simpa using hs1)
  have hg : fourierR gaussR = gaussR := by
    funext y
    rw [gaussR, fourierR_gaussian_pi, gaussianSchwartz_apply, Real.norm_eq_abs, sq_abs]
    push_cast; ring_nf
  have hs1' : 0 < (1 - s).re := by rw [sub_re, one_re]; linarith
  have hinv1 : (1 : ℝˣ →* ℂˣ)⁻¹ = 1 := by ext u; simp
  simp only [hinv1] at h
  rw [hg, zetaIntegral_gaussian_real hs1', zetaIntegral_gaussian_real hs0] at h
  have hne : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  rw [div_mul_eq_mul_div, eq_div_iff hne, mul_comm, ← h, mul_comm]

end

end NumberFieldKB.LocalZeta
