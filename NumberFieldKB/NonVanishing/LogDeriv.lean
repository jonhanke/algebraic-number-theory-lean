import NumberFieldKB.NonVanishing.Summation

/-!
# The logarithmic derivative of an Euler product

$F$ is a number field, $|a(v)|\le1$, $w_v(s) = a(v)N(v)^{-s}$, $\lambda_v = \log N(v)$.

* **`hasDerivAt_logEuler`**: for $\operatorname{Re}s>1$, $\frac d{ds}\sum_v-\log(1-w_v(s)) =
  -\sum_v\lambda_vw_v(s)/(1-w_v(s))$ (termwise differentiation, Mathlib's `Complex.hasSum_deriv_of_summable_norm`).
* **`neg_logDeriv_eq`**: if $L = \exp(\texttt{logEuler}\ a)$ on $\operatorname{Re}s>1$, then
  $-L'(s)/L(s) = \sum_v\lambda_vw_v(s)/(1-w_v(s)) = \sum_va(v)\lambda_vN(v)^{-s}+H(s)$ with
  $H(s) = \sum_v\lambda_vw_v(s)^2/(1-w_v(s))$ (`hFun`).
* **`differentiableOn_hFun`**: $H$ is holomorphic on $\operatorname{Re}s>3/4$.
-/

open Complex MeasureTheory Set Filter Topology IsDedekindDomain NumberField
open QuadFormsKB.NFEuler

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

theorem log_normP_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Real.log (normP v) :=
  Real.log_pos (by have := two_le_normP v; exact_mod_cast (by omega : 1 < normP v))

/-- $\sum_v\log N(v)\,N(v)^{-\sigma}<\infty$ for $\sigma>1$. -/
theorem summable_log_mul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => Real.log (normP v) * (normP v : ℝ) ^ (-σ) := by
  set ε := (σ - 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  refine ((summable_normP_rpow (σ := σ - ε) (by simp only [ε]; linarith)).div_const ε).of_nonneg_of_le
    (fun v => mul_nonneg (log_normP_pos v).le (Real.rpow_nonneg (normP_pos' v).le _)) fun v => ?_
  have h1 := Real.log_le_rpow_div (normP_pos' v).le hε
  calc Real.log (normP v) * (normP v : ℝ) ^ (-σ) ≤ (normP v : ℝ) ^ ε / ε * (normP v : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (normP_pos' v).le _)
    _ = (normP v : ℝ) ^ (-(σ - ε)) / ε := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add (normP_pos' v)]
        congr 2
        ring

theorem norm_nps_lt_one (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) : ‖nps v s‖ < 1 := by
  rw [norm_nps]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by have := two_le_normP v; exact_mod_cast (by omega : 1 < normP v))
    (by linarith)

theorem one_sub_mem_slitPlane {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) : 1 - a v * nps v s ∈ slitPlane := by
  refine mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : ‖a v * nps v s‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (ha v)) (norm_nps_lt_one v hs)
  have h2 := Complex.re_le_norm (a v * nps v s)
  simp only [sub_re, one_re]
  linarith

theorem hasDerivAt_nps (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    HasDerivAt (fun w => nps v w) (-(Real.log (normP v) : ℂ) * nps v s) s := by
  have h := (hasDerivAt_neg s).const_cpow (c := ((normP v : ℝ) : ℂ))
    (Or.inl (by exact_mod_cast (normP_pos' v).ne'))
  rw [← ofReal_log (normP_pos' v).le] at h
  convert h using 1
  simp only [nps]
  ring

theorem hasDerivAt_neg_log_term {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun w => -log (1 - a v * nps v w))
      (-(a v * Real.log (normP v) * nps v s / (1 - a v * nps v s))) s := by
  have h1 : HasDerivAt (fun w => 1 - a v * nps v w) (a v * (Real.log (normP v) : ℂ) * nps v s) s := by
    convert ((hasDerivAt_nps v s).const_mul (a v)).const_sub 1 using 1
    ring
  convert (h1.clog (one_sub_mem_slitPlane ha v hs)).neg using 1

/-- **The derivative of `logEuler`** for $\operatorname{Re}s>1$. -/
theorem hasDerivAt_logEuler {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt (logEuler a)
      (-∑' v, a v * Real.log (normP v) * nps v s / (1 - a v * nps v s)) s := by
  set σ₀ : ℝ := (1 + s.re) / 2
  have hσ₀ : 1 < σ₀ := by simp only [σ₀]; linarith
  set U : Set ℂ := {w | σ₀ < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by simp only [U, mem_setOf_eq, σ₀]; linarith
  set Fv : HeightOneSpectrum (𝓞 F) → ℂ → ℂ := fun v w => -log (1 - a v * nps v w)
  have hdiff : ∀ v, DifferentiableOn ℂ (Fv v) U := fun v w hw =>
    (hasDerivAt_neg_log_term ha v (by simp only [U, mem_setOf_eq] at hw; linarith)).differentiableAt
      |>.differentiableWithinAt
  have hle : ∀ v, ∀ w ∈ U, ‖Fv v w‖ ≤ 3 / 2 * (normP v : ℝ) ^ (-σ₀) := fun v w hw => by
    have hw' : σ₀ < w.re := hw
    have hz : ‖-(a v * nps v w)‖ ≤ 1 / 2 := by
      rw [norm_neg]; exact norm_mul_nps_le_half ha v (by linarith)
    have h := norm_log_one_add_half_le_self hz
    rw [← sub_eq_add_neg] at h
    simp only [Fv, norm_neg]
    refine h.trans ?_
    rw [norm_neg, norm_mul, norm_nps]
    have : (normP v : ℝ) ^ (-w.re) ≤ (normP v : ℝ) ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le (by have := two_le_normP v; exact_mod_cast (by omega : 1 ≤ normP v))
        (by linarith)
    have h0 : 0 ≤ (normP v : ℝ) ^ (-w.re) := Real.rpow_nonneg (normP_pos' v).le _
    nlinarith [norm_nonneg (a v), ha v]
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => 3 / 2 * (normP v : ℝ) ^ (-σ₀) :=
    (summable_normP_rpow hσ₀).mul_left _
  have hdiffL : DifferentiableOn ℂ (fun w => ∑' v, Fv v w) U :=
    differentiableOn_tsum_of_summable_norm hsum hdiff hU hle
  have hd := hasSum_deriv_of_summable_norm hsum hdiff hU hle hsU
  have hderiv : ∀ v, deriv (Fv v) s = -(a v * Real.log (normP v) * nps v s / (1 - a v * nps v s)) := fun v =>
    (hasDerivAt_neg_log_term ha v (by linarith)).deriv
  simp only [hderiv] at hd
  have e : logEuler a = fun w => ∑' v, Fv v w := rfl
  have h1 : HasDerivAt (fun w => ∑' v, Fv v w) (deriv (fun w => ∑' v, Fv v w) s) s :=
    (hdiffL.differentiableAt (hU.mem_nhds hsU)).hasDerivAt
  rw [← hd.tsum_eq, tsum_neg] at h1
  rw [e]
  exact h1

/-- **The logarithmic derivative**: if $L = \exp(\texttt{logEuler}\ a)$ on $\operatorname{Re}s>1$, then
$-L'(s)/L(s) = \sum_v\lambda_vw_v(s)/(1-w_v(s))$. -/
theorem neg_logDeriv_eq {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {L : ℂ → ℂ}
    (hL : ∀ s : ℂ, 1 < s.re → L s = cexp (logEuler a s)) {s : ℂ} (hs : 1 < s.re) :
    -deriv L s / L s = ∑' v, a v * Real.log (normP v) * nps v s / (1 - a v * nps v s) := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : L =ᶠ[𝓝 s] fun w => cexp (logEuler a w) :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw => hL w hw
  have hd := (hasDerivAt_logEuler ha hs).cexp
  rw [heq.deriv_eq, hd.deriv, hL s hs]
  have := Complex.exp_ne_zero (logEuler a s)
  field_simp

/-- **$H(s) = \sum_v\lambda_vw_v(s)^2/(1-w_v(s))$**, the prime-power part of $-L'/L$. -/
def hFun (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) : ℂ :=
  ∑' v, Real.log (normP v) * (a v * nps v s) ^ 2 / (1 - a v * nps v s)

theorem norm_hFun_term_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) (v : HeightOneSpectrum (𝓞 F))
    {σ : ℝ} (hσ : 0 < σ) {s : ℂ} (hs : σ ≤ s.re) :
    ‖(Real.log (normP v) : ℂ) * (a v * nps v s) ^ 2 / (1 - a v * nps v s)‖ ≤
      Real.log (normP v) * (normP v : ℝ) ^ (-(2 * σ)) / (1 - (2 : ℝ) ^ (-σ)) := by
  have hN1 : (1 : ℝ) ≤ normP v := by have := two_le_normP v; exact_mod_cast (by omega : 1 ≤ normP v)
  have hw : ‖a v * nps v s‖ ≤ (normP v : ℝ) ^ (-σ) := by
    rw [norm_mul, norm_nps]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (normP_pos' v).le _) (ha v)).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have h2 : (normP v : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast two_le_normP v) (by linarith)
  have hc : 0 < 1 - (2 : ℝ) ^ (-σ) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith : -σ < 0)
    linarith
  have hden : 1 - (2 : ℝ) ^ (-σ) ≤ ‖1 - a v * nps v s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a v * nps v s)
    rw [norm_one] at this
    linarith
  rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (log_normP_pos v)]
  have hsq : ‖a v * nps v s‖ ^ 2 ≤ (normP v : ℝ) ^ (-(2 * σ)) := by
    calc ‖a v * nps v s‖ ^ 2 ≤ ((normP v : ℝ) ^ (-σ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
      _ = (normP v : ℝ) ^ (-(2 * σ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (normP_pos' v).le]; congr 1; push_cast; ring
  rw [div_le_div_iff₀ (hc.trans_le hden) hc]
  have hl := (log_normP_pos v).le
  calc Real.log (normP v) * ‖a v * nps v s‖ ^ 2 * (1 - (2 : ℝ) ^ (-σ))
      ≤ Real.log (normP v) * (normP v : ℝ) ^ (-(2 * σ)) * (1 - (2 : ℝ) ^ (-σ)) := by gcongr
    _ ≤ Real.log (normP v) * (normP v : ℝ) ^ (-(2 * σ)) * ‖1 - a v * nps v s‖ := by
        gcongr

/-- **$H$ is holomorphic on $\operatorname{Re}s>3/4$.** -/
theorem differentiableOn_hFun {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) :
    DifferentiableOn ℂ (hFun a) {s | 3 / 4 < s.re} := by
  have hU : IsOpen {s : ℂ | 3 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum := ((summable_log_mul_rpow (F := F) (σ := 2 * (3 / 4)) (by norm_num)).div_const
    (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ))))
  refine differentiableOn_tsum_of_summable_norm hsum (fun v w hw => ?_) hU
    (fun v w hw => norm_hFun_term_le ha v (by norm_num) (le_of_lt hw))
  have hw' : 0 < w.re := by have : 3 / 4 < w.re := hw; linarith
  have hd : DifferentiableAt ℂ (fun s => a v * nps v s) w := ((hasDerivAt_nps v w).const_mul (a v)).differentiableAt
  have hne : 1 - a v * nps v w ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane ha v hw')
  exact ((differentiableAt_const _).mul (hd.pow 2)).div ((differentiableAt_const _).sub hd) hne
    |>.differentiableWithinAt

/-- $\sum_v\lambda_vw_v/(1-w_v) = \sum_va(v)\lambda_vN(v)^{-s}+H(s)$ for $\operatorname{Re}s>1$. -/
theorem tsum_logDeriv_eq {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ∑' v, a v * Real.log (normP v) * nps v s / (1 - a v * nps v s) =
      (∑' v, a v * Real.log (normP v) * nps v s) + hFun a s := by
  have hs1 : Summable fun v => a v * Real.log (normP v) * nps v s := by
    refine (summable_log_mul_rpow (F := F) hs).of_norm_bounded fun v => ?_
    rw [norm_mul, norm_mul, norm_nps, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (log_normP_pos v)]
    exact mul_le_of_le_one_left (mul_nonneg (log_normP_pos v).le (Real.rpow_nonneg (normP_pos' v).le _))
      (ha v) |>.trans_eq' (by ring)
  have hs2 : Summable fun v => (Real.log (normP v) : ℂ) * (a v * nps v s) ^ 2 / (1 - a v * nps v s) :=
    ((summable_log_mul_rpow (F := F) (σ := 2 * (3 / 4)) (by norm_num)).div_const
      (1 - (2 : ℝ) ^ (-(3 / 4 : ℝ)))).of_norm_bounded fun v => norm_hFun_term_le ha v (by norm_num) (by linarith)
  rw [hFun, ← hs1.tsum_add hs2]
  refine tsum_congr fun v => ?_
  have hne : 1 - a v * nps v s ≠ 0 := one_sub_mul_nps_ne_zero ha v hs.le
  field_simp
  ring

end

end NumberFieldKB.NonVanishing
