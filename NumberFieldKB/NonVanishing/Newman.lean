import NumberFieldKB.NonVanishing.Rectangle
import QuadFormsKB.Citation

/-!
# Newman's Tauberian theorem

**Theorem (Newman 1980; Zagier's form).** Let $f:[0,\infty)\to\mathbb C$ be bounded, $|f|\le B$, and measurable.
Its Laplace transform $g(z) = \int_0^\infty f(t)e^{-zt}\,dt$ is holomorphic for $\operatorname{Re}z>0$. If $g$ extends
holomorphically to an open set containing the closed half-plane $\operatorname{Re}z\ge0$, then
$$\int_0^Tf(t)\,dt\longrightarrow g(0)\qquad(T\to\infty)\qquad(\texttt{newman}).$$

Mathlib has no Tauberian theorem; this is the analytic input for the natural-order Euler product at $s = 1$
(`NaturalOrder.lean`), in place of the prime ideal theorem with an error term.

*Proof* (Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104 (1997), with rectangles
instead of the circle). Put $g_T(z) = \int_0^Tf(t)e^{-zt}\,dt$ (entire, `differentiable_laplaceTrunc`),
$k(z) = 1+z^2/R^2$, and for $R>0$ choose $\delta>0$ with $g$ holomorphic on $[-\delta,R]\times[-R,R]$. By the Cauchy
integral formula on rectangles (`rectBd_div_eq`),
$$2\pi i\,(g(0)-g_T(0)) = \oint_{\partial([-\delta,R]\times[-R,R])}g\,e^{zT}k\frac{dz}z
-\oint_{\partial([-R,R]\times[-R,R])}g_T\,e^{zT}k\frac{dz}z .$$
On the right half ($x = \operatorname{Re}z>0$) the two contours agree and $|(g-g_T)(z)e^{zT}|\le B/x$; on the left half
$|g_T(z)e^{zT}|\le B/|x|$; since $|k(x\pm iR)|\le3|x|/R$ and $|k|\le3$ on the vertical sides, both contributions are at
most $12B/R$ (`norm_rightPart_le`, `norm_leftPart_le`). The remaining piece, $g\,e^{zT}k/z$ on the left part of the
small rectangle, tends to $0$ as $T\to\infty$ because $|e^{zT}| = e^{xT}$ with $x\le0$, and $x = -\delta<0$ on its vertical
side. So $\limsup_T|g(0)-g_T(0)|\le24B/(2\pi R)$ for every $R$.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped Interval

namespace NumberFieldKB.NonVanishing

noncomputable section

/-- The truncated Laplace transform $g_T(z) = \int_0^Tf(t)e^{-zt}\,dt$. -/
def laplaceTrunc (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..T, f t * cexp (-(z * t))

/-! ### Elementary bounds -/

theorem norm_cexp_neg_mul (z : ℂ) (t : ℝ) : ‖cexp (-(z * t))‖ = Real.exp (-(z.re * t)) := by
  rw [Complex.norm_exp]; simp

theorem norm_cexp_mul (z : ℂ) (t : ℝ) : ‖cexp (z * t)‖ = Real.exp (z.re * t) := by
  rw [Complex.norm_exp]; simp

/-- $\int_a^0e^{Tx}\,dx\le1/T$ for $T>0$ (and $a\le0$). -/
theorem integral_exp_mul_le {T : ℝ} (hT : 0 < T) (a : ℝ) :
    ∫ x in a..0, Real.exp (T * x) ≤ 1 / T := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := 0) (fun x => Real.exp x) hT.ne'
  rw [h, integral_exp, mul_zero, Real.exp_zero, smul_eq_mul, one_div]
  have : 0 ≤ Real.exp (T * a) := (Real.exp_pos _).le
  have hT' : 0 < T⁻¹ := inv_pos.mpr hT
  nlinarith

section bounds

variable {f : ℝ → ℂ} {B : ℝ}

theorem norm_integrand_le (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) (z : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖f t * cexp (-(z * t))‖ ≤ B * Real.exp (-(z.re * t)) := by
  rw [norm_mul, norm_cexp_neg_mul]
  exact mul_le_mul_of_nonneg_right (hB t ht) (Real.exp_pos _).le

theorem aestronglyMeasurable_integrand (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (z : ℂ)
    {s : Set ℝ} (hs : s ⊆ Ioi 0) :
    AEStronglyMeasurable (fun t : ℝ => f t * cexp (-(z * t))) (volume.restrict s) :=
  (hf.mono_set hs).mul (by fun_prop : Continuous fun t : ℝ => cexp (-(z * t))).aestronglyMeasurable

theorem integrableOn_integrand_Ioi (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun t : ℝ => f t * cexp (-(z * t))) (Ioi c) := by
  have hi : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Ioi c) :=
    (integrableOn_exp_mul_Ioi (by linarith) c).const_mul B
  refine hi.mono' (aestronglyMeasurable_integrand hf z (Ioi_subset_Ioi hc)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have := norm_integrand_le hB z (t := t) (hc.trans (le_of_lt ht))
  simpa [neg_mul] using this

theorem intervalIntegrable_integrand (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => f t * cexp (-(z * t))) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hi : IntegrableOn (fun t : ℝ => B * Real.exp (|z.re| * T)) (Ioc 0 T) := integrableOn_const (by simp)
  refine hi.mono' (aestronglyMeasurable_integrand hf z Ioc_subset_Ioi_self) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
  refine (norm_integrand_le hB z ht.1.le).trans (mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hB 0 le_rfl)))
  refine Real.exp_le_exp.mpr ?_
  have h1 : -(z.re * t) ≤ |z.re| * t := by
    have := neg_abs_le z.re; nlinarith [ht.1]
  nlinarith [abs_nonneg z.re, ht.2]

/-- **$g_T$ is entire.** -/
theorem differentiable_laplaceTrunc (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) {T : ℝ} (hT : 0 ≤ T) : Differentiable ℂ (laplaceTrunc f T) := by
  intro z₀
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  have hΙ : Ι (0 : ℝ) T = Ioc 0 T := uIoc_of_le hT
  set C : ℝ := B * T * Real.exp ((‖z₀‖ + 1) * T)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := T)
    (F := fun z t => f t * cexp (-(z * t))) (F' := fun z t => f t * (cexp (-(z * t)) * (-(t : ℂ))))
    (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := fun _ => C) (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => by rw [hΙ]; exact aestronglyMeasurable_integrand hf z Ioc_subset_Ioi_self)
    (intervalIntegrable_integrand hf hB z₀ hT)
    (by
      rw [hΙ]
      exact (hf.mono_set Ioc_subset_Ioi_self).mul
        (by fun_prop : Continuous fun t : ℝ => cexp (-(z₀ * t)) * (-(t : ℂ))).aestronglyMeasurable)
    (Eventually.of_forall fun t ht z hz => by
      rw [hΙ] at ht
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_le_norm_add_norm_sub' z z₀
        rw [Metric.mem_ball, dist_eq_norm] at hz
        linarith
      rw [norm_mul, norm_mul, norm_neg, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht.1]
      have h1 : ‖f t‖ ≤ B := hB t ht.1.le
      have h2 : Real.exp (-(z.re * t)) ≤ Real.exp ((‖z₀‖ + 1) * T) := by
        refine Real.exp_le_exp.mpr ?_
        have := neg_abs_le z.re
        have := abs_re_le_norm z
        nlinarith [ht.1, ht.2, norm_nonneg z₀]
      calc ‖f t‖ * (Real.exp (-(z.re * t)) * t) ≤ B * (Real.exp ((‖z₀‖ + 1) * T) * T) :=
            mul_le_mul h1 (mul_le_mul h2 ht.2 ht.1.le (Real.exp_pos _).le) (mul_nonneg (Real.exp_pos _).le ht.1.le) hB0
        _ = C := by ring)
    intervalIntegrable_const
    (Eventually.of_forall fun t _ z _ => by
      have h : HasDerivAt (fun z : ℂ => cexp (-(z * t))) (cexp (-(z * t)) * (-(t : ℂ))) z := by
        have := ((hasDerivAt_id z).mul_const (t : ℂ)).neg.cexp
        simpa using this
      exact h.const_mul (f t))
  exact key.2.differentiableAt

/-- **The tail bound**: for $\operatorname{Re}z = x>0$, $x\,|(g(z)-g_T(z))e^{zT}|\le B$. -/
theorem re_mul_norm_tail_le (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    z.re * ‖((∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t))) - laplaceTrunc f T z) * cexp (z * T)‖ ≤ B := by
  have hsplit : (∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t))) - laplaceTrunc f T z =
      ∫ t in Ioi T, f t * cexp (-(z * t)) := by
    rw [laplaceTrunc, intervalIntegral.integral_of_le hT, ← Ioc_union_Ioi_eq_Ioi hT,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((integrableOn_integrand_Ioi hf hB hz le_rfl).mono_set Ioc_subset_Ioi_self)
        (integrableOn_integrand_Ioi hf hB hz hT)]
    ring
  rw [hsplit, norm_mul, norm_cexp_mul]
  have hbd : ‖∫ t in Ioi T, f t * cexp (-(z * t))‖ ≤ ∫ t in Ioi T, B * Real.exp (-z.re * t) := by
    refine norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (by linarith) T).const_mul B) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    simpa [neg_mul] using norm_integrand_le hB z (t := t) (hT.trans (le_of_lt ht))
  rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith)] at hbd
  have hx := Real.exp_pos (z.re * T)
  calc z.re * (‖∫ t in Ioi T, f t * cexp (-(z * t))‖ * Real.exp (z.re * T))
      ≤ z.re * (B * (-Real.exp (-z.re * T) / -z.re) * Real.exp (z.re * T)) := by gcongr
    _ = B := by
      have hx' : z.re * z.re⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
      have hEe : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
        rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
      rw [neg_div_neg_eq, div_eq_mul_inv]
      linear_combination (B * Real.exp (-z.re * T) * Real.exp (z.re * T)) * hx' + B * hEe

/-- **The bound on the left**: for $\operatorname{Re}z = x\le0$, $|x|\,|g_T(z)e^{zT}|\le B$. -/
theorem abs_re_mul_norm_trunc_le (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) {z : ℂ} (hz : z.re ≤ 0) {T : ℝ} (hT : 0 ≤ T) :
    |z.re| * ‖laplaceTrunc f T z * cexp (z * T)‖ ≤ B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  rcases hz.lt_or_eq with hz | hz
  · have hbd : ‖laplaceTrunc f T z‖ ≤ ∫ t in (0 : ℝ)..T, B * Real.exp (-z.re * t) := by
      refine intervalIntegral.norm_integral_le_of_norm_le hT (Eventually.of_forall fun t ht => ?_)
        ((by fun_prop : Continuous fun t : ℝ => B * Real.exp (-z.re * t)).intervalIntegrable 0 T)
      simpa [neg_mul] using norm_integrand_le hB z (t := t) ht.1.le
    have hint : ∫ t in (0 : ℝ)..T, B * Real.exp (-z.re * t) = B * ((Real.exp (-z.re * T) - 1) / (-z.re)) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have h := intervalIntegral.integral_comp_mul_left (a := 0) (b := T) (fun x => Real.exp x)
        (c := -z.re) (by linarith)
      rw [h, integral_exp, mul_zero, Real.exp_zero, smul_eq_mul, div_eq_inv_mul]
    rw [hint] at hbd
    rw [norm_mul, norm_cexp_mul, abs_of_neg hz]
    have he : Real.exp (z.re * T) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 := Real.exp_pos (z.re * T)
    calc -z.re * (‖laplaceTrunc f T z‖ * Real.exp (z.re * T))
        ≤ -z.re * (B * ((Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T)) := by
          gcongr
          linarith
      _ = B * (1 - Real.exp (z.re * T)) := by
          have hne : -z.re ≠ 0 := by linarith
          have hx' : -z.re * (-z.re)⁻¹ = 1 := mul_inv_cancel₀ hne
          have hEe : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
            rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
          rw [div_eq_mul_inv]
          linear_combination (B * (Real.exp (-z.re * T) - 1) * Real.exp (z.re * T)) * hx' + B * hEe
      _ ≤ B := by nlinarith
  · rw [hz, abs_zero, zero_mul]; exact hB0

end bounds

/-! ### The kernel $k(z) = 1+z^2/R^2$ -/

theorem norm_kernel_horiz {R x y : ℝ} (hR : 0 < R) (hx : |x| ≤ R) (hy : y ^ 2 = R ^ 2) :
    ‖1 + ((x : ℂ) + y * I) ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 * |x| / R := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have heq : 1 + ((x : ℂ) + y * I) ^ 2 / (R : ℂ) ^ 2 = (x : ℂ) * ((x : ℂ) + 2 * y * I) / (R : ℂ) ^ 2 := by
    have hy' : (y : ℂ) ^ 2 = (R : ℂ) ^ 2 := by exact_mod_cast hy
    field_simp
    linear_combination (-1 : ℂ) * hy' + (y : ℂ) ^ 2 * I_sq
  have hyR : |y| = R := by
    have h : |y| ^ 2 = R ^ 2 := by rw [sq_abs]; exact hy
    exact (pow_left_inj₀ (abs_nonneg y) hR.le two_ne_zero).mp h
  rw [heq, norm_div, norm_mul, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have h2 : ‖(x : ℂ) + 2 * y * I‖ ≤ 3 * R := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, hyR]
    norm_num
    linarith
  rw [div_le_div_iff₀ (by positivity) hR]
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg x) hR.le)]

theorem norm_kernel_vert {R x y : ℝ} (hR : 0 < R) (hx : |x| = R) (hy : |y| ≤ R) :
    ‖1 + ((x : ℂ) + y * I) ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 := by
  have hR' : (R : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hR 2).ne'
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have h1 : ‖(x : ℂ) + y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [h1]
  have hx2 : x ^ 2 = R ^ 2 := by rw [← sq_abs, hx]
  have hy2 : y ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have : (x ^ 2 + y ^ 2) / R ^ 2 ≤ 2 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

/-! ### Splitting a rectangle at $\operatorname{Re}z = 0$ -/

/-- The part of $\oint_{\partial([x_0,R]\times[-R,R])}G$ with $\operatorname{Re}z\le0$. -/
def leftPart (G : ℂ → ℂ) (x₀ R : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..0, G (x + (-R : ℝ) * I)) - (∫ x : ℝ in x₀..0, G (x + R * I)) -
    I * ∫ y : ℝ in (-R)..R, G (x₀ + y * I)

/-- The part of $\oint_{\partial([x_0,R]\times[-R,R])}G$ with $\operatorname{Re}z\ge0$. -/
def rightPart (G : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..R, G (x + (-R : ℝ) * I)) - (∫ x : ℝ in (0 : ℝ)..R, G (x + R * I)) +
    I * ∫ y : ℝ in (-R)..R, G (R + y * I)

theorem rectBd_eq_left_add_right (G : ℂ → ℂ) {x₀ R : ℝ}
    (hb : IntervalIntegrable (fun x : ℝ => G (x + (-R : ℝ) * I)) volume x₀ R)
    (ht : IntervalIntegrable (fun x : ℝ => G (x + R * I)) volume x₀ R) (hx₀ : x₀ ≤ 0) (hR : 0 ≤ R) :
    rectBd G x₀ R (-R) R = leftPart G x₀ R + rightPart G R := by
  have hsub1 : [[x₀, (0 : ℝ)]] ⊆ [[x₀, R]] := uIcc_subset_uIcc left_mem_uIcc (by simp [uIcc_of_le (hx₀.trans hR), hx₀, hR])
  have hsub2 : [[(0 : ℝ), R]] ⊆ [[x₀, R]] := uIcc_subset_uIcc (by simp [uIcc_of_le (hx₀.trans hR), hx₀, hR]) right_mem_uIcc
  rw [rectBd, leftPart, rightPart, ← intervalIntegral.integral_add_adjacent_intervals (hb.mono_set hsub1)
      (hb.mono_set hsub2), ← intervalIntegral.integral_add_adjacent_intervals (ht.mono_set hsub1)
      (ht.mono_set hsub2)]
  ring

theorem norm_rightPart_le (G : ℂ → ℂ) {R C : ℝ} (hR : 0 ≤ R)
    (hh : ∀ x ∈ Ioc (0 : ℝ) R, ‖G (x + (-R : ℝ) * I)‖ ≤ C ∧ ‖G (x + R * I)‖ ≤ C)
    (hv : ∀ y ∈ Ι (-R) R, ‖G (R + y * I)‖ ≤ C) : ‖rightPart G R‖ ≤ 4 * C * R := by
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R)
    (f := fun x : ℝ => G (x + (-R : ℝ) * I)) (C := C) (fun x hx => (hh x (by rwa [uIoc_of_le hR] at hx)).1)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := R)
    (f := fun x : ℝ => G (x + R * I)) (C := C) (fun x hx => (hh x (by rwa [uIoc_of_le hR] at hx)).2)
  have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R) (b := R)
    (f := fun y : ℝ => G (R + y * I)) (C := C) hv
  rw [sub_zero, abs_of_nonneg hR] at h1 h2
  rw [show R - -R = 2 * R by ring, abs_of_nonneg (by linarith)] at h3
  rw [rightPart]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) (le_of_eq (by rw [norm_mul, Complex.norm_I, one_mul]))).trans ?_
  linarith

theorem norm_leftPart_le (G : ℂ → ℂ) {x₀ R C : ℝ} (hx₀ : x₀ ≤ 0) (hR : 0 ≤ R)
    (hh : ∀ x ∈ Ioc x₀ 0, ‖G (x + (-R : ℝ) * I)‖ ≤ C ∧ ‖G (x + R * I)‖ ≤ C)
    (hv : ∀ y ∈ Ι (-R) R, ‖G (x₀ + y * I)‖ ≤ C) : ‖leftPart G x₀ R‖ ≤ 2 * C * (-x₀) + 2 * C * R := by
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀) (b := 0)
    (f := fun x : ℝ => G (x + (-R : ℝ) * I)) (C := C) (fun x hx => (hh x (by rwa [uIoc_of_le hx₀] at hx)).1)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀) (b := 0)
    (f := fun x : ℝ => G (x + R * I)) (C := C) (fun x hx => (hh x (by rwa [uIoc_of_le hx₀] at hx)).2)
  have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R) (b := R)
    (f := fun y : ℝ => G (x₀ + y * I)) (C := C) hv
  rw [zero_sub, abs_neg, abs_of_nonpos hx₀] at h1 h2
  rw [show R - -R = 2 * R by ring, abs_of_nonneg (by linarith)] at h3
  rw [leftPart]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) (le_of_eq (by rw [norm_mul, Complex.norm_I, one_mul]))).trans ?_
  linarith

/-! ### Newman's theorem -/

/-- The kernel $k(z) = 1+z^2/R^2$. -/
def kerR (R : ℝ) (z : ℂ) : ℂ := 1 + z ^ 2 / (R : ℂ) ^ 2

theorem kerR_zero (R : ℝ) : kerR R 0 = 1 := by simp [kerR]

theorem continuous_kerR (R : ℝ) : Continuous (kerR R) := by unfold kerR; fun_prop

/-- $|w k/z|\le3B/R^2$ from $a|w|\le B$, $|k|\le3a/R$, $|z|\ge R$. -/
theorem norm_mul_div_le {w k z : ℂ} {a R B : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (hw : a * ‖w‖ ≤ B)
    (hk : ‖k‖ ≤ 3 * a / R) (hz : R ≤ ‖z‖) : ‖w * k / z‖ ≤ 3 * B / R ^ 2 := by
  rw [norm_div, norm_mul, div_le_div_iff₀ (hR.trans_le hz) (by positivity)]
  have h1 : ‖w‖ * ‖k‖ ≤ ‖w‖ * (3 * a / R) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
  have h2 : ‖w‖ * (3 * a / R) * R = 3 * (a * ‖w‖) := by field_simp
  have hB : 0 ≤ B := (mul_nonneg ha (norm_nonneg _)).trans hw
  calc ‖w‖ * ‖k‖ * R ^ 2 ≤ ‖w‖ * (3 * a / R) * R * R := by nlinarith
    _ = 3 * (a * ‖w‖) * R := by rw [h2]
    _ ≤ 3 * B * R := by nlinarith
    _ ≤ 3 * B * ‖z‖ := by nlinarith

theorem intervalIntegrable_comp {G : ℂ → ℂ} {K : Set ℂ} (hG : ContinuousOn G K) {γ : ℝ → ℂ} (hγ : Continuous γ)
    {a b : ℝ} (h : ∀ t ∈ [[a, b]], γ t ∈ K) : IntervalIntegrable (fun t => G (γ t)) volume a b :=
  (hG.comp hγ.continuousOn h).intervalIntegrable

theorem rightPart_sub (G₁ G₂ : ℂ → ℂ) {R : ℝ}
    (h1b : IntervalIntegrable (fun x : ℝ => G₁ (x + (-R : ℝ) * I)) volume 0 R)
    (h1t : IntervalIntegrable (fun x : ℝ => G₁ (x + R * I)) volume 0 R)
    (h1v : IntervalIntegrable (fun y : ℝ => G₁ (R + y * I)) volume (-R) R)
    (h2b : IntervalIntegrable (fun x : ℝ => G₂ (x + (-R : ℝ) * I)) volume 0 R)
    (h2t : IntervalIntegrable (fun x : ℝ => G₂ (x + R * I)) volume 0 R)
    (h2v : IntervalIntegrable (fun y : ℝ => G₂ (R + y * I)) volume (-R) R) :
    rightPart G₁ R - rightPart G₂ R = rightPart (fun z => G₁ z - G₂ z) R := by
  simp only [rightPart]
  rw [intervalIntegral.integral_sub h1b h2b, intervalIntegral.integral_sub h1t h2t,
    intervalIntegral.integral_sub h1v h2v]
  ring

section newman

variable {f : ℝ → ℂ} {B : ℝ} {g : ℂ → ℂ} {U : Set ℂ}

/-- **The contour identity**: $2\pi i(g(0)-g_T(0))$ is the left part of the small rectangle for $g$, minus the left
part of the square for $g_T$, plus the right part for $g-g_T$. -/
theorem two_pi_I_mul_sub_eq (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ < R) (hQ : [[-δ, R]] ×ℂ [[-R, R]] ⊆ U) {T : ℝ} (hT : 0 ≤ T) :
    2 * Real.pi * I * (g 0 - laplaceTrunc f T 0) =
      leftPart (fun z => g z * cexp (z * T) * kerR R z / z) (-δ) R -
        leftPart (fun z => laplaceTrunc f T z * cexp (z * T) * kerR R z / z) (-R) R +
        rightPart (fun z => g z * cexp (z * T) * kerR R z / z -
          laplaceTrunc f T z * cexp (z * T) * kerR R z / z) R := by
  set φ₁ : ℂ → ℂ := fun z => g z * cexp (z * T) * kerR R z
  set φ₂ : ℂ → ℂ := fun z => laplaceTrunc f T z * cexp (z * T) * kerR R z
  have hk : Differentiable ℂ (kerR R) := by unfold kerR; fun_prop
  have hd2 : Differentiable ℂ φ₂ := fun z =>
    (((differentiable_laplaceTrunc hf hB hT) z).mul (by fun_prop)).mul (hk z)
  have hc1 : ContinuousOn φ₁ ([[-δ, R]] ×ℂ [[-R, R]]) :=
    ((hg.continuousOn.mono hQ).mul (by fun_prop)).mul (continuous_kerR R).continuousOn
  have hC1 : rectBd (fun z => φ₁ z / z) (-δ) R (-R) R = 2 * Real.pi * I * φ₁ 0 :=
    rectBd_div_eq (by linarith) hR (by linarith) hR hc1 fun z hz => by
      have hzQ : z ∈ [[-δ, R]] ×ℂ [[-R, R]] := by
        rw [mem_reProdIm] at hz ⊢
        exact ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hz.1), Icc_subset_uIcc (Ioo_subset_Icc_self hz.2)⟩
      exact ((hg.differentiableAt (hU.mem_nhds (hQ hzQ))).mul (by fun_prop)).mul (hk z)
  have hC2 : rectBd (fun z => φ₂ z / z) (-R) R (-R) R = 2 * Real.pi * I * φ₂ 0 :=
    rectBd_div_eq (by linarith) hR (by linarith) hR hd2.continuous.continuousOn fun z _ => hd2 z
  have h10 : φ₁ 0 = g 0 := by simp [φ₁, kerR_zero]
  have h20 : φ₂ 0 = laplaceTrunc f T 0 := by simp [φ₂, kerR_zero]
  -- continuity away from 0
  set K₁ : Set ℂ := ([[-δ, R]] ×ℂ [[-R, R]]) ∩ {z | z ≠ 0}
  have hG1 : ContinuousOn (fun z => φ₁ z / z) K₁ :=
    (hc1.mono inter_subset_left).div continuousOn_id fun z hz => hz.2
  have hG2 : ContinuousOn (fun z => φ₂ z / z) {z | z ≠ 0} :=
    hd2.continuous.continuousOn.div continuousOn_id fun z hz => hz
  have hRR : (R : ℝ) ∈ [[-R, R]] := right_mem_uIcc
  have hRR' : (-R : ℝ) ∈ [[-R, R]] := left_mem_uIcc
  have hδR' : (R : ℝ) ∈ [[-δ, R]] := right_mem_uIcc
  have hb1 : IntervalIntegrable (fun x : ℝ => φ₁ (x + (-R : ℝ) * I) / (x + (-R : ℝ) * I)) volume (-δ) R :=
    intervalIntegrable_comp hG1 (by fun_prop) fun t ht => ⟨by simp [mem_reProdIm, ht, hRR'],
      fun h => by have := congrArg im h; simp at this; linarith⟩
  have ht1 : IntervalIntegrable (fun x : ℝ => φ₁ (x + R * I) / (x + R * I)) volume (-δ) R :=
    intervalIntegrable_comp hG1 (by fun_prop) fun t ht => ⟨by simp [mem_reProdIm, ht, hRR],
      fun h => by have := congrArg im h; simp at this; linarith⟩
  have hb2 : IntervalIntegrable (fun x : ℝ => φ₂ (x + (-R : ℝ) * I) / (x + (-R : ℝ) * I)) volume (-R) R :=
    intervalIntegrable_comp hG2 (by fun_prop) fun t _ h => by have := congrArg im h; simp at this; linarith
  have ht2 : IntervalIntegrable (fun x : ℝ => φ₂ (x + R * I) / (x + R * I)) volume (-R) R :=
    intervalIntegrable_comp hG2 (by fun_prop) fun t _ h => by have := congrArg im h; simp at this; linarith
  have hs1 := rectBd_eq_left_add_right (fun z => φ₁ z / z) hb1 ht1 (by linarith) hR.le
  have hs2 := rectBd_eq_left_add_right (fun z => φ₂ z / z) hb2 ht2 (by linarith) hR.le
  have h0δ : (0 : ℝ) ∈ [[-δ, R]] := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have h0R : (0 : ℝ) ∈ [[-R, R]] := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  have hsubδ : [[(0 : ℝ), R]] ⊆ [[-δ, R]] := uIcc_subset_uIcc h0δ hδR'
  have hsubR : [[(0 : ℝ), R]] ⊆ [[-R, R]] := uIcc_subset_uIcc h0R hRR
  have hv1 : IntervalIntegrable (fun y : ℝ => φ₁ (R + y * I) / (R + y * I)) volume (-R) R :=
    intervalIntegrable_comp hG1 (by fun_prop) fun t ht => ⟨by simp [mem_reProdIm, ht, hδR'],
      fun h => by have := congrArg re h; simp at this; linarith⟩
  have hv2 : IntervalIntegrable (fun y : ℝ => φ₂ (R + y * I) / (R + y * I)) volume (-R) R :=
    intervalIntegrable_comp hG2 (by fun_prop) fun t _ h => by have := congrArg re h; simp at this; linarith
  have hsub := rightPart_sub (fun z => φ₁ z / z) (fun z => φ₂ z / z) (R := R) (hb1.mono_set hsubδ)
    (ht1.mono_set hsubδ) hv1 (hb2.mono_set hsubR) (ht2.mono_set hsubR) hv2
  rw [hs1, h10] at hC1
  rw [hs2, h20] at hC2
  rw [mul_sub, ← hC1, ← hC2, ← hsub]
  ring

end newman

section newman2

variable {f : ℝ → ℂ} {B : ℝ} {g : ℂ → ℂ}

theorem re_add_mul_I (x y : ℝ) : ((x : ℂ) + y * I).re = x := by simp

theorem im_add_mul_I (x y : ℝ) : ((x : ℂ) + y * I).im = y := by simp

theorem le_norm_of_sq_eq {x y R : ℝ} (hR : 0 < R) (hy : y ^ 2 = R ^ 2) : R ≤ ‖(x : ℂ) + y * I‖ := by
  have h : |y| ^ 2 = R ^ 2 := by rw [sq_abs]; exact hy
  have hyR := (pow_left_inj₀ (abs_nonneg y) hR.le two_ne_zero).mp h
  have := abs_im_le_norm ((x : ℂ) + y * I)
  rw [im_add_mul_I, hyR] at this
  exact this

theorem le_norm_of_abs_re {x y R : ℝ} (hx : |x| = R) : R ≤ ‖(x : ℂ) + y * I‖ := by
  have := abs_re_le_norm ((x : ℂ) + y * I)
  rwa [re_add_mul_I, hx] at this

/-- **The right part**: $|\text{right part of }(g-g_T)e^{zT}k/z|\le12B/R$. -/
theorem norm_rightPart_tail_le (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B)
    (hlap : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t)))
    {R : ℝ} (hR : 0 < R) {T : ℝ} (hT : 0 ≤ T) :
    ‖rightPart (fun z => g z * cexp (z * T) * kerR R z / z -
        laplaceTrunc f T z * cexp (z * T) * kerR R z / z) R‖ ≤ 12 * B / R := by
  have hpt : ∀ z : ℂ, 0 < z.re → g z * cexp (z * T) * kerR R z / z -
      laplaceTrunc f T z * cexp (z * T) * kerR R z / z =
      (((∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t))) - laplaceTrunc f T z) * cexp (z * T)) * kerR R z / z := by
    intro z hz
    rw [hlap z hz]
    ring
  have hhor : ∀ x ∈ Ioc (0 : ℝ) R, ∀ y : ℝ, y ^ 2 = R ^ 2 →
      ‖g (x + y * I) * cexp ((x + y * I) * T) * kerR R (x + y * I) / (x + y * I) -
        laplaceTrunc f T (x + y * I) * cexp ((x + y * I) * T) * kerR R (x + y * I) / (x + y * I)‖ ≤
      3 * B / R ^ 2 := by
    intro x hx y hy
    have hre : 0 < ((x : ℂ) + y * I).re := by rw [re_add_mul_I]; exact hx.1
    rw [hpt _ hre]
    refine norm_mul_div_le hR hx.1.le ?_ ?_ (le_norm_of_sq_eq hR hy)
    · have := re_mul_norm_tail_le hf hB hre hT
      rwa [re_add_mul_I] at this
    · have := norm_kernel_horiz hR (x := x) (by rw [abs_of_pos hx.1]; exact hx.2) hy
      rwa [abs_of_pos hx.1] at this
  have h := norm_rightPart_le (fun z => g z * cexp (z * T) * kerR R z / z -
      laplaceTrunc f T z * cexp (z * T) * kerR R z / z) (C := 3 * B / R ^ 2) hR.le
    (fun x hx => ⟨hhor x hx (-R) (by ring), hhor x hx R rfl⟩) (fun y hy => by
      have hy' : |y| ≤ R := by
        rw [uIoc_of_le (by linarith)] at hy
        exact abs_le.mpr ⟨hy.1.le, hy.2⟩
      have hre : 0 < ((R : ℂ) + y * I).re := by rw [re_add_mul_I]; exact hR
      rw [hpt _ hre]
      refine norm_mul_div_le hR hR.le ?_ ?_ (le_norm_of_abs_re (abs_of_pos hR))
      · have := re_mul_norm_tail_le hf hB hre hT
        rwa [re_add_mul_I] at this
      · rw [mul_div_assoc, div_self hR.ne', mul_one]
        exact norm_kernel_vert hR (abs_of_pos hR) hy')
  calc _ ≤ 4 * (3 * B / R ^ 2) * R := h
    _ = 12 * B / R := by field_simp; ring

/-- **The left part of the square for $g_T$**: at most $12B/R$. -/
theorem norm_leftPart_trunc_le (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B) {R : ℝ} (hR : 0 < R) {T : ℝ} (hT : 0 ≤ T) :
    ‖leftPart (fun z => laplaceTrunc f T z * cexp (z * T) * kerR R z / z) (-R) R‖ ≤ 12 * B / R := by
  have hhor : ∀ x ∈ Ioc (-R) 0, ∀ y : ℝ, y ^ 2 = R ^ 2 →
      ‖laplaceTrunc f T (x + y * I) * cexp ((x + y * I) * T) * kerR R (x + y * I) / (x + y * I)‖ ≤
      3 * B / R ^ 2 := by
    intro x hx y hy
    have hre : ((x : ℂ) + y * I).re ≤ 0 := by rw [re_add_mul_I]; exact hx.2
    refine norm_mul_div_le hR (abs_nonneg x) ?_ ?_ (le_norm_of_sq_eq hR hy)
    · have := abs_re_mul_norm_trunc_le hB hre hT
      rwa [re_add_mul_I] at this
    · exact norm_kernel_horiz hR (abs_le.mpr ⟨hx.1.le, by linarith [hx.2]⟩) hy
  have h := norm_leftPart_le (fun z => laplaceTrunc f T z * cexp (z * T) * kerR R z / z) (x₀ := -R)
    (C := 3 * B / R ^ 2) (by linarith) hR.le
    (fun x hx => ⟨hhor x hx (-R) (by ring), hhor x hx R rfl⟩) (fun y hy => by
      have hy' : |y| ≤ R := by
        rw [uIoc_of_le (by linarith)] at hy
        exact abs_le.mpr ⟨hy.1.le, hy.2⟩
      have hre : (((-R : ℝ) : ℂ) + y * I).re ≤ 0 := by rw [re_add_mul_I]; linarith
      have habs : |(-R : ℝ)| = R := by rw [abs_neg, abs_of_pos hR]
      refine norm_mul_div_le hR hR.le ?_ ?_ (le_norm_of_abs_re habs)
      · have := abs_re_mul_norm_trunc_le hB hre hT
        rwa [re_add_mul_I, habs] at this
      · rw [mul_div_assoc, div_self hR.ne', mul_one]
        exact norm_kernel_vert hR habs hy')
  calc _ ≤ 2 * (3 * B / R ^ 2) * (- -R) + 2 * (3 * B / R ^ 2) * R := h
    _ = 12 * B / R := by field_simp; ring

/-- **The left part of the small rectangle for $g$**: if $|g(z)k(z)/z|\le M$ there, it is at most
$2M/T+2RMe^{-\delta T}$. -/
theorem norm_leftPart_g_le {R δ M : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hδR : δ < R) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ ([[-δ, 0]] ×ℂ [[-R, R]]) ∩ {z | δ ≤ ‖z‖}, ‖g z * kerR R z / z‖ ≤ M) {T : ℝ} (hT : 0 < T) :
    ‖leftPart (fun z => g z * cexp (z * T) * kerR R z / z) (-δ) R‖ ≤
      2 * M / T + 2 * R * M * Real.exp (-(δ * T)) := by
  have hpt : ∀ z ∈ ([[-δ, 0]] ×ℂ [[-R, R]]) ∩ {z | δ ≤ ‖z‖},
      ‖g z * cexp (z * T) * kerR R z / z‖ ≤ M * Real.exp (z.re * T) := fun z hz => by
    rw [show g z * cexp (z * T) * kerR R z / z = (g z * kerR R z / z) * cexp (z * T) by ring, norm_mul,
      norm_cexp_mul]
    exact mul_le_mul_of_nonneg_right (hM z hz) (Real.exp_pos _).le
  have hRR : ∀ y : ℝ, y ^ 2 = R ^ 2 → y ∈ [[-R, R]] := fun y hy => by
    have h : |y| ^ 2 = R ^ 2 := by rw [sq_abs]; exact hy
    have hyR := (pow_left_inj₀ (abs_nonneg y) hR.le two_ne_zero).mp h
    rw [uIcc_of_le (by linarith)]
    exact abs_le.mp hyR.le
  have hhor : ∀ y : ℝ, y ^ 2 = R ^ 2 → ‖∫ x : ℝ in (-δ)..0, g (x + y * I) * cexp ((x + y * I) * T) *
      kerR R (x + y * I) / (x + y * I)‖ ≤ M / T := by
    intro y hy
    refine (intervalIntegral.norm_integral_le_of_norm_le (g := fun x => M * Real.exp (T * x)) (by linarith)
      (Eventually.of_forall fun x hx => ?_)
      ((by fun_prop : Continuous fun x : ℝ => M * Real.exp (T * x)).intervalIntegrable _ _)).trans ?_
    · have hmem : (x : ℂ) + y * I ∈ ([[-δ, 0]] ×ℂ [[-R, R]]) ∩ {z | δ ≤ ‖z‖} := by
        refine ⟨?_, (le_norm_of_sq_eq hR hy).trans' hδR.le⟩
        rw [mem_reProdIm, re_add_mul_I, im_add_mul_I, uIcc_of_le (by linarith : -δ ≤ 0)]
        exact ⟨Ioc_subset_Icc_self hx, hRR y hy⟩
      have := hpt _ hmem
      rwa [re_add_mul_I, mul_comm x T] at this
    · rw [intervalIntegral.integral_const_mul]
      have := integral_exp_mul_le hT (-δ)
      calc M * ∫ x in (-δ)..0, Real.exp (T * x) ≤ M * (1 / T) := mul_le_mul_of_nonneg_left this hM0
        _ = M / T := by ring
  have hver : ‖I * ∫ y : ℝ in (-R)..R, g (((-δ : ℝ) : ℂ) + y * I) * cexp ((((-δ : ℝ) : ℂ) + y * I) * T) *
      kerR R (((-δ : ℝ) : ℂ) + y * I) / (((-δ : ℝ) : ℂ) + y * I)‖ ≤ 2 * R * M * Real.exp (-(δ * T)) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -R) (b := R)
      (f := fun y : ℝ => g (((-δ : ℝ) : ℂ) + y * I) * cexp ((((-δ : ℝ) : ℂ) + y * I) * T) *
        kerR R (((-δ : ℝ) : ℂ) + y * I) / (((-δ : ℝ) : ℂ) + y * I)) (C := M * Real.exp (-(δ * T))) (fun y hy => by
        have hy' : y ∈ [[-R, R]] := uIoc_subset_uIcc hy
        have hmem : ((-δ : ℝ) : ℂ) + y * I ∈ ([[-δ, 0]] ×ℂ [[-R, R]]) ∩ {z | δ ≤ ‖z‖} := by
          refine ⟨?_, le_norm_of_abs_re (by rw [abs_neg, abs_of_pos hδ])⟩
          rw [mem_reProdIm, re_add_mul_I, im_add_mul_I]
          exact ⟨left_mem_uIcc, hy'⟩
        have := hpt _ hmem
        rwa [re_add_mul_I, neg_mul] at this)
    rw [show R - -R = 2 * R by ring, abs_of_pos (by linarith)] at h
    linarith
  rw [leftPart]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) hver).trans ?_
  have h1 := hhor (-R) (by ring)
  have h2 := hhor R rfl
  have : 2 * M / T = M / T + M / T := by ring
  linarith

/-- **Newman's Tauberian theorem.** If $|f(t)|\le B$ on $[0,\infty)$ ($f$ measurable) and the Laplace transform
$\int_0^\infty f(t)e^{-zt}\,dt$ ($\operatorname{Re}z>0$) agrees with a function $g$ holomorphic on an open set
containing $\{\operatorname{Re}z\ge0\}$, then $\int_0^Tf(t)\,dt\to g(0)$ as $T\to\infty$. -/
@[kb "zagier1997" "Newman's short proof of the prime number theorem, Analytic Theorem [unverified locator]"]
theorem newman {U : Set ℂ} (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))) (hB : ∀ t, 0 ≤ t → ‖f t‖ ≤ B)
    (hU : IsOpen U) (hHU : {z : ℂ | 0 ≤ z.re} ⊆ U) (hg : DifferentiableOn ℂ g U)
    (hlap : ∀ z : ℂ, 0 < z.re → g z = ∫ t in Ioi (0 : ℝ), f t * cexp (-(z * t))) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 (g 0)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 le_rfl)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hπε : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
  set R : ℝ := 24 * B / (Real.pi * ε) + 1 with hRdef
  have hR : 0 < R := by positivity
  have hRB : 24 * B / R < Real.pi * ε := by
    rw [div_lt_iff₀ hR]
    have : Real.pi * ε * (24 * B / (Real.pi * ε)) = 24 * B := by field_simp
    rw [hRdef, mul_add, this]
    linarith
  -- a strip of width δ to the left of the segment [-iR, iR] on which g is holomorphic
  obtain ⟨δ, hδ, hδR, hQ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ [[-δ, R]] ×ℂ [[-R, R]] ⊆ U := by
    set K₀ : Set ℂ := (fun y : ℝ => (y : ℂ) * I) '' Icc (-R) R
    have hK₀ : IsCompact K₀ := isCompact_Icc.image (by fun_prop)
    have hK₀U : K₀ ⊆ U := by
      rintro _ ⟨y, _, rfl⟩
      exact hHU (by simp)
    obtain ⟨δ₀, hδ₀, hsub⟩ := hK₀.exists_cthickening_subset_open hU hK₀U
    have hm : 0 < min δ₀ (R / 2) := lt_min hδ₀ (by linarith)
    refine ⟨min δ₀ (R / 2), lt_min hδ₀ (by linarith), (min_le_right _ _).trans_lt (by linarith), ?_⟩
    intro z hz
    rw [mem_reProdIm, uIcc_of_le (by linarith [min_le_right δ₀ (R / 2)]), uIcc_of_le (by linarith)] at hz
    rcases le_or_gt 0 z.re with h0 | h0
    · exact hHU h0
    · refine hsub (Metric.mem_cthickening_of_dist_le z ((z.im : ℂ) * I) δ₀ K₀ ⟨z.im, hz.2, rfl⟩ ?_)
      have : z - (z.im : ℂ) * I = (z.re : ℂ) := by
        apply Complex.ext <;> simp
      rw [dist_eq_norm, this, Complex.norm_real, Real.norm_eq_abs, abs_of_neg h0]
      linarith [hz.1.1, min_le_left δ₀ (R / 2)]
  -- a bound for g k / z on the left part of the small rectangle
  set Kc : Set ℂ := ([[-δ, 0]] ×ℂ [[-R, R]]) ∩ {z | δ ≤ ‖z‖}
  have hKcQ : Kc ⊆ [[-δ, R]] ×ℂ [[-R, R]] := fun z hz => by
    have h := hz.1
    rw [mem_reProdIm] at h ⊢
    refine ⟨?_, h.2⟩
    have h0 : (0 : ℝ) ∈ [[-δ, R]] := by rw [uIcc_of_le (by linarith)]; constructor <;> linarith
    exact uIcc_subset_uIcc left_mem_uIcc h0 h.1
  have hKc : IsCompact Kc :=
    (isCompact_uIcc.reProdIm isCompact_uIcc).inter_right (isClosed_le continuous_const continuous_norm)
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (f := fun z => g z * kerR R z / z)
    (((hg.continuousOn.mono (hKcQ.trans hQ)).mul (continuous_kerR R).continuousOn).div continuousOn_id
      fun z hz h => by have := hz.2; simp only [mem_setOf_eq, id, h, norm_zero] at this; linarith)
  have hM0 : 0 ≤ M := by
    have hmem : (((-δ : ℝ) : ℂ) + (0 : ℝ) * I) ∈ Kc := by
      refine ⟨?_, le_norm_of_abs_re (by rw [abs_neg, abs_of_pos hδ])⟩
      rw [mem_reProdIm, re_add_mul_I, im_add_mul_I]
      refine ⟨left_mem_uIcc, ?_⟩
      rw [uIcc_of_le (by linarith)]; constructor <;> linarith
    exact (norm_nonneg _).trans (hM _ hmem)
  have hlim : Tendsto (fun T : ℝ => 2 * M / T + 2 * R * M * Real.exp (-(δ * T))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 2 * M / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
    have h2 : Tendsto (fun T : ℝ => Real.exp (-(δ * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hδ)
    simpa using h1.add (h2.const_mul (2 * R * M))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hπε))
  refine ⟨max T₀ 1, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_of_max_le_right hT
  have hT0 : 0 ≤ T := by linarith
  have hid := two_pi_I_mul_sub_eq hf hB hU hg hR hδ hδR hQ hT0
  have h1 := norm_leftPart_g_le hR hδ hδR hM0 hM (by linarith : (0 : ℝ) < T)
  have h1' := hT₀ T (le_of_max_le_left hT)
  have h2 := norm_leftPart_trunc_le hB hR hT0 (f := f)
  have h3 := norm_rightPart_tail_le hf hB hlap hR hT0
  have htot : ‖2 * Real.pi * I * (g 0 - laplaceTrunc f T 0)‖ < 2 * (Real.pi * ε) := by
    rw [hid]
    refine (norm_add_le _ _).trans_lt ?_
    refine (add_le_add (norm_sub_le _ _) h3).trans_lt ?_
    have : 12 * B / R + 12 * B / R = 24 * B / R := by ring
    linarith
  have hnorm : ‖2 * Real.pi * I * (g 0 - laplaceTrunc f T 0)‖ = 2 * Real.pi * ‖g 0 - laplaceTrunc f T 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hnorm] at htot
  have htr : laplaceTrunc f T 0 = ∫ t in (0 : ℝ)..T, f t := by simp [laplaceTrunc]
  rw [dist_eq_norm, ← htr, norm_sub_rev]
  nlinarith [Real.pi_pos]

end newman2

end

end NumberFieldKB.NonVanishing
