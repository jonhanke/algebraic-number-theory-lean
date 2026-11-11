import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Filter

/-!
# The Cauchy integral formula on a rectangle

Mathlib has the Cauchy–Goursat theorem on rectangles (`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`)
and the Cauchy integral formula on circles, but not the integral formula on rectangles. Newman's Tauberian theorem
(`Newman.lean`) is proved here with rectangular contours, so we add it.

* **`rectBd f x₀ x₁ y₀ y₁`**: the integral of $f$ over the positively oriented boundary of the rectangle
  $[x_0,x_1]\times[y_0,y_1]$, in the form of Mathlib's Cauchy–Goursat theorem.
* **`rectBd_inv`**: $\oint dz/z = 2\pi i$ when $x_0<0<x_1$, $y_0<0<y_1$ (computed with the principal logarithm on
  each side; the left side uses $\log(-z)$).
* **`rectBd_div_eq`**: **the Cauchy integral formula at $0$**: if $\varphi$ is continuous on the closed rectangle and
  holomorphic on the open one, $\oint\varphi(z)\,dz/z = 2\pi i\,\varphi(0)$ (Cauchy–Goursat for `dslope φ 0`).
-/

open Complex MeasureTheory Set intervalIntegral Real
open scoped Interval

namespace NumberFieldKB.NonVanishing

noncomputable section

/-- **The boundary integral over a rectangle** $[x_0,x_1]\times[y_0,y_1]$ (positively oriented when $x_0<x_1$,
$y_0<y_1$): bottom, minus top, plus $i$ times the right side, minus $i$ times the left side. -/
def rectBd (f : ℂ → ℂ) (x₀ x₁ y₀ y₁ : ℝ) : ℂ :=
  (∫ x : ℝ in x₀..x₁, f (x + y₀ * I)) - (∫ x : ℝ in x₀..x₁, f (x + y₁ * I)) +
    I * (∫ y : ℝ in y₀..y₁, f (x₁ + y * I)) - I * (∫ y : ℝ in y₀..y₁, f (x₀ + y * I))

/-- Cauchy–Goursat in the form of `rectBd`. -/
theorem rectBd_eq_zero_of_off_countable (f : ℂ → ℂ) {x₀ x₁ y₀ y₁ : ℝ} (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[x₀, x₁]] ×ℂ [[y₀, y₁]]))
    (Hd : ∀ z ∈ Ioo (min x₀ x₁) (max x₀ x₁) ×ℂ Ioo (min y₀ y₁) (max y₀ y₁) \ s, DifferentiableAt ℂ f z) :
    rectBd f x₀ x₁ y₀ y₁ = 0 := by
  have h := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (x₀ + y₀ * I) (x₁ + y₁ * I) s hs
    (by simpa using Hc) (by simpa using Hd)
  simpa [rectBd, smul_eq_mul] using h

/-! ### $\oint dz/z = 2\pi i$ -/

theorem integral_inv_horizontal {y : ℝ} (hy : y ≠ 0) (a b : ℝ) :
    ∫ x : ℝ in a..b, ((x : ℂ) + y * I)⁻¹ = log (b + y * I) - log (a + y * I) := by
  have hne : ∀ x : ℝ, (x : ℂ) + y * I ≠ 0 := fun x h => hy (by simpa using congrArg im h)
  have hslit : ∀ x : ℝ, (x : ℂ) + y * I ∈ slitPlane := fun x => mem_slitPlane_iff.mpr (Or.inr (by simpa using hy))
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (E := ℂ) (f := fun x : ℝ => log ((x : ℂ) + y * I))
    (fun x _ => ?_) ?_
  · have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + y * I) 1 x := (hasDerivAt_id x).ofReal_comp.add_const _
    simpa [one_div] using h1.clog_real (hslit x)
  · exact (Continuous.continuousOn (by fun_prop) |>.inv₀ fun x _ => hne x).intervalIntegrable

theorem integral_inv_vertical_pos {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    I * ∫ y : ℝ in a..b, ((x : ℂ) + y * I)⁻¹ = log (x + b * I) - log (x + a * I) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I ≠ 0 := fun y h => hx.ne' (by simpa using congrArg re h)
  have hslit : ∀ y : ℝ, (x : ℂ) + y * I ∈ slitPlane := fun y => mem_slitPlane_iff.mpr (Or.inl (by simpa using hx))
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (E := ℂ) (f := fun y : ℝ => log ((x : ℂ) + y * I))
    (fun y _ => ?_) ?_
  · have h1 : HasDerivAt (fun y : ℝ => (x : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
    simpa [div_eq_mul_inv] using h1.clog_real (hslit y)
  · exact (continuousOn_const.mul (Continuous.continuousOn (by fun_prop) |>.inv₀ fun y _ => hne y)).intervalIntegrable

theorem integral_inv_vertical_neg {x : ℝ} (hx : x < 0) (a b : ℝ) :
    I * ∫ y : ℝ in a..b, ((x : ℂ) + y * I)⁻¹ = log (-(x + b * I)) - log (-(x + a * I)) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I ≠ 0 := fun y h => hx.ne (by simpa using congrArg re h)
  have hslit : ∀ y : ℝ, -((x : ℂ) + y * I) ∈ slitPlane := fun y =>
    mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (E := ℂ) (f := fun y : ℝ => log (-((x : ℂ) + y * I)))
    (fun y _ => ?_) ?_
  · have h1 : HasDerivAt (fun y : ℝ => -((x : ℂ) + y * I)) (-I) y := by
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := by
        simpa using (hasDerivAt_id y).ofReal_comp
      convert ((h0.mul_const I).const_add (x : ℂ)).fun_neg using 1
      ring
    have h2 := h1.clog_real (hslit y)
    convert h2 using 1
    have := hne y
    field_simp
  · exact (continuousOn_const.mul (Continuous.continuousOn (by fun_prop) |>.inv₀ fun y _ => hne y)).intervalIntegrable

/-- $\log w-\log(-w) = \pi i$ for $\operatorname{Im}w>0$. -/
theorem log_sub_log_neg_of_im_pos {w : ℂ} (hw : 0 < w.im) : log w - log (-w) = Real.pi * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hw]

/-- $\log w-\log(-w) = -\pi i$ for $\operatorname{Im}w<0$. -/
theorem log_sub_log_neg_of_im_neg {w : ℂ} (hw : w.im < 0) : log w - log (-w) = -(Real.pi * I) := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg hw]

/-- **$\oint dz/z = 2\pi i$** over a rectangle containing $0$ in its interior. -/
theorem rectBd_inv {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : x₀ < 0) (hx₁ : 0 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁) :
    rectBd (fun z => z⁻¹) x₀ x₁ y₀ y₁ = 2 * Real.pi * I := by
  simp only [rectBd]
  rw [integral_inv_horizontal hy₀.ne, integral_inv_horizontal hy₁.ne', integral_inv_vertical_pos hx₁,
    integral_inv_vertical_neg hx₀]
  have h1 := log_sub_log_neg_of_im_pos (w := (x₀ : ℂ) + y₁ * I) (by simpa using hy₁)
  have h2 := log_sub_log_neg_of_im_neg (w := (x₀ : ℂ) + y₀ * I) (by simpa using hy₀)
  linear_combination h1 - h2

/-! ### The Cauchy integral formula on a rectangle -/

/-- On a segment avoiding $0$: $\int\varphi(\gamma)/\gamma = \int(\mathrm{dslope}\,\varphi\,0)(\gamma)+\varphi(0)\int1/\gamma$. -/
theorem integral_div_eq_dslope {φ : ℂ → ℂ} {K : Set ℂ} (hψ : ContinuousOn (dslope φ 0) K) {γ : ℝ → ℂ}
    (hγ : Continuous γ) {a b : ℝ} (hK : ∀ t ∈ [[a, b]], γ t ∈ K) (h0 : ∀ t ∈ [[a, b]], γ t ≠ 0) :
    ∫ t in a..b, φ (γ t) / γ t = (∫ t in a..b, dslope φ 0 (γ t)) + φ 0 * ∫ t in a..b, (γ t)⁻¹ := by
  have hi1 : IntervalIntegrable (fun t => dslope φ 0 (γ t)) volume a b :=
    (hψ.comp hγ.continuousOn fun t ht => hK t ht).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => (γ t)⁻¹) volume a b :=
    (hγ.continuousOn.inv₀ fun t ht => h0 t ht).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 (hi2.const_mul _)]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [dslope_of_ne _ (h0 t ht), slope_def_field, sub_zero]
  have := h0 t ht
  field_simp
  ring

/-- **The Cauchy integral formula on a rectangle**: if $\varphi$ is continuous on $[x_0,x_1]\times[y_0,y_1]$ with
$x_0<0<x_1$, $y_0<0<y_1$ and holomorphic on the open rectangle, then $\oint\varphi(z)\,dz/z = 2\pi i\,\varphi(0)$. -/
theorem rectBd_div_eq {φ : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx₀ : x₀ < 0) (hx₁ : 0 < x₁) (hy₀ : y₀ < 0) (hy₁ : 0 < y₁)
    (Hc : ContinuousOn φ ([[x₀, x₁]] ×ℂ [[y₀, y₁]]))
    (Hd : ∀ z ∈ Ioo x₀ x₁ ×ℂ Ioo y₀ y₁, DifferentiableAt ℂ φ z) :
    rectBd (fun z => φ z / z) x₀ x₁ y₀ y₁ = 2 * Real.pi * I * φ 0 := by
  set K := [[x₀, x₁]] ×ℂ [[y₀, y₁]]
  have h0mem : (0 : ℂ) ∈ Ioo x₀ x₁ ×ℂ Ioo y₀ y₁ := by
    simp [mem_reProdIm, hx₀, hx₁, hy₀, hy₁]
  have hKn : K ∈ nhds (0 : ℂ) := by
    refine Filter.mem_of_superset ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds h0mem) ?_
    exact reProdIm_subset_iff'.mpr (Or.inl ⟨Ioo_subset_Icc_self.trans Icc_subset_uIcc,
      Ioo_subset_Icc_self.trans Icc_subset_uIcc⟩)
  have hψ : ContinuousOn (dslope φ 0) K := (continuousOn_dslope hKn).mpr ⟨Hc, Hd 0 h0mem⟩
  have hzero : rectBd (dslope φ 0) x₀ x₁ y₀ y₁ = 0 := by
    refine rectBd_eq_zero_of_off_countable _ {0} (countable_singleton 0) hψ fun z hz => ?_
    have hz0 : z ≠ 0 := hz.2
    rw [min_eq_left (hx₀.trans hx₁).le, max_eq_right (hx₀.trans hx₁).le, min_eq_left (hy₀.trans hy₁).le,
      max_eq_right (hy₀.trans hy₁).le] at hz
    exact (differentiableAt_dslope_of_ne hz0).mpr (Hd z hz.1)
  have hinv := rectBd_inv hx₀ hx₁ hy₀ hy₁
  have hreIcc : ∀ {a b c : ℝ}, c ∈ [[a, b]] → c ∈ [[a, b]] := fun h => h
  -- the four sides
  have hb : ∫ x : ℝ in x₀..x₁, φ (x + y₀ * I) / (x + y₀ * I) =
      (∫ x : ℝ in x₀..x₁, dslope φ 0 (x + y₀ * I)) + φ 0 * ∫ x : ℝ in x₀..x₁, ((x : ℂ) + y₀ * I)⁻¹ :=
    integral_div_eq_dslope hψ (by fun_prop) (fun t ht => by simp [K, mem_reProdIm, ht, left_mem_uIcc])
      (fun t _ h => hy₀.ne (by simpa using congrArg im h))
  have ht : ∫ x : ℝ in x₀..x₁, φ (x + y₁ * I) / (x + y₁ * I) =
      (∫ x : ℝ in x₀..x₁, dslope φ 0 (x + y₁ * I)) + φ 0 * ∫ x : ℝ in x₀..x₁, ((x : ℂ) + y₁ * I)⁻¹ :=
    integral_div_eq_dslope hψ (by fun_prop) (fun t ht => by simp [K, mem_reProdIm, ht, right_mem_uIcc])
      (fun t _ h => hy₁.ne' (by simpa using congrArg im h))
  have hr : ∫ y : ℝ in y₀..y₁, φ (x₁ + y * I) / (x₁ + y * I) =
      (∫ y : ℝ in y₀..y₁, dslope φ 0 (x₁ + y * I)) + φ 0 * ∫ y : ℝ in y₀..y₁, ((x₁ : ℂ) + y * I)⁻¹ :=
    integral_div_eq_dslope hψ (by fun_prop) (fun t ht => by simp [K, mem_reProdIm, ht, right_mem_uIcc])
      (fun t _ h => hx₁.ne' (by simpa using congrArg re h))
  have hl : ∫ y : ℝ in y₀..y₁, φ (x₀ + y * I) / (x₀ + y * I) =
      (∫ y : ℝ in y₀..y₁, dslope φ 0 (x₀ + y * I)) + φ 0 * ∫ y : ℝ in y₀..y₁, ((x₀ : ℂ) + y * I)⁻¹ :=
    integral_div_eq_dslope hψ (by fun_prop) (fun t ht => by simp [K, mem_reProdIm, ht, left_mem_uIcc])
      (fun t _ h => hx₀.ne (by simpa using congrArg re h))
  simp only [rectBd] at hzero hinv ⊢
  rw [hb, ht, hr, hl]
  linear_combination hzero + φ 0 * hinv

end

end NumberFieldKB.NonVanishing
