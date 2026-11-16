import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Order.Field.Power
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2PadicDefs

/-!
# Milne, *Elliptic Curves*, Chapter II, Lemma 5.9

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8). Definitions in `Ch2PadicDefs.lean`.

Milne's proof works in the chart $y \neq 0$ with coordinates $x' = x/y$, $z' = 1/y$, where the curve is
$z' = x'^3 + ax'z'^2 + bz'^3$ (17) and three points add to $O$ iff they are collinear; the line through
$P_1, P_2$ is $z' = \alpha x' + \beta$ with $\alpha \in p^{2n}\mathbb Z_p$, $\beta \in p^{3n}\mathbb Z_p$, and
$x'_1 + x'_2 + x'_3 = -(2a\alpha\beta + 3b\alpha^2\beta)/(1 + a\alpha^2 + b\alpha^3)$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric inequality for a sum of two terms with a common bound. -/
lemma norm_add_le_of_le {x y : ℚ_[p]} {M : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) : ‖x + y‖ ≤ M :=
  (Padic.nonarchimedean x y).trans (max_le hx hy)

/-- The norms of the integers $2$ and $3$ in $\mathbb Q_p$ are at most $1$. -/
lemma norm_two_le_one : ‖(2 : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) 2

lemma norm_three_le_one : ‖(3 : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) 3

/-- If $y \ne 0$ lies on the curve then $1/y$ satisfies the equation (17) in the chart $(x/y, 1/y)$. -/
lemma chart_eq {a b x y : ℚ_[p]} (hy : y ≠ 0) (e : y ^ 2 = x ^ 3 + a * x + b) :
    1 / y = (x / y) ^ 3 + a * (x / y) * (1 / y) ^ 2 + b * (1 / y) ^ 3 := by
  field_simp
  linear_combination e

/-- Product of norm bounds. -/
lemma norm_mul_le_of_le {x y : ℚ_[p]} {A B : ℝ} (hx : ‖x‖ ≤ A) (hy : ‖y‖ ≤ B) : ‖x * y‖ ≤ A * B := by
  rw [norm_mul]; exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

/-- Chart bounds for two distinct points on the line $y = \ell x + \nu$, in the chart $(x/y, 1/y)$ (here
$t = p^{-n}$): the line has $\|\ell\| \le t^2 \|\nu\|$ and $1 \le t^3 \|\nu\|$. -/
lemma line_bounds_of_ne {a b x₁ y₁ x₂ y₂ ℓ ν : ℚ_[p]} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (e₁ : y₁ ^ 2 = x₁ ^ 3 + a * x₁ + b) (e₂ : y₂ ^ 2 = x₂ ^ 3 + a * x₂ + b)
    (hy₁ : 1 ≤ t ^ 3 * ‖y₁‖) (hy₂ : 1 ≤ t ^ 3 * ‖y₂‖)
    (hu₁ : ‖x₁ / y₁‖ ≤ t) (hu₂ : ‖x₂ / y₂‖ ≤ t)
    (l₁ : y₁ = ℓ * x₁ + ν) (l₂ : y₂ = ℓ * x₂ + ν) (hx : x₁ ≠ x₂) :
    1 ≤ t ^ 3 * ‖ν‖ ∧ ‖ℓ‖ ≤ t ^ 2 * ‖ν‖ := by
  have hy₁0 : y₁ ≠ 0 := by
    rintro rfl
    simp at hy₁; linarith
  have hy₂0 : y₂ ≠ 0 := by
    rintro rfl
    simp at hy₂; linarith
  have hn₁ : 0 < ‖y₁‖ := norm_pos_iff.2 hy₁0
  have hn₂ : 0 < ‖y₂‖ := norm_pos_iff.2 hy₂0
  have t3 : t ^ 3 < 1 := pow_lt_one₀ ht0.le ht1 (by norm_num)
  have t4 : t ^ 4 < 1 := pow_lt_one₀ ht0.le ht1 (by norm_num)
  have t6 : t ^ 6 < 1 := pow_lt_one₀ ht0.le ht1 (by norm_num)
  have t2pos : 0 < t ^ 2 := by positivity
  have t3le : t ^ 3 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
  have t6le : t ^ 6 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
  have hw₁ : ‖1 / y₁‖ ≤ t ^ 3 := by
    rw [norm_div, norm_one, div_le_iff₀ hn₁]; linarith
  have hw₂ : ‖1 / y₂‖ ≤ t ^ 3 := by
    rw [norm_div, norm_one, div_le_iff₀ hn₂]; linarith
  have c₁ := chart_eq (a := a) (b := b) hy₁0 e₁
  have c₂ := chart_eq (a := a) (b := b) hy₂0 e₂
  have r₁ : ν * (1 / y₁) + ℓ * (x₁ / y₁) = 1 := by
    field_simp; linear_combination -l₁
  have r₂ : ν * (1 / y₂) + ℓ * (x₂ / y₂) = 1 := by
    field_simp; linear_combination -l₂
  have xu₁ : x₁ = (x₁ / y₁) * y₁ := by field_simp
  have xu₂ : x₂ = (x₂ / y₂) * y₂ := by field_simp
  generalize hu₁d : x₁ / y₁ = u₁ at *
  generalize hu₂d : x₂ / y₂ = u₂ at *
  generalize hw₁d : 1 / y₁ = w₁ at *
  generalize hw₂d : 1 / y₂ = w₂ at *
  have key : (w₁ - w₂) * (1 - (a * u₂ * (w₁ + w₂) + b * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2))) =
      (u₁ - u₂) * (u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2 + a * w₁ ^ 2) := by
    linear_combination c₁ - c₂
  have hw₁' : ‖w₁‖ ≤ t ^ 3 := hw₁
  have hu₁' : ‖u₁‖ ≤ t := hu₁
  -- norm of the unit factor
  have hr : ‖a * u₂ * (w₁ + w₂) + b * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)‖ < 1 := by
    have h1 : ‖a * u₂ * (w₁ + w₂)‖ ≤ t ^ 4 := by
      have := norm_mul_le_of_le (norm_mul_le_of_le ha hu₂) (norm_add_le_of_le hw₁ hw₂)
      calc _ ≤ 1 * t * t ^ 3 := this
        _ = t ^ 4 := by ring
    have h2 : ‖b * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)‖ ≤ t ^ 6 := by
      have s1 : ‖w₁ ^ 2‖ ≤ t ^ 3 * t ^ 3 := by rw [sq]; exact norm_mul_le_of_le hw₁ hw₁
      have s2 : ‖w₁ * w₂‖ ≤ t ^ 3 * t ^ 3 := norm_mul_le_of_le hw₁ hw₂
      have s3 : ‖w₂ ^ 2‖ ≤ t ^ 3 * t ^ 3 := by rw [sq]; exact norm_mul_le_of_le hw₂ hw₂
      have := norm_mul_le_of_le hb (norm_add_le_of_le (norm_add_le_of_le s1 s2) s3)
      calc _ ≤ 1 * (t ^ 3 * t ^ 3) := this
        _ = t ^ 6 := by ring
    have t64 : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
    exact lt_of_le_of_lt (norm_add_le_of_le h1 (h2.trans t64)) t4
  have hU : ‖1 - (a * u₂ * (w₁ + w₂) + b * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2))‖ = 1 := by
    rw [sub_eq_add_neg]
    have hne : ‖(1 : ℚ_[p])‖ ≠ ‖-(a * u₂ * (w₁ + w₂) + b * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2))‖ := by
      rw [norm_neg, norm_one]; exact hr.ne'
    rw [Padic.add_eq_max_of_ne hne, norm_neg, norm_one]
    exact max_eq_left hr.le
  have hV : ‖u₁ ^ 2 + u₁ * u₂ + u₂ ^ 2 + a * w₁ ^ 2‖ ≤ t ^ 2 := by
    have s1 : ‖u₁ ^ 2‖ ≤ t ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hu₁ 2
    have s2 : ‖u₁ * u₂‖ ≤ t ^ 2 := by rw [sq]; exact norm_mul_le_of_le hu₁ hu₂
    have s3 : ‖u₂ ^ 2‖ ≤ t ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hu₂ 2
    have s4 : ‖a * w₁ ^ 2‖ ≤ t ^ 2 := by
      have := norm_mul_le_of_le ha (show ‖w₁ ^ 2‖ ≤ t ^ 3 * t ^ 3 by
        rw [sq]; exact norm_mul_le_of_le hw₁ hw₁)
      calc _ ≤ 1 * (t ^ 3 * t ^ 3) := this
        _ = t ^ 6 := by ring
        _ ≤ t ^ 2 := t6le
    exact norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le s1 s2) s3) s4
  have hdiff : ‖w₁ - w₂‖ ≤ t ^ 2 * ‖u₁ - u₂‖ := by
    have := congrArg norm key
    rw [norm_mul, norm_mul, hU, mul_one] at this
    rw [this, mul_comm (t ^ 2)]
    exact mul_le_mul_of_nonneg_left hV (norm_nonneg (u₁ - u₂))
  have hU0 : (1 - (a * u₂ * (w₁ + w₂) + b * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2))) ≠ 0 := by
    intro h; rw [h, norm_zero] at hU; exact zero_ne_one hU
  have hune : u₁ ≠ u₂ := by
    intro h
    rw [h, sub_self, zero_mul] at key
    have hw : w₁ - w₂ = 0 := by
      rcases mul_eq_zero.1 key with h' | h'
      · exact h'
      · exact absurd h' hU0
    have hw' : w₁ = w₂ := sub_eq_zero.1 hw
    have hyy : y₁ = y₂ := by
      rw [← hw₁d, ← hw₂d] at hw'
      simp only [one_div] at hw'
      exact inv_injective hw'
    have hh := xu₁
    rw [h, hyy] at hh
    exact hx (hh.trans xu₂.symm)
  have hpos : 0 < ‖u₁ - u₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hune)
  have hlin : ℓ * (u₁ - u₂) = -(ν * (w₁ - w₂)) := by linear_combination r₁ - r₂
  have hℓ : ‖ℓ‖ ≤ t ^ 2 * ‖ν‖ := by
    have h1 := congrArg norm hlin
    rw [norm_mul, norm_neg, norm_mul] at h1
    have h2 : ‖ℓ‖ * ‖u₁ - u₂‖ ≤ (t ^ 2 * ‖ν‖) * ‖u₁ - u₂‖ := by
      rw [h1]
      calc ‖ν‖ * ‖w₁ - w₂‖ ≤ ‖ν‖ * (t ^ 2 * ‖u₁ - u₂‖) := mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
        _ = _ := by ring
    exact le_of_mul_le_mul_right h2 hpos
  refine ⟨?_, hℓ⟩
  by_contra hcon
  push Not at hcon
  have hlu : ‖ℓ * u₁‖ < 1 := by
    have := norm_mul_le_of_le hℓ hu₁
    calc _ ≤ t ^ 2 * ‖ν‖ * t := this
      _ = t ^ 3 * ‖ν‖ := by ring
      _ < 1 := hcon
  have hnw : ν * w₁ = 1 + -(ℓ * u₁) := by linear_combination r₁
  have h1 : ‖ν * w₁‖ = 1 := by
    have hne : ‖(1 : ℚ_[p])‖ ≠ ‖-(ℓ * u₁)‖ := by
      rw [norm_neg, norm_one]; exact hlu.ne'
    rw [hnw, Padic.add_eq_max_of_ne hne, norm_neg, norm_one]
    exact max_eq_left hlu.le
  have h2 : ‖ν * w₁‖ ≤ ‖ν‖ * t ^ 3 := by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hw₁ (norm_nonneg _)
  linarith

/-- Bounds for the tangent line $y = \ell x + \nu$ at a point of $E^n$ (here $t = p^{-n}$), where
$2\ell y = 3x^2 + a$: again $\|\ell\| \le t^2\|\nu\|$ and $1 \le t^3\|\nu\|$. -/
lemma line_bounds_tangent {a b x y ℓ ν : ℚ_[p]} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (e : y ^ 2 = x ^ 3 + a * x + b)
    (hx1 : 1 < ‖x‖) (hx2 : 1 ≤ t ^ 2 * ‖x‖) (hyx : ‖y‖ ^ 2 = ‖x‖ ^ 3) (hy : 1 ≤ t ^ 3 * ‖y‖)
    (hℓ : ℓ * (2 * y) = 3 * x ^ 2 + a) (l : y = ℓ * x + ν) :
    1 ≤ t ^ 3 * ‖ν‖ ∧ ‖ℓ‖ ≤ t ^ 2 * ‖ν‖ := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy; linarith
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have c0 : 0 < ‖(2 : ℚ_[p])‖ := norm_pos_iff.2 two_ne_zero
  have c1 : ‖(2 : ℚ_[p])‖ ≤ 1 := norm_two_le_one
  have hxx : ‖x‖ < ‖x‖ ^ 3 := by
    calc ‖x‖ = ‖x‖ ^ 1 := (pow_one _).symm
      _ < ‖x‖ ^ 3 := pow_lt_pow_right₀ hx1 (by norm_num)
  have h2yν : 2 * y * ν = -(x ^ 3) + (a * x + 2 * b) := by
    linear_combination (-2 * y) * l + 2 * e - x * hℓ
  have hsmall : ‖a * x + 2 * b‖ < ‖x ^ 3‖ := by
    rw [norm_pow]
    refine lt_of_le_of_lt (Padic.nonarchimedean _ _ |>.trans (max_le ?_ ?_)) hxx
    · rw [norm_mul]
      calc ‖a‖ * ‖x‖ ≤ 1 * ‖x‖ := by gcongr
        _ = ‖x‖ := one_mul _
    · rw [norm_mul]
      calc ‖(2 : ℚ_[p])‖ * ‖b‖ ≤ 1 * 1 := by gcongr
        _ ≤ ‖x‖ := by linarith
  have hN : ‖2 * y * ν‖ = ‖x‖ ^ 3 := by
    rw [h2yν]
    have hne : ‖-(x ^ 3)‖ ≠ ‖a * x + 2 * b‖ := by
      rw [norm_neg]; exact hsmall.ne'
    rw [Padic.add_eq_max_of_ne hne, norm_neg, max_eq_left hsmall.le, norm_pow]
  have hcν : ‖(2 : ℚ_[p])‖ * ‖ν‖ = ‖y‖ := by
    rw [norm_mul, norm_mul] at hN
    have : ‖y‖ * (‖(2 : ℚ_[p])‖ * ‖ν‖) = ‖y‖ * ‖y‖ := by
      nlinarith [hN, hyx]
    exact mul_left_cancel₀ hyn.ne' this
  have hyν : ‖y‖ ≤ ‖ν‖ := by nlinarith [norm_nonneg ν]
  refine ⟨?_, ?_⟩
  · calc (1 : ℝ) ≤ t ^ 3 * ‖y‖ := hy
      _ ≤ t ^ 3 * ‖ν‖ := by gcongr
  · have hnum : ‖ℓ‖ * (‖(2 : ℚ_[p])‖ * ‖y‖) ≤ ‖x‖ ^ 2 := by
      have h1 : ‖ℓ * (2 * y)‖ ≤ ‖x‖ ^ 2 := by
        rw [hℓ]
        refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
        · rw [norm_mul, norm_pow]
          calc ‖(3 : ℚ_[p])‖ * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 := by
                gcongr; exact norm_three_le_one
            _ = ‖x‖ ^ 2 := one_mul _
        · calc ‖a‖ ≤ 1 := ha
            _ ≤ ‖x‖ ^ 2 := by nlinarith
      rw [norm_mul, norm_mul] at h1
      linarith
    have hc : 0 < ‖(2 : ℚ_[p])‖ * ‖y‖ := mul_pos c0 hyn
    refine le_of_mul_le_mul_right ?_ hc
    calc ‖ℓ‖ * (‖(2 : ℚ_[p])‖ * ‖y‖) ≤ ‖x‖ ^ 2 := hnum
      _ = 1 * ‖x‖ ^ 2 := (one_mul _).symm
      _ ≤ (t ^ 2 * ‖x‖) * ‖x‖ ^ 2 := by gcongr
      _ = t ^ 2 * ‖x‖ ^ 3 := by ring
      _ = t ^ 2 * ‖y‖ ^ 2 := by rw [hyx]
      _ = t ^ 2 * ‖ν‖ * (‖(2 : ℚ_[p])‖ * ‖y‖) := by
          linear_combination (t ^ 2 * ‖y‖) * hcν.symm

/-- Core estimate (Milne's computation with the cubic in the chart $(x/y, 1/y)$): three points
$(x_i, \ell x_i + \nu)$ of the curve whose abscissae have the elementary symmetric functions of the roots of
$(\ell x + \nu)^2 = x^3 + ax + b$, with $\|\ell\| \le t^2\|\nu\|$ and $1 \le t^3\|\nu\|$, satisfy
$\|x_3\| > 1$ and $\|\sum x_i/y_i\| \le t^5$ (here $t = p^{-n}$). -/
lemma line_core {a b x₁ x₂ x₃ ℓ ν : ℚ_[p]} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hν : 1 ≤ t ^ 3 * ‖ν‖) (hℓ : ‖ℓ‖ ≤ t ^ 2 * ‖ν‖)
    (hy₁ : ℓ * x₁ + ν ≠ 0) (hy₂ : ℓ * x₂ + ν ≠ 0)
    (hs1 : x₁ + x₂ + x₃ = ℓ ^ 2) (hs2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = a - 2 * ℓ * ν)
    (hs3 : x₁ * x₂ * x₃ = ν ^ 2 - b) :
    1 < ‖x₃‖ ∧ ℓ * x₃ + ν ≠ 0 ∧
      ‖x₁ / (ℓ * x₁ + ν) + x₂ / (ℓ * x₂ + ν) + x₃ / (ℓ * x₃ + ν)‖ ≤ t ^ 5 := by
  have t2 : t ^ 2 < 1 := pow_lt_one₀ ht0.le ht1 (by norm_num)
  have t3 : t ^ 3 < 1 := pow_lt_one₀ ht0.le ht1 (by norm_num)
  have t4 : t ^ 4 < 1 := pow_lt_one₀ ht0.le ht1 (by norm_num)
  have t3pos : 0 < t ^ 3 := by positivity
  have t2pos : 0 < t ^ 2 := by positivity
  have hνpos : 0 < ‖ν‖ := by
    rcases (norm_nonneg ν).eq_or_lt with h | h
    · rw [← h] at hν; simp at hν; linarith
    · exact h
  have hν1 : 1 < ‖ν‖ := by nlinarith
  have hℓν : ‖ℓ‖ < ‖ν‖ := by nlinarith
  have e3 : (ℓ * x₃ + ν) ^ 2 = x₃ ^ 3 + a * x₃ + b := by
    linear_combination (-(x₃ ^ 2)) * hs1 + x₃ * hs2 - hs3
  have hx3 : 1 < ‖x₃‖ := by
    by_contra hcon
    push Not at hcon
    have h1 := norm_y_le_one ha hb hcon e3
    have h2 : ‖ℓ * x₃‖ < ‖ν‖ := by
      calc ‖ℓ * x₃‖ ≤ ‖ℓ‖ * 1 := by rw [norm_mul]; gcongr
        _ < ‖ν‖ := by linarith
    have h3 : ‖ℓ * x₃ + ν‖ = ‖ν‖ := by
      rw [Padic.add_eq_max_of_ne h2.ne]
      exact max_eq_right h2.le
    linarith
  have hy₃ : ℓ * x₃ + ν ≠ 0 := by
    intro h0
    have := norm_sq_eq_of_one_lt ha hb hx3 e3
    rw [h0, norm_zero] at this
    have : 0 < ‖x₃‖ ^ 3 := by positivity
    simp_all
  refine ⟨hx3, hy₃, ?_⟩
  set K := ‖ν‖ with hK
  -- the denominator
  have hD : (ℓ * x₁ + ν) * (ℓ * x₂ + ν) * (ℓ * x₃ + ν) = ν ^ 3 + (a * ℓ ^ 2 * ν - b * ℓ ^ 3) := by
    linear_combination ℓ ^ 3 * hs3 + ℓ ^ 2 * ν * hs2 + ℓ * ν ^ 2 * hs1
  have hN : x₁ * ((ℓ * x₂ + ν) * (ℓ * x₃ + ν)) + x₂ * ((ℓ * x₁ + ν) * (ℓ * x₃ + ν)) +
      x₃ * ((ℓ * x₁ + ν) * (ℓ * x₂ + ν)) = ℓ * (2 * a * ν - 3 * b * ℓ) := by
    linear_combination (3 * ℓ ^ 2) * hs3 + (2 * ℓ * ν) * hs2 + ν ^ 2 * hs1
  have hsmall : ‖a * ℓ ^ 2 * ν - b * ℓ ^ 3‖ ≤ t ^ 4 * K ^ 3 := by
    have hℓ' : ‖ℓ‖ ≤ t ^ 2 * K := hℓ
    have s1 : ‖a * ℓ ^ 2 * ν‖ ≤ t ^ 4 * K ^ 3 := by
      have := norm_mul_le_of_le (norm_mul_le_of_le ha
        (show ‖ℓ ^ 2‖ ≤ (t ^ 2 * K) * (t ^ 2 * K) by rw [sq]; exact norm_mul_le_of_le hℓ' hℓ'))
        (le_refl ‖ν‖)
      calc _ ≤ 1 * ((t ^ 2 * K) * (t ^ 2 * K)) * K := this
        _ = t ^ 4 * K ^ 3 := by ring
    have s2 : ‖b * ℓ ^ 3‖ ≤ t ^ 4 * K ^ 3 := by
      have := norm_mul_le_of_le hb
        (show ‖ℓ ^ 3‖ ≤ (t ^ 2 * K) * (t ^ 2 * K) * (t ^ 2 * K) by
          rw [pow_succ, pow_two]; exact norm_mul_le_of_le (norm_mul_le_of_le hℓ' hℓ') hℓ')
      calc _ ≤ 1 * ((t ^ 2 * K) * (t ^ 2 * K) * (t ^ 2 * K)) := this
        _ = t ^ 6 * K ^ 3 := by ring
        _ ≤ t ^ 4 * K ^ 3 := by
          have : t ^ 6 ≤ t ^ 4 := pow_le_pow_of_le_one ht0.le ht1.le (by norm_num)
          gcongr
    rw [sub_eq_add_neg]
    refine norm_add_le_of_le s1 ?_
    rw [norm_neg]; exact s2
  have hK3 : 0 < K ^ 3 := by positivity
  have hDn : ‖ν ^ 3 + (a * ℓ ^ 2 * ν - b * ℓ ^ 3)‖ = K ^ 3 := by
    have hne : ‖ν ^ 3‖ ≠ ‖a * ℓ ^ 2 * ν - b * ℓ ^ 3‖ := by
      rw [norm_pow]; nlinarith
    rw [Padic.add_eq_max_of_ne hne, norm_pow]
    exact max_eq_left (by nlinarith)
  have hD0 : ν ^ 3 + (a * ℓ ^ 2 * ν - b * ℓ ^ 3) ≠ 0 := by
    intro h; rw [h, norm_zero] at hDn; linarith
  have hNn : ‖ℓ * (2 * a * ν - 3 * b * ℓ)‖ ≤ t ^ 2 * K ^ 2 := by
    have h1 : ‖2 * a * ν - 3 * b * ℓ‖ ≤ K := by
      rw [sub_eq_add_neg]
      refine norm_add_le_of_le ?_ ?_
      · have := norm_mul_le_of_le (norm_mul_le_of_le norm_two_le_one ha) (le_refl ‖ν‖)
        calc _ ≤ 1 * 1 * K := this
          _ = K := by ring
      · rw [norm_neg]
        have := norm_mul_le_of_le (norm_mul_le_of_le norm_three_le_one hb) (le_refl ‖ℓ‖)
        calc _ ≤ 1 * 1 * ‖ℓ‖ := this
          _ ≤ K := by linarith
    have := norm_mul_le_of_le hℓ h1
    calc _ ≤ (t ^ 2 * K) * K := this
      _ = t ^ 2 * K ^ 2 := by ring
  -- the sum
  set s := x₁ / (ℓ * x₁ + ν) + x₂ / (ℓ * x₂ + ν) + x₃ / (ℓ * x₃ + ν) with hs
  have hsD : s * (ν ^ 3 + (a * ℓ ^ 2 * ν - b * ℓ ^ 3)) = ℓ * (2 * a * ν - 3 * b * ℓ) := by
    have hy₁' : x₁ * ℓ + ν ≠ 0 := by rwa [mul_comm]
    have hy₂' : x₂ * ℓ + ν ≠ 0 := by rwa [mul_comm]
    have hy₃' : x₃ * ℓ + ν ≠ 0 := by rwa [mul_comm]
    rw [← hD, ← hN, hs]
    field_simp
  have h1 : ‖s‖ * K ^ 3 ≤ t ^ 2 * K ^ 2 := by
    have := congrArg norm hsD
    rw [norm_mul, hDn] at this
    rw [this]; exact hNn
  have h2 : ‖s‖ * K ≤ t ^ 2 := by
    have : (‖s‖ * K) * K ^ 2 ≤ t ^ 2 * K ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  calc ‖s‖ ≤ ‖s‖ * (t ^ 3 * K) := by nlinarith [norm_nonneg s]
    _ = t ^ 3 * (‖s‖ * K) := by ring
    _ ≤ t ^ 3 * t ^ 2 := by gcongr
    _ = t ^ 5 := by ring

lemma one_lt_natCast_p : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt

omit [Fact p.Prime] in
/-- $p^{-n}$ as an inverse of a natural power. -/
lemma zpow_neg_natCast_eq (n : ℕ) : (p : ℝ) ^ (-(n : ℤ)) = (((p : ℝ) ^ n)⁻¹) := by
  rw [zpow_neg, zpow_natCast]

omit [Fact p.Prime] in
/-- $(p^n)^{-5}$ as a power with negative integer exponent. -/
lemma inv_pow_five_eq (n : ℕ) : (((p : ℝ) ^ n)⁻¹) ^ 5 = (p : ℝ) ^ (-(5 * n : ℤ)) := by
  rw [inv_pow, ← pow_mul, show (-(5 * n : ℤ)) = -((5 * n : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, mul_comm]

lemma inv_pow_pos (n : ℕ) : 0 < ((p : ℝ) ^ n)⁻¹ := by
  have := one_lt_natCast_p (p := p)
  positivity

lemma inv_pow_lt_one {n : ℕ} (hn : 1 ≤ n) : ((p : ℝ) ^ n)⁻¹ < 1 := by
  have hp := one_lt_natCast_p (p := p)
  have : 1 < (p : ℝ) ^ n := one_lt_pow₀ hp (by omega)
  exact inv_lt_one_of_one_lt₀ this

/-- Data of a point $(x, y)$ of $E^n(\mathbb Q_p)$, $n \ge 1$, with $t = p^{-n}$. -/
lemma mem_En_data {a b : ℤ_[p]} {n : ℕ} {x y : ℚ_[p]}
    {h : (curveQp a b).toAffine.Nonsingular x y} (hP : Affine.Point.some x y h ∈ En a b n) :
    1 < ‖x‖ ∧ 1 ≤ (((p : ℝ) ^ n)⁻¹) ^ 2 * ‖x‖ ∧ 1 ≤ (((p : ℝ) ^ n)⁻¹) ^ 3 * ‖y‖ ∧
      ‖y‖ ^ 2 = ‖x‖ ^ 3 ∧ ‖x / y‖ ≤ ((p : ℝ) ^ n)⁻¹ := by
  have hp := one_lt_natCast_p (p := p)
  obtain ⟨hE1, hle⟩ := hP
  rcases (mem_E1_iff _).1 hE1 with h0 | ⟨x', y', h', he, hx⟩
  · exact absurd h0 (Affine.Point.some_ne_zero h)
  · simp only [Affine.Point.some.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have e := shortCurve_equation h.1
    obtain ⟨m, hm, nx, ny⟩ := exists_norm_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx e
    have hxy : ‖x / y‖ = (p : ℝ) ^ (-(m : ℤ)) := by
      simp only [norm_div, nx, ny]
      rw [← zpow_sub₀ (by positivity)]
      congr 1; ring
    simp only [xPrime] at hle
    have hle' := hle
    rw [hxy] at hle
    have hnm : n ≤ m := by
      have := (zpow_le_zpow_iff_right₀ hp).1 hle
      omega
    have hA : 0 < (p : ℝ) ^ n := by positivity
    have hAB : (p : ℝ) ^ n ≤ (p : ℝ) ^ m := pow_le_pow_right₀ hp.le hnm
    have hr : 1 ≤ (((p : ℝ) ^ n)⁻¹) * (p : ℝ) ^ m := by
      rw [← div_eq_inv_mul, le_div_iff₀ hA]; linarith
    have nx' : ‖x‖ = ((p : ℝ) ^ m) ^ 2 := by
      rw [nx, show (2 * m : ℤ) = ((2 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']
    have ny' : ‖y‖ = ((p : ℝ) ^ m) ^ 3 := by
      rw [ny, show (3 * m : ℤ) = ((3 * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul']
    refine ⟨hx, ?_, ?_, norm_sq_eq_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx e, ?_⟩
    · rw [nx', ← mul_pow]; exact one_le_pow₀ hr
    · rw [ny', ← mul_pow]; exact one_le_pow₀ hr
    · rw [← zpow_neg_natCast_eq]; exact hle'

/-- Affine case of Lemma 5.9. -/
lemma lemma_5_9_affine {a b : ℤ_[p]} {n : ℕ} (hn : 1 ≤ n) {x₁ y₁ x₂ y₂ x₃ y₃ : ℚ_[p]}
    {h₁ : (curveQp a b).toAffine.Nonsingular x₁ y₁} {h₂ : (curveQp a b).toAffine.Nonsingular x₂ y₂}
    {h₃ : (curveQp a b).toAffine.Nonsingular x₃ y₃}
    (hsum : Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ + Affine.Point.some x₃ y₃ h₃ = 0)
    (hP₁ : Affine.Point.some x₁ y₁ h₁ ∈ En a b n) (hP₂ : Affine.Point.some x₂ y₂ h₂ ∈ En a b n) :
    Affine.Point.some x₃ y₃ h₃ ∈ En a b n ∧
      ‖x₁ / y₁ + x₂ / y₂ + x₃ / y₃‖ ≤ (p : ℝ) ^ (-(5 * n : ℤ)) := by
  obtain ⟨hx₁, hx₁', hy₁, hyx₁, hu₁⟩ := mem_En_data hP₁
  obtain ⟨hx₂, hx₂', hy₂, hyx₂, hu₂⟩ := mem_En_data hP₂
  have e₁ := shortCurve_equation h₁.1
  have e₂ := shortCurve_equation h₂.1
  have ht0 := inv_pow_pos (p := p) n
  have ht1 := inv_pow_lt_one (p := p) hn
  set t := ((p : ℝ) ^ n)⁻¹ with htd
  have hy₁0 : y₁ ≠ 0 := by
    rintro rfl; simp at hy₁; linarith
  have hy₂0 : y₂ ≠ 0 := by
    rintro rfl; simp at hy₂; linarith
  have hneg : Affine.Point.some x₁ y₁ h₁ + Affine.Point.some x₂ y₂ h₂ = -Affine.Point.some x₃ y₃ h₃ :=
    eq_neg_of_add_eq_zero_left hsum
  rw [Affine.Point.neg_some] at hneg
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curveQp a b).toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2] at hneg
    exact absurd hneg.symm (Affine.Point.some_ne_zero _)
  · rw [Affine.Point.add_some hxy, Affine.Point.some.injEq] at hneg
    obtain ⟨hX, hY⟩ := hneg
    have hslope₁ : x₁ ≠ x₂ → (curveQp a b).toAffine.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
      intro hx
      rw [Affine.slope_of_X_ne hx]
      exact div_mul_cancel₀ _ (sub_ne_zero.2 hx)
    have hslope₂ : x₁ = x₂ → y₂ = y₁ →
        (curveQp a b).toAffine.slope x₁ x₂ y₁ y₂ * (2 * y₁) = 3 * x₁ ^ 2 + (a : ℚ_[p]) := by
      intro hx hy
      obtain rfl := hx
      rw [hy]
      have hne : y₁ ≠ (curveQp a b).toAffine.negY x₁ y₁ := fun h' => hxy ⟨rfl, hy ▸ h'⟩
      rw [Affine.slope_of_Y_ne rfl hne]
      simp only [Affine.negY, shortCurve_a₁, shortCurve_a₂, shortCurve_a₃, shortCurve_a₄]
      have h2y : y₁ - (-y₁ - 0 * x₁ - 0) = 2 * y₁ := by ring
      rw [h2y]
      simp only [mul_zero, zero_mul, add_zero, sub_zero]
      exact div_mul_cancel₀ _ (mul_ne_zero two_ne_zero hy₁0)
    have hyeq : x₁ = x₂ → y₂ = y₁ := by
      intro hx
      subst hx
      have hne : y₁ ≠ -y₂ := by
        intro h'; apply hxy; refine ⟨rfl, ?_⟩
        simp only [Affine.negY, shortCurve_a₁, shortCurve_a₃]; linear_combination h'
      have : (y₂ - y₁) * (y₂ + y₁) = 0 := by linear_combination e₂ - e₁
      rcases mul_eq_zero.1 this with h' | h'
      · linear_combination h'
      · exact absurd (by linear_combination h') hne
    generalize (curveQp a b).toAffine.slope x₁ x₂ y₁ y₂ = ℓ at hX hY hslope₁ hslope₂
    obtain ⟨ν, l₁⟩ : ∃ ν, y₁ = ℓ * x₁ + ν := ⟨y₁ - ℓ * x₁, by ring⟩
    have hx3 : x₃ = ℓ ^ 2 - x₁ - x₂ := by
      simp only [Affine.addX, shortCurve_a₁, shortCurve_a₂] at hX
      linear_combination -hX
    have hy3 : y₃ = ℓ * x₃ + ν := by
      simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, shortCurve_a₁, shortCurve_a₂,
        shortCurve_a₃] at hY
      linear_combination hY - ℓ * hx3 + l₁
    have l₂ : y₂ = ℓ * x₂ + ν := by
      by_cases hx : x₁ = x₂
      · have hy := hyeq hx
        rw [hy, ← hx]; exact l₁
      · linear_combination hslope₁ hx + l₁
    have ha := norm_coe_le_one a
    have hb := norm_coe_le_one b
    have e₁' : (ℓ * x₁ + ν) ^ 2 = x₁ ^ 3 + (a : ℚ_[p]) * x₁ + b := by rw [← l₁]; exact e₁
    have e₂' : (ℓ * x₂ + ν) ^ 2 = x₂ ^ 3 + (a : ℚ_[p]) * x₂ + b := by rw [← l₂]; exact e₂
    have hbounds : 1 ≤ t ^ 3 * ‖ν‖ ∧ ‖ℓ‖ ≤ t ^ 2 * ‖ν‖ := by
      by_cases hx : x₁ = x₂
      · have hy := hyeq hx
        exact line_bounds_tangent ht0 ht1 ha hb e₁ hx₁ hx₁' hyx₁ hy₁ (hslope₂ hx hy) l₁
      · exact line_bounds_of_ne ht0 ht1 ha hb e₁ e₂ hy₁ hy₂ hu₁ hu₂ l₁ l₂ hx
    have hD : ℓ ^ 2 * (x₁ + x₂) + 2 * ℓ * ν = x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a : ℚ_[p]) := by
      by_cases hx : x₁ = x₂
      · have hy := hyeq hx
        have := hslope₂ hx hy
        subst hx
        linear_combination this - 2 * ℓ * l₁
      · have h0 : (x₁ - x₂) * (ℓ ^ 2 * (x₁ + x₂) + 2 * ℓ * ν -
            (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (a : ℚ_[p]))) = 0 := by linear_combination e₁' - e₂'
        rcases mul_eq_zero.1 h0 with h | h
        · exact absurd (sub_eq_zero.1 h) hx
        · linear_combination h
    have hs1 : x₁ + x₂ + x₃ = ℓ ^ 2 := by linear_combination hx3
    have hs2 : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = (a : ℚ_[p]) - 2 * ℓ * ν := by
      rw [hx3]; linear_combination hD
    have hs3 : x₁ * x₂ * x₃ = ν ^ 2 - b := by
      linear_combination (-1) * e₁' - x₁ ^ 2 * hs1 + x₁ * hs2
    have hy₁' : ℓ * x₁ + ν ≠ 0 := l₁ ▸ hy₁0
    have hy₂' : ℓ * x₂ + ν ≠ 0 := l₂ ▸ hy₂0
    obtain ⟨hx3', hy3', hs⟩ := line_core ht0 ht1 ha hb hbounds.1 hbounds.2 hy₁' hy₂' hs1 hs2 hs3
    rw [← l₁, ← l₂, ← hy3] at hs
    have t5le : t ^ 5 ≤ t := pow_le_of_le_one ht0.le ht1.le (by norm_num)
    refine ⟨⟨(mem_E1_iff _).2 (Or.inr ⟨x₃, y₃, h₃, rfl, hx3'⟩), ?_⟩, ?_⟩
    · simp only [xPrime]
      rw [zpow_neg_natCast_eq]
      have : x₃ / y₃ = (x₁ / y₁ + x₂ / y₂ + x₃ / y₃) + (-(x₁ / y₁)) + (-(x₂ / y₂)) := by ring
      rw [this]
      refine norm_add_le_of_le (norm_add_le_of_le (hs.trans t5le) ?_) ?_
      · rw [norm_neg]; exact hu₁
      · rw [norm_neg]; exact hu₂
    · rw [← inv_pow_five_eq]; exact hs

/-- $x'(O) = 0$. -/
lemma xPrime_zero (a b : ℤ_[p]) : xPrime (0 : (curveQp a b).toAffine.Point) = 0 := rfl

/-- $O \in E^n(\mathbb Q_p)$. -/
lemma zero_mem_En (a b : ℤ_[p]) (n : ℕ) : (0 : (curveQp a b).toAffine.Point) ∈ En a b n := by
  refine ⟨(mem_E1_iff _).2 (Or.inl rfl), ?_⟩
  have hp := one_lt_natCast_p (p := p)
  have : xPrime (0 : (curveQp a b).toAffine.Point) = 0 := rfl
  rw [this, norm_zero]; positivity

/-- $x'(-P) = -x'(P)$. -/
lemma xPrime_neg {a b : ℤ_[p]} (P : (curveQp a b).toAffine.Point) : xPrime (-P) = -xPrime P := by
  cases P with
  | zero =>
    show xPrime (-(0 : (curveQp a b).toAffine.Point)) = -xPrime (0 : (curveQp a b).toAffine.Point)
    rw [Affine.Point.neg_zero, xPrime_zero, neg_zero]
  | some x y h =>
    rw [Affine.Point.neg_some]
    simp [xPrime, Affine.negY, div_neg]

/-- $E^n(\mathbb Q_p)$ is closed under negation. -/
lemma neg_mem_En {a b : ℤ_[p]} {n : ℕ} {P : (curveQp a b).toAffine.Point} (hP : P ∈ En a b n) :
    -P ∈ En a b n := by
  refine ⟨?_, ?_⟩
  · rcases (mem_E1_iff _).1 hP.1 with h0 | ⟨x, y, h, rfl, hx⟩
    · rw [h0, Affine.Point.neg_zero]; exact (mem_E1_iff _).2 (Or.inl rfl)
    · rw [Affine.Point.neg_some]; exact (mem_E1_iff _).2 (Or.inr ⟨x, _, _, rfl, hx⟩)
  · rw [xPrime_neg, norm_neg]; exact hP.2

/-- **Lemma 5.9** (pdf p. 75). Let $P_1 + P_2 + P_3 = O$ in $E(\mathbb Q_p)$, $n \ge 1$. If $P_1, P_2 \in
E^n(\mathbb Q_p)$ then $P_3 \in E^n(\mathbb Q_p)$ and $x'(P_1) + x'(P_2) + x'(P_3) \in p^{5n}\mathbb Z_p$. -/
@[kb "milne2006ec" "Ch. II, Lemma 5.9, pdf p. 75"]
theorem lemma_5_9 {a b : ℤ_[p]} {n : ℕ} (hn : 1 ≤ n) {P₁ P₂ P₃ : (curveQp a b).toAffine.Point}
    (hsum : P₁ + P₂ + P₃ = 0) (h₁ : P₁ ∈ En a b n) (h₂ : P₂ ∈ En a b n) :
    P₃ ∈ En a b n ∧ ‖xPrime P₁ + xPrime P₂ + xPrime P₃‖ ≤ (p : ℝ) ^ (-(5 * n : ℤ)) := by
  have hp := one_lt_natCast_p (p := p)
  have hnn : 0 ≤ (p : ℝ) ^ (-(5 * n : ℤ)) := by positivity
  have x0 := xPrime_zero a b
  have z : (Affine.Point.zero : (curveQp a b).toAffine.Point) = 0 := rfl
  cases P₁ with
  | zero =>
    simp only [z] at hsum h₁ ⊢
    have h3 : P₃ = -P₂ := by
      rw [zero_add] at hsum; exact eq_neg_of_add_eq_zero_right hsum
    subst h3
    refine ⟨neg_mem_En h₂, ?_⟩
    rw [xPrime_neg, x0]; simpa using hnn
  | some x₁ y₁ h₁' =>
    cases P₂ with
    | zero =>
      simp only [z] at hsum h₂ ⊢
      have h3 : P₃ = -(Affine.Point.some x₁ y₁ h₁') := by
        rw [add_zero] at hsum; exact eq_neg_of_add_eq_zero_right hsum
      subst h3
      refine ⟨neg_mem_En h₁, ?_⟩
      rw [xPrime_neg, x0]; simpa using hnn
    | some x₂ y₂ h₂' =>
      cases P₃ with
      | zero =>
        simp only [z] at hsum ⊢
        have h3 : Affine.Point.some x₂ y₂ h₂' = -(Affine.Point.some x₁ y₁ h₁') := by
          rw [add_zero] at hsum; exact eq_neg_of_add_eq_zero_right hsum
        refine ⟨zero_mem_En a b n, ?_⟩
        rw [h3, xPrime_neg, x0]; simpa using hnn
      | some x₃ y₃ h₃' =>
        obtain ⟨hm, hb⟩ := lemma_5_9_affine hn hsum h₁ h₂
        exact ⟨hm, by simpa only [xPrime] using hb⟩

end NumberFieldKB.MilneEC.II
