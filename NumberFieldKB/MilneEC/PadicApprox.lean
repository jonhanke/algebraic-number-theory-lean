import NumberFieldKB.MilneEC.LocalPointsAlg
import NumberFieldKB.MilneEC.Ch2Short
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Integrality
import Mathlib.NumberTheory.Padics.Hensel

/-!
# Algebraic points are dense in $E(\mathbb Q_p)$

For $E : y^2 = x^3 + ax + b$ over $\mathbb Q$ and a point $R \in E(\mathbb Q_p)$, there are algebraic points $T$
with $R - T = O$ or $\|x(R - T)\|$ as large as wanted (`exists_isAlgPoint_sub_large_padic`). This is the $p$-adic
analogue of `RealApprox.exists_isAlgPoint_sub_large`:

* if $x(R)$ is algebraic over $\mathbb Q$, so is $y(R)$, and $T = R$;
* otherwise $y_0 = y(R) \ne 0$; take $q \in \mathbb Q$ close to $x_0 = x(R)$ (`Padic.rat_dense`), and
  $y_q = y_0 z$ with $z^2 = f(q)/f(x_0)$, $f(X) = X^3 + aX + b$, $\|z - 1\| < \|2\|$: Hensel's lemma for $X^2 - (1 + u)$
  at $1$, $\|u\| < \|4\|$. Then $T = (q, y_q)$ is algebraic, $\|y_0 + y_q\| = \|2y_0\|$, and
  $x(R - T) = \lambda^2 - x_0 - q$ with $\lambda = (y_0 + y_q)/(x_0 - q)$ is large when $q$ is close to $x_0$.
-/

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped Classical

namespace NumberFieldKB.MilneEC

open II (shortCurve)

variable {p : ℕ} [Fact p.Prime]

/-- The Weierstrass equation of the base change of $E(a,b)$ to $\mathbb Q_p$ is $y^2 = x^3 + ax + b$. -/
theorem equation_shortCurve_iff (a b : ℚ) (x y : ℚ_[p]) :
    ((shortCurve a b).toAffine⁄ℚ_[p]).Equation x y ↔ y ^ 2 = x ^ 3 + (a : ℚ_[p]) * x + b := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, II.shortCurve,
    map_zero, eq_ratCast]
  constructor <;> intro h <;> linear_combination h

/-- Hensel square root: if $\|u\| < \|4\|$ then $1 + u$ is a square $z^2$ with $\|z - 1\| < \|2\|$. -/
theorem exists_sqrt_one_add (u : ℚ_[p]) (hu : ‖u‖ < ‖(4 : ℚ_[p])‖) :
    ∃ z : ℚ_[p], z ^ 2 = 1 + u ∧ ‖z - 1‖ < ‖(2 : ℚ_[p])‖ := by
  have h4 : ‖(4 : ℚ_[p])‖ ≤ 1 := by
    have : ((4 : ℕ) : ℚ_[p]) = 4 := by norm_num
    rw [← this]; exact IsUltrametricDist.norm_natCast_le_one _ 4
  have hw : ‖1 + u‖ ≤ 1 := by
    have h1 : ‖u‖ < 1 := hu.trans_le h4
    calc ‖1 + u‖ ≤ max ‖(1 : ℚ_[p])‖ ‖u‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := by simp [h1.le]
  let w : ℤ_[p] := ⟨1 + u, hw⟩
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.C w
  have hF1 : ‖F.aeval (1 : ℤ_[p])‖ = ‖u‖ := by
    have : F.aeval (1 : ℤ_[p]) = 1 - w := by simp [F]
    rw [this, PadicInt.norm_def]
    have : (((1 - w : ℤ_[p]) : ℚ_[p])) = -u := by
      change (1 : ℚ_[p]) - (1 + u) = -u
      ring
    rw [this, norm_neg]
  have hF2 : F.derivative.aeval (1 : ℤ_[p]) = 2 := by simp [F, one_add_one_eq_two]
  have h2n : ‖(2 : ℤ_[p])‖ = ‖(2 : ℚ_[p])‖ := by
    rw [PadicInt.norm_def]; rfl
  have h4n : ‖(2 : ℚ_[p])‖ ^ 2 = ‖(4 : ℚ_[p])‖ := by
    rw [← norm_pow]; norm_num
  have hev : ‖F.aeval (1 : ℤ_[p])‖ < ‖F.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    rw [hF1, hF2, h2n, h4n]; exact hu
  obtain ⟨z, hz, hzlt, -, -⟩ := hensels_lemma (F := F) (a := 1) hev
  refine ⟨(z : ℚ_[p]), ?_, ?_⟩
  · have : z ^ 2 = w := by
      have hz' : F.aeval z = 0 := hz
      simp only [F, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hz'
      simpa [sub_eq_zero] using hz'
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) this
    simpa [w] using this
  · rw [hF2, h2n] at hzlt
    rw [PadicInt.norm_def] at hzlt
    simpa using hzlt

/-- Strict ultrametric: if $\|y\| < \|x\|$ then $\|x + y\| = \|x\|$. -/
theorem norm_add_eq_of_lt {x y : ℚ_[p]} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h)]
  exact max_eq_left h.le

/-- **Second coordinate over a nearby rational.** If $y_0^2 = f(x_0)$, $y_0 \ne 0$, and $q$ is close enough to
$x_0$ (precisely $\delta \cdot K < \|4\|\|y_0\|^2$ with $\|q - x_0\| < \delta \le 1$), then there is $z$
with $(y_0 z)^2 = f(q)$ and $\|y_0 + y_0 z\| = \|2y_0\|$. -/
theorem exists_sqrt_approx (a b : ℚ) (x₀ y₀ : ℚ_[p]) (q : ℚ) (hy : y₀ ≠ 0)
    (hE : y₀ ^ 2 = x₀ ^ 3 + (a : ℚ_[p]) * x₀ + b) (δ : ℝ) (hδ1 : δ ≤ 1)
    (hq : ‖(q : ℚ_[p]) - x₀‖ < δ)
    (hδK : δ * ((max ‖x₀‖ 1) ^ 2 * max ‖(a : ℚ_[p])‖ 1) < ‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2) :
    ∃ z : ℚ_[p], (y₀ * z) ^ 2 = (q : ℚ_[p]) ^ 3 + (a : ℚ_[p]) * q + b ∧ ‖y₀ + y₀ * z‖ = ‖2 * y₀‖ := by
  set m := max ‖x₀‖ 1 with hm
  set A := max ‖(a : ℚ_[p])‖ 1 with hA
  have hm1 : 1 ≤ m := le_max_right _ _
  have hA1 : 1 ≤ A := le_max_right _ _
  have hy2 : 0 < ‖y₀‖ ^ 2 := by positivity
  have hqm : ‖(q : ℚ_[p])‖ ≤ m := by
    have : (q : ℚ_[p]) = x₀ + ((q : ℚ_[p]) - x₀) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (le_max_left _ _) ?_)
    exact (hq.le.trans hδ1).trans hm1
  have hx0m : ‖x₀‖ ≤ m := le_max_left _ _
  have hS : ‖(q : ℚ_[p]) ^ 2 + q * x₀ + x₀ ^ 2 + a‖ ≤ m ^ 2 * A := by
    have h1 : ‖(q : ℚ_[p]) ^ 2‖ ≤ m ^ 2 := by rw [norm_pow]; gcongr
    have h2 : ‖(q : ℚ_[p]) * x₀‖ ≤ m ^ 2 := by
      rw [norm_mul, sq]; gcongr
    have h3 : ‖x₀ ^ 2‖ ≤ m ^ 2 := by rw [norm_pow]; gcongr
    have h4 : ‖(q : ℚ_[p]) ^ 2 + q * x₀ + x₀ ^ 2‖ ≤ m ^ 2 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)) h3)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · calc _ ≤ m ^ 2 := h4
        _ ≤ m ^ 2 * A := le_mul_of_one_le_right (by positivity) hA1
    · calc _ ≤ A := le_max_left _ _
        _ ≤ m ^ 2 * A := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hm1)
  have hK : 0 < m ^ 2 * A := by positivity
  set u : ℚ_[p] := (((q : ℚ_[p]) ^ 3 + a * q + b) - (x₀ ^ 3 + a * x₀ + b)) / y₀ ^ 2 with hu
  have hu_eq : u = ((q : ℚ_[p]) - x₀) * ((q : ℚ_[p]) ^ 2 + q * x₀ + x₀ ^ 2 + a) / y₀ ^ 2 := by
    rw [hu]; congr 1; ring
  have hun : ‖u‖ < ‖(4 : ℚ_[p])‖ := by
    rw [hu_eq, norm_div, norm_mul, norm_pow, div_lt_iff₀ hy2]
    calc ‖(q : ℚ_[p]) - x₀‖ * ‖(q : ℚ_[p]) ^ 2 + q * x₀ + x₀ ^ 2 + a‖
        ≤ ‖(q : ℚ_[p]) - x₀‖ * (m ^ 2 * A) := mul_le_mul_of_nonneg_left hS (norm_nonneg _)
      _ < δ * (m ^ 2 * A) := mul_lt_mul_of_pos_right hq hK
      _ < _ := hδK
  obtain ⟨z, hz, hzlt⟩ := exists_sqrt_one_add u hun
  refine ⟨z, ?_, ?_⟩
  · rw [mul_pow, hz, hu]
    field_simp
    linear_combination hE
  · have e : y₀ + y₀ * z = 2 * y₀ + y₀ * (z - 1) := by ring
    rw [e]
    apply norm_add_eq_of_lt
    rw [norm_mul, norm_mul, mul_comm ‖(2 : ℚ_[p])‖]
    exact mul_lt_mul_of_pos_left hzlt (norm_pos_iff.2 hy)

/-- **Largeness of the chord $x$-coordinate.** If $x_0 \ne q$ are close ($\|x_0 - q\| < \delta \le 1$),
$\|q\| \le \max(\|x_0\|,1)$ and $\delta L \le \|s\|^2$ with $L = \max(N, \max(\|x_0\|,1)) + 1$, then
$\|(s/(x_0 - q))^2 - x_0 - q\| > N$. -/
theorem norm_slope_sq_large (N : ℝ) (x₀ q s : ℚ_[p]) (δ : ℝ) (hd0 : x₀ ≠ q) (hδ1 : δ ≤ 1)
    (hd : ‖x₀ - q‖ < δ) (hq : ‖q‖ ≤ max ‖x₀‖ 1)
    (hδL : δ * (max N (max ‖x₀‖ 1) + 1) ≤ ‖s‖ ^ 2) :
    N < ‖(s / (x₀ - q)) ^ 2 - x₀ - q‖ := by
  set m := max ‖x₀‖ 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  set L := max N m + 1 with hL
  have hNL : N < L := by have := le_max_left N m; linarith
  have hmL : m < L := by have := le_max_right N m; linarith
  have hL0 : 0 < L := by linarith
  have hdpos : 0 < ‖x₀ - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hd0)
  have hd1 : ‖x₀ - q‖ < 1 := hd.trans_le hδ1
  have hd2 : ‖x₀ - q‖ ^ 2 < δ := by
    calc ‖x₀ - q‖ ^ 2 ≤ ‖x₀ - q‖ := by nlinarith
      _ < δ := hd
  have hlam : L < ‖(s / (x₀ - q)) ^ 2‖ := by
    rw [norm_pow, norm_div, div_pow, lt_div_iff₀ (by positivity)]
    calc L * ‖x₀ - q‖ ^ 2 < L * δ := mul_lt_mul_of_pos_left hd2 hL0
      _ ≤ ‖s‖ ^ 2 := by linarith
  have hxq : ‖x₀ + q‖ ≤ m :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (le_max_left _ _) hq)
  have e : (s / (x₀ - q)) ^ 2 - x₀ - q = (s / (x₀ - q)) ^ 2 + (-(x₀ + q)) := by ring
  rw [e, norm_add_eq_of_lt (by rw [norm_neg]; linarith)]
  linarith

/-- **Density**: for $E : y^2 = x^3 + ax + b$ over $\mathbb Q$, every point $R \in E(\mathbb Q_p)$ is
approximated by an algebraic point $T$: $R - T = O$ or $\|x(R - T)\| > N$. -/
theorem exists_isAlgPoint_sub_large_padic (a b : ℚ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (R : ((shortCurve a b).toAffine⁄ℚ_[p]).Point) (N : ℝ) :
    ∃ T : ((shortCurve a b).toAffine⁄ℚ_[p]).Point, IsAlgPoint (shortCurve a b) ℚ_[p] T ∧
      (R - T = 0 ∨ ∃ (x y : ℚ_[p]) (h : ((shortCurve a b).toAffine⁄ℚ_[p]).Nonsingular x y),
        R - T = Point.some x y h ∧ N < ‖x‖) := by
  rcases R with _ | ⟨x₀, y₀, h₀⟩
  · exact ⟨0, isAlgPoint_zero _ _, Or.inl (sub_zero _)⟩
  have hE := (equation_shortCurve_iff a b x₀ y₀).1 h₀.1
  by_cases hx : IsAlgebraic ℚ x₀
  · refine ⟨Point.some x₀ y₀ h₀, ⟨hx, ?_⟩, Or.inl (sub_self _)⟩
    exact (WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x (R := ℚ) (W := shortCurve a b)
      h₀.1 (isAlgebraic_iff_isIntegral.1 hx)).isAlgebraic
  -- transcendental case
  have hxq : ∀ q : ℚ, (q : ℚ_[p]) ≠ x₀ := fun q h => hx (h ▸ isAlgebraic_algebraMap q)
  have hy : y₀ ≠ 0 := by
    rintro rfl
    apply hx
    refine isAlgebraic_iff_isIntegral.2 ⟨Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b,
      by monicity!, ?_⟩
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
      Polynomial.eval₂_X, eq_ratCast]
    linear_combination -hE
  have hΔ' : ((shortCurve a b).toAffine⁄ℚ_[p]).Δ ≠ 0 := by
    have : ((shortCurve a b).toAffine⁄ℚ_[p]).Δ = algebraMap ℚ ℚ_[p] (-16 * (4 * a ^ 3 + 27 * b ^ 2)) := by
      change ((shortCurve a b).baseChange ℚ_[p]).Δ = _
      rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, II.Δ_shortCurve]
    rw [this]
    exact (_root_.map_ne_zero _).2 (mul_ne_zero (by norm_num) hΔ)
  set m := max ‖x₀‖ 1 with hm
  set A := max ‖(a : ℚ_[p])‖ 1 with hA
  have hm1 : 1 ≤ m := le_max_right _ _
  have hA1 : 1 ≤ A := le_max_right _ _
  set K := m ^ 2 * A with hK
  have hK0 : 0 < K := by positivity
  set L := max N m + 1 with hL
  have hL0 : 0 < L := by have := le_max_right N m; linarith
  have h4 : 0 < ‖(4 : ℚ_[p])‖ := norm_pos_iff.2 (by norm_num)
  have hy0 : 0 < ‖y₀‖ := norm_pos_iff.2 hy
  have hc0 : 0 < ‖(2 : ℚ_[p]) * y₀‖ := norm_pos_iff.2 (mul_ne_zero (by norm_num) hy)
  set δ : ℝ := min 1 (min (‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2 / (2 * K)) (‖(2 : ℚ_[p]) * y₀‖ ^ 2 / L)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ ‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2 / (2 * K) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ ‖(2 : ℚ_[p]) * y₀‖ ^ 2 / L := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨q, hq⟩ := Padic.rat_dense p x₀ hδ0
  have hq' : ‖(q : ℚ_[p]) - x₀‖ < δ := by rwa [norm_sub_rev]
  have hδK : δ * K < ‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2 := by
    have hX : 0 < ‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2 := by positivity
    calc δ * K ≤ ‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2 / (2 * K) * K := by gcongr
      _ = ‖(4 : ℚ_[p])‖ * ‖y₀‖ ^ 2 / 2 := by field_simp
      _ < _ := by linarith
  have hδL : δ * L ≤ ‖(2 : ℚ_[p]) * y₀‖ ^ 2 := by
    calc δ * L ≤ ‖(2 : ℚ_[p]) * y₀‖ ^ 2 / L * L := by gcongr
      _ = _ := by field_simp
  obtain ⟨z, hz, hzn⟩ := exists_sqrt_approx a b x₀ y₀ q hy hE δ hδ1 hq' hδK
  have hTe : ((shortCurve a b).toAffine⁄ℚ_[p]).Equation (q : ℚ_[p]) (y₀ * z) :=
    (equation_shortCurve_iff a b _ _).2 hz
  have hT := (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').1 hTe
  have hTalg : IsAlgPoint (shortCurve a b) ℚ_[p] (Point.some _ _ hT) :=
    ⟨isAlgebraic_algebraMap (q : ℚ), (WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x
      (R := ℚ) (W := shortCurve a b) hTe
      (isAlgebraic_iff_isIntegral.1 (isAlgebraic_algebraMap (q : ℚ)))).isAlgebraic⟩
  refine ⟨_, hTalg, Or.inr ?_⟩
  have hx0 : x₀ ≠ (q : ℚ_[p]) := (hxq q).symm
  have hneg := (nonsingular_neg (W' := ((shortCurve a b).toAffine⁄ℚ_[p])) (q : ℚ_[p]) (y₀ * z)).2 hT
  refine ⟨_, _, nonsingular_add h₀ hneg (fun h => hx0 h.1), ?_, ?_⟩
  · rw [sub_eq_add_neg]
    change Point.some x₀ y₀ h₀ + -Point.some _ _ hT = _
    rw [Point.neg_some, Point.add_some (fun h => hx0 h.1)]
  · rw [slope_of_X_ne hx0]
    have hqm : ‖(q : ℚ_[p])‖ ≤ m := by
      have : (q : ℚ_[p]) = x₀ + ((q : ℚ_[p]) - x₀) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (le_max_left _ _) ((hq'.le.trans hδ1).trans hm1))
    have key := norm_slope_sq_large N x₀ q (y₀ + y₀ * z) δ hx0 hδ1 hq hqm
      (by rw [hzn]; exact hδL)
    convert key using 2
    simp [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, WeierstrassCurve.baseChange,
      II.shortCurve, sub_eq_add_neg]

end NumberFieldKB.MilneEC
