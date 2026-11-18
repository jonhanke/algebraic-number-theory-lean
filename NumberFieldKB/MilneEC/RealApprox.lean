import NumberFieldKB.MilneEC.LocalPointsAlg
import NumberFieldKB.MilneEC.RealHalving

/-!
# Algebraic points approximate every point of $E(\mathbb R)$

`exists_isAlgPoint_sub_large`: for an elliptic curve $E/\mathbb Q$, a point $R \in E(\mathbb R)$ and a bound $N$,
there is a point $T \in E(\mathbb R)$ with algebraic coordinates such that $R - T = 0$ or $x(R - T) > N$.

If $R = 0$ or $2R = 0$, take $T = R$ (torsion points are algebraic, `exists_closureEmb_of_torsion`). Otherwise
$s_0 = 2y_0 + a_1x_0 + a_3 \neq 0$ and $D(x_0) = s_0^2 > 0$; for rational $q$ slightly larger than $x_0$, the point
$T = (q, (\pm\sqrt{D(q)} - a_1q - a_3)/2)$ is algebraic and close to $R$, and the slope of the line through $R$ and
$-T$ tends to infinity as $q \to x_0$, so $x(R - T)$ does too.
-/

open WeierstrassCurve WeierstrassCurve.Affine Filter Topology Polynomial
open scoped Classical

namespace NumberFieldKB.MilneEC

namespace RealApprox

variable (W : WeierstrassCurve ℚ)

/-- $E$ over $\mathbb R$. -/
noncomputable abbrev Wr : WeierstrassCurve ℝ := W.baseChange ℝ

/-- A real point with rational $x$-coordinate has algebraic $y$-coordinate. -/
theorem isIntegral_y (q : ℚ) (y : ℝ) (h : (Wr W).toAffine.Equation (q : ℝ) y) : IsIntegral ℚ y := by
  let D : ℚ := 4 * q ^ 3 + W.b₂ * q ^ 2 + 2 * W.b₄ * q + W.b₆
  have hD : (2 * y + (Wr W).a₁ * q + (Wr W).a₃) ^ 2 = (D : ℝ) := by
    rw [← den_duplication_eq h]
    simp only [D, Wr, WeierstrassCurve.baseChange, map_b₂, map_b₄, map_b₆, eq_ratCast]
    push_cast
    ring
  have hs : IsIntegral ℚ (2 * y + (Wr W).a₁ * q + (Wr W).a₃) := by
    refine ⟨X ^ 2 - Polynomial.C D, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hD, eq_ratCast, sub_self]
  have hc : IsIntegral ℚ ((Wr W).a₁ * q + (Wr W).a₃) := by
    have : (Wr W).a₁ * q + (Wr W).a₃ = algebraMap ℚ ℝ (W.a₁ * q + W.a₃) := by
      simp only [Wr, WeierstrassCurve.baseChange, map_a₁, map_a₃, eq_ratCast]
      push_cast
      ring
    rw [this]
    exact isIntegral_algebraMap
  have := ((hs.sub hc).smul (1 / 2 : ℚ))
  convert this using 1
  rw [Rat.smul_def]
  push_cast
  ring

/-- $2$-torsion points are algebraic. -/
theorem isAlgPoint_of_Y_eq [W.IsElliptic] {x y : ℝ} (h : (Wr W).toAffine.Nonsingular x y)
    (hy : y = (Wr W).toAffine.negY x y) : IsAlgPoint W ℝ (Point.some x y h) := by
  have h2 : 2 • (Point.some x y h : (W.toAffine⁄ℝ).Point) = 0 := by
    rw [two_nsmul]
    exact Point.add_self_of_Y_eq hy
  obtain ⟨U, hU⟩ := exists_closureEmb_of_torsion ℝ W (inclPoints W ℝ (Point.some x y h)) 2 two_pos
    (by rw [← map_nsmul, h2, map_zero])
  exact (isAlgPoint_iff W ℝ _).2 ⟨U, hU⟩

section Analysis

variable (C : WeierstrassCurve ℝ)

/-- The duplication denominator $D(X)$. -/
noncomputable def den (X : ℝ) : ℝ := 4 * X ^ 3 + C.b₂ * X ^ 2 + 2 * C.b₄ * X + C.b₆

/-- The $y$-coordinate over $q$ on the branch of sign `σ`. -/
noncomputable def yq (σ q : ℝ) : ℝ := (σ * Real.sqrt (den C q) - C.a₁ * q - C.a₃) / 2

/-- The slope of the line through $(x_0, y_0)$ and $-(q, y_q)$. -/
noncomputable def lam (σ x₀ y₀ q : ℝ) : ℝ := (y₀ - C.toAffine.negY q (yq C σ q)) / (x₀ - q)

theorem continuous_den : Continuous (den C) := by unfold den; fun_prop

theorem continuous_yq (σ : ℝ) : Continuous (yq C σ) := by
  unfold yq
  have := continuous_den C
  fun_prop

/-- As $q \downarrow x_0$, $x(R - T_q) \to \infty$. -/
theorem tendsto_addX {x₀ y₀ : ℝ} (heq : C.toAffine.Equation x₀ y₀) (hne : y₀ ≠ C.toAffine.negY x₀ y₀) :
    let s₀ := 2 * y₀ + C.a₁ * x₀ + C.a₃
    let σ := s₀ / |s₀|
    Tendsto (fun q => C.toAffine.addX x₀ q (lam C σ x₀ y₀ q)) (𝓝[>] x₀) atTop := by
  intro s₀ σ
  have hs₀ : s₀ ≠ 0 := by
    intro h
    apply hne
    simp only [negY]
    linear_combination h
  have hD₀ : den C x₀ = s₀ ^ 2 := den_duplication_eq heq
  have hy₀ : yq C σ x₀ = y₀ := by
    simp only [yq, hD₀, Real.sqrt_sq_eq_abs, σ]
    rw [div_mul_cancel₀ _ (abs_ne_zero.2 hs₀)]
    simp only [s₀]
    ring
  -- the numerator of the slope tends to `s₀ ≠ 0`
  let num := fun q => y₀ - C.toAffine.negY q (yq C σ q)
  have hnum_cont : Continuous num := by
    have := continuous_yq C σ
    simp only [num, negY]
    fun_prop
  have hnum₀ : num x₀ = s₀ := by
    simp only [num, negY, hy₀, s₀]
    ring
  have hnum : Tendsto (fun q => |num q|) (𝓝[>] x₀) (𝓝 |s₀|) := by
    rw [← hnum₀]
    exact ((continuous_abs.comp hnum_cont).tendsto x₀).mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun q => |x₀ - q|⁻¹) (𝓝[>] x₀) atTop := by
    have h1 : Tendsto (fun q => q - x₀) (𝓝[>] x₀) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Tendsto (fun q => q - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) := (continuous_sub_right x₀).tendsto x₀
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with q hq
        exact sub_pos.2 (Set.mem_Ioi.1 hq)
    refine (tendsto_inv_nhdsGT_zero.comp h1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [Function.comp_apply]
    rw [abs_sub_comm, abs_of_pos (sub_pos.2 (show x₀ < q from hq))]
  have habsL : Tendsto (fun q => |lam C σ x₀ y₀ q|) (𝓝[>] x₀) atTop := by
    refine (hnum.pos_mul_atTop (abs_pos.2 hs₀) hinv).congr' (Eventually.of_forall fun q => ?_)
    simp only [lam, div_eq_mul_inv, num]
    rw [abs_mul, abs_inv]
  have hG : Tendsto (fun q => |lam C σ x₀ y₀ q| * (|lam C σ x₀ y₀ q| + -|C.a₁|) + -(C.a₂ + x₀ + q))
      (𝓝[>] x₀) atTop := by
    refine (habsL.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _ habsL)).atTop_add
      (C := -(C.a₂ + x₀ + x₀)) ?_
    have : Continuous fun q : ℝ => -(C.a₂ + x₀ + q) := by fun_prop
    exact (this.tendsto x₀).mono_left nhdsWithin_le_nhds
  refine tendsto_atTop_mono (fun q => ?_) hG
  simp only [addX]
  have h1 : |lam C σ x₀ y₀ q| * |lam C σ x₀ y₀ q| = lam C σ x₀ y₀ q ^ 2 := by
    rw [abs_mul_abs_self, sq]
  have h2 : -(|C.a₁| * |lam C σ x₀ y₀ q|) ≤ C.a₁ * lam C σ x₀ y₀ q := by
    rw [← abs_mul]
    exact neg_abs_le _
  nlinarith

end Analysis

/-- **Algebraic points approximate every point of $E(\mathbb R)$.** -/
theorem exists_isAlgPoint_sub_large [W.IsElliptic] (R : (W.toAffine⁄ℝ).Point) (N : ℝ) :
    ∃ T : (W.toAffine⁄ℝ).Point, IsAlgPoint W ℝ T ∧
      (R - T = 0 ∨ ∃ (x y : ℝ) (h : (W.toAffine⁄ℝ).Nonsingular x y), R - T = Point.some x y h ∧ N < x) := by
  rcases R with _ | ⟨x₀, y₀, h₀⟩
  · exact ⟨0, isAlgPoint_zero W ℝ, Or.inl (sub_zero _)⟩
  by_cases hy : y₀ = (Wr W).toAffine.negY x₀ y₀
  · exact ⟨_, isAlgPoint_of_Y_eq W h₀ hy, Or.inl (sub_self _)⟩
  set C := Wr W
  set s₀ := 2 * y₀ + C.a₁ * x₀ + C.a₃
  set σ := s₀ / |s₀|
  have hs₀ : s₀ ≠ 0 := by
    intro h
    apply hy
    simp only [negY]
    linear_combination h
  have hσ : σ ≠ 0 := div_ne_zero hs₀ (abs_ne_zero.2 hs₀)
  have hD₀ : 0 < den C x₀ := by
    rw [den, den_duplication_eq h₀.1]
    positivity
  -- eventually (in `𝓝[>] x₀`): `D(q) > 0` and `x(R - T_q) > N`
  have hev : ∀ᶠ q in 𝓝[>] x₀, 0 < den C q ∧ N < C.toAffine.addX x₀ q (lam C σ x₀ y₀ q) := by
    refine Eventually.and ?_ ((tendsto_addX C h₀.1 hy).eventually (eventually_gt_atTop N))
    exact (((continuous_den C).tendsto x₀).eventually (lt_mem_nhds hD₀)).filter_mono nhdsWithin_le_nhds
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x₀ < u from hu)
  obtain ⟨hDq, hNq⟩ := hsub ⟨hq1, hq2⟩
  -- the algebraic point `T = (q, y_q)`
  have hsq : (σ * Real.sqrt (den C q)) ^ 2 = 4 * (q : ℝ) ^ 3 + C.b₂ * q ^ 2 + 2 * C.b₄ * q + C.b₆ := by
    have hσ2 : σ ^ 2 = 1 := by
      simp only [σ, div_pow, sq_abs]
      exact div_self (pow_ne_zero 2 hs₀)
    rw [mul_pow, hσ2, one_mul, Real.sq_sqrt hDq.le, den]
  have hs0 : σ * Real.sqrt (den C q) ≠ 0 := mul_ne_zero hσ (Real.sqrt_pos.2 hDq).ne'
  obtain ⟨hT, hTne⟩ := RealHalving.nonsingular_of_sq C q _ hsq hs0
  let T : (W.toAffine⁄ℝ).Point := Point.some _ _ hT
  have hTalg : IsAlgPoint W ℝ T := by
    refine ⟨isAlgebraic_algebraMap (q : ℚ), ?_⟩
    exact (isIntegral_y W q _ hT.1).isAlgebraic
  refine ⟨T, hTalg, Or.inr ?_⟩
  have hx : x₀ ≠ q := (ne_of_lt hq1)
  have hneg := (nonsingular_neg (W' := C.toAffine) (q : ℝ) ((σ * Real.sqrt (den C q) - C.a₁ * q - C.a₃) / 2)).2 hT
  refine ⟨_, _, nonsingular_add h₀ hneg (fun h => hx h.1), ?_, ?_⟩
  · rw [sub_eq_add_neg]
    change Point.some x₀ y₀ h₀ + -Point.some _ _ hT = _
    rw [Point.neg_some, Point.add_some (fun h => hx h.1)]
  · rw [slope_of_X_ne hx]
    exact hNq

end RealApprox

end NumberFieldKB.MilneEC
