import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Points of $E(\mathbb R)$ far from the origin are doubles

`exists_two_nsmul_eq_of_lt`: for a Weierstrass curve over $\mathbb R$ there is $N$ such that every affine point
$(x, y)$ with $x > N$ is $2Q$ for some $Q \in E(\mathbb R)$. The $x$-coordinate of $2Q$, $Q = (X, Y)$, is
$\varphi(X)/D(X)$ with $\varphi(X) = X^4 - b_4X^2 - 2b_6X - b_8$ and $D(X) = 4X^3 + b_2X^2 + 2b_4X + b_6$
(`addX_self_of_Y_ne`). For large $x$ the quartic $\varphi(X) - xD(X)$ is negative at $X = 2x$ and positive at
$X = 8x$, so it has a root $X$ (intermediate value theorem); $D(X) > 0$ there, so
$Y = (\sqrt{D(X)} - a_1X - a_3)/2$ is real.
-/

open WeierstrassCurve WeierstrassCurve.Affine Filter Topology
open scoped Classical

namespace NumberFieldKB.MilneEC

namespace RealHalving

variable (C : WeierstrassCurve ℝ)

/-- The quartic whose roots are the $x$-coordinates of the halves of a point with $x$-coordinate `x`. -/
noncomputable def quartic (x X : ℝ) : ℝ :=
  (X ^ 4 - C.b₄ * X ^ 2 - 2 * C.b₆ * X - C.b₈) - x * (4 * X ^ 3 + C.b₂ * X ^ 2 + 2 * C.b₄ * X + C.b₆)

/-- `quartic (c x) / x^4`, as a polynomial in `u = 1/x`. -/
noncomputable def scaled (c u : ℝ) : ℝ :=
  (c ^ 4 - C.b₄ * c ^ 2 * u ^ 2 - 2 * C.b₆ * c * u ^ 3 - C.b₈ * u ^ 4) -
    (4 * c ^ 3 + C.b₂ * c ^ 2 * u + 2 * C.b₄ * c * u ^ 2 + C.b₆ * u ^ 3)

theorem quartic_eq (c x : ℝ) (hx : x ≠ 0) : quartic C x (c * x) = x ^ 4 * scaled C c x⁻¹ := by
  unfold quartic scaled
  field_simp

theorem tendsto_scaled (c : ℝ) : Tendsto (fun x : ℝ => scaled C c x⁻¹) atTop (𝓝 (c ^ 4 - 4 * c ^ 3)) := by
  have hc : Continuous (scaled C c) := by unfold scaled; fun_prop
  have h0 : scaled C c 0 = c ^ 4 - 4 * c ^ 3 := by unfold scaled; ring
  rw [← h0]
  exact (hc.tendsto 0).comp tendsto_inv_atTop_zero

theorem eventually_quartic_pos : ∀ᶠ x : ℝ in atTop, 0 < quartic C x (8 * x) := by
  have h := (tendsto_scaled C 8).eventually (lt_mem_nhds (show (0 : ℝ) < 8 ^ 4 - 4 * 8 ^ 3 by norm_num))
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  rw [quartic_eq C 8 x hx0.ne']
  positivity

theorem eventually_quartic_neg : ∀ᶠ x : ℝ in atTop, quartic C x (2 * x) < 0 := by
  have h := (tendsto_scaled C 2).eventually (gt_mem_nhds (show (2 : ℝ) ^ 4 - 4 * 2 ^ 3 < 0 by norm_num))
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  rw [quartic_eq C 2 x hx0.ne']
  exact mul_neg_of_pos_of_neg (by positivity) hx

/-- The duplication denominator is eventually positive. -/
theorem eventually_den_pos : ∀ᶠ X : ℝ in atTop, 0 < 4 * X ^ 3 + C.b₂ * X ^ 2 + 2 * C.b₄ * X + C.b₆ := by
  have hc : Continuous fun u : ℝ => 4 + C.b₂ * u + 2 * C.b₄ * u ^ 2 + C.b₆ * u ^ 3 := by fun_prop
  have h := ((hc.tendsto 0).comp tendsto_inv_atTop_zero).eventually
    (lt_mem_nhds (show (0 : ℝ) < 4 + C.b₂ * 0 + 2 * C.b₄ * 0 ^ 2 + C.b₆ * 0 ^ 3 by norm_num))
  filter_upwards [h, eventually_gt_atTop 0] with X hX hX0
  have : 4 * X ^ 3 + C.b₂ * X ^ 2 + 2 * C.b₄ * X + C.b₆ =
      X ^ 3 * (4 + C.b₂ * X⁻¹ + 2 * C.b₄ * X⁻¹ ^ 2 + C.b₆ * X⁻¹ ^ 3) := by
    field_simp
  rw [this]
  exact mul_pos (by positivity) hX

/-- A point with prescribed $X$, given a nonzero square root $s$ of $D(X)$. -/
theorem nonsingular_of_sq (X s : ℝ) (hs : s ^ 2 = 4 * X ^ 3 + C.b₂ * X ^ 2 + 2 * C.b₄ * X + C.b₆)
    (hs0 : s ≠ 0) :
    C.toAffine.Nonsingular X ((s - C.a₁ * X - C.a₃) / 2) ∧
      (s - C.a₁ * X - C.a₃) / 2 ≠ C.toAffine.negY X ((s - C.a₁ * X - C.a₃) / 2) := by
  have hne : (s - C.a₁ * X - C.a₃) / 2 ≠ C.toAffine.negY X ((s - C.a₁ * X - C.a₃) / 2) := by
    intro h
    apply hs0
    simp only [negY] at h
    linarith
  have heq : C.toAffine.Equation X ((s - C.a₁ * X - C.a₃) / 2) := by
    rw [equation_iff]
    simp only [b₂, b₄, b₆] at hs
    linear_combination (1 / 4 : ℝ) * hs
  refine ⟨(nonsingular_iff' X _).2 ⟨heq, ?_⟩, hne⟩
  right
  intro h
  apply hs0
  linarith

end RealHalving

/-- **Points of $E(\mathbb R)$ with large $x$-coordinate are doubles.** -/
theorem exists_two_nsmul_eq_of_lt (C : WeierstrassCurve ℝ) :
    ∃ N : ℝ, ∀ (x y : ℝ) (h : C.toAffine.Nonsingular x y), N < x →
      ∃ Q : C.toAffine.Point, 2 • Q = Point.some x y h := by
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (RealHalving.eventually_quartic_pos C)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (RealHalving.eventually_quartic_neg C)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (RealHalving.eventually_den_pos C)
  refine ⟨max (max N₁ N₂) (max N₃ 0), fun x y h hx => ?_⟩
  simp only [max_lt_iff] at hx
  obtain ⟨⟨h1, h2⟩, h3, h0⟩ := hx
  have hcont : ContinuousOn (RealHalving.quartic C x) (Set.Icc (2 * x) (8 * x)) := by
    unfold RealHalving.quartic
    fun_prop
  obtain ⟨X, hXI, hX⟩ := intermediate_value_Icc (by linarith) hcont
    ⟨(hN₂ x h2.le).le, (hN₁ x h1.le).le⟩
  have hD := hN₃ X (by linarith [hXI.1])
  obtain ⟨hns, hne⟩ := RealHalving.nonsingular_of_sq C X _ (Real.sq_sqrt hD.le) (Real.sqrt_pos.2 hD).ne'
  set Y := (Real.sqrt (4 * X ^ 3 + C.b₂ * X ^ 2 + 2 * C.b₄ * X + C.b₆) - C.a₁ * X - C.a₃) / 2
  have hdup : (Point.some X Y hns + Point.some X Y hns).xRep = (Point.some x y h).xRep := by
    rw [Point.xRep_add_self_of_Y_ne hns hne, Point.xRep_some]
    congr 1
    rw [div_eq_iff hD.ne']
    unfold RealHalving.quartic at hX
    linarith
  rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hdup with h' | h'
  · exact ⟨Point.some X Y hns, by rw [two_nsmul, h']⟩
  · refine ⟨-Point.some X Y hns, ?_⟩
    rw [two_nsmul, ← neg_add, h', neg_neg]

end NumberFieldKB.MilneEC
