import Mathlib.Algebra.CubicDiscriminant
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import QuadFormsKB.Citation
import NumberFieldKB.FormalConjectures.EllipticCurve

/-!
# The real period of a Weierstrass curve over $\mathbb R$ from its largest root

Real-variable facts about Formal Conjectures' `realPeriod` $\Omega(W) = 2\int_{\mathbb R} dx/\sqrt{F(x)}$ (integrand
$0$ where $F \le 0$), $F = \Psi_2^2 = 4x^3 + b_2x^2 + 2b_4x + b_6$, for an elliptic curve $W$ over $\mathbb R$:

* `realPeriod_variableChange_of_u_eq_one`: $\Omega$ is unchanged by a change of variables with $u = 1$ (then
  $F$ is translated by $r$);
* `exists_variableChange_short`: a change of variables with $u = 1$ brings $W$ to the form $y^2 = x^3 + Ax + B$;
* `realPeriod_eq_of_largest_root`: if $e$ is a root of $F$ with $F > 0$ on $(e, \infty)$ and
  $I = \int_e^\infty dx/\sqrt{F(x)}$, then $\Omega(W) = 2I$ if $\Delta < 0$ (one real root; $E(\mathbb R)$ has one
  component) and $\Omega(W) = 4I$ if $\Delta > 0$ (three real roots $e_3 < e_2 < e_1 = e$; two components, and the
  substitution $x \mapsto e_3 + (e_3 - e_2)(e_3 - e_1)/(x - e_3)$, which on points is translation by the point of
  order 2 over $e_3$, carries $(e_1, \infty)$ onto $(e_3, e_2)$ and preserves $dx/\sqrt{F(x)}$).
-/

open Set MeasureTheory

namespace NumberFieldKB.MilneEC.III

/-- A change of variables with $u = 1$ does not change the real period. -/
theorem realPeriod_variableChange_of_u_eq_one (W : WeierstrassCurve ℝ) (C : WeierstrassCurve.VariableChange ℝ)
    (hu : C.u = 1) : FormalConjectures.realPeriod (C • W) = FormalConjectures.realPeriod W := by
  have hF : ∀ x, (C • W).Ψ₂Sq.eval x = W.Ψ₂Sq.eval (x + C.r) := by
    intro x
    simp only [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.variableChange_b₂,
      WeierstrassCurve.variableChange_b₄, WeierstrassCurve.variableChange_b₆, hu]
    simp
    ring
  unfold FormalConjectures.realPeriod FormalConjectures.realPeriodIntegrand
  congr 1
  simp_rw [hF]
  exact integral_add_right_eq_self (fun x => (√(W.Ψ₂Sq.eval x))⁻¹) C.r

/-- Every Weierstrass curve over $\mathbb R$ becomes $y^2 = x^3 + Ax + B$ after a change of variables with $u = 1$
(complete the square in $y$, then the cube in $x$). -/
theorem exists_variableChange_short (W : WeierstrassCurve ℝ) :
    ∃ C : WeierstrassCurve.VariableChange ℝ, C.u = 1 ∧ (C • W).a₁ = 0 ∧ (C • W).a₂ = 0 ∧ (C • W).a₃ = 0 := by
  set s : ℝ := -W.a₁ / 2 with hs
  set r : ℝ := (s * W.a₁ + s ^ 2 - W.a₂) / 3 with hr
  set t : ℝ := -(W.a₃ + r * W.a₁) / 2 with ht
  refine ⟨⟨1, r, s, t⟩, rfl, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.variableChange_a₁]
    simp only [inv_one, Units.val_one, one_mul]
    rw [hs]; ring
  · rw [WeierstrassCurve.variableChange_a₂]
    simp only [inv_one, one_pow, one_mul, Units.val_one]
    rw [hr]; ring
  · rw [WeierstrassCurve.variableChange_a₃]
    simp only [inv_one, one_pow, one_mul, Units.val_one]
    rw [ht]; ring

private lemma cubic_nonpos {e₁ e₂ e₃ x : ℝ} (h₂ : e₃ < e₂) (h₁ : e₂ < e₁)
    (hx : x ≤ e₃ ∨ (e₂ ≤ x ∧ x ≤ e₁)) : 4 * (x - e₁) * (x - e₂) * (x - e₃) ≤ 0 := by
  rcases hx with hx | ⟨hx1, hx2⟩
  · have h : 0 < 4 * ((x - e₁) * (x - e₂)) :=
      mul_pos (by norm_num) (mul_pos_of_neg_of_neg (by linarith) (by linarith))
    have := mul_nonpos_of_nonneg_of_nonpos h.le (by linarith : x - e₃ ≤ 0)
    linarith
  · have h1 : 4 * (x - e₁) ≤ 0 := by linarith
    have h2 := mul_nonpos_of_nonpos_of_nonneg h1 (by linarith : 0 ≤ x - e₂)
    exact mul_nonpos_of_nonpos_of_nonneg h2 (by linarith)

private lemma integrand_zero_of_nonpos {y : ℝ} (h : y ≤ 0) : (√y)⁻¹ = 0 := by
  rw [Real.sqrt_eq_zero_of_nonpos h, inv_zero]

private lemma integral_three_roots {e₁ e₂ e₃ : ℝ} (h₂ : e₃ < e₂) (h₁ : e₂ < e₁)
    (hint : IntegrableOn (fun x => (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹) (Ioi e₁)) :
    ∫ x, (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ =
      2 * ∫ x in Ioi e₁, (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ := by
  set f : ℝ → ℝ := fun x => (√(4 * (x - e₁) * (x - e₂) * (x - e₃)))⁻¹ with hf
  set k : ℝ := (e₃ - e₂) * (e₃ - e₁) with hk
  have hkpos : 0 < k := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  set φ : ℝ → ℝ := fun x => e₃ + k * (x - e₃)⁻¹ with hφ
  have hderiv : ∀ x ∈ Ioi e₁, HasDerivWithinAt φ (k * (-1 / (x - e₃) ^ 2)) (Ioi e₁) x := by
    intro x hx
    have hx' : x - e₃ ≠ 0 := (by have : e₁ < x := hx; linarith : 0 < x - e₃).ne'
    have := ((((hasDerivAt_id x).sub_const e₃).inv hx').const_mul k).const_add e₃
    exact this.hasDerivWithinAt
  have himg : φ '' Ioi e₁ = Ioo e₃ e₂ := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : e₁ < x := hx
      have hy : 0 < x - e₃ := by linarith
      have hp : 0 < k * (x - e₃)⁻¹ := mul_pos hkpos (inv_pos.2 hy)
      refine ⟨by simp only [hφ]; linarith, ?_⟩
      have : k * (x - e₃)⁻¹ < e₂ - e₃ := by
        rw [← div_eq_mul_inv, div_lt_iff₀ hy, hk]
        nlinarith [mul_pos (by linarith : 0 < e₂ - e₃) (by linarith : 0 < x - e₁)]
      simp only [hφ]; linarith
    · rintro ⟨hz1, hz2⟩
      have hz : 0 < z - e₃ := by linarith
      have hzi : 0 < k * (z - e₃)⁻¹ := mul_pos hkpos (inv_pos.2 hz)
      refine ⟨e₃ + k * (z - e₃)⁻¹, ?_, ?_⟩
      · show e₁ < _
        have : e₁ - e₃ < k * (z - e₃)⁻¹ := by
          rw [← div_eq_mul_inv, lt_div_iff₀ hz, hk]
          nlinarith [mul_pos (by linarith : 0 < e₁ - e₃) (by linarith : 0 < e₂ - z)]
        linarith
      · simp only [hφ, add_sub_cancel_left]
        field_simp
        ring
  have hinj : InjOn φ (Ioi e₁) := by
    intro x hx x' hx' h
    have hx1 : e₁ < x := hx
    have hx2 : e₁ < x' := hx'
    simp only [hφ, add_right_inj] at h
    have h' := mul_left_cancel₀ hkpos.ne' h
    have := inv_injective h'
    linarith
  have heq : ∀ x ∈ Ioi e₁, |k * (-1 / (x - e₃) ^ 2)| • f (φ x) = f x := by
    intro x hx
    have hx1 : e₁ < x := hx
    have hy : 0 < x - e₃ := by linarith
    have hFx : 0 ≤ 4 * (x - e₁) * (x - e₂) * (x - e₃) := by
      have : 0 < 4 * (x - e₁) * (x - e₂) * (x - e₃) :=
        mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (by linarith)
      exact this.le
    have hF : 4 * (φ x - e₁) * (φ x - e₂) * (φ x - e₃) =
        (k * ((x - e₃) ^ 2)⁻¹) ^ 2 * (4 * (x - e₁) * (x - e₂) * (x - e₃)) := by
      simp only [hφ, hk]
      field_simp
      ring
    have hc : 0 < k * ((x - e₃) ^ 2)⁻¹ := mul_pos hkpos (inv_pos.2 (pow_pos hy 2))
    have habs : |k * (-1 / (x - e₃) ^ 2)| = k * ((x - e₃) ^ 2)⁻¹ := by
      rw [show k * (-1 / (x - e₃) ^ 2) = -(k * ((x - e₃) ^ 2)⁻¹) by ring, abs_neg, abs_of_pos hc]
    have hs : √(4 * (φ x - e₁) * (φ x - e₂) * (φ x - e₃)) =
        (k * ((x - e₃) ^ 2)⁻¹) * √(4 * (x - e₁) * (x - e₂) * (x - e₃)) := by
      rw [hF, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le]
    have hsp : 0 < √(4 * (x - e₁) * (x - e₂) * (x - e₃)) := by
      apply Real.sqrt_pos.2
      exact mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) (by linarith)
    simp only [hf, smul_eq_mul]
    rw [habs, hs]
    field_simp
  have hrhs_int : IntegrableOn f (Ioo e₃ e₂) ∧ ∫ x in Ioo e₃ e₂, f x = ∫ x in Ioi e₁, f x := by
    constructor
    · rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
      exact hint.congr_fun (fun x hx => (heq x hx).symm) measurableSet_Ioi
    · rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
      exact setIntegral_congr_fun measurableSet_Ioi heq
  have hS : ∫ x, f x = ∫ x in Ioo e₃ e₂ ∪ Ioi e₁, f x := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [mem_union, mem_Ioo, mem_Ioi, not_or, not_and_or, not_lt] at hx
    obtain ⟨h1, h2⟩ := hx
    apply integrand_zero_of_nonpos
    apply cubic_nonpos h₂ h₁
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by linarith, h2⟩
  have hdisj : Disjoint (Ioo e₃ e₂) (Ioi e₁) :=
    Set.disjoint_left.2 fun x hx hx' => by
      have : e₁ < x := hx'
      linarith [hx.2]
  rw [hS, setIntegral_union hdisj measurableSet_Ioi hrhs_int.1 hint, hrhs_int.2]
  ring

private lemma Ψ₂Sq_eval (W : WeierstrassCurve ℝ) (x : ℝ) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [WeierstrassCurve.Ψ₂Sq]

private lemma Δ_eq_b (W : WeierstrassCurve ℝ) :
    W.Δ = -W.b₂ ^ 2 * ((W.b₂ * W.b₆ - W.b₄ ^ 2) / 4) - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2
      + 9 * W.b₂ * W.b₄ * W.b₆ := by
  have h : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by linarith [W.b_relation]
  unfold WeierstrassCurve.Δ
  rw [h]

private lemma exists_root_Ψ₂Sq (W : WeierstrassCurve ℝ) : ∃ e, W.Ψ₂Sq.eval e = 0 := by
  have hcont : Continuous fun x => W.Ψ₂Sq.eval x := W.Ψ₂Sq.continuous
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + |W.b₂| + 2 * |W.b₄| + |W.b₆| := ⟨_, rfl⟩
  have h2 := abs_nonneg W.b₂
  have h4 := abs_nonneg W.b₄
  have h6 := abs_nonneg W.b₆
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have hS : |W.b₂| * M ^ 2 + 2 * |W.b₄| * M ^ 2 + |W.b₆| * M ^ 2 = (M - 1) * M ^ 2 := by
    have : M - 1 = |W.b₂| + 2 * |W.b₄| + |W.b₆| := by rw [hM]; ring
    rw [this]; ring
  have t1 := mul_le_mul_of_nonneg_right (neg_abs_le W.b₂) (sq_nonneg M)
  have t1' := mul_le_mul_of_nonneg_right (le_abs_self W.b₂) (sq_nonneg M)
  have t2 := mul_le_mul_of_nonneg_right (neg_abs_le W.b₄) hM0
  have t2' := mul_le_mul_of_nonneg_right (le_abs_self W.b₄) hM0
  have t2a := mul_le_mul_of_nonneg_left hMM h4
  have t3 := le_mul_of_one_le_right h6 hM2
  have t3a := neg_abs_le W.b₆
  have t3b := le_abs_self W.b₆
  have hpos : 0 < W.Ψ₂Sq.eval M := by
    rw [Ψ₂Sq_eval]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < M) 3, pow_pos (by linarith : (0 : ℝ) < M) 2]
  have hneg : W.Ψ₂Sq.eval (-M) < 0 := by
    rw [Ψ₂Sq_eval]
    nlinarith [pow_pos (by linarith : (0 : ℝ) < M) 3, pow_pos (by linarith : (0 : ℝ) < M) 2]
  have := intermediate_value_Icc (by linarith : -M ≤ M) hcont.continuousOn
  obtain ⟨e, -, he⟩ := this ⟨hneg.le, hpos.le⟩
  exact ⟨e, he⟩

private lemma factor_at_root (W : WeierstrassCurve ℝ) {e : ℝ} (he : W.Ψ₂Sq.eval e = 0) :
    ∃ p q : ℝ, (∀ x, W.Ψ₂Sq.eval x = 4 * (x - e) * (x ^ 2 + p * x + q)) ∧
      W.Δ = 16 * (p ^ 2 - 4 * q) * (e ^ 2 + p * e + q) ^ 2 := by
  rw [Ψ₂Sq_eval] at he
  have h6 : W.b₆ = -(4 * e ^ 3 + W.b₂ * e ^ 2 + 2 * W.b₄ * e) := by linarith
  refine ⟨W.b₂ / 4 + e, W.b₄ / 2 + e * (W.b₂ / 4 + e), ?_, ?_⟩
  · intro x
    rw [Ψ₂Sq_eval, h6]; ring
  · rw [Δ_eq_b, h6]; ring

private lemma sort3 {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ e₁ e₂ e₃ : ℝ, e₃ < e₂ ∧ e₂ < e₁ ∧
      ∀ x, 4 * (x - a) * (x - b) * (x - c) = 4 * (x - e₁) * (x - e₂) * (x - e₃) := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3 <;>
  first
  | exact ⟨a, b, c, by linarith, by linarith, fun x => by ring⟩
  | exact ⟨a, c, b, by linarith, by linarith, fun x => by ring⟩
  | exact ⟨b, a, c, by linarith, by linarith, fun x => by ring⟩
  | exact ⟨b, c, a, by linarith, by linarith, fun x => by ring⟩
  | exact ⟨c, a, b, by linarith, by linarith, fun x => by ring⟩
  | exact ⟨c, b, a, by linarith, by linarith, fun x => by ring⟩

private lemma delta_pos_iff_aux (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    0 < W.Δ ↔ ∃ e₁ e₂ e₃ : ℝ, e₃ < e₂ ∧ e₂ < e₁ ∧
      ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃) := by
  constructor
  · intro hΔ
    obtain ⟨e, he⟩ := exists_root_Ψ₂Sq W
    obtain ⟨p, q, hFac, hΔe⟩ := factor_at_root W he
    have hprod : 0 < (p ^ 2 - 4 * q) * (e ^ 2 + p * e + q) ^ 2 := by linarith
    have hD : 0 < p ^ 2 - 4 * q := by
      by_contra hcon
      have hcon := not_lt.1 hcon
      nlinarith [sq_nonneg (e ^ 2 + p * e + q)]
    have hQe : e ^ 2 + p * e + q ≠ 0 := by
      intro h; rw [h] at hprod; simp at hprod
    obtain ⟨ρ, hρ0, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = p ^ 2 - 4 * q :=
      ⟨√(p ^ 2 - 4 * q), Real.sqrt_pos.2 hD, Real.sq_sqrt hD.le⟩
    have hQ' : ∀ x, x ^ 2 + p * x + q = (x - (-p + ρ) / 2) * (x - (-p - ρ) / 2) := by
      intro x; linear_combination (1 / 4 : ℝ) * hρ
    have h1 : e ≠ (-p + ρ) / 2 := by
      intro h; apply hQe; rw [hQ' e, h]; ring
    have h2 : e ≠ (-p - ρ) / 2 := by
      intro h; apply hQe; rw [hQ' e, h]; ring
    have h3 : (-p + ρ) / 2 ≠ (-p - ρ) / 2 := by
      intro h; linarith
    obtain ⟨e₁, e₂, e₃, hlt2, hlt1, hs⟩ := sort3 h1 h2 h3
    refine ⟨e₁, e₂, e₃, hlt2, hlt1, fun x => ?_⟩
    rw [hFac, hQ', ← hs]; ring
  · rintro ⟨e₁, e₂, e₃, h₂, h₁, hF⟩
    have he : W.Ψ₂Sq.eval e₁ = 0 := by rw [hF]; ring
    obtain ⟨p, q, hFac, hΔe⟩ := factor_at_root W he
    have hQ2 : e₂ ^ 2 + p * e₂ + q = 0 := by
      have := hFac e₂
      rw [hF] at this
      have h' : 4 * (e₂ - e₁) * (e₂ ^ 2 + p * e₂ + q) = 0 := by rw [← this]; ring
      rcases mul_eq_zero.1 h' with h | h
      · exfalso; have : e₂ - e₁ ≠ 0 := by linarith
        simp_all
      · exact h
    have hQ3 : e₃ ^ 2 + p * e₃ + q = 0 := by
      have := hFac e₃
      rw [hF] at this
      have h' : 4 * (e₃ - e₁) * (e₃ ^ 2 + p * e₃ + q) = 0 := by rw [← this]; ring
      rcases mul_eq_zero.1 h' with h | h
      · exfalso; have : e₃ - e₁ ≠ 0 := by linarith
        simp_all
      · exact h
    have hp : p = -(e₂ + e₃) := by
      have : (e₂ - e₃) * (e₂ + e₃ + p) = 0 := by linear_combination hQ2 - hQ3
      rcases mul_eq_zero.1 this with h | h
      · exfalso; linarith
      · linarith
    have hq : q = e₂ * e₃ := by rw [hp] at hQ2; linear_combination hQ2
    rw [hΔe, hp, hq]
    have a1 : 0 < (e₂ - e₃) ^ 2 := by positivity
    have a2 : 0 < (e₁ - e₂) * (e₁ - e₃) := mul_pos (by linarith) (by linarith)
    have : 16 * ((-(e₂ + e₃)) ^ 2 - 4 * (e₂ * e₃)) * (e₁ ^ 2 + -(e₂ + e₃) * e₁ + e₂ * e₃) ^ 2 =
        16 * (e₂ - e₃) ^ 2 * ((e₁ - e₂) * (e₁ - e₃)) ^ 2 := by ring
    rw [this]; positivity

/-- **The real period from the largest root.** For an elliptic curve over $\mathbb R$ and a root $e$ of
$F = \Psi_2^2$ with $F > 0$ on $(e, \infty)$ and $1/\sqrt F$ integrable there with integral $I$:
$\Omega(W) = 2I$ if $\Delta < 0$, $\Omega(W) = 4I$ if $\Delta > 0$. -/
theorem realPeriod_eq_of_largest_root (W : WeierstrassCurve ℝ) [W.IsElliptic] {e : ℝ}
    (he : W.Ψ₂Sq.eval e = 0) (hpos : ∀ x, e < x → 0 < W.Ψ₂Sq.eval x)
    (hint : IntegrableOn (fun x => (√(W.Ψ₂Sq.eval x))⁻¹) (Ioi e)) :
    FormalConjectures.realPeriod W =
      (if 0 < W.Δ then 2 else 1) * (2 * ∫ x in Ioi e, (√(W.Ψ₂Sq.eval x))⁻¹) := by
  obtain ⟨p, q, hFac, hΔ⟩ := factor_at_root W he
  unfold FormalConjectures.realPeriod FormalConjectures.realPeriodIntegrand
  by_cases hΔpos : 0 < W.Δ
  · simp only [hΔpos, ↓reduceIte]
    obtain ⟨e₁, e₂, e₃, h₂, h₁, hF⟩ := (delta_pos_iff_aux W).1 hΔpos
    have hle : e₁ ≤ e := by
      by_contra hcon
      have := hpos e₁ (not_le.1 hcon)
      rw [hF] at this
      simp at this
    have hge : e ≤ e₁ := by
      rw [hF] at he
      have : (e - e₁) * (e - e₂) * (e - e₃) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · rcases mul_eq_zero.1 h with h | h
        · linarith
        · linarith
      · linarith
    have he1 : e = e₁ := le_antisymm hge hle
    simp only [hF] at hint ⊢
    rw [he1] at hint ⊢
    rw [integral_three_roots h₂ h₁ hint]
  · simp only [hΔpos, ↓reduceIte]
    have hΔne : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have hΔneg : W.Δ < 0 := lt_of_le_of_ne (not_lt.1 hΔpos) hΔne
    have hD : p ^ 2 - 4 * q < 0 := by
      by_contra hcon
      have hcon := not_lt.1 hcon
      have : 0 ≤ 16 * (p ^ 2 - 4 * q) * (e ^ 2 + p * e + q) ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hcon) (sq_nonneg _)
      linarith
    have hQ : ∀ x, 0 < x ^ 2 + p * x + q := fun x => by nlinarith [sq_nonneg (2 * x + p)]
    have hz : ∀ x ∉ Ioi e, (√(W.Ψ₂Sq.eval x))⁻¹ = 0 := by
      intro x hx
      apply integrand_zero_of_nonpos
      rw [hFac]
      have : x ≤ e := not_lt.1 hx
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hQ x).le
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    ring

/-- $\Delta > 0$ iff $\Psi_2^2$ has three distinct real roots (for an elliptic curve over $\mathbb R$). This justifies
reading `if 0 < W.Δ then 2 else 1` as the number of connected components of $E(\mathbb R)$: the real points lie over
the set where $\Psi_2^2 \ge 0$, which is one half-line or a half-line and a bounded interval. -/
theorem delta_pos_iff_three_real_roots (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    0 < W.Δ ↔ ∃ e₁ e₂ e₃ : ℝ, e₃ < e₂ ∧ e₂ < e₁ ∧
      ∀ x, W.Ψ₂Sq.eval x = 4 * (x - e₁) * (x - e₂) * (x - e₃) := delta_pos_iff_aux W

end NumberFieldKB.MilneEC.III
