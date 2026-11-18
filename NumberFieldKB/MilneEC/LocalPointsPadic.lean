import NumberFieldKB.MilneEC.LocalPointsReal
import NumberFieldKB.MilneEC.Ch2Corollary42
import NumberFieldKB.MilneEC.PadicApprox
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Integrality
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Kummer approximation at the finite places of $\mathbb Q$

For an elliptic curve $E/\mathbb Q$, a prime $p$ and an integer $\ell \ge 1$, every point of $E(\mathbb Q_p)$ is
$\ell S + T$ with $S \in E(\mathbb Q_p)$ and $T$ a point with coordinates algebraic over $\mathbb Q$. This is the named
statement `FiniteKummerPrime`, proved here (`finiteKummerPrime`); with it
`LocalPointsInjective`, `ShaComparison` and the three Conjecture IV.10.5 comparisons hold with no named input.

The route mirrors the real place (`kummerApprox_real_two`):

* **Openness**. On a short integral model $y^2 = x^3 + ax + b$ over $\mathbb Z_p$, multiplication by
  $m \ne 0$ is onto the points with $\|x\| > \|m\|^{-4}$ (`II.exists_zsmul_eq_of_norm`): Hensel's lemma on the
  reflected division polynomials $s\,\Phi_m^{\mathrm{rev}} - \Psi_m^{2,\mathrm{rev}}$, $s = 1/x$, exactly as in the proof
  of Milne's Corollary II.4.2 (`II.exists_x_of_hensel`, the case $p \nmid m$), whose Hensel condition
  $\|s\| < \|m\|^4$ holds also when $p \mid m$, $p = 2$ included. Hence $E^1(\mathbb Q_p) \subseteq \ell E^1(\mathbb Q_p)$
  for $\ell \ne p$ (`II.E1_subset_zsmul_of_not_dvd`) and $E^n(\mathbb Q_p) \subseteq pE^1(\mathbb Q_p)$ for
  $n \ge 3$ (`II.En_subset_zsmul_p`). The formal group is not needed.
* **Density** (`exists_isAlgPoint_sub_large_padic`, in `PadicApprox.lean`). Given $R = (x_0, y_0)$ with $x_0$ transcendental,
  take $q \in \mathbb Q$ close to $x_0$ and $y_q = y_0\sqrt{f(q)/f(x_0)}$, the square root of a $p$-adic number
  $1 + u$ with $\|u\| < \|4\|$ by Hensel's lemma; then $T = (q, y_q)$ is algebraic and $\|x(R - T)\|$ is as large
  as wanted.
* **Assembly**. `kummerApprox_shortQ` for $y^2 = x^3 + ax + b$, $a, b \in \mathbb Z$; transported along a
  change of variables over $\mathbb Q$ (`kummerApprox_of_variableChange`) and along Mathlib's
  $\mathbb Q_p \cong \mathbb Q_v$ (`adicCompletion.padicEquiv`).
-/

open WeierstrassCurve WeierstrassCurve.Affine NumberField Polynomial
open scoped Classical

namespace NumberFieldKB.MilneEC

/-! ## Openness: multiplication by $m$ is onto the points with large $x$ -/

namespace II

variable {p : ℕ} [Fact p.Prime]

/-- **Hensel step for every $m \ne 0$**: if $\|x_P\|\,\|m\|^4 > 1$ there is $x_1 \in \mathbb Q_p$ with
$\|x_1\| > 1$ and $\Phi_m(x_1) = x_P\,\Psi_m^2(x_1)$. (`exists_x_of_hensel` is the case $p \nmid m$.) -/
theorem exists_x_of_hensel_of_norm (a b : ℤ_[p]) {m : ℤ} (hm0 : m ≠ 0) {xP : ℚ_[p]}
    (hx : 1 < ‖xP‖ * ‖(m : ℚ_[p])‖ ^ 4) :
    ∃ x₁ : ℚ_[p], 1 < ‖x₁‖ ∧ ((curveQp a b).Φ m).eval x₁ = xP * ((curveQp a b).ΨSq m).eval x₁ := by
  have hxP0 : xP ≠ 0 := by rintro rfl; rw [norm_zero, zero_mul] at hx; linarith
  set W₀ := shortZp a b with hW₀
  set N := m.natAbs ^ 2 with hN
  have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (Int.natAbs_pos.2 hm0)
  set μ : ℝ := ‖(m : ℤ_[p])‖ with hμ
  have hμq : ‖(m : ℚ_[p])‖ = μ := by rw [hμ, PadicInt.norm_def, PadicInt.coe_intCast]
  have hμ1 : μ ≤ 1 := PadicInt.norm_le_one _
  have hμ0 : 0 < μ := norm_pos_iff.2 (by exact_mod_cast hm0)
  rw [hμq] at hx
  have hxP1 : 0 < ‖xP‖ := norm_pos_iff.2 hxP0
  have hsn : ‖xP⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    refine inv_le_one_of_one_le₀ ?_
    have : μ ^ 4 ≤ 1 := pow_le_one₀ hμ0.le hμ1
    nlinarith
  set s : ℤ_[p] := ⟨xP⁻¹, hsn⟩ with hs
  have hs4 : ‖s‖ < μ ^ 4 := by
    show ‖xP⁻¹‖ < μ ^ 4
    rw [norm_inv, inv_lt_iff_one_lt_mul₀ hxP1]
    linarith [mul_comm ‖xP‖ (μ ^ 4)]
  have hμ4 : μ ^ 4 ≤ μ ^ 2 := pow_le_pow_of_le_one hμ0.le hμ1 (by norm_num)
  have hμ2 : μ ^ 2 ≤ 1 := pow_le_one₀ hμ0.le hμ1
  have hs0 : s ≠ 0 := by
    intro h; apply hxP0
    have : xP⁻¹ = 0 := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) h
    simpa using this
  set Φ₀ := W₀.Φ m
  set Ψ₀ := W₀.ΨSq m
  set h : ℤ_[p][X] := C s * reflect N Φ₀ - reflect N Ψ₀ with hh
  have hΦN : Φ₀.coeff N = 1 := W₀.coeff_Φ m
  have hΨdeg : Ψ₀.natDegree ≤ N - 1 := W₀.natDegree_ΨSq_le m
  have hΨN : Ψ₀.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hΨ1 : Ψ₀.coeff (N - 1) = (m : ℤ_[p]) ^ 2 := W₀.coeff_ΨSq m
  have hΦdeg : Φ₀.natDegree ≤ N := W₀.natDegree_Φ_le m
  have h0 : h.coeff 0 = s := by
    simp [hh, coeff_reflect, hΦN, hΨN]
  have h1 : h.coeff 1 = s * Φ₀.coeff (N - 1) - (m : ℤ_[p]) ^ 2 := by
    simp [hh, coeff_reflect, revAt_le hNpos, hΨ1]
  have hd : ‖h.derivative.aeval (0 : ℤ_[p])‖ = μ ^ 2 := by
    rw [aeval_def, eval₂_at_zero]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, coeff_derivative, Nat.cast_zero, zero_add,
      mul_one, h1]
    have e1 : ‖s * Φ₀.coeff (N - 1)‖ < μ ^ 2 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _))
        (lt_of_lt_of_le hs4 hμ4)
    have e2 : ‖-((m : ℤ_[p]) ^ 2)‖ = μ ^ 2 := by rw [norm_neg, norm_pow]
    rw [sub_eq_add_neg, PadicInt.norm_add_eq_max_of_ne
      (q := s * Φ₀.coeff (N - 1)) (r := -((m : ℤ_[p]) ^ 2)) (by rw [e2]; exact e1.ne), e2]
    exact max_eq_right e1.le
  have hev : ‖h.aeval (0 : ℤ_[p])‖ < ‖h.derivative.aeval (0 : ℤ_[p])‖ ^ 2 := by
    rw [hd, aeval_def, eval₂_at_zero]
    have : ‖h.coeff 0‖ < (μ ^ 2) ^ 2 := by rw [h0, ← pow_mul]; exact hs4
    simpa using this
  obtain ⟨z, hz, hzlt, -, -⟩ := hensels_lemma (F := h) (a := 0) hev
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hs0
    rw [← h0]
    simpa [aeval_def, eval₂_at_zero] using hz
  have hzq : (z : ℚ_[p]) ≠ 0 := fun h => hz0 (Subtype.ext h)
  refine ⟨(z : ℚ_[p])⁻¹, ?_, ?_⟩
  · have : ‖(z : ℚ_[p])‖ < 1 := by
      have := hzlt
      rw [hd, sub_zero] at this
      exact lt_of_lt_of_le (by simpa using this) hμ2
    rw [norm_inv]; exact one_lt_inv_iff₀.2 ⟨norm_pos_iff.2 hzq, this⟩
  · have hz' : aeval (algebraMap ℤ_[p] ℚ_[p] z) h = 0 := by
      rw [aeval_algebraMap_apply, hz, map_zero]
    rw [aeval_def, hh, eval₂_sub, eval₂_mul, eval₂_C] at hz'
    let _ : Invertible ((z : ℚ_[p])⁻¹) := invertibleOfNonzero (inv_ne_zero hzq)
    have hinv : ⅟((z : ℚ_[p])⁻¹) = algebraMap ℤ_[p] ℚ_[p] z := by
      rw [invOf_eq_inv, inv_inv]; rfl
    have k1 := eval₂_reflect_mul_pow (algebraMap ℤ_[p] ℚ_[p]) ((z : ℚ_[p])⁻¹) N Φ₀ hΦdeg
    have k2 := eval₂_reflect_mul_pow (algebraMap ℤ_[p] ℚ_[p]) ((z : ℚ_[p])⁻¹) N Ψ₀ (by omega)
    rw [hinv] at k1 k2
    rw [curveQp_eq_map, map_Φ, map_ΨSq, eval_map, eval_map, ← k1, ← k2]
    have hsq : algebraMap ℤ_[p] ℚ_[p] s = xP⁻¹ := rfl
    rw [hsq] at hz'
    generalize eval₂ (algebraMap ℤ_[p] ℚ_[p]) (algebraMap ℤ_[p] ℚ_[p] z) (reflect N Φ₀) = A at hz' ⊢
    generalize eval₂ (algebraMap ℤ_[p] ℚ_[p]) (algebraMap ℤ_[p] ℚ_[p] z) (reflect N Ψ₀) = B at hz' ⊢
    have hB : B = xP⁻¹ * A := by linear_combination (-1 : ℚ_[p]) * hz'
    rw [hB]
    field_simp

/-- **Multiplication by $m \ne 0$ is onto the points with $\|x\| > \|m\|^{-4}$**, on a short
integral model over $\mathbb Z_p$, every $p$ including $p = 2$. -/
theorem exists_zsmul_eq_of_norm (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {m : ℤ} (hm0 : m ≠ 0)
    {xP yP : ℚ_[p]} (hP : (curveQp a b).toAffine.Nonsingular xP yP)
    (hx : 1 < ‖xP‖ * ‖(m : ℚ_[p])‖ ^ 4) :
    ∃ Q ∈ E1 a b, m • Q = Affine.Point.some xP yP hP := by
  have hm4 : ‖(m : ℚ_[p])‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) (by
    rw [← PadicInt.coe_intCast, ← PadicInt.norm_def]; exact PadicInt.norm_le_one _)
  have hx1 : 1 < ‖xP‖ := by
    by_contra hle
    push_neg at hle
    have := mul_le_one₀ hle (by positivity) hm4
    linarith
  obtain ⟨x₁, hx₁, h₁⟩ := exists_x_of_hensel_of_norm a b hm0 hx
  obtain ⟨y₁, hy₁⟩ := exists_y_of_x a b hΔ hm0 hP hx1 h₁
  have hQ : (curveQp a b).toAffine.Nonsingular x₁ y₁ :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero (curveQp_Δ_ne_zero a b hΔ)).1 hy₁
  have hQ1 : (Affine.Point.some x₁ y₁ hQ : (curveQp a b).toAffine.Point) ∈ E1 a b :=
    (mem_E1_iff _).2 (Or.inr ⟨x₁, y₁, hQ, rfl, hx₁⟩)
  rcases smul_eq_of_eval (curveQp a b) (curveQp_Δ_ne_zero a b hΔ) hP hQ h₁ with h | h
  · exact ⟨_, hQ1, h⟩
  · exact ⟨_, neg_mem_E1 hQ1, h⟩

/-- For $p \nmid m$, $E^1(\mathbb Q_p) \subseteq mE^1(\mathbb Q_p)$ (`corollary_4_2`). -/
theorem E1_subset_zsmul_of_not_dvd (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {m : ℤ}
    (hm : ¬(p : ℤ) ∣ m) {P : (curveQp a b).toAffine.Point} (hP : P ∈ E1 a b) :
    ∃ Q ∈ E1 a b, m • Q = P := by
  obtain ⟨Q, hQ, hQP⟩ := (corollary_4_2.bij p a b hΔ m hm).surjOn hP
  exact ⟨Q, hQ, hQP⟩

/-- $E^n(\mathbb Q_p) \subseteq pE^1(\mathbb Q_p)$ for $n \ge 3$, every $p$ including $p = 2$. -/
theorem En_subset_zsmul_p (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {n : ℕ} (hn : 3 ≤ n)
    {P : (curveQp a b).toAffine.Point} (hP : P ∈ En a b n) :
    ∃ Q ∈ E1 a b, (p : ℤ) • Q = P := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨hE1, hle⟩ := hP
  rcases (mem_E1_iff P).1 hE1 with rfl | ⟨x, y, h, rfl, hx⟩
  · exact ⟨0, (mem_E1_iff _).2 (Or.inl rfl), zsmul_zero _⟩
  have e := shortCurve_equation h.1
  obtain ⟨k, hk, nx, ny⟩ := exists_norm_of_one_lt (norm_coe_le_one a) (norm_coe_le_one b) hx e
  have hxy : ‖xPrime (Affine.Point.some x y h)‖ = (p : ℝ) ^ (-(k : ℤ)) := by
    simp only [xPrime, norm_div, nx, ny]
    rw [← zpow_sub₀ (by positivity)]
    congr 1; ring
  rw [hxy] at hle
  have hkn : (n : ℤ) ≤ k := by
    have := (zpow_le_zpow_iff_right₀ hp).1 hle
    omega
  refine exists_zsmul_eq_of_norm a b hΔ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) h ?_
  have hpn : ‖((p : ℤ) : ℚ_[p])‖ = (p : ℝ) ^ (-1 : ℤ) := by
    rw [Int.cast_natCast, Padic.norm_p, zpow_neg_one]
  rw [nx, hpn, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by positivity)]
  exact one_lt_zpow₀ hp (by omega)

end II

open II (shortCurve Δ_shortCurve theorem_2_1_a)

/-! ## Short curves over $\mathbb Q$ with integral coefficients, over $\mathbb Q_p$ -/

section Padic

variable {p : ℕ} [Fact p.Prime]

/-- The curve $y^2 = x^3 + ax + b$ over $\mathbb Q$, $a, b \in \mathbb Z$. -/
noncomputable abbrev shortQ (a b : ℤ) : WeierstrassCurve ℚ := shortCurve (a : ℚ) (b : ℚ)

theorem baseChange_shortQ (a b : ℤ) :
    (shortQ a b).baseChange ℚ_[p] = II.curveQp (a : ℤ_[p]) (b : ℤ_[p]) := by
  ext <;> simp [shortCurve, WeierstrassCurve.baseChange, II.curveQp]

/-- The points of `shortQ a b` over $\mathbb Q_p$ are those of `II.curveQp a b` (same coordinates). -/
noncomputable def shortQPointEquiv (a b : ℤ) :
    ((shortQ a b).toAffine⁄ℚ_[p]).Point ≃+ (II.curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.Point :=
  AddEquiv.cast (M := fun V : WeierstrassCurve ℚ_[p] ↦ V.toAffine.Point) (baseChange_shortQ a b)

/-- **Openness**: for $\ell \ge 1$, the points of $E(\mathbb Q_p)$ with $\|x\|$ large are in $\ell E(\mathbb Q_p)$. -/
theorem exists_nsmul_eq_of_lt_norm (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ N : ℝ, ∀ (x y : ℚ_[p]) (h : ((shortQ a b).toAffine⁄ℚ_[p]).Nonsingular x y), N < ‖x‖ →
      ∃ Q : ((shortQ a b).toAffine⁄ℚ_[p]).Point, ℓ • Q = Point.some x y h := by
  have hℓ0 : ((ℓ : ℤ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hpos : 0 < ‖((ℓ : ℤ) : ℚ_[p])‖ ^ 4 := by positivity
  have hΔp : 4 * (a : ℤ_[p]) ^ 3 + 27 * (b : ℤ_[p]) ^ 2 ≠ 0 := by
    intro h0; apply hΔ
    exact_mod_cast (show (((4 * a ^ 3 + 27 * b ^ 2 : ℤ)) : ℤ_[p]) = 0 by push_cast; exact h0)
  refine ⟨(‖((ℓ : ℤ) : ℚ_[p])‖ ^ 4)⁻¹, fun x y h hN => ?_⟩
  have hx : 1 < ‖x‖ * ‖((ℓ : ℤ) : ℚ_[p])‖ ^ 4 := by
    calc (1 : ℝ) = (‖((ℓ : ℤ) : ℚ_[p])‖ ^ 4)⁻¹ * ‖((ℓ : ℤ) : ℚ_[p])‖ ^ 4 :=
          (inv_mul_cancel₀ hpos.ne').symm
      _ < ‖x‖ * ‖((ℓ : ℤ) : ℚ_[p])‖ ^ 4 := mul_lt_mul_of_pos_right hN hpos
  have h' : (II.curveQp (a : ℤ_[p]) (b : ℤ_[p])).toAffine.Nonsingular x y := baseChange_shortQ (p := p) a b ▸ h
  obtain ⟨Q', -, hQ'⟩ := II.exists_zsmul_eq_of_norm (a : ℤ_[p]) (b : ℤ_[p]) hΔp
    (by exact_mod_cast hℓ.ne') h' hx
  have he : shortQPointEquiv a b (Point.some x y h) = Point.some x y h' := by
    rw [shortQPointEquiv, AddEquiv.cast_apply]
    exact Affine.Point.cast_some (baseChange_shortQ (p := p) a b) h
  refine ⟨(shortQPointEquiv a b).symm Q', ?_⟩
  rw [← map_nsmul, ← natCast_zsmul, hQ', ← he, AddEquiv.symm_apply_apply]

/-- Kummer approximation over $\mathbb Q_p$ for $y^2 = x^3 + ax + b$, $a, b \in \mathbb Z$. -/
theorem kummerApprox_shortQ (a b : ℤ) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    KummerApprox (shortQ a b) ℚ_[p] ℓ := by
  rw [kummerApprox_iff]
  intro R
  obtain ⟨N, hN⟩ := exists_nsmul_eq_of_lt_norm (p := p) a b hΔ ℓ hℓ
  have hΔ' : 4 * (a : ℚ) ^ 3 + 27 * (b : ℚ) ^ 2 ≠ 0 := by exact_mod_cast hΔ
  obtain ⟨T, hT, hRT⟩ := exists_isAlgPoint_sub_large_padic (a : ℚ) (b : ℚ) hΔ' R N
  rcases hRT with h0 | ⟨x, y, h, hxy, hx⟩
  · exact ⟨0, T, hT, by rw [smul_zero, zero_add]; exact sub_eq_zero.1 h0⟩
  · obtain ⟨Q, hQ⟩ := hN x y h hx
    refine ⟨Q, T, hT, ?_⟩
    rw [hQ, ← hxy, sub_add_cancel]

end Padic

/-! ## Transport along a change of variables -/

section VariableChange

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K) (Kv : Type) [Field Kv] [Algebra K Kv]

/-- **Transport of `KummerApprox` along a change of variables over $K$.** -/
theorem kummerApprox_of_variableChange (C : VariableChange K) (n : ℕ) (h : KummerApprox (C • W) Kv n) :
    KummerApprox W Kv n := by
  rw [kummerApprox_iff] at h ⊢
  intro R
  let φ := W.pointEquivVariableChange Kv C
  obtain ⟨S, T, hT, hR⟩ := h (φ.symm R)
  refine ⟨φ S, φ T, ?_, ?_⟩
  · rcases T with _ | ⟨x, y, hxy⟩
    · change IsAlgPoint W Kv (φ 0)
      rw [map_zero]
      exact isAlgPoint_zero W Kv
    · have hx := isAlgebraic_iff_isIntegral.1 hT.1
      have hy := isAlgebraic_iff_isIntegral.1 hT.2
      have hc : ∀ c : K, IsIntegral K (algebraMap K Kv c) := fun c => isIntegral_algebraMap
      change IsAlgPoint W Kv (W.pointEquivVariableChange Kv C (Point.some x y hxy))
      rw [pointEquivVariableChange_some]
      simp only [VariableChange.baseChange, VariableChange.map]
      refine ⟨isAlgebraic_iff_isIntegral.2 ?_, isAlgebraic_iff_isIntegral.2 ?_⟩
      · exact ((hc _).pow 2 |>.mul hx).add (hc _)
      · exact (((hc _).pow 3 |>.mul hy).add (((hc _).pow 2 |>.mul (hc _)).mul hx)).add (hc _)
  · rw [← map_nsmul, ← map_add, ← hR, AddEquiv.apply_symm_apply]

end VariableChange

/-- Every elliptic curve over $\mathbb Q$ is isomorphic over $\mathbb Q$ to $y^2 = x^3 + ax + b$ with
$a, b \in \mathbb Z$, $4a^3 + 27b^2 \ne 0$. -/
theorem exists_variableChange_shortQ (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ (C : VariableChange ℚ) (a b : ℤ), C • E = shortQ a b ∧ 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 := by
  obtain ⟨C, a, b, hC⟩ := theorem_2_1_a E
  set d : ℚ := ((a.den * b.den : ℕ) : ℚ) with hd
  have hd0 : d ≠ 0 := by rw [hd]; positivity
  set A : ℤ := a.num * a.den ^ 3 * b.den ^ 4 with hA
  set B : ℤ := b.num * b.den ^ 5 * a.den ^ 6 with hB
  have hAa : (A : ℚ) = d ^ 4 * a := by
    have : (a.den : ℚ) ≠ 0 := by positivity
    rw [hA, hd]; push_cast
    nth_rewrite 4 [← Rat.num_div_den a]
    field_simp
  have hBb : (B : ℚ) = d ^ 6 * b := by
    have : (b.den : ℚ) ≠ 0 := by positivity
    rw [hB, hd]; push_cast
    nth_rewrite 4 [← Rat.num_div_den b]
    field_simp
  let C' : VariableChange ℚ := ⟨Units.mk0 d⁻¹ (inv_ne_zero hd0), 0, 0, 0⟩
  have hC' : C' • shortCurve a b = shortQ A B := by
    ext <;> simp [C', shortCurve, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, hAa, hBb]
  have hE : (C' * C) • E = shortQ A B := by rw [mul_smul, hC, hC']
  refine ⟨C' * C, A, B, hE, ?_⟩
  have hell : (shortQ A B).IsElliptic := hE ▸ inferInstance
  have hΔ := hell.isUnit.ne_zero
  rw [Δ_shortCurve] at hΔ
  intro h0
  apply hΔ
  have : (4 * (A : ℚ) ^ 3 + 27 * (B : ℚ) ^ 2) = 0 := by exact_mod_cast h0
  rw [this, mul_zero]

/-- Kummer approximation over $\mathbb Q_p$, every elliptic curve over $\mathbb Q$, every $\ell \ge 1$. -/
theorem kummerApprox_padic (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (hℓ : 0 < ℓ) :
    KummerApprox E ℚ_[p] ℓ := by
  obtain ⟨C, a, b, hC, hΔ⟩ := exists_variableChange_shortQ E
  refine kummerApprox_of_variableChange E ℚ_[p] C ℓ ?_
  rw [hC]
  exact kummerApprox_shortQ a b hΔ ℓ hℓ

/-! ## Assembly and the main results -/

section Assembly

attribute [-instance] DivisionRing.toRatAlgebra

/-- **`FiniteKummerPrime` holds.** -/
theorem finiteKummerPrime : FiniteKummerPrime := by
  refine ⟨fun E _ v ℓ hℓ => ?_⟩
  have : Fact (Rat.HeightOneSpectrum.primesEquiv v : ℕ).Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  letI : Algebra ℚ ℚ_[Rat.HeightOneSpectrum.primesEquiv v] := DivisionRing.toRatAlgebra
  let e : v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[Rat.HeightOneSpectrum.primesEquiv v] :=
    AlgEquiv.ofRingEquiv (f := (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toRingEquiv) fun q => by
      rw [eq_ratCast (algebraMap ℚ _), map_ratCast, eq_ratCast]
  exact kummerApprox_of_algEquiv E e ℓ (kummerApprox_padic E _ ℓ hℓ.pos)

/-- **Local injectivity at every place of $\mathbb Q$**, unconditionally. -/
theorem localPointsInjective : LocalPointsInjective :=
  localPointsInjective_of_finiteKummerPrime finiteKummerPrime

/-- **The comparison of the Tate–Shafarevich groups**, unconditionally. -/
theorem shaComparison : ShaComparison :=
  shaComparison_of_localPointsInjective localPointsInjective

end Assembly

section BSD

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **Conjecture IV.10.5 (corrected normalization) is Formal Conjectures' `StrongBSD` over $\mathbb Q$** for a
minimal equation, with no named input (Mordell–Weil is `mordell_weil_rat`). -/
theorem conjecture10_5Corrected_iff_strongBSD_unconditional (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    Conjecture10_5Corrected E ↔ FormalConjectures.StrongBSD E.toAffine :=
  conjecture10_5Corrected_iff_strongBSD_of_finiteKummerPrime E finiteKummerPrime hmin

/-- **In rank $0$, Conjecture IV.10.5 as printed is `StrongBSD`**, with no named input. -/
theorem conjecture10_5_iff_strongBSD_of_rank_eq_zero_unconditional (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    rank E = 0 → (Conjecture10_5 E ↔ FormalConjectures.StrongBSD E.toAffine) :=
  conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_finiteKummerPrime E finiteKummerPrime hmin

/-- **In positive rank, `StrongBSD` refutes Conjecture IV.10.5 as printed**, with no named input. -/
theorem not_conjecture10_5_of_strongBSD_unconditional (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    0 < rank E → FormalConjectures.StrongBSD E.toAffine → ¬ Conjecture10_5 E :=
  not_conjecture10_5_of_strongBSD_of_finiteKummerPrime E finiteKummerPrime hmin

end BSD

end NumberFieldKB.MilneEC
