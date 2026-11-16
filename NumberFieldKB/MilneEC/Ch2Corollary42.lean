import Mathlib.Algebra.Polynomial.SpecificDegree
import NumberFieldKB.MilneEC.Ch2Padic
import NumberFieldKB.MilneEC.Ch4Lemma21

/-!
# Milne, *Elliptic Curves*, Chapter II, Corollary 4.2: multiplication by $m$ on $E^1(\mathbb Q_p)$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter II, Corollary 4.2 (pdf p. 71): for an integer $m$
not divisible by $p$, $P \mapsto mP$ is a bijection $E^1(\mathbb Q_p) \to E^1(\mathbb Q_p)$.  Injectivity is
`corollary_4_2_injective` (`Ch2Padic.lean`).

**Surjectivity, by a different argument from Milne's.**  Milne sums a convergent series in the compact group
$E(\mathbb Q_p)$.  Here, for $P = (x_P, y_P) \in E^1(\mathbb Q_p)$, $P \ne O$:
1. (`exists_x_of_hensel`) put $s = 1/x_P \in p\mathbb Z_p$ and $N = m^2$; the polynomial
   $h(u) = s\,u^N\Phi_m(1/u) - u^N\Psi_m^2(1/u) \in \mathbb Z_p[u]$ has $h(0) = s$ and $h'(0) \equiv -m^2$, a unit, so by
   Hensel's lemma it has a root $u_0$ with $0 < \|u_0\| < 1$; then $x_1 = 1/u_0$ satisfies
   $\Phi_m(x_1) = x_P\,\Psi_m^2(x_1)$ and $\|x_1\| > 1$;
2. (`exists_y_of_x`) a point $Q = (x_1, y_1)$ over $\mathbb Q_p(y_1)$ has $x(mQ) = x_P$ by the division-polynomial
   formula, so $mQ = \pm P$; if $y_1 \notin \mathbb Q_p$, the conjugation $y_1 \mapsto -y_1$ sends $Q$ to $-Q$ and fixes
   $mQ$, so $2P = O$, impossible since $E^1(\mathbb Q_p)$ is torsion-free (`proposition_5_4`).  Hence $y_1 \in \mathbb Q_p$;
3. (`corollary_4_2`) $Q \in E^1(\mathbb Q_p)$ and $mQ = P$ or $m(-Q) = P$.
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve Polynomial

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- The short Weierstrass curve $Y^2 = X^3 + aX + b$ over $\mathbb Z_p$ (helper for the Hensel step). -/
noncomputable def shortZp (a b : ℤ_[p]) : WeierstrassCurve ℤ_[p] := ⟨0, 0, 0, a, b⟩

/-- `curveQp a b` is the base change of `shortZp a b` from $\mathbb Z_p$ to $\mathbb Q_p$. -/
lemma curveQp_eq_map (a b : ℤ_[p]) :
    curveQp a b = (shortZp a b).map (algebraMap ℤ_[p] ℚ_[p]) := by
  ext <;> simp [shortCurve, shortZp]

/-- Step 1 (Hensel): for $\|x_P\| > 1$ and $p \nmid m$ there is $x_1 \in \mathbb Q_p$ with $\|x_1\| > 1$ and
$\Phi_m(x_1) = x_P\,\Psi_m^2(x_1)$. -/
theorem exists_x_of_hensel (a b : ℤ_[p]) {m : ℤ} (hm : ¬(p : ℤ) ∣ m) {xP : ℚ_[p]} (hx : 1 < ‖xP‖) :
    ∃ x₁ : ℚ_[p], 1 < ‖x₁‖ ∧ ((curveQp a b).Φ m).eval x₁ = xP * ((curveQp a b).ΨSq m).eval x₁ := by
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
  have hxP0 : xP ≠ 0 := by rintro rfl; rw [norm_zero] at hx; linarith
  set W₀ := shortZp a b with hW₀
  set N := m.natAbs ^ 2 with hN
  have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (Int.natAbs_pos.2 hm0)
  have hsn : ‖xP⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hx.le
  set s : ℤ_[p] := ⟨xP⁻¹, hsn⟩ with hs
  have hs_lt : ‖s‖ < 1 := by
    show ‖xP⁻¹‖ < 1
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hx
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
  have hmn : ‖(m : ℤ_[p])‖ = 1 :=
    le_antisymm (PadicInt.norm_le_one _) (not_lt.1 (by rwa [PadicInt.norm_int_lt_one_iff_dvd]))
  have hd : ‖h.derivative.aeval (0 : ℤ_[p])‖ = 1 := by
    rw [aeval_def, eval₂_at_zero]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, coeff_derivative, Nat.cast_zero, zero_add,
      mul_one, h1]
    have e1 : ‖s * Φ₀.coeff (N - 1)‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)) hs_lt
    have e2 : ‖-((m : ℤ_[p]) ^ 2)‖ = 1 := by rw [norm_neg, norm_pow, hmn, one_pow]
    rw [sub_eq_add_neg, PadicInt.norm_add_eq_max_of_ne
      (q := s * Φ₀.coeff (N - 1)) (r := -((m : ℤ_[p]) ^ 2)) (by rw [e2]; exact e1.ne), e2]
    exact max_eq_right e1.le
  have hev : ‖h.aeval (0 : ℤ_[p])‖ < ‖h.derivative.aeval (0 : ℤ_[p])‖ ^ 2 := by
    rw [hd, aeval_def, eval₂_at_zero]
    simpa [h0] using hs_lt
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
      simpa using this
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

/-- Core of Step 2: over an extension $K$ carrying an automorphism $\sigma$ with $\sigma r = -r$ and
$r^2 = x_1^3 + ax_1 + b$, the existence of a point $P \ne$ 2-torsion with $\Phi_m(x_1) = x_P\Psi_m^2(x_1)$ is
contradictory. -/
theorem key_aux {F K : Type*} [Field F] [DecidableEq F] [Field K] [Algebra F K] (a b : F)
    (hΔ : (shortCurve a b).Δ ≠ 0) {m : ℤ} {xP yP : F}
    (hP : (shortCurve a b).toAffine.Nonsingular xP yP)
    (h2 : (2 : ℕ) • Affine.Point.some xP yP hP ≠ 0) {x₁ : F}
    (h₁ : ((shortCurve a b).Φ m).eval x₁ = xP * ((shortCurve a b).ΨSq m).eval x₁)
    (σ : K →ₐ[F] K) (r : K)
    (hr : r ^ 2 = algebraMap F K x₁ ^ 3 + algebraMap F K a * algebraMap F K x₁ + algebraMap F K b)
    (hσ : σ r = -r) : False := by
  classical
  set ι := algebraMap F K with hι
  have hι0 : Function.Injective ι := (algebraMap F K).injective
  set WK := (shortCurve a b).baseChange K with hWK
  have hΔK : WK.Δ ≠ 0 := by
    rw [hWK, WeierstrassCurve.baseChange, map_Δ]
    exact (map_ne_zero_iff _ hι0).2 hΔ
  have hEq : WK.toAffine.Equation (ι x₁) r := by
    rw [Affine.equation_iff]
    simp [hWK, WeierstrassCurve.baseChange, shortCurve]
    linear_combination hr
  have hnsQ := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔK).1 hEq
  have hΨ : ((shortCurve a b).ΨSq m).eval x₁ ≠ 0 := by
    intro h0
    have hΦ : ((shortCurve a b).Φ m).eval x₁ = 0 := by rw [h₁, h0, mul_zero]
    obtain ⟨u, v, huv⟩ := (shortCurve a b).isCoprime_Φ_ΨSq m hΔ
    have := congrArg (eval x₁) huv
    simp [hΦ, h0] at this
  have hΨK : (WK.ΨSq m).eval (ι x₁) ≠ 0 := by
    rw [hWK, WeierstrassCurve.baseChange, map_ΨSq, eval_map, eval₂_at_apply]
    exact (map_ne_zero_iff _ hι0).2 hΨ
  have hΦK : (WK.Φ m).eval (ι x₁) = ι xP * (WK.ΨSq m).eval (ι x₁) := by
    rw [hWK, WeierstrassCurve.baseChange, map_ΨSq, map_Φ, eval_map, eval_map, eval₂_at_apply,
      eval₂_at_apply, h₁, map_mul]
  have hsq : (WK.ψ m).evalEval (ι x₁) r ^ 2 = (WK.ΨSq m).eval (ι x₁) := by
    rw [evalEval_ψ_eq_evalEval_Ψ WK hEq m, evalEval_Ψ_sq_eq_eval_ΨSq WK hEq m]
  have hψ : (WK.ψ m).evalEval (ι x₁) r ≠ 0 := fun h0 => hΨK (by rw [← hsq, h0]; ring)
  obtain ⟨h', heq⟩ := zsmul_some_eq_of_evalEval_ψ_ne_zero WK hnsQ m hψ
  have hx : (WK.φ m).evalEval (ι x₁) r / (WK.ψ m).evalEval (ι x₁) r ^ 2 = ι xP := by
    rw [evalEval_φ_eq_eval_Φ WK hEq m, hsq, div_eq_iff hΨK, hΦK]
  set P := Affine.Point.some xP yP hP with hPdef
  set PK := Affine.Point.baseChange (W' := (shortCurve a b).toAffine) F K P with hPK
  have hPKns : WK.toAffine.Nonsingular (ι xP) (ι yP) :=
    (Affine.baseChange_nonsingular (W := (shortCurve a b).toAffine) (B := K)
        (f := Algebra.ofId F K) hι0 xP yP).2 hP
  have hPKs : PK = Affine.Point.some (ι xP) (ι yP) hPKns := rfl
  set Q := Affine.Point.some (ι x₁) r hnsQ with hQdef
  have hmQ : m • Q = PK ∨ m • Q = -PK := by
    rw [hQdef, heq, hPKs, Affine.Point.neg_some]
    rcases Affine.Y_eq_of_X_eq h'.1 hPKns.1 hx with hy | hy
    · left; simp only [Affine.Point.some.injEq]; exact ⟨hx, hy⟩
    · right; simp only [Affine.Point.some.injEq]; exact ⟨hx, hy⟩
  have hσQ : Affine.Point.map (W' := (shortCurve a b).toAffine) σ Q = -Q := by
    rw [hQdef, Affine.Point.map_some, Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    refine ⟨AlgHom.commutes σ x₁, ?_⟩
    simp [Affine.negY, hWK, WeierstrassCurve.baseChange, shortCurve, hσ]
  have hσPK : Affine.Point.map (W' := (shortCurve a b).toAffine) σ PK = PK :=
    Affine.Point.map_baseChange (W' := (shortCurve a b).toAffine) σ P
  have hneg : PK = -PK := by
    have h1 : Affine.Point.map (W' := (shortCurve a b).toAffine) σ (m • Q) = -(m • Q) := by
      rw [map_zsmul, hσQ, smul_neg]
    rcases hmQ with h | h
    · rw [h, hσPK] at h1; exact h1
    · rw [h, map_neg, hσPK, neg_neg] at h1; exact h1.symm
  apply h2
  have h3 : (2 : ℕ) • PK = 0 := by
    rw [two_nsmul]; nth_rewrite 1 [hneg]; exact neg_add_cancel _
  have h4 : Affine.Point.baseChange (W' := (shortCurve a b).toAffine) F K (2 • P) = 0 :=
    (map_nsmul (Affine.Point.baseChange (W' := (shortCurve a b).toAffine) F K) 2 P).trans h3
  exact Affine.Point.map_injective (W' := (shortCurve a b).toAffine) (f := Algebra.ofId F K)
    (h4.trans (map_zero _).symm)

/-- Step 2 over a general field: if $P$ is not 2-torsion and $\Phi_m(x_1) = x_P\Psi_m^2(x_1)$, then
$x_1^3 + ax_1 + b$ is a square (adjoin a square root and use the conjugation). -/
theorem exists_y_aux {F : Type*} [Field F] [DecidableEq F] (a b : F)
    (hΔ : (shortCurve a b).Δ ≠ 0) {m : ℤ} {xP yP : F}
    (hP : (shortCurve a b).toAffine.Nonsingular xP yP)
    (h2 : (2 : ℕ) • Affine.Point.some xP yP hP ≠ 0) {x₁ : F}
    (h₁ : ((shortCurve a b).Φ m).eval x₁ = xP * ((shortCurve a b).ΨSq m).eval x₁) :
    ∃ y : F, (shortCurve a b).toAffine.Equation x₁ y := by
  classical
  by_contra hno
  push Not at hno
  set c : F := x₁ ^ 3 + a * x₁ + b with hcdef
  have hc : ∀ y : F, y ^ 2 ≠ c := fun y hy =>
    hno y ((Affine.equation_iff _ _).2 (by simp [shortCurve]; linear_combination hy))
  have firr : Irreducible (X ^ 2 - C c : F[X]) :=
    irreducible_of_degree_le_three_of_not_isRoot
      (by rw [natDegree_X_pow_sub_C]; simp) (fun y hy => hc y (by simpa [sub_eq_zero] using hy))
  have : Fact (Irreducible (X ^ 2 - C c : F[X])) := ⟨firr⟩
  have hroot : (AdjoinRoot.root (X ^ 2 - C c : F[X])) ^ 2 =
      algebraMap F (AdjoinRoot (X ^ 2 - C c : F[X])) c := by
    have := AdjoinRoot.eval₂_root (X ^ 2 - C c : F[X])
    simpa [sub_eq_zero, AdjoinRoot.algebraMap_eq] using this
  refine key_aux (K := AdjoinRoot (X ^ 2 - C c : F[X])) a b hΔ hP h2 h₁
    (AdjoinRoot.liftAlgHom (X ^ 2 - C c : F[X]) (Algebra.ofId F _) (-AdjoinRoot.root _) ?_)
    (AdjoinRoot.root _) ?_ ?_
  · simp [hroot]
  · rw [hroot]; simp [hcdef]
  · simp

/-- The discriminant of `curveQp a b` is nonzero when $4a^3 + 27b^2 \ne 0$. -/
lemma curveQp_Δ_ne_zero (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) : (curveQp a b).Δ ≠ 0 := by
  show (shortCurve (a : ℚ_[p]) (b : ℚ_[p])).Δ ≠ 0
  rw [Δ_shortCurve]
  refine mul_ne_zero (by norm_num) fun h => hΔ ?_
  have : (((4 * a ^ 3 + 27 * b ^ 2 : ℤ_[p])) : ℚ_[p]) = 0 := by push_cast; exact h
  exact Subtype.ext this

/-- Step 2: a solution $x_1$ of $\Phi_m(x_1) = x_P\,\Psi_m^2(x_1)$, for a nonzero point $P = (x_P, y_P)$ of
$E^1(\mathbb Q_p)$, is the $x$-coordinate of a point of $E(\mathbb Q_p)$. -/
theorem exists_y_of_x (a b : ℤ_[p]) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {m : ℤ} (hm0 : m ≠ 0) {xP yP : ℚ_[p]}
    (hP : (curveQp a b).toAffine.Nonsingular xP yP) (hx : 1 < ‖xP‖) {x₁ : ℚ_[p]}
    (h₁ : ((curveQp a b).Φ m).eval x₁ = xP * ((curveQp a b).ΨSq m).eval x₁) :
    ∃ y₁ : ℚ_[p], (curveQp a b).toAffine.Equation x₁ y₁ := by
  refine exists_y_aux (a : ℚ_[p]) (b : ℚ_[p]) (curveQp_Δ_ne_zero a b hΔ) hP ?_ h₁
  intro h2
  have hE : (Affine.Point.some xP yP hP : (curveQp a b).toAffine.Point) ∈ E1 a b :=
    (mem_E1_iff _).2 (Or.inr ⟨xP, yP, hP, rfl, hx⟩)
  exact Affine.Point.some_ne_zero hP (proposition_5_4 a b hΔ hE (m := 2) (by norm_num) h2)

/-- If $x(Q) = x_1$ satisfies $\Phi_m(x_1) = x_P\Psi_m^2(x_1)$, then $mQ = P$ or $m(-Q) = P$. -/
theorem smul_eq_of_eval {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0)
    {m : ℤ} {xP yP : F} (hP : W.toAffine.Nonsingular xP yP) {x₁ y₁ : F}
    (hQ : W.toAffine.Nonsingular x₁ y₁)
    (h₁ : (W.Φ m).eval x₁ = xP * (W.ΨSq m).eval x₁) :
    m • Affine.Point.some x₁ y₁ hQ = Affine.Point.some xP yP hP ∨
      m • -Affine.Point.some x₁ y₁ hQ = Affine.Point.some xP yP hP := by
  have hy₁ : W.toAffine.Equation x₁ y₁ := hQ.1
  have hΨ : (W.ΨSq m).eval x₁ ≠ 0 := by
    intro h0
    have hΦ : (W.Φ m).eval x₁ = 0 := by rw [h₁, h0, mul_zero]
    obtain ⟨u, v, huv⟩ := W.isCoprime_Φ_ΨSq m hΔ
    have := congrArg (eval x₁) huv
    simp [hΦ, h0] at this
  have hsq : (W.ψ m).evalEval x₁ y₁ ^ 2 = (W.ΨSq m).eval x₁ := by
    rw [evalEval_ψ_eq_evalEval_Ψ W hy₁ m, evalEval_Ψ_sq_eq_eval_ΨSq W hy₁ m]
  have hψ : (W.ψ m).evalEval x₁ y₁ ≠ 0 := fun h0 => hΨ (by rw [← hsq, h0]; ring)
  obtain ⟨h', heq⟩ := zsmul_some_eq_of_evalEval_ψ_ne_zero W hQ m hψ
  have hx : (W.φ m).evalEval x₁ y₁ / (W.ψ m).evalEval x₁ y₁ ^ 2 = xP := by
    rw [evalEval_φ_eq_eval_Φ W hy₁ m, hsq, div_eq_iff hΨ, h₁]
  rcases Affine.Y_eq_of_X_eq h'.1 hP.1 hx with hy | hy
  · left
    rw [heq]
    simp only [Affine.Point.some.injEq]
    exact ⟨hx, hy⟩
  · right
    rw [smul_neg, heq, Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    refine ⟨hx, ?_⟩
    rw [hy, hx, Affine.negY_negY]

/-- **Corollary 4.2** (Milne, pdf p. 71): for $p \nmid m$, $P \mapsto mP$ is a bijection
$E^1(\mathbb Q_p) \to E^1(\mathbb Q_p)$.  Surjectivity by Hensel's lemma on the division polynomials (see the module
docstring), injectivity is `corollary_4_2_injective`. -/
@[kb "milne2006ec" "Ch. II, Corollary 4.2, pdf p. 71"]
theorem corollary_4_2 : Corollary4_2 where
  bij p _ a b hΔ m hm := by
    have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero _)
    have hmem : ∀ P : (curveQp a b).toAffine.Point, P ∈ E1 a b ↔ P ∈ EnSubgroup a b 1 le_rfl := by
      intro P
      change P ∈ E1 a b ↔ P ∈ En a b 1
      rw [En_one]
    refine ⟨?_, ?_, ?_⟩
    · intro P hP
      exact (hmem _).2 ((EnSubgroup a b 1 le_rfl).zsmul_mem ((hmem _).1 hP) m)
    · intro P hP Q hQ h
      have h0 : m • (P - Q) = 0 := by
        have h' : m • P = m • Q := h
        rw [zsmul_sub, sub_eq_zero]; exact h'
      have hPQ : P - Q ∈ E1 a b :=
        (hmem _).2 ((EnSubgroup a b 1 le_rfl).sub_mem ((hmem _).1 hP) ((hmem _).1 hQ))
      exact sub_eq_zero.1 (corollary_4_2_injective a b hΔ hm hPQ h0)
    · intro P hP
      rcases (mem_E1_iff P).1 hP with rfl | ⟨xP, yP, hPns, rfl, hx⟩
      · exact ⟨0, (mem_E1_iff _).2 (Or.inl rfl), zsmul_zero m⟩
      · obtain ⟨x₁, hx₁, h₁⟩ := exists_x_of_hensel a b hm hx
        obtain ⟨y₁, hy₁⟩ := exists_y_of_x a b hΔ hm0 hPns hx h₁
        have hQ : (curveQp a b).toAffine.Nonsingular x₁ y₁ :=
          (Affine.equation_iff_nonsingular_of_Δ_ne_zero (curveQp_Δ_ne_zero a b hΔ)).1 hy₁
        have hQ1 : (Affine.Point.some x₁ y₁ hQ : (curveQp a b).toAffine.Point) ∈ E1 a b :=
          (mem_E1_iff _).2 (Or.inr ⟨x₁, y₁, hQ, rfl, hx₁⟩)
        rcases smul_eq_of_eval (curveQp a b) (curveQp_Δ_ne_zero a b hΔ) hPns hQ h₁ with h | h
        · exact ⟨_, hQ1, h⟩
        · exact ⟨_, neg_mem_E1 hQ1, h⟩

end NumberFieldKB.MilneEC.II
