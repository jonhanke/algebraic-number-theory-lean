import NumberFieldKB.MilneEC.Ch4ValuedGeneral
import NumberFieldKB.MilneEC.Ch4DivPointsAux

/-!
# General Weierstrass models over a Henselian valuation ring: surjectivity, injectivity on the kernel

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter II §4 (Theorem 4.1 (b), Corollary 4.2,
pdf pp. 69-71) and Chapter IV, Lemma 3.2 (pdf p. 119).  Continuation of `Ch4ValuedGeneral.lean` (port of
`Ch4ValuedShort.lean` / `Ch4DivPointsAux.lean` to general models).

* `redPt_surjective`: reduction is onto when $R$ is Henselian (Hensel's lemma in $x$ if
  $\partial F/\partial X \not\equiv 0$, in $y$ if $\partial F/\partial Y \not\equiv 0$; the reduced point is
  nonsingular so one of them holds).
* `eq_zero_of_zsmul_eq_zero`: the kernel of reduction has no $n$-torsion for $n$ a unit.
* `key_fixed`: an automorphism trivial on the residue field fixes $Q$ whenever $nQ = P$ is fixed.
* `exists_x_of_hensel_valued`: Hensel step in $x$ for the division polynomials.
-/

namespace NumberFieldKB.MilneEC.II.ValuedGen

open WeierstrassCurve Polynomial IsLocalRing
open NumberFieldKB.MilneEC.II.Valued (IsInt liftInt ι_inj ι_eq isInt_zero isInt_add isInt_mul isInt_neg
  isInt_sub isInt_pow exists_small liftInt_algebraMap isInt_algebraMap isInt_of_mul_unit isInt_of_root)

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {W : WeierstrassCurve R}

local notation "ι" => algebraMap R K

/-- **Theorem 4.1 (b)** over $R$, surjectivity (Hensel's lemma): every point of $\bar E(k)$ lifts. -/
theorem redPt_surjective [HenselianLocalRing R] (hΔ : IsUnit W.Δ) :
    Function.Surjective (redPt (K := K) W hΔ) := by
  intro A
  cases A with
  | zero => exact ⟨0, rfl⟩
  | some u v hA =>
    obtain ⟨X0, rfl⟩ := IsLocalRing.residue_surjective u
    obtain ⟨Y0, rfl⟩ := IsLocalRing.residue_surjective v
    obtain ⟨-, hns0⟩ := (Affine.nonsingular_iff' _ _).1 hA
    have hns : IsLocalRing.residue R W.a₁ * IsLocalRing.residue R Y0 -
        (3 * IsLocalRing.residue R X0 ^ 2 + 2 * IsLocalRing.residue R W.a₂ * IsLocalRing.residue R X0 +
          IsLocalRing.residue R W.a₄) ≠ 0 ∨
        2 * IsLocalRing.residue R Y0 + IsLocalRing.residue R W.a₁ * IsLocalRing.residue R X0 +
          IsLocalRing.residue R W.a₃ ≠ 0 := hns0
    have heqA : IsLocalRing.residue R Y0 ^ 2 + IsLocalRing.residue R W.a₁ * IsLocalRing.residue R X0 * IsLocalRing.residue R Y0 +
        IsLocalRing.residue R W.a₃ * IsLocalRing.residue R Y0 = IsLocalRing.residue R X0 ^ 3 + IsLocalRing.residue R W.a₂ * IsLocalRing.residue R X0 ^ 2 +
        IsLocalRing.residue R W.a₄ * IsLocalRing.residue R X0 + IsLocalRing.residue R W.a₆ := (Affine.equation_iff _ _).1 hA.1
    obtain ⟨X, Y, hXY, hXu, hYv⟩ : ∃ X Y : R, W.toAffine.Equation X Y ∧
        IsLocalRing.residue R X = IsLocalRing.residue R X0 ∧ IsLocalRing.residue R Y = IsLocalRing.residue R Y0 := by
      by_cases hc : IsUnit (3 * X0 ^ 2 + 2 * W.a₂ * X0 + (W.a₄ - W.a₁ * Y0))
      · let F : R[X] := Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
          Polynomial.C (W.a₄ - W.a₁ * Y0) * Polynomial.X + Polynomial.C (W.a₆ - Y0 ^ 2 - W.a₃ * Y0)
        have hF : F.Monic := by
          unfold F; monicity!
        have hFe : ∀ z : R, F.eval z = z ^ 3 + W.a₂ * z ^ 2 + (W.a₄ - W.a₁ * Y0) * z +
            (W.a₆ - Y0 ^ 2 - W.a₃ * Y0) := by
          intro z; simp [F]
        have hFd : ∀ z : R, F.derivative.eval z =
            3 * z ^ 2 + 2 * W.a₂ * z + (W.a₄ - W.a₁ * Y0) := by
          intro z; simp [F, derivative_pow]; ring
        obtain ⟨z, hz, hzx⟩ := HenselianLocalRing.is_henselian F hF X0
          (by
            rw [hFe, ← IsLocalRing.residue_eq_zero_iff]
            simp only [map_add, map_mul, map_pow, map_sub]
            linear_combination -heqA)
          (by rw [hFd]; exact hc)
        refine ⟨z, Y0, ?_, ?_, rfl⟩
        · have := hz.eq_zero
          rw [hFe] at this
          rw [Affine.equation_iff]
          linear_combination -this
        · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hzx
      · have hc' : IsUnit (2 * Y0 + (W.a₁ * X0 + W.a₃)) := by
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
          rcases hns with n | n
          · exfalso; apply hc; rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
            intro h0
            apply n
            simp only [map_add, map_mul, map_sub, map_pow, map_ofNat] at h0 ⊢
            linear_combination -h0
          · intro h0
            apply n
            simp only [map_add, map_mul, map_ofNat] at h0 ⊢
            linear_combination h0
        let F : R[X] := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * X0 + W.a₃) * Polynomial.X -
          Polynomial.C (X0 ^ 3 + W.a₂ * X0 ^ 2 + W.a₄ * X0 + W.a₆)
        have hF : F.Monic := by
          unfold F; monicity!
        have hFe : ∀ z : R, F.eval z = z ^ 2 + (W.a₁ * X0 + W.a₃) * z -
            (X0 ^ 3 + W.a₂ * X0 ^ 2 + W.a₄ * X0 + W.a₆) := by
          intro z; simp [F]
        have hFd : ∀ z : R, F.derivative.eval z = 2 * z + (W.a₁ * X0 + W.a₃) := by
          intro z; simp [F, derivative_pow]
        obtain ⟨z, hz, hzy⟩ := HenselianLocalRing.is_henselian F hF Y0
          (by
            rw [hFe, ← IsLocalRing.residue_eq_zero_iff]
            simp only [map_add, map_mul, map_pow, map_sub]
            linear_combination heqA)
          (by rw [hFd]; exact hc')
        refine ⟨X0, z, ?_, rfl, ?_⟩
        · have := hz.eq_zero
          rw [hFe] at this
          rw [Affine.equation_iff]
          linear_combination this
        · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hzy
    have hnsK : (curveK K W).toAffine.Nonsingular (ι X) (ι Y) :=
      (Affine.equation_iff_nonsingular_of_Δ_ne_zero (curveK_Δ_ne_zero W hΔ)).1
        (Affine.Equation.map (algebraMap R K) hXY)
    obtain ⟨hA', e⟩ := redPt_some_of_alg hΔ hnsK rfl rfl
    refine ⟨_, e.trans ?_⟩
    simp only [Affine.Point.some.injEq]
    exact ⟨hXu, hYv⟩

/-- **Corollary 4.2** over $R$, injectivity: for $n$ a unit of $R$, the kernel of reduction has no
$n$-torsion. -/
theorem eq_zero_of_zsmul_eq_zero (hΔ : IsUnit W.Δ) {n : ℤ} (hn : IsUnit (n : R))
    {P : (curveK K W).toAffine.Point} (hP : redPt W hΔ P = 0) (hnP : n • P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
    exfalso
    have hx := (redPt_eq_zero_iff hΔ _).1 hP x y hxy rfl
    have hψ : ((curveK K W).ψ n).evalEval x y = 0 := by
      by_contra hψ
      obtain ⟨h', heq⟩ := zsmul_some_eq_of_evalEval_ψ_ne_zero (curveK K W) hxy n hψ
      rw [hnP] at heq
      exact Affine.Point.some_ne_zero _ heq.symm
    have hΨ : ((curveK K W).ΨSq n).eval x = 0 := by
      rw [← evalEval_Ψ_sq_eq_eval_ΨSq _ hxy.1 n, ← evalEval_ψ_eq_evalEval_Ψ _ hxy.1 n, hψ]; ring
    apply hx
    refine isInt_of_root (W.ΨSq n) ?_ ?_
    · rw [W.leadingCoeff_ΨSq hn.ne_zero]; exact hn.pow 2
    · rw [← map_ΨSq]; exact hΨ

section Inertia

variable (σR : R →+* R) (σK : K →+* K)
  (hc : ∀ x, algebraMap R K (σR x) = σK (algebraMap R K x))
  (hin : ∀ x, σR x - x ∈ maximalIdeal R)

include hc hin

lemma redPt_some_map (hΔ : IsUnit W.Δ) {x y x' y' : K}
    (hxy : (curveK K W).toAffine.Nonsingular x y)
    (hxy' : (curveK K W).toAffine.Nonsingular x' y') (hx : x' = σK x) (hy : y' = σK y) :
    redPt W hΔ (Affine.Point.some x' y' hxy') = redPt W hΔ (Affine.Point.some x y hxy) := by
  by_cases hX : IsInt R x
  · obtain ⟨X, rfl⟩ := hX
    obtain ⟨Y, rfl⟩ := isInt_y W hxy.1 ⟨X, rfl⟩
    have hx' : algebraMap R K (σR X) = x' := by rw [hc, hx]
    have hy' : algebraMap R K (σR Y) = y' := by rw [hc, hy]
    obtain ⟨A1, e1⟩ := redPt_some_of_alg hΔ hxy rfl rfl
    obtain ⟨A2, e2⟩ := redPt_some_of_alg hΔ hxy' hx' hy'
    rw [e1, e2]
    have rX : IsLocalRing.residue R (σR X) = IsLocalRing.residue R X := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hin X
    have rY : IsLocalRing.residue R (σR Y) = IsLocalRing.residue R Y := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hin Y
    simp only [Affine.Point.some.injEq]
    exact ⟨rX, rY⟩
  · rw [redPt_some_of_not_isInt hΔ hxy hX,
      redPt_some_of_not_isInt hΔ hxy' (hx ▸ Valued.not_isInt_map σR σK hc hin hX)]

/-- If `σ` is trivial modulo the maximal ideal, `nQ = P` and `σP = P`, then `σQ = Q`
(`n` a unit, unit discriminant). -/
theorem key_fixed (hΔ : IsUnit W.Δ) {W' : WeierstrassCurve K} (e : W' = curveK K W)
    (φ : W'.toAffine.Point →+ W'.toAffine.Point)
    (hφ : ∀ x y (hxy : W'.toAffine.Nonsingular x y),
      ∃ hxy' : W'.toAffine.Nonsingular (σK x) (σK y), φ (.some x y hxy) = .some (σK x) (σK y) hxy')
    {n : ℤ} (hn : IsUnit (n : R)) (Q P : W'.toAffine.Point) (hQ : n • Q = P) (hP : φ P = P) :
    φ Q = Q := by
  subst e
  have h0 : redPt W hΔ (φ Q - Q) = 0 := by
    rw [← redHom_apply, map_sub, redHom_apply, redHom_apply, sub_eq_zero]
    cases Q with
    | zero =>
      rw [show (Affine.Point.zero : (curveK K W).toAffine.Point) = 0 from rfl, map_zero]
    | some x y hxy =>
      obtain ⟨hxy', e⟩ := hφ x y hxy
      rw [e]
      exact redPt_some_map σR σK hc hin hΔ hxy hxy' rfl rfl
  have h1 : n • (φ Q - Q) = 0 := by
    rw [smul_sub, ← map_zsmul, hQ, hP, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_zsmul_eq_zero hΔ hn h0 h1)

end Inertia

/-- Step 1 (Hensel): for `xP` not integral and `n` a unit there is `x₁` not integral with
`Φₙ(x₁) = xP Ψₙ²(x₁)`. -/
theorem exists_x_of_hensel_valued [HenselianLocalRing R] (W : WeierstrassCurve R) {n : ℤ}
    (hn : IsUnit (n : R)) {xP : K} (hx : ¬ IsInt R xP) :
    ∃ x₁ : K, ¬ IsInt R x₁ ∧
      ((curveK K W).Φ n).eval x₁ = xP * ((curveK K W).ΨSq n).eval x₁ := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨S, hS, hSx⟩ := exists_small hx
  have hxP0 : xP ≠ 0 := fun h0 => hx (h0 ▸ isInt_zero)
  have hS0 : S ≠ 0 := by
    rintro rfl; rw [map_zero, zero_mul] at hSx; exact zero_ne_one hSx
  set N := n.natAbs ^ 2 with hN
  have hNpos : 1 ≤ N := Nat.one_le_pow _ _ (Int.natAbs_pos.2 hn0)
  set Φ₀ := W.Φ n
  set Ψ₀ := W.ΨSq n
  set hh : R[X] := C S * reflect N Φ₀ - reflect N Ψ₀ with hhdef
  have hΦN : Φ₀.coeff N = 1 := W.coeff_Φ n
  have hΨdeg : Ψ₀.natDegree ≤ N - 1 := W.natDegree_ΨSq_le n
  have hΨN : Ψ₀.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have hΨ1 : Ψ₀.coeff (N - 1) = (n : R) ^ 2 := W.coeff_ΨSq n
  have hΦdeg : Φ₀.natDegree ≤ N := W.natDegree_Φ_le n
  have h0 : hh.coeff 0 = S := by
    simp [hhdef, coeff_reflect, hΦN, hΨN]
  have h1 : hh.coeff 1 = S * Φ₀.coeff (N - 1) - (n : R) ^ 2 := by
    simp [hhdef, coeff_reflect, revAt_le hNpos, hΨ1]
  have hunit : IsUnit (hh.derivative.eval 0) := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp only [Nat.cast_zero, zero_add, mul_one, h1]
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have : IsLocalRing.residue R S = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hS
    have hn' : IsLocalRing.residue R (n : R) ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hn
    simp only [map_sub, map_mul, map_pow, this, zero_mul, zero_sub, ne_eq, neg_eq_zero]
    exact pow_ne_zero 2 hn'
  have hev : hh.eval 0 ∈ maximalIdeal R := by
    rw [← coeff_zero_eq_eval_zero, h0]; exact hS
  obtain ⟨z, hz, hzm⟩ := Polynomial.exists_isRoot_sub_mem (J := maximalIdeal R) hh (a₀ := 0) hev
    (hunit.map (Ideal.Quotient.mk (maximalIdeal R)))
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hS0
    rw [← h0, coeff_zero_eq_eval_zero]
    exact hz.eq_zero
  have hzq : algebraMap R K z ≠ 0 := by
    intro h0'; exact hz0 (ι_eq (K := K) (by rw [h0', map_zero]))
  have hzm' : z ∈ maximalIdeal R := by simpa using hzm
  refine ⟨(algebraMap R K z)⁻¹, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    have : t * z = 1 := ι_eq (K := K) (by rw [map_mul, ht, map_one]; exact inv_mul_cancel₀ hzq)
    exact ((IsLocalRing.mem_maximalIdeal _).1 hzm') (IsUnit.of_mul_eq_one t (by rw [mul_comm]; exact this))
  · have hz' : eval₂ (algebraMap R K) (algebraMap R K z) hh = 0 := by
      rw [eval₂_at_apply, hz.eq_zero, map_zero]
    rw [hhdef, eval₂_sub, eval₂_mul, eval₂_C] at hz'
    let _ : Invertible ((algebraMap R K z)⁻¹) := invertibleOfNonzero (inv_ne_zero hzq)
    have hinv : ⅟((algebraMap R K z)⁻¹) = algebraMap R K z := by
      rw [invOf_eq_inv, inv_inv]
    have k1 := eval₂_reflect_mul_pow (algebraMap R K) ((algebraMap R K z)⁻¹) N Φ₀ hΦdeg
    have k2 := eval₂_reflect_mul_pow (algebraMap R K) ((algebraMap R K z)⁻¹) N Ψ₀ (by omega)
    rw [hinv] at k1 k2
    show ((W.map (algebraMap R K)).Φ n).eval _ = _ * ((W.map (algebraMap R K)).ΨSq n).eval _
    rw [map_Φ, map_ΨSq, eval_map, eval_map, ← k1, ← k2]
    have hsq : algebraMap R K S = xP⁻¹ := eq_inv_of_mul_eq_one_left hSx
    rw [hsq] at hz'
    generalize eval₂ (algebraMap R K) (algebraMap R K z) (reflect N Φ₀) = A at hz' ⊢
    generalize eval₂ (algebraMap R K) (algebraMap R K z) (reflect N Ψ₀) = B at hz' ⊢
    have hB : B = xP⁻¹ * A := by linear_combination (-1 : K) * hz'
    rw [hB]
    field_simp

end NumberFieldKB.MilneEC.II.ValuedGen
