import NumberFieldKB.MilneEC.Ch2Corollary42
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Chord-and-tangent and the `y`-step of Corollary 4.2 for a general Weierstrass model over a field

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter II §4 (pdf pp. 69-71) and Chapter IV, Lemma 3.2
(pdf p. 119).  This file ports the short-model field-level lemmas `add_some_eq`, `exists_slope`
(`Ch2Reduction.lean`) and `key_aux`, `exists_y_aux` (`Ch2Corollary42.lean`) from
$Y^2 = X^3 + aX + b$ to a general Weierstrass equation

$$Y^2 + a_1XY + a_3Y = X^3 + a_2X^2 + a_4X + a_6$$

over a field $k$.  The chord through $(x_1,y_1)$ and $(x_2,y_2)$ has slope $\ell$ with

* $\ell\,(x_1 - x_2) = y_1 - y_2$ and
* $\ell\,(y_1 + y_2 + a_1x_2 + a_3) = x_1^2 + x_1x_2 + x_2^2 + a_2(x_1+x_2) + a_4 - a_1y_1$,

and then $(x_1,y_1) + (x_2,y_2) = (\mathrm{addX}, \mathrm{addY})$ (Mathlib's formulas).
-/

namespace NumberFieldKB.MilneEC.II.ValuedGen

open WeierstrassCurve Polynomial

attribute [local instance] Classical.propDecidable

/-- The chord or tangent slope of two points that are not negatives of each other (general model). -/
lemma exists_slope_gen {k : Type*} [Field k] (W : WeierstrassCurve k) {x1 y1 x2 y2 : k}
    (e1 : W.toAffine.Equation x1 y1) (e2 : W.toAffine.Equation x2 y2)
    (hne : ¬(x1 = x2 ∧ y1 = W.toAffine.negY x2 y2)) :
    ∃ ℓ, ℓ * (x1 - x2) = y1 - y2 ∧
      ℓ * (y1 + y2 + W.a₁ * x2 + W.a₃) =
        x1 ^ 2 + x1 * x2 + x2 ^ 2 + W.a₂ * (x1 + x2) + W.a₄ - W.a₁ * y1 := by
  rw [Affine.equation_iff] at e1 e2
  by_cases hx : x1 = x2
  · subst hx
    have hy : y1 + y2 + W.a₁ * x1 + W.a₃ ≠ 0 := fun h =>
      hne ⟨rfl, by simp only [Affine.negY]; linear_combination h⟩
    have hyy : y1 = y2 := by
      have : (y1 - y2) * (y1 + y2 + W.a₁ * x1 + W.a₃) = 0 := by linear_combination e1 - e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hy)
    subst hyy
    exact ⟨(x1 ^ 2 + x1 * x1 + x1 ^ 2 + W.a₂ * (x1 + x1) + W.a₄ - W.a₁ * y1) /
      (y1 + y1 + W.a₁ * x1 + W.a₃), by ring, div_mul_cancel₀ _ hy⟩
  · have hd : x1 - x2 ≠ 0 := sub_ne_zero.2 hx
    refine ⟨(y1 - y2) / (x1 - x2), by field_simp, ?_⟩
    field_simp
    linear_combination e1 - e2

/-- Chord-and-tangent formula on a general Weierstrass curve for a slope given by two linear relations. -/
lemma add_some_eq_gen {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k)
    {x1 y1 x2 y2 ℓ : k} (h1 : W.toAffine.Nonsingular x1 y1) (h2 : W.toAffine.Nonsingular x2 y2)
    (hne : ¬(x1 = x2 ∧ y1 = W.toAffine.negY x2 y2)) (H1 : ℓ * (x1 - x2) = y1 - y2)
    (H2 : ℓ * (y1 + y2 + W.a₁ * x2 + W.a₃) =
      x1 ^ 2 + x1 * x2 + x2 ^ 2 + W.a₂ * (x1 + x2) + W.a₄ - W.a₁ * y1) :
    ∃ h3, Affine.Point.some x1 y1 h1 + Affine.Point.some x2 y2 h2 =
      Affine.Point.some (W.toAffine.addX x1 x2 ℓ) (W.toAffine.addY x1 x2 y1 ℓ) h3 := by
  have e1 := (Affine.equation_iff _ _).1 h1.1
  have hs : W.toAffine.slope x1 x2 y1 y2 = ℓ := by
    by_cases hx : x1 = x2
    · subst hx
      have hy : y1 ≠ W.toAffine.negY x1 y2 := fun h => hne ⟨rfl, h⟩
      have hyy : y1 = y2 := by
        rcases Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with h | h
        · exact h
        · exact absurd h hy
      subst hyy
      have h2y : y1 - W.toAffine.negY x1 y1 ≠ 0 := sub_ne_zero.2 hy
      rw [Affine.slope_of_Y_ne rfl hy, div_eq_iff h2y]
      simp only [Affine.negY] at h2y ⊢
      linear_combination (-1 : k) * H2
    · rw [Affine.slope_of_X_ne hx]
      field_simp [sub_ne_zero.2 hx]
      linear_combination (-1 : k) * H1
  have key := Affine.Point.add_some hne (h₁ := h1) (h₂ := h2)
  have hn := Affine.nonsingular_add h1 h2 hne
  simp only [hs] at key hn
  exact ⟨hn, key⟩

/-- Core of the `y`-step: over an extension `K` carrying an automorphism `σ` with `σ r = -r - (a₁x₁ + a₃)`
and `r² + (a₁x₁ + a₃) r = x₁³ + a₂x₁² + a₄x₁ + a₆`, the existence of a non-2-torsion point `P` with
`Φₘ(x₁) = x_P Ψₘ²(x₁)` is contradictory. -/
theorem key_aux_gen {F K : Type*} [Field F] [DecidableEq F] [Field K] [Algebra F K]
    (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) {m : ℤ} {xP yP : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (h2 : (2 : ℕ) • Affine.Point.some xP yP hP ≠ 0) {x₁ : F}
    (h₁ : (W.Φ m).eval x₁ = xP * (W.ΨSq m).eval x₁)
    (σ : K →ₐ[F] K) (r : K) (b c : F) (hb : b = W.a₁ * x₁ + W.a₃)
    (hc : c = x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆)
    (hr : r ^ 2 + algebraMap F K b * r = algebraMap F K c)
    (hσ : σ r = -r - algebraMap F K b) : False := by
  classical
  subst hb hc
  set ι := algebraMap F K with hι
  have hι0 : Function.Injective ι := (algebraMap F K).injective
  set WK := W.baseChange K with hWK
  have hΔK : WK.Δ ≠ 0 := by
    rw [hWK, WeierstrassCurve.baseChange, map_Δ]
    exact (map_ne_zero_iff _ hι0).2 hΔ
  have hEq : WK.toAffine.Equation (ι x₁) r := by
    rw [Affine.equation_iff]
    show r ^ 2 + ι W.a₁ * ι x₁ * r + ι W.a₃ * r = ι x₁ ^ 3 + ι W.a₂ * ι x₁ ^ 2 + ι W.a₄ * ι x₁ + ι W.a₆
    simp only [map_add, map_mul, map_pow] at hr
    linear_combination hr
  have hnsQ := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔK).1 hEq
  have hΨ : (W.ΨSq m).eval x₁ ≠ 0 := by
    intro h0
    have hΦ : (W.Φ m).eval x₁ = 0 := by rw [h₁, h0, mul_zero]
    obtain ⟨u, v, huv⟩ := W.isCoprime_Φ_ΨSq m hΔ
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
  set PK := Affine.Point.baseChange (W' := W.toAffine) F K P with hPK
  have hPKns : WK.toAffine.Nonsingular (ι xP) (ι yP) :=
    (Affine.baseChange_nonsingular (W := W.toAffine) (B := K)
        (f := Algebra.ofId F K) hι0 xP yP).2 hP
  have hPKs : PK = Affine.Point.some (ι xP) (ι yP) hPKns := rfl
  set Q := Affine.Point.some (ι x₁) r hnsQ with hQdef
  have hmQ : m • Q = PK ∨ m • Q = -PK := by
    rw [hQdef, heq, hPKs, Affine.Point.neg_some]
    rcases Affine.Y_eq_of_X_eq h'.1 hPKns.1 hx with hy | hy
    · left; simp only [Affine.Point.some.injEq]; exact ⟨hx, hy⟩
    · right; simp only [Affine.Point.some.injEq]; exact ⟨hx, hy⟩
  have hσQ : Affine.Point.map (W' := W.toAffine) σ Q = -Q := by
    rw [hQdef, Affine.Point.map_some, Affine.Point.neg_some]
    simp only [Affine.Point.some.injEq]
    refine ⟨AlgHom.commutes σ x₁, ?_⟩
    simp only [Affine.negY]
    show σ r = -r - ι W.a₁ * ι x₁ - ι W.a₃
    rw [hσ]
    simp only [map_add, map_mul]
    ring
  have hσPK : Affine.Point.map (W' := W.toAffine) σ PK = PK :=
    Affine.Point.map_baseChange (W' := W.toAffine) σ P
  have hneg : PK = -PK := by
    have h1 : Affine.Point.map (W' := W.toAffine) σ (m • Q) = -(m • Q) := by
      rw [map_zsmul, hσQ, smul_neg]
    rcases hmQ with h | h
    · rw [h, hσPK] at h1; exact h1
    · rw [h, map_neg, hσPK, neg_neg] at h1; exact h1.symm
  apply h2
  have h3 : (2 : ℕ) • PK = 0 := by
    rw [two_nsmul]; nth_rewrite 1 [hneg]; exact neg_add_cancel _
  have h4 : Affine.Point.baseChange (W' := W.toAffine) F K (2 • P) = 0 :=
    (map_nsmul (Affine.Point.baseChange (W' := W.toAffine) F K) 2 P).trans h3
  exact Affine.Point.map_injective (W' := W.toAffine) (f := Algebra.ofId F K)
    (h4.trans (map_zero _).symm)

/-- The monic quadratic `Y² + bY - c`. -/
noncomputable def quadPoly {F : Type*} [Field F] (b c : F) : F[X] := C 1 * X ^ 2 + C b * X + C (-c)

lemma natDegree_quadPoly {F : Type*} [Field F] (b c : F) : (quadPoly b c).natDegree = 2 :=
  natDegree_quadratic one_ne_zero

lemma eval_quadPoly {F : Type*} [Field F] (b c y : F) : (quadPoly b c).eval y = y ^ 2 + b * y - c := by
  simp [quadPoly, sub_eq_add_neg]

lemma eval₂_quadPoly {F S : Type*} [Field F] [CommRing S] (b c : F) (f : F →+* S) (z : S) :
    (quadPoly b c).eval₂ f z = z ^ 2 + f b * z - f c := by
  simp [quadPoly, sub_eq_add_neg]

/-- The `y`-step over a general field: if `P` is not 2-torsion and `Φₘ(x₁) = x_P Ψₘ²(x₁)`, then the quadratic
`Y² + (a₁x₁ + a₃)Y - (x₁³ + a₂x₁² + a₄x₁ + a₆)` has a root in `F` (otherwise adjoin a root and use the
conjugation `r ↦ -r - a₁x₁ - a₃`). -/
theorem exists_y_aux_gen {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (hΔ : W.Δ ≠ 0) {m : ℤ} {xP yP : F} (hP : W.toAffine.Nonsingular xP yP)
    (h2 : (2 : ℕ) • Affine.Point.some xP yP hP ≠ 0) {x₁ : F}
    (h₁ : (W.Φ m).eval x₁ = xP * (W.ΨSq m).eval x₁) :
    ∃ y : F, W.toAffine.Equation x₁ y := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨b, hb⟩ : ∃ b : F, b = W.a₁ * x₁ + W.a₃ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : F, c = x₁ ^ 3 + W.a₂ * x₁ ^ 2 + W.a₄ * x₁ + W.a₆ := ⟨_, rfl⟩
  have hno' : ∀ y : F, y ^ 2 + b * y - c ≠ 0 := fun y hy =>
    hno y ((Affine.equation_iff _ _).2 (by rw [hb, hc] at hy; linear_combination hy))
  have firr : Irreducible (quadPoly b c) :=
    irreducible_of_degree_le_three_of_not_isRoot
      (by rw [natDegree_quadPoly]; simp)
      (fun y hy => hno' y (by rw [IsRoot, eval_quadPoly] at hy; exact hy))
  have : Fact (Irreducible (quadPoly b c)) := ⟨firr⟩
  have hroot : (AdjoinRoot.root (quadPoly b c)) ^ 2 +
      algebraMap F (AdjoinRoot (quadPoly b c)) b * AdjoinRoot.root (quadPoly b c) =
      algebraMap F (AdjoinRoot (quadPoly b c)) c := by
    have h0 := AdjoinRoot.eval₂_root (quadPoly b c)
    rw [eval₂_quadPoly] at h0
    rw [AdjoinRoot.algebraMap_eq]
    linear_combination h0
  refine key_aux_gen (K := AdjoinRoot (quadPoly b c)) W hΔ hP h2 h₁
    (AdjoinRoot.liftAlgHom (quadPoly b c) (Algebra.ofId F _)
      (-AdjoinRoot.root (quadPoly b c) - algebraMap F _ b) ?_)
    (AdjoinRoot.root (quadPoly b c)) b c hb hc hroot ?_
  · rw [eval₂_quadPoly]
    simp only [RingHom.coe_coe, Algebra.ofId_apply]
    linear_combination hroot
  · simp

end NumberFieldKB.MilneEC.II.ValuedGen
