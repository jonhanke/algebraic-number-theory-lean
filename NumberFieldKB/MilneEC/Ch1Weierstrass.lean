import NumberFieldKB.MilneEC.Ch1Examples
import NumberFieldKB.MilneEC.Ch1Projective
import NumberFieldKB.MilneEC.Ch1Resultant
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# Milne, Elliptic Curves, Chapter I: comparison with Mathlib's Weierstrass curves

The plane curves of Chapter I (`IsAffinePlaneCurve`, `IsNonsingularPoint`, `projectivePoints`, the
coordinate ring $k[X,Y]/(f)$) specialize, for a Weierstrass equation, to Mathlib's
`WeierstrassCurve.Affine` and `WeierstrassCurve.Projective` notions.  These comparison lemmas let later
chapters (elliptic curves, Chapter II) use Mathlib's group law with the definitions of Chapter I.

`weierstrassPoly W` is the affine Weierstrass polynomial
$Y^2 + a_1XY + a_3Y - (X^3 + a_2X^2 + a_4X + a_6)$ in `MvPolynomial (Fin 2) k`, Mathlib's
`W.toAffine.polynomial` transported along `yPolyEquiv` ($k[X][Y] \cong k[X, Y]$).
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-- The affine Weierstrass polynomial of `W` as a polynomial in two variables. -/
noncomputable def weierstrassPoly (W : WeierstrassCurve k) : MvPolynomial (Fin 2) k :=
  yPolyEquiv.symm W.toAffine.polynomial

/-- `weierstrassPoly W` in coordinates. -/
theorem weierstrassPoly_eq (W : WeierstrassCurve k) :
    weierstrassPoly W = X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
      (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆) := by
  apply yPolyEquiv.injective
  simp only [weierstrassPoly, AlgEquiv.apply_symm_apply, WeierstrassCurve.Affine.polynomial,
    map_sub, map_add, map_mul, map_pow, yPolyEquiv_X_zero, yPolyEquiv_X_one, yPolyEquiv_C]
  ring

/-- The curve $Y^2 = X^3 + aX + b$ of Example 1.5 is the Weierstrass curve with
$a_1 = a_2 = a_3 = 0$, $a_4 = a$, $a_6 = b$. -/
theorem shortWeierstrass_eq_weierstrassPoly (a b : k) :
    shortWeierstrass a b = weierstrassPoly ⟨0, 0, 0, a, b⟩ := by
  rw [weierstrassPoly_eq, shortWeierstrass]
  simp

/-- Helper: evaluation of `weierstrassPoly W` is Mathlib's evaluation of the Weierstrass polynomial. -/
lemma evalAt_weierstrassPoly (W : WeierstrassCurve k) (x y : k) :
    evalAt (weierstrassPoly W) (x, y) = W.toAffine.polynomial.evalEval x y := by
  rw [WeierstrassCurve.Affine.evalEval_polynomial, weierstrassPoly_eq]
  simp [evalAt]

/-- Helper: evaluation of `∂/∂X` of `weierstrassPoly W`. -/
lemma evalAt_dX_weierstrassPoly (W : WeierstrassCurve k) (x y : k) :
    evalAt (dX (weierstrassPoly W)) (x, y) = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  rw [weierstrassPoly_eq]
  simp [evalAt, dX]
  ring

/-- Helper: evaluation of `∂/∂Y` of `weierstrassPoly W`. -/
lemma evalAt_dY_weierstrassPoly (W : WeierstrassCurve k) (x y : k) :
    evalAt (dY (weierstrassPoly W)) (x, y) = 2 * y + W.a₁ * x + W.a₃ := by
  rw [weierstrassPoly_eq]
  simp [evalAt, dY]

/-- The points of the affine curve are the solutions of Mathlib's Weierstrass equation. -/
theorem mem_affinePoints_weierstrassPoly_iff (W : WeierstrassCurve k) (x y : k) :
    (x, y) ∈ affinePoints (weierstrassPoly W) k ↔ W.toAffine.Equation x y := by
  simp only [affinePoints, Set.mem_ofPred_eq, evalAt_weierstrassPoly]
  rfl

/-- Nonsingular points in the sense of Chapter I, §1 are Mathlib's nonsingular points of `W`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of nonsingular point (Weierstrass curves), pdf p. 14"]
theorem isNonsingularPoint_weierstrassPoly_iff (W : WeierstrassCurve k) (x y : k) :
    IsNonsingularPoint (weierstrassPoly W) (x, y) ↔ W.toAffine.Nonsingular x y := by
  rw [IsNonsingularPoint, mem_affinePoints_weierstrassPoly_iff, evalAt_dX_weierstrassPoly,
    evalAt_dY_weierstrassPoly, WeierstrassCurve.Affine.nonsingular_iff']

/-- The coordinate ring $k[X, Y]/(f)$ of Chapter I, §4 is Mathlib's `CoordinateRing` of `W`. -/
@[kb "milne2006ec" "Ch. I, §4, Def. of k[C] (Weierstrass curves), pdf p. 37"]
noncomputable def coordinateRingEquivWeierstrass (W : WeierstrassCurve k) :
    (MvPolynomial (Fin 2) k ⧸ Ideal.span {weierstrassPoly W}) ≃ₐ[k] W.toAffine.CoordinateRing :=
  Ideal.quotientEquivAlg _ (Ideal.span {W.toAffine.polynomial}) yPolyEquiv (by
    rw [Ideal.map_span, Set.image_singleton]
    simp [weierstrassPoly])

/-- The projective Weierstrass cubic of Chapter I, §1 is Mathlib's projective Weierstrass polynomial of the
curve with $a_1 = a_2 = a_3 = 0$, $a_4 = a$, $a_6 = b$. -/
theorem weierstrassCubic_eq (a b : k) :
    weierstrassCubic a b = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve k).toProjective.polynomial := by
  simp [weierstrassCubic, WeierstrassCurve.Projective.polynomial]

/-- Points of the projective curve are Mathlib's solutions of the projective Weierstrass equation. -/
theorem mem_projectivePoints_iff (W : WeierstrassCurve k) (v : Fin 3 → k) (hv : v ≠ 0) :
    Projectivization.mk k v hv ∈ projectivePoints W.toProjective.polynomial k ↔
      W.toProjective.Equation v := by
  simp only [projectivePoints, Set.mem_ofPred_eq, WeierstrassCurve.Projective.Equation]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  have h : aeval (Projectivization.mk k v hv).rep W.toProjective.polynomial =
      eval (a • v) W.toProjective.polynomial := by
    rw [← ha]
    rfl
  rw [h]
  have := WeierstrassCurve.Projective.equation_smul (W' := W) v a.isUnit
  exact this

end NumberFieldKB.MilneEC
