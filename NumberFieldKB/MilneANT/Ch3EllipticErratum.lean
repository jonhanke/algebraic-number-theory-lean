import NumberFieldKB.MilneANT.Ch3Elliptic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Milne, *Algebraic Number Theory*, Example 3.22: an erratum in the named statement

The first version of the named statement `EllipticCoordinateRingInput a b` (Example 3.22) had no hypothesis
$4a^3 + 27b^2 \ne 0$, which Milne's example assumes. Without it the statement is **false**: for $a = b = 0$ the
coordinate ring $\mathbb C[X,Y]/(Y^2 - X^3)$ of the cusp is not integrally closed, since $t = y/x$ satisfies
$t^2 = x$ but is not in the ring, so it is not a Dedekind domain (`not_isDedekindDomain_ellipticW_zero_zero`,
with `ellipticW_zero_zero_Δ` : $\Delta = 0$). The statement now assumes `(ellipticW a b).Δ ≠ 0`.
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace NumberFieldKB.MilneANT

open WeierstrassCurve.Affine

private abbrev Rc : Type := (ellipticW 0 0).CoordinateRing

private lemma cusp_y_sq :
    (CoordinateRing.mk (ellipticW 0 0) Y) ^ 2 = (CoordinateRing.mk (ellipticW 0 0) (C X)) ^ 3 := by
  rw [← map_pow, ← map_pow]
  refine AdjoinRoot.mk_eq_mk.mpr ⟨1, ?_⟩
  simp only [WeierstrassCurve.Affine.polynomial, ellipticW, map_zero, zero_mul, add_zero, mul_one]
  simp [map_pow]

private lemma cusp_x_ne_zero : (CoordinateRing.mk (ellipticW 0 0) (C X) : Rc) ≠ 0 := by
  intro h
  have h' : (X : ℂ[X]) • (1 : Rc) + (0 : ℂ[X]) • CoordinateRing.mk (ellipticW 0 0) Y = 0 := by
    rw [zero_smul, add_zero, CoordinateRing.smul, mul_one]
    exact h
  exact X_ne_zero (CoordinateRing.smul_basis_eq_zero h').1

/-- The coordinate ring of the cusp $Y^2 = X^3$ over $\mathbb C$ is not integrally closed. -/
theorem not_isIntegrallyClosed_ellipticW_zero_zero :
    ¬ IsIntegrallyClosed (ellipticW 0 0).CoordinateRing := by
  intro hic
  let x : Rc := CoordinateRing.mk (ellipticW 0 0) (C X)
  let y : Rc := CoordinateRing.mk (ellipticW 0 0) Y
  have hy2 : y ^ 2 = x ^ 3 := cusp_y_sq
  have hx0 : x ≠ 0 := cusp_x_ne_zero
  let φ : Rc →+* FractionRing Rc := algebraMap Rc (FractionRing Rc)
  have hinj : Function.Injective φ := IsFractionRing.injective Rc (FractionRing Rc)
  have hxF : φ x ≠ 0 := by
    intro h
    exact hx0 (hinj (h.trans φ.map_zero.symm))
  let t : FractionRing Rc := φ y / φ x
  have ht2 : t ^ 2 = φ x := by
    have h3 : (φ y) ^ 2 = (φ x) ^ 3 := by simpa only [map_pow] using congrArg φ hy2
    simp only [t, div_pow, h3]
    field_simp
  have hint : IsIntegral Rc t := by
    refine ⟨X ^ 2 - C x, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, ht2]
    exact sub_self _
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Rc) (K := FractionRing Rc)).mp hint
  have hyr : y = x * r := by
    apply hinj
    rw [map_mul]
    rw [hr]
    simp only [t]
    field_simp
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq r
  have e1 : x * (p • (1 : Rc) + q • y) = (X * p) • (1 : Rc) + (X * q) • y := by
    simp only [x, y, CoordinateRing.smul, map_mul]
    ring
  have hcomb : (0 - X * p) • (1 : Rc) + (1 - X * q) • y = 0 := by
    have h2 := hyr
    rw [e1] at h2
    rw [show (0 - X * p) • (1 : Rc) + (1 - X * q) • y = y - ((X * p) • (1 : Rc) + (X * q) • y) by
      rw [sub_smul, sub_smul, one_smul, zero_smul]; abel, ← h2, sub_self]
  have h1 := (CoordinateRing.smul_basis_eq_zero hcomb).2
  have hXq : (X * q : ℂ[X]) = 1 := (sub_eq_zero.mp h1).symm
  have hq : q ≠ 0 := by rintro rfl; simp at hXq
  have hdeg := congrArg natDegree hXq
  rw [natDegree_one, natDegree_mul X_ne_zero hq, natDegree_X] at hdeg
  omega

/-- The cusp $Y^2 = X^3$ is singular: $\Delta = 0$. -/
theorem ellipticW_zero_zero_Δ : (ellipticW 0 0).Δ = 0 := by
  simp [ellipticW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- **Erratum to the first version of `EllipticCoordinateRingInput`** (which had no hypothesis $\Delta \ne 0$): for
$a = b = 0$ the coordinate ring $\mathbb C[X,Y]/(Y^2 - X^3)$ is not a Dedekind domain. So Milne's hypothesis
$4a^3 + 27b^2 \ne 0$ is needed; the corrected statement assumes `(ellipticW a b).Δ ≠ 0`. -/
@[kb "milne2020ant" "v3.08, Example 3.22, p. 54 (erratum: the hypothesis 4a^3+27b^2 ≠ 0 is needed)"]
theorem not_isDedekindDomain_ellipticW_zero_zero : ¬ IsDedekindDomain (ellipticW 0 0).CoordinateRing := fun h => by
  have := h
  exact not_isIntegrallyClosed_ellipticW_zero_zero inferInstance

end NumberFieldKB.MilneANT
