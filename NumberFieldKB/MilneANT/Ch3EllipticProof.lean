import NumberFieldKB.MilneANT.Ch3Elliptic
import NumberFieldKB.MilneEC.Ch3Curve
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing
import NumberFieldKB.TauCetiPort.AlgebraicGeometry.EllipticCurve.Affine.Point.ToClass

/-!
# Milne, *Algebraic Number Theory*, Example 3.22: the coordinate ring of a complex affine elliptic curve

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Example 3.22 and its footnote, p. 54; bib key
`milne2020ant`.

**`ellipticCoordinateRingInput`** proves the named statement `EllipticCoordinateRingInput a b` (Ch3Elliptic.lean)
unconditionally. Milne's footnote: $\mathrm{Cl}(A) \cong \mathrm{Pic}^0(E) \cong E(\mathbb C) \cong \mathbb C/\Lambda$.

* Dedekind: Tau Ceti `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain_coordinateRing` (the coordinate ring
  of an elliptic curve is integrally closed of dimension one; ported under `NumberFieldKB/TauCetiPort`).
* $E(\mathbb C) \cong \mathrm{Cl}(A)$: Tau Ceti `WeierstrassCurve.Affine.Point.toClassEquiv` (Mathlib's injective
  `toClass`, with surjectivity from the genus-one codimension argument).
* $\mathbb C/\Lambda \cong E(\mathbb C)$: the uniformization of the MilneEC track,
  `NumberFieldKB.MilneEC.III.quotEquivCurve` (Milne, *Elliptic Curves*, III, Prop. 3.7 and Cor. 3.9), for the lattice
  $\Lambda$ with $g_2(\Lambda) = -4a$, $g_3(\Lambda) = -4b$ (`exists_lattice_with_g`, from the surjectivity of $j$),
  whose curve $y^2 = x^3 - \tfrac{g_2}{4}x - \tfrac{g_3}{4}$ is exactly $Y^2 = X^3 + aX + b$.
-/

open WeierstrassCurve

namespace NumberFieldKB.MilneANT

theorem ellipticW_Δ (a b : ℂ) : (ellipticW a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
  simp only [ellipticW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

theorem isElliptic_ellipticW {a b : ℂ} (hΔ : (ellipticW a b).Δ ≠ 0) : (ellipticW a b).IsElliptic :=
  ⟨hΔ.isUnit⟩

/-- **Example 3.22** (proved, unconditionally): for $4a^3 + 27b^2 \ne 0$, the coordinate ring of
$Y^2 = X^3 + aX + b$ over $\mathbb C$ is a Dedekind domain whose class group is isomorphic to $\mathbb C/\Lambda$ for a
lattice $\Lambda$. -/
@[kb "milne2020ant" "v3.08, Example 3.22, p. 54"]
theorem ellipticCoordinateRingInput (a b : ℂ) : EllipticCoordinateRingInput a b where
  isDedekindDomain hΔ := by
    haveI := isElliptic_ellipticW hΔ
    infer_instance
  classGroup_equiv hΔ := by
    classical
    haveI := isElliptic_ellipticW hΔ
    have hΔ' : (-4 * a) ^ 3 - 27 * (-4 * b) ^ 2 ≠ 0 := by
      rw [ellipticW_Δ] at hΔ
      intro h
      apply hΔ
      linear_combination h
    obtain ⟨L, h2, h3⟩ := MilneEC.III.CurveAux.exists_lattice_with_g (-4 * a) (-4 * b) hΔ'
    have hcurve : (MilneEC.III.curveOf L) = ellipticW a b := by
      simp only [MilneEC.III.curveOf, ellipticW, h2, h3]
      congr 1 <;> ring
    refine ⟨L.lattice, inferInstance, inferInstance, ⟨?_⟩⟩
    have e1 : ℂ ⧸ L.lattice ≃+ (ellipticW a b).Point := by
      have := MilneEC.III.quotEquivCurve L
      rw [hcurve] at this
      exact this
    exact (WeierstrassCurve.Affine.Point.toClassEquiv (W := ellipticW a b)).symm.trans e1.symm

end NumberFieldKB.MilneANT
