import NumberFieldKB.MilneEC.Ch3Curve
import NumberFieldKB.MilneEC.Ch5JFunction
import NumberFieldKB.MilneEC.Ch5HStar
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# $j$ is injective on $\mathrm{SL}_2(\mathbb Z)\backslash\mathbb H$ (Milne, Proposition V.2.2)

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 2.2 (pdf p. 191), the injectivity half, which this
repository recorded as the named statement `NumberFieldKB.MilneEC.V.JInjective`. It is proved here from Chapter III:

* if $j(z) = j(w)$, the invariants $(g_2, g_3)$ of the lattices $\Lambda_z = \mathbb Z z + \mathbb Z$ and
  $\Lambda_w$ satisfy $g_2^3(\Lambda_z) g_3^2(\Lambda_w) = g_2^3(\Lambda_w) g_3^2(\Lambda_z)$, so there is $u \ne 0$ with
  $u^4 g_2(\Lambda_z) = g_2(\Lambda_w)$, $u^6 g_3(\Lambda_z) = g_3(\Lambda_w)$ (`CurveAux.exists_scale`);
* by homogeneity (`G_of_lattice_eq_smul`) the lattice $u^{-1}\Lambda_z$ has the invariants of $\Lambda_w$, hence equals
  it (`CurveAux.lattice_eq_of_g_eq`: a lattice is determined by $g_2, g_3$, through the Laurent expansion of $\wp$);
* two oriented bases of one lattice differ by $\mathrm{SL}_2(\mathbb Z)$ (`prop_1_1_lattice_eq_iff`), so
  $w = A z$.
-/

open UpperHalfPlane
open scoped MatrixGroups

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC NumberFieldKB.MilneEC.III NumberFieldKB.MilneEC.III.CurveAux

/-- The oriented pair $(\tau, 1)$. -/
def pairOf (τ : ℍ) : OrientedPair := ⟨((τ : ℂ), 1), by simpa using τ.im_pos⟩

theorem ratio_pairOf (τ : ℍ) : (pairOf τ).ratio = τ := by
  apply UpperHalfPlane.ext
  show (τ : ℂ) / 1 = τ
  rw [div_one]

/-- **Milne, Proposition V.2.2 (injectivity)**: $j(z) = j(w)$ only if $w \in \mathrm{SL}_2(\mathbb Z) z$. -/
@[kb "milne2006ec" "Ch. V, Proposition 2.2 (j is injective on SL₂(ℤ)∖ℍ), pdf p. 191"]
theorem jInjective : V.JInjective := by
  refine ⟨fun z w hzw => ?_⟩
  set L := III.periodPairOf z
  set L' := III.periodPairOf w
  have hj : III.jFun z = III.jFun w := by
    rw [III.jFun_eq, III.jFun_eq, ← V.jFun_eq', ← V.jFun_eq', hzw]
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  have hΔ' := g₂_cube_sub_g₃_sq_ne_zero L'
  have hrel : L.g₂ ^ 3 * L'.g₃ ^ 2 = L'.g₂ ^ 3 * L.g₃ ^ 2 := by
    have h := hj
    simp only [III.jFun, jOf] at h
    rw [div_eq_div_iff hΔ hΔ'] at h
    linear_combination h / (-27 * 1728)
  obtain ⟨u, hu, h4, h6⟩ := exists_scale hΔ hΔ' hrel
  set c : ℂ := u⁻¹
  have hc : c ≠ 0 := inv_ne_zero hu
  set p' : OrientedPair := ⟨(c * z, c * 1), by
    show 0 < (c * z / (c * 1)).im
    rw [mul_div_mul_left _ _ hc, div_one]
    exact z.im_pos⟩
  have hlat : p'.toPeriodPair.lattice = Submodule.span ℤ {c * L.ω₁, c * L.ω₂} := rfl
  have hG := fun k => G_of_lattice_eq_smul (L := L) (L' := p'.toPeriodPair) hc hlat k
  have hg2 : p'.toPeriodPair.g₂ = L'.g₂ := by
    rw [← h4, PeriodPair.g₂, PeriodPair.g₂, hG 4]
    simp [c]
    ring
  have hg3 : p'.toPeriodPair.g₃ = L'.g₃ := by
    rw [← h6, PeriodPair.g₃, PeriodPair.g₃, hG 6]
    simp [c]
    ring
  have hl := lattice_eq_of_g_eq hg2 hg3
  have hl' : p'.lattice = (pairOf w).lattice := hl
  obtain ⟨A, hA⟩ := (prop_1_1_lattice_eq_iff p' (pairOf w)).1 hl'
  refine ⟨A, ?_⟩
  have hr : p'.ratio = z := by
    apply UpperHalfPlane.ext
    show c * z / (c * 1) = z
    rw [mul_div_mul_left _ _ hc, div_one]
  rw [← ratio_pairOf w, ← hA, ratio_smul, hr]

/-- **Proposition V.1.9** (pdf p. 187) in the topological form of `V.prop_1_9`, now from the named `Prop1_7` alone:
$X_0(1)$ is homeomorphic to the sphere through $j$. -/
@[kb "milne2006ec" "Ch. V, Proposition 1.9, pdf p. 187"]
theorem prop_1_9_of_prop1_7 (h17 : V.Prop1_7) :
    ∃ e : V.XGamma ⊤ ≃ₜ OnePoint ℂ, ∀ x : V.HStar, e (Quotient.mk _ x) = V.jStar x :=
  V.prop_1_9 h17 jInjective

end NumberFieldKB.ModularCurves
