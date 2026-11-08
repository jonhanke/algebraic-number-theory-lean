import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Example 3.22: the coordinate ring of an affine elliptic curve

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Example 3.22, p. 54; bib key `milne2020ant`.

For $a, b \in \mathbb C$ with $4a^3 + 27b^2 \ne 0$, the ring $A = \mathbb C[X,Y]/(Y^2 - X^3 - aX - b)$ is a Dedekind
domain whose class group is uncountable; in fact $\mathrm{Cl}(A) \cong \mathbb C/\Lambda$ for a lattice $\Lambda$.

* `example_3_22_uncountable` (**proved**): $\mathrm{Cl}(A)$ is uncountable. Proof: Mathlib's injective homomorphism
  `WeierstrassCurve.Affine.Point.toClass` from the points of the curve to $\mathrm{Cl}(A)$, and the curve has
  uncountably many points (one over each $x \in \mathbb C$).
* `EllipticCoordinateRingInput` (**named statement**): $A$ is a Dedekind domain and $\mathrm{Cl}(A) \cong
  \mathbb C/\Lambda$ for some full lattice $\Lambda \subset \mathbb C$ (Milne's footnote: $\mathrm{Cl}(A) \cong
  \mathrm{Pic}^0(E) \cong E(\mathbb C) \cong \mathbb C/\Lambda$; the last step is the uniformization of complex
  elliptic curves, not in Mathlib).

The curve is Mathlib's Weierstrass curve with $a_1 = a_2 = a_3 = 0$, $a_4 = a$, $a_6 = b$; its discriminant is
$\Delta = -16(4a^3 + 27b^2)$, so Milne's condition is `W.Δ ≠ 0`.
-/

namespace NumberFieldKB.MilneANT

/-- The affine Weierstrass curve $Y^2 = X^3 + aX + b$ over $\mathbb C$. -/
def ellipticW (a b : ℂ) : WeierstrassCurve.Affine ℂ := ⟨0, 0, 0, a, b⟩

/-- **Example 3.22** (named statement): for $4a^3 + 27b^2 \ne 0$ (`(ellipticW a b).Δ ≠ 0`), the coordinate ring
$\mathbb C[X,Y]/(Y^2 - X^3 - aX - b)$ of the affine elliptic curve is a Dedekind domain, and its class group is
isomorphic (as an abelian group) to $\mathbb C/\Lambda$ for some lattice $\Lambda$ in $\mathbb C$.

*Erratum:* the first version omitted Milne's hypothesis $\Delta \ne 0$ and was false
for $a = b = 0$ (`not_isDedekindDomain_ellipticW_zero_zero`, `Ch3EllipticErratum.lean`). -/
@[kb "milne2020ant" "v3.08, Example 3.22, p. 54"]
structure EllipticCoordinateRingInput (a b : ℂ) : Prop where
  isDedekindDomain : (ellipticW a b).Δ ≠ 0 → IsDedekindDomain (ellipticW a b).CoordinateRing
  classGroup_equiv : (ellipticW a b).Δ ≠ 0 → ∃ (Λ : Submodule ℤ ℂ) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
    Nonempty (Additive (ClassGroup (ellipticW a b).CoordinateRing) ≃+ ℂ ⧸ Λ.toAddSubgroup)

/-- **Example 3.22**, uncountability (proved unconditionally): for $4a^3 + 27b^2 \ne 0$ the class group of
$\mathbb C[X,Y]/(Y^2 - X^3 - aX - b)$ is uncountable. -/
@[kb "milne2020ant" "v3.08, Example 3.22, p. 54"]
theorem example_3_22_uncountable (a b : ℂ) (hΔ : (ellipticW a b).Δ ≠ 0) :
    Uncountable (ClassGroup (ellipticW a b).CoordinateRing) := by
  classical
  have hy : ∀ x : ℂ, ∃ y : ℂ, (ellipticW a b).Equation x y := by
    intro x
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + a * x + b) (n := 2) (by norm_num)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    simp [ellipticW, hy.symm]
  choose y hy using hy
  have hns : ∀ x : ℂ, (ellipticW a b).Nonsingular x (y x) := fun x =>
    (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (hy x)
  let f : ℂ → (ellipticW a b).Point := fun x => .some x (y x) (hns x)
  have hf : Function.Injective f := by
    intro x x' h
    simp only [f, WeierstrassCurve.Affine.Point.some.injEq] at h
    exact h.1
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  have : Uncountable (ellipticW a b).Point := hf.uncountable
  exact (Additive.toMul.injective.comp
    (WeierstrassCurve.Affine.Point.toClass_injective (W := ellipticW a b))).uncountable

end NumberFieldKB.MilneANT
