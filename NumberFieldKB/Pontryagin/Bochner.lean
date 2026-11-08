import NumberFieldKB.Pontryagin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Bochner's theorem on a locally compact commutative group (named input)

$G$ is a locally compact commutative group (written multiplicatively, as in Mathlib), $G^*$ = Mathlib's
`PontryaginDual G`.

* `IsPositiveDefinite φ`: $\sum_{i,j}c_i\overline{c_j}\,\varphi(v_iv_j^{-1})\ge0$ for all finite families
  (Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §3.3; the inequality is in `ℂ`, i.e. the sum is a
  non-negative real number).
* `fourierStieltjes μ g` $=\int_{G^*}\chi(g)\,d\mu(\chi)$, the Fourier–Stieltjes transform of a measure on $G^*$.
* **Named input `BochnerTheorem`** (Folland, Theorem 4.18): (existence) a positive-definite function continuous at $1$
  is the Fourier–Stieltjes transform of a finite inner regular measure on $G^*$; (uniqueness) two finite inner regular
  measures on $G^*$ with the same Fourier–Stieltjes transform are equal.

Both halves are proved in Tau Ceti (main `7ed979d`, 2026-11-04), for an additive group `G` with dual
`PontryaginDual (Multiplicative G)` and the same hypotheses (topological group, locally compact; no Hausdorff
hypothesis):
* existence: `TauCeti.IsPositiveDefiniteSub.exists_pontryaginMeasureTransform_eq_of_continuousAt`
  (`TauCeti/Analysis/Bochner/LocallyCompactGroup.lean`), where `IsPositiveDefiniteSub φ` is
  `∀ n c v, 0 ≤ ∑ i, ∑ j, c i * conj (c j) * φ (v i - v j)` and
  `μ.pontryaginMeasureTransform g = ∫ χ, χ (ofAdd g) ∂μ`;
* uniqueness: `MeasureTheory.FiniteMeasure.ext_of_forall_pontryaginMeasureTransform_eq_of_innerRegular`
  (`TauCeti/Analysis/Fourier/Pontryagin/Uniqueness.lean`).

For a multiplicative group `G`, Tau Ceti's statements applied to `Additive G` are the two fields below (the dual
`PontryaginDual (Multiplicative (Additive G))` is `PontryaginDual G`, and `v i - v j` is `v i * (v j)⁻¹`). Tau Ceti
cannot be imported here (toolchain v4.36 against our v4.35), so the theorem is cited, not re-proved. It is not the
conclusion of anything proved from it here: it produces measures on $G^*$ from functions on $G$; duality, inversion
and the dual measure are derived from it in `NumberFieldKB.Pontryagin.GelfandRaikov` and the files that import it.
-/

open MeasureTheory ComplexConjugate ComplexOrder

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

/-- A function $\varphi$ on a group is **positive definite**: $\sum_{i,j}c_i\overline{c_j}\varphi(v_iv_j^{-1})\ge0$. -/
def IsPositiveDefinite {G : Type*} [Group G] (φ : G → ℂ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℂ) (v : Fin n → G), 0 ≤ ∑ i, ∑ j, c i * conj (c j) * φ (v i * (v j)⁻¹)

/-- The Fourier–Stieltjes transform $g\mapsto\int_{G^*}\chi(g)\,d\mu(\chi)$ of a measure on the dual group. -/
def fourierStieltjes {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace (PontryaginDual G)]
    (μ : Measure (PontryaginDual G)) (g : G) : ℂ :=
  ∫ χ, ((χ g : Circle) : ℂ) ∂μ

/-- **Named input: Bochner's theorem** on locally compact commutative groups in universe `u` (Folland, Theorem
4.18), existence and uniqueness halves. Cited from Tau Ceti (see the module docstring for the declarations). -/
structure BochnerTheorem : Prop where
  /-- A positive-definite function continuous at `1` is the transform of a finite inner regular measure. -/
  exists_measure : ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (φ : G → ℂ), IsPositiveDefinite φ → ContinuousAt φ 1 →
      ∃ μ : Measure (PontryaginDual G), IsFiniteMeasure μ ∧ μ.InnerRegular ∧
        ∀ g, fourierStieltjes μ g = φ g
  /-- Finite inner regular measures on the dual with the same transform are equal. -/
  ext : ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (μ ν : Measure (PontryaginDual G)), IsFiniteMeasure μ → IsFiniteMeasure ν → μ.InnerRegular →
      ν.InnerRegular → (∀ g, fourierStieltjes μ g = fourierStieltjes ν g) → μ = ν

end NumberFieldKB.Pontryagin
