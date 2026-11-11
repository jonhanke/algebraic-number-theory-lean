/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Hanke
-/
import NumberFieldKB.Pontryagin.Unconditional

/-!
# Headline statements of NumberFieldKB 0.2.1: Pontryagin duality, proved

The declarations of `Challenge.lean`, with the same names and statements, each proved by citing the library theorems
named in its proof. `lake comparator` (configured by `comparator.json`) checks that every theorem here has exactly the
statement of its counterpart in `Challenge.lean` and depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. Read `Challenge.lean` for the statements, their docstrings and the definitions they use.
-/

noncomputable section

namespace NumberFieldKB.Headlines

/-! ## Pontryagin duality -/

open MeasureTheory Topology in
/-- **Pontryagin duality** (Folland, *A Course in Abstract Harmonic Analysis*, Theorem 4.32; Weil, *Basic Number
Theory*, Chapter II, §5): for every locally compact commutative Hausdorff topological group $G$, the canonical map
$G \to G^{**}$, $g \mapsto (\chi \mapsto \chi(g))$, is an isomorphism of topological groups. Only Mathlib definitions occur
(`PontryaginDual` is Mathlib's group of continuous characters to the circle, with the compact-open topology). -/
theorem pontryaginDuality {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ (g : G) (χ : PontryaginDual G), e g χ = χ g :=
  by
    obtain ⟨e, he⟩ := NumberFieldKB.Pontryagin.Unconditional.pontryaginDuality (G := G)
    exact ⟨e, fun g χ => by rw [he]; rfl⟩

open MeasureTheory Topology in
open NumberFieldKB.Pontryagin in
/-- **Fourier inversion and the dual measure** (Weil, *Basic Number Theory*, Chapter VII, §2, p. 105): for every regular
Haar measure $\alpha$ on a locally compact commutative Hausdorff group $G$ there is a regular Haar measure $\beta$ on
$G^*$ (the dual measure) for which Fourier inversion $\Phi(g) = \int \Phi^*(g^*) \langle -g, g^* \rangle\,d\beta(g^*)$ holds for
every function $\Phi$ admissible for $G$ (integrable and continuous with integrable Fourier transform, the library's
`IsAdmissible`). -/
theorem fourierInversion_dualMeasure {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure] [α.Regular]
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)] :
    ∃ β : Measure (PontryaginDual G), β.IsHaarMeasure ∧ β.Regular ∧ IsDualMeasure α β :=
  NumberFieldKB.Pontryagin.Unconditional.exists_isDualMeasure α

open MeasureTheory Topology in
open NumberFieldKB.Pontryagin in
/-- **Closed subgroups and annihilators** (Weil, *Basic Number Theory*, Chapter II, §5, pp. 38–39): let $G$ be a locally
compact commutative Hausdorff group, $H$ a closed subgroup and $H^* \subseteq G^*$ its annihilator (the characters
trivial on $H$). Then the elements of $G$ on which every character of $H^*$ is trivial are exactly those of $H$; $H$ is
isomorphic, as a topological group, to the dual of $G^*/H^*$; $H$ is open if and only if $H^*$ is compact; $H$ is
compact if and only if $H^*$ is open; and $G/H$ is compact if and only if $H^*$ is discrete. -/
theorem pontryagin_closedSubgroups {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] (H : Subgroup G) [IsClosed (H : Set G)] :
    {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H ∧
    Nonempty (H ≃ₜ* PontryaginDual (PontryaginDual G ⧸ annihilator H)) ∧
    (IsOpen (H : Set G) ↔ IsCompact (annihilator H : Set (PontryaginDual G))) ∧
    (IsCompact (H : Set G) ↔ IsOpen (annihilator H : Set (PontryaginDual G))) ∧
    (CompactSpace (G ⧸ H) ↔ DiscreteTopology (annihilator H)) :=
  ⟨NumberFieldKB.Pontryagin.Unconditional.doubleAnnihilator_eq H,
      ⟨NumberFieldKB.Pontryagin.Unconditional.subgroupEquivDualQuotient H⟩,
      NumberFieldKB.Pontryagin.Unconditional.isOpen_iff_isCompact_annihilator H,
      NumberFieldKB.Pontryagin.Unconditional.isCompact_iff_isOpen_annihilator H,
      NumberFieldKB.Pontryagin.Unconditional.compactSpace_quotient_iff H⟩

open MeasureTheory Topology in
/-- **Compact and discrete groups are dual to each other** (Weil, *Basic Number Theory*, Chapter II, §5, p. 38): for a
locally compact commutative Hausdorff group $G$, $G$ is compact if and only if $G^*$ is discrete, and $G$ is discrete if
and only if $G^*$ is compact. (Mathlib has the directions from $G$ to $G^*$; the converses use the duality theorem.)
Only Mathlib definitions occur. -/
theorem compact_iff_dual_discrete {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] :
    (CompactSpace G ↔ DiscreteTopology (PontryaginDual G)) ∧
    (DiscreteTopology G ↔ CompactSpace (PontryaginDual G)) :=
  ⟨NumberFieldKB.Pontryagin.Unconditional.compactSpace_iff_discreteTopology_dual,
      NumberFieldKB.Pontryagin.Unconditional.discreteTopology_iff_compactSpace_dual⟩

end NumberFieldKB.Headlines
