import NumberFieldKB.Pontryagin.BochnerProof
import NumberFieldKB.Pontryagin.Surjectivity
import NumberFieldKB.Pontryagin.Correspondences
import NumberFieldKB.Pontryagin.DualMeasure
import NumberFieldKB.Pontryagin.Inversion

/-!
# Pontryagin duality, unconditionally

With Bochner's theorem proved (`NumberFieldKB.Pontryagin.bochnerTheorem`, the proof of Tau Ceti ported in
`NumberFieldKB/TauCetiPort/`), the results of `Surjectivity`, `Correspondences`, `GelfandRaikov` and `DualMeasure`
that were stated given the named input `BochnerTheorem` hold for every locally compact commutative Hausdorff group.
They are restated here without that hypothesis, in the namespace `NumberFieldKB.Pontryagin.Unconditional`
(G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §§4.2–4.4; A. Weil, *Basic Number Theory*, II.§5
and VII.§2).

## Main declarations
* `Unconditional.pontryaginDuality`: $G\to G^{**}$ is an isomorphism of topological groups (Folland, Theorem 4.32).
* `Unconditional.charactersSeparate`: the characters separate points (Gelfand–Raikov).
* `Unconditional.compactSpace_iff_discreteTopology_dual`, `Unconditional.discreteTopology_iff_compactSpace_dual`,
  `Unconditional.doubleAnnihilator_eq`, `Unconditional.subgroupEquivDualQuotient`,
  `Unconditional.isOpen_iff_isCompact_annihilator`, `Unconditional.isCompact_iff_isOpen_annihilator`,
  `Unconditional.compactSpace_quotient_iff`: the correspondences of Weil II.§5.
* `Unconditional.exists_isDualMeasure`, `Unconditional.isDualMeasure_unique`,
  `Unconditional.exists_isDualMeasure_map_self`, `Unconditional.isDualMeasure_map_self_unique`,
  `Unconditional.isDualMeasure_count_of_compact`: Weil's dual measure (VII.§2, p. 105).
-/

open MeasureTheory Topology

noncomputable section

namespace NumberFieldKB.Pontryagin.Unconditional

open NumberFieldKB.Pontryagin

universe u

section Duality

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G]

/-- The characters of a locally compact commutative Hausdorff group separate points (Gelfand–Raikov). -/
theorem charactersSeparate : CharactersSeparate G :=
  charactersSeparate_of_bochner bochnerTheorem

/-- The canonical map $G\to G^{**}$ is injective. -/
theorem dualEval_injective : Function.Injective (dualEval G) :=
  dualEval_injective_of_bochner bochnerTheorem

/-- The canonical map $G\to G^{**}$ is a closed embedding. -/
theorem isClosedEmbedding_dualEval : IsClosedEmbedding (dualEval G) :=
  Pontryagin.isClosedEmbedding_dualEval bochnerTheorem

/-- The canonical map $G\to G^{**}$ is surjective. -/
theorem dualEval_surjective : Function.Surjective (dualEval G) :=
  Pontryagin.dualEval_surjective bochnerTheorem

/-- **Pontryagin duality**: for every locally compact commutative Hausdorff group $G$, the canonical map
$G\to G^{**}$ is an isomorphism of topological groups. -/
theorem pontryaginDuality : PontryaginDualityStatement G :=
  Pontryagin.pontryaginDuality bochnerTheorem

/-- $G$ is compact iff $G^*$ is discrete (Weil II.§5, p. 38). -/
theorem compactSpace_iff_discreteTopology_dual : CompactSpace G ↔ DiscreteTopology (PontryaginDual G) :=
  ⟨fun _ => inferInstance, fun _ => compactSpace_of_discreteTopology_dual bochnerTheorem⟩

/-- $G$ is discrete iff $G^*$ is compact (Weil II.§5, p. 38). -/
theorem discreteTopology_iff_compactSpace_dual : DiscreteTopology G ↔ CompactSpace (PontryaginDual G) :=
  ⟨fun _ => inferInstance, fun _ => discreteTopology_of_compactSpace_dual bochnerTheorem⟩

variable (H : Subgroup G) [IsClosed (H : Set G)]

omit [T2Space G] in
/-- For a closed subgroup $H$, the subgroup of $G$ associated with $H^*$ is $H$ (Weil II.§5, p. 38). -/
theorem doubleAnnihilator_eq : {g : G | ∀ χ ∈ annihilator H, χ g = 1} = H :=
  doubleAnnihilator_eq_of_bochner bochnerTheorem H

/-- A closed subgroup $H$ is isomorphic, as a topological group, to the dual of $G^*/H^*$ (Weil II.§5, p. 38). -/
def subgroupEquivDualQuotient : H ≃ₜ* PontryaginDual (PontryaginDual G ⧸ annihilator H) :=
  Pontryagin.subgroupEquivDualQuotient bochnerTheorem pontryaginDuality H

omit [T2Space G] in
/-- $H$ is open iff $H^*$ is compact (Weil II.§5, p. 39). -/
theorem isOpen_iff_isCompact_annihilator :
    IsOpen (H : Set G) ↔ IsCompact (annihilator H : Set (PontryaginDual G)) :=
  ⟨isCompact_annihilator_of_isOpen H, isOpen_of_isCompact_annihilator bochnerTheorem H⟩

/-- $H$ is compact iff $H^*$ is open (Weil II.§5, p. 39). -/
theorem isCompact_iff_isOpen_annihilator :
    IsCompact (H : Set G) ↔ IsOpen (annihilator H : Set (PontryaginDual G)) :=
  ⟨isOpen_annihilator_of_isCompact H, isCompact_of_isOpen_annihilator bochnerTheorem H⟩

omit [T2Space G] in
/-- $G/H$ is compact iff $H^*$ is discrete (Weil II.§5, p. 39). -/
theorem compactSpace_quotient_iff : CompactSpace (G ⧸ H) ↔ DiscreteTopology (annihilator H) :=
  Pontryagin.compactSpace_quotient_iff bochnerTheorem H

end Duality

section DualMeasure

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure] [α.Regular]
  [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]

/-- **Weil VII.§2, p. 105**: the dual measure of $\alpha$ exists and is a regular Haar measure on $G^*$. -/
theorem exists_isDualMeasure :
    ∃ β : Measure (PontryaginDual G), β.IsHaarMeasure ∧ β.Regular ∧ IsDualMeasure α β :=
  Pontryagin.exists_isDualMeasure bochnerTheorem

/-- **Weil VII.§2, p. 105**: the dual measure is unique among regular Haar measures on $G^*$. -/
theorem isDualMeasure_unique (β β' : Measure (PontryaginDual G)) [β.IsHaarMeasure] [β.Regular]
    [β'.IsHaarMeasure] [β'.Regular] (h : IsDualMeasure α β) (h' : IsDualMeasure α β') : β = β' :=
  (Pontryagin.isDualMeasure_unique bochnerTheorem β h).trans
    (Pontryagin.isDualMeasure_unique bochnerTheorem β' h').symm

omit [α.IsHaarMeasure] [α.Regular] in
/-- **Weil VII.§2, p. 105**: under an identification $\iota:G\cong G^*$ some regular Haar measure $\alpha'$ is
self-dual, i.e. its dual measure is $\iota_*\alpha'$. -/
theorem exists_isDualMeasure_map_self (ι : G ≃ₜ* PontryaginDual G) :
    ∃ α' : Measure G, α'.IsHaarMeasure ∧ α'.Regular ∧ IsDualMeasure α' (α'.map ι) :=
  Pontryagin.exists_isDualMeasure_map_self bochnerTheorem ι Measure.haar

omit [α.IsHaarMeasure] [α.Regular] in
/-- **Weil VII.§2, p. 105**: under an identification $\iota:G\cong G^*$ the self-dual regular Haar measure is
unique. -/
theorem isDualMeasure_map_self_unique (ι : G ≃ₜ* PontryaginDual G) (α₁ α₂ : Measure G) [α₁.IsHaarMeasure]
    [α₁.Regular] [α₂.IsHaarMeasure] [α₂.Regular] (h₁ : IsDualMeasure α₁ (α₁.map ι))
    (h₂ : IsDualMeasure α₂ (α₂.map ι)) : α₁ = α₂ :=
  Pontryagin.isDualMeasure_map_self_unique bochnerTheorem ι α₂ α₁ h₂ h₁

end DualMeasure

/-- **Weil VII.§2, p. 105, compact groups**: if $G$ is compact and $\alpha(G)=1$, the dual measure is the counting
measure on the discrete group $G^*$. -/
theorem isDualMeasure_count_of_compact {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (α : Measure G) [α.IsHaarMeasure]
    [IsProbabilityMeasure α] [MeasurableSpace (PontryaginDual G)]
    [MeasurableSingletonClass (PontryaginDual G)] :
    IsDualMeasure α (Measure.count : Measure (PontryaginDual G)) :=
  isDualMeasure_count_of_compact_of_separates charactersSeparate α

end NumberFieldKB.Pontryagin.Unconditional
