import NumberFieldKB.Pontryagin.Embedding

/-!
# Consequences of the closed embedding $G\to G^{**}$ (Weil II.§5, pp. 38–39), given Bochner

$G$ is a locally compact commutative Hausdorff group; Bochner's theorem is the named input `BochnerTheorem`.

* **`pontryaginDuality_of_dual`**: duality for $G^*$ implies duality for $G$. A character $\Psi$ of $G^{**}$ trivial
  on the image of $G$ is evaluation at some $\chi\in G^*$ (duality for $G^*$), and then $\chi(x)=1$ for all $x$; so
  the image is dense (`denseRange_dualEval_of_annihilator`), hence everything (`pontryaginDualityStatement_of_denseRange`).
* **`pontryaginDuality_compact_of_bochner`**: duality for compact groups, from Bochner instead of Peter–Weyl
  ($G^*$ is discrete and discrete duality is unconditional).
* **`compactSpace_of_discreteTopology_dual`**, **`discreteTopology_of_compactSpace_dual`**: $G^*$ discrete ⇒ $G$
  compact, $G^*$ compact ⇒ $G$ discrete (Weil II.§5, p. 38: "and conversely").
* Converse correspondences for a closed subgroup $H$ (Weil II.§5, p. 39): $H^*$ compact ⇒ $H$ open
  (`isOpen_of_isCompact_annihilator`), $H^*$ open ⇒ $H$ compact (`isCompact_of_isOpen_annihilator`), and $G/H$ compact
  iff $H^*$ discrete (`compactSpace_quotient_iff`).
* **`subgroupEquivDualQuotient`**: given the duality theorem for $G$, $H\cong(G^*/H^*)^*$ as topological groups
  (Weil II.§5, p. 38).
-/

open Topology

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G]

/-- **Duality for $G^*$ implies duality for $G$** (given Bochner). -/
theorem pontryaginDuality_of_dual (hB : BochnerTheorem.{u})
    (hD : PontryaginDualityStatement (PontryaginDual G)) : PontryaginDualityStatement G := by
  refine pontryaginDualityStatement_of_denseRange hB (denseRange_dualEval_of_annihilator hB fun Ψ hΨ => ?_)
  obtain ⟨e, he⟩ := hD
  obtain ⟨χ, rfl⟩ := e.surjective Ψ
  have hχ : χ = 1 := by
    ext x
    have := hΨ x
    rw [he, dualEval_apply, dualEval_apply] at this
    rw [this]; rfl
  rw [hχ, map_one]

/-- **Pontryagin duality for compact groups** (given Bochner; compare `pontryaginDuality_compact`, given
Peter–Weyl). -/
theorem pontryaginDuality_compact_of_bochner [CompactSpace G] (hB : BochnerTheorem.{u}) :
    PontryaginDualityStatement G :=
  pontryaginDuality_of_dual hB pontryaginDuality_discrete

/-- **Weil II.§5, p. 38**: if $G^*$ is discrete then $G$ is compact (given Bochner). -/
theorem compactSpace_of_discreteTopology_dual [DiscreteTopology (PontryaginDual G)] (hB : BochnerTheorem.{u}) :
    CompactSpace G := by
  obtain ⟨e, -⟩ := pontryaginDuality_of_dual hB (pontryaginDuality_discrete (G := PontryaginDual G))
  exact e.toHomeomorph.symm.compactSpace

/-- **Weil II.§5, p. 38**: if $G^*$ is compact then $G$ is discrete (given Bochner). -/
theorem discreteTopology_of_compactSpace_dual [CompactSpace (PontryaginDual G)] (hB : BochnerTheorem.{u}) :
    DiscreteTopology G := by
  obtain ⟨e, -⟩ := pontryaginDuality_of_dual hB
    (pontryaginDuality_compact_of_bochner (G := PontryaginDual G) hB)
  exact e.toHomeomorph.isEmbedding.discreteTopology

omit [T2Space G] in
/-- **Weil II.§5, p. 39**: if $H^*$ is compact, then $H$ is open (given Bochner). -/
theorem isOpen_of_isCompact_annihilator (hB : BochnerTheorem.{u}) (H : Subgroup G) [IsClosed (H : Set G)]
    (h : IsCompact (annihilator H : Set (PontryaginDual G))) : IsOpen (H : Set G) := by
  have : CompactSpace (annihilator H) := isCompact_iff_compactSpace.mp h
  have : CompactSpace (PontryaginDual (G ⧸ H)) := (annihilatorEquiv H).toHomeomorph.symm.compactSpace
  have : DiscreteTopology (G ⧸ H) := discreteTopology_of_compactSpace_dual hB
  have : (H : Set G) = (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {1} := by
    ext g; simp [QuotientGroup.eq_one_iff]
  rw [this]
  exact (isOpen_discrete ({1} : Set (G ⧸ H))).preimage continuous_quot_mk

/-- **Weil II.§5, p. 39**: if $H^*$ is open, then $H$ is compact (given Bochner): $H$ is the preimage of the compact
annihilator of $H^*$ in $G^{**}$ under the closed embedding $G\to G^{**}$. -/
theorem isCompact_of_isOpen_annihilator (hB : BochnerTheorem.{u}) (H : Subgroup G) [IsClosed (H : Set G)]
    (h : IsOpen (annihilator H : Set (PontryaginDual G))) : IsCompact (H : Set G) := by
  have hc := isCompact_annihilator_of_isOpen (annihilator H) h
  have hpre : dualEval G ⁻¹' (annihilator (annihilator H) : Set (PontryaginDual (PontryaginDual G))) =
      (H : Set G) := by
    rw [← doubleAnnihilator_eq_of_bochner hB H]
    ext x
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_annihilator, dualEval_apply, Set.mem_ofPred_eq]
  rw [← hpre]
  exact (isClosedEmbedding_dualEval hB).isCompact_preimage hc

omit [T2Space G] in
/-- **Weil II.§5, p. 39**: $G/H$ is compact iff $H^*$ is discrete (given Bochner). -/
theorem compactSpace_quotient_iff (hB : BochnerTheorem.{u}) (H : Subgroup G) [IsClosed (H : Set G)] :
    CompactSpace (G ⧸ H) ↔ DiscreteTopology (annihilator H) := by
  constructor
  · intro _
    exact (annihilatorEquiv H).toHomeomorph.symm.isEmbedding.discreteTopology
  · intro _
    have : DiscreteTopology (PontryaginDual (G ⧸ H)) :=
      (annihilatorEquiv H).toHomeomorph.isEmbedding.discreteTopology
    exact compactSpace_of_discreteTopology_dual hB

/-- Given the duality theorem for $G$, the isomorphism $G\cong G^{**}$ maps a closed subgroup $H$ onto the
annihilator of $H^*$. -/
def subgroupEquivDoubleAnnihilator (hB : BochnerTheorem.{u}) (hD : PontryaginDualityStatement G) (H : Subgroup G)
    [IsClosed (H : Set G)] : H ≃ₜ* annihilator (annihilator H) :=
  let e := Classical.choose hD
  have he : ⇑e = dualEval G := Classical.choose_spec hD
  have hmem : ∀ x : G, e x ∈ annihilator (annihilator H) ↔ x ∈ H := by
    intro x
    have := Set.ext_iff.mp (doubleAnnihilator_eq_of_bochner hB H) x
    rw [SetLike.mem_coe] at this
    rw [← this, he]
    exact Iff.rfl
  { toFun := fun h => ⟨e (h : G), (hmem h).mpr h.2⟩
    invFun := fun ω => ⟨e.symm ω, (hmem _).mp (by rw [e.apply_symm_apply]; exact ω.2)⟩
    left_inv := fun h => Subtype.ext (e.symm_apply_apply (h : G))
    right_inv := fun ω => Subtype.ext (e.apply_symm_apply ω)
    map_mul' := fun a b => Subtype.ext (map_mul e (a : G) b)
    continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

/-- **Weil II.§5, p. 38**: given the duality theorem for $G$ (and Bochner), a closed subgroup $H$ is isomorphic, as a
topological group, to the dual of $G^*/H^*$. -/
def subgroupEquivDualQuotient (hB : BochnerTheorem.{u}) (hD : PontryaginDualityStatement G) (H : Subgroup G)
    [IsClosed (H : Set G)] :
    H ≃ₜ* PontryaginDual (PontryaginDual G ⧸ annihilator H) :=
  have : IsClosed (annihilator H : Set (PontryaginDual G)) := isClosed_annihilator H
  (subgroupEquivDoubleAnnihilator hB hD H).trans (annihilatorEquiv (annihilator H)).symm

end NumberFieldKB.Pontryagin
