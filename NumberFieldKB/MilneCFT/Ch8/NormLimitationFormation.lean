import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Formation.NormLimitation

/-!
# Norm limitation for intermediate levels of a class formation (toward Milne VIII, Theorem 4.8)

Milne's Theorem VIII.4.8 (norm limitation for a finite extension $E/K$ that need not be Galois) rests on the
functoriality of the Artin map under the norm from an intermediate field: for $K\subseteq E\subseteq L$ with $L/K$
Galois, the Artin symbol over $K$ of $\mathrm{Nm}_{E/K}b$ is the image of the Artin symbol of $b$ over $E$. Tau Ceti
proves this for an arbitrary class formation (`TauCeti.ClassFieldTheory.ClassFormation.artinMap_groundNorm`). This file
draws the consequence at the level of class formations:

* `range_groundNorm_eq_comap`: the norm group of an intermediate level is the preimage under the Artin map of the
  image of the smaller Galois group, $\mathrm{Nm}_{E/K}A_E=\mathrm{art}_{L/K}^{-1}\bigl(\mathrm{im}(\mathrm{Gal}(L/E)^{\mathrm{ab}}
  \to\mathrm{Gal}(L/K)^{\mathrm{ab}})\bigr)$;
* `range_groundNorm_eq_of_range_inclusionHom_eq`: two intermediate levels whose Galois groups have the same image in
  $\mathrm{Gal}(L/K)^{\mathrm{ab}}$ have the same norm group (for $E$ and its maximal abelian subextension $M$ this is
  Theorem 4.8).

Reading this on number fields (levels = idele class groups, ground norm = $\mathrm{Nm}_{E/K}$ on idele classes) gives
Theorem 4.8: `Ch8.theorem4_8` (MilneCFT/Ch8/NormLimitationTauCeti.lean).
-/

namespace NumberFieldKB.MilneCFT.Ch8

open TauCeti.ClassFieldTheory

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {F : Formation G} (cf : ClassFormation F)

/-- **The norm group of an intermediate level is a preimage under the Artin map** (Milne, *CFT*, VIII, proof of
Theorem 4.8; Tau Ceti's `artinMap_groundNorm`): for a restriction `T` of a layer (in field terms
$K\subseteq E\subseteq L$, $L/K$ Galois), the norms from the level of $E$ are exactly the elements whose Artin symbol
for $L/K$ lies in the image of $\mathrm{Gal}(L/E)^{\mathrm{ab}}$. -/
theorem range_groundNorm_eq_comap {small big : NormalLayer G} (T : LayerRestriction small big) :
    (T.groundNorm F).range = (T.inclusionHom.range).comap (cf.artinMap big) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨cf.artinMap small b, (cf.artinMap_groundNorm T b).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨b, rfl⟩ := cf.surjective_artinMap small y
    have h0 : a - T.groundNorm F b ∈ (cf.artinMap big).ker := by
      rw [AddMonoidHom.mem_ker, map_sub, cf.artinMap_groundNorm, hy, sub_self]
    rw [cf.ker_artinMap] at h0
    have hT : big.top ≤ small.ground := T.same_top ▸ small.top_le_ground
    obtain ⟨c, hc⟩ := NormalLayer.normSubgroup_le_range_levelNorm big F hT T.ground_le h0
    refine ⟨c + b, ?_⟩
    change F.levelNorm T.ground_le (c + b) = a
    rw [map_add, hc]
    change a - T.groundNorm F b + T.groundNorm F b = a
    rw [sub_add_cancel]

include cf in
/-- **Norm limitation for intermediate levels**: two restrictions of the same layer whose Galois groups have the same
image in the abelianized Galois group of the layer have the same norm group. -/
theorem range_groundNorm_eq_of_range_inclusionHom_eq {small small' big : NormalLayer G}
    (T : LayerRestriction small big) (T' : LayerRestriction small' big)
    (h : T.inclusionHom.range = T'.inclusionHom.range) :
    (T.groundNorm F).range = (T'.groundNorm F).range := by
  rw [range_groundNorm_eq_comap cf T, range_groundNorm_eq_comap cf T', h]

end NumberFieldKB.MilneCFT.Ch8
