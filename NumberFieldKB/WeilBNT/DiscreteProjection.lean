import Mathlib
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, Chapter V, §2, Lemma 1 (projection of a cocompact discrete subgroup)

**Lemma 1** (p. 82): let $G$ be a locally compact group with an open subgroup $G_1=G'\times G''$, $G'$ locally compact and
$G''$ compact; let $\Gamma$ be a discrete subgroup of $G$ with $G/\Gamma$ compact, and $\Gamma'$ the projection of
$\Gamma\cap G_1$ onto $G'$. Then $\Gamma'$ is discrete in $G'$ and $G'/\Gamma'$ is compact.

Weil uses it with $G=k_{\mathbb A}$, $G_1=k_\infty\times\prod_vr_v$, $\Gamma=k$ to get that $\mathfrak r$ is a lattice in
$k_\infty$ (Thm. 1). Formalization: "$G_1=G'\times G''$ is an open subgroup" is an injective continuous homomorphism
$\iota:G'\times G''\to G$ that is an open embedding; all groups are Hausdorff (Weil's standing convention). The quotient
$G/\Gamma$ is Mathlib's left coset space with the quotient topology.

* **`weil_V_2_lemma1`**: $\Gamma'=\mathrm{pr}_1(\iota^{-1}(\Gamma))$ is discrete and $G'/\Gamma'$ is compact.

Weil's proof: for a compact neighbourhood $W$ of $1$ in $G'$, $(W\times G'')\cap\Gamma$ is finite (compact meets
closed discrete), and its projection is $W\cap\Gamma'$, so $\Gamma'$ is discrete; $G_1\Gamma$ is open and closed, so the
image of $G_1$ in $G/\Gamma$ is compact, $G_1=C\cdot\Gamma_1$ with $C$ compact, and $G'=C'\Gamma'$ with $C'$ the projection.
-/

open Topology Pointwise

namespace NumberFieldKB.WeilBNT

variable {G G' G'' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] [LocallyCompactSpace G']
  [Group G''] [TopologicalSpace G''] [CompactSpace G'']

/-- A subgroup of a Hausdorff topological group meeting some neighbourhood of `1` in a finite set is
discrete. -/
theorem discrete_of_finite_inter {H' : Type*} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H']
    [T2Space H'] (H : Subgroup H') (W : Set H') (hW : W ∈ 𝓝 (1 : H'))
    (hfin : (W ∩ (H : Set H')).Finite) : DiscreteTopology H := by
  apply discreteTopology_of_isOpen_singleton_one
  have hF : IsClosed ((W ∩ (H : Set H')) \ {1}) := (hfin.subset Set.sdiff_subset).isClosed
  have hU : W ∩ ((W ∩ (H : Set H')) \ {1})ᶜ ∈ 𝓝 (1 : H') :=
    Filter.inter_mem hW (hF.isOpen_compl.mem_nhds (by simp))
  obtain ⟨O, hOU, hO, h1O⟩ := mem_nhds_iff.1 hU
  have : ({1} : Set H) = Subtype.val ⁻¹' O := by
    ext h
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    constructor
    · rintro rfl
      exact h1O
    · intro hh
      by_contra hne
      have hne' : (h : H') ≠ 1 := fun e => hne (Subtype.ext e)
      have := hOU hh
      exact this.2 ⟨⟨this.1, h.2⟩, hne'⟩
  rw [this]
  exact hO.preimage continuous_subtype_val

/-- **Weil, V.§2, Lemma 1** (p. 82): if $G'\times G''$ ($G''$ compact) is an open subgroup of $G$ and $\Gamma$ is a
discrete subgroup of $G$ with $G/\Gamma$ compact, then the projection $\Gamma'$ of $\Gamma\cap(G'\times G'')$ onto $G'$ is
discrete and $G'/\Gamma'$ is compact. -/
@[kb "weil1973bnt" "Ch. V, §2, Lemma 1 (p. 82)"]
theorem weil_V_2_lemma1 (ι : G' × G'' →* G) (hι : IsOpenEmbedding ι) (Γ : Subgroup G) [DiscreteTopology Γ]
    [CompactSpace (G ⧸ Γ)] :
    DiscreteTopology ((Γ.comap ι).map (MonoidHom.fst G' G'')) ∧
      CompactSpace (G' ⧸ (Γ.comap ι).map (MonoidHom.fst G' G'')) := by
  have hmem : ∀ a : G', a ∈ (Γ.comap ι).map (MonoidHom.fst G' G'') ↔ ∃ b : G'', ι (a, b) ∈ Γ := by
    intro a
    simp only [Subgroup.mem_map, Subgroup.mem_comap]
    constructor
    · rintro ⟨⟨a', b⟩, h, rfl⟩
      exact ⟨b, h⟩
    · rintro ⟨b, h⟩
      exact ⟨(a, b), h, rfl⟩
  have hΓc : IsClosed (Γ : Set G) := Subgroup.isClosed_of_discreteTopology
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (1 : G')
  refine ⟨?_, ?_⟩
  · have hK : IsCompact (ι '' (W ×ˢ (Set.univ : Set G''))) :=
      (hWc.prod isCompact_univ).image hι.continuous
    have hKΓ : IsCompact (ι '' (W ×ˢ (Set.univ : Set G'')) ∩ (Γ : Set G)) := hK.inter_right hΓc
    have hD : IsDiscrete (Γ : Set G) := ⟨‹DiscreteTopology Γ›⟩
    have hfin := (hKΓ.finite (hD.mono Set.inter_subset_right)).preimage hι.injective.injOn
    have hfin2 := hfin.image (MonoidHom.fst G' G'')
    refine discrete_of_finite_inter _ W hW (hfin2.subset ?_)
    rintro a ⟨haW, ha⟩
    obtain ⟨b, hb⟩ := (hmem a).1 ha
    refine ⟨(a, b), ⟨⟨(a, b), ⟨haW, Set.mem_univ _⟩, rfl⟩, hb⟩, rfl⟩
  · set Γ' := (Γ.comap ι).map (MonoidHom.fst G' G'') with hΓ'
    obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G')
    have hVi : (1 : G') ∈ interior V := mem_interior_iff_mem_nhds.2 hV
    -- the open subgroup image in the quotient
    set S : Set (G ⧸ Γ) := Set.range (fun y : G' × G'' => ((ι y : G) : G ⧸ Γ)) with hS
    have hSpre : (fun g : G => (g : G ⧸ Γ)) ⁻¹' S = (Set.range ι) * (Γ : Set G) := by
      ext g
      simp only [Set.mem_preimage, hS, Set.mem_range, Set.mem_mul, SetLike.mem_coe]
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨ι y, ⟨y, rfl⟩, (ι y)⁻¹ * g, ?_, by simp⟩
        exact QuotientGroup.eq.1 hy
      · rintro ⟨_, ⟨y, rfl⟩, γ, hγ, rfl⟩
        exact ⟨y, QuotientGroup.eq.2 (by simpa using hγ)⟩
    have hSclosed : IsClosed S := by
      rw [← (QuotientGroup.isQuotientMap_mk Γ).isClosed_preimage, hSpre, ← isOpen_compl_iff]
      rw [isOpen_iff_forall_mem_open]
      intro g hg
      refine ⟨(Set.range ι) * {g} * (Γ : Set G), ?_, ?_, ?_⟩
      · rintro _ ⟨_, ⟨_, ⟨y, rfl⟩, g', hg', rfl⟩, γ, hγ, rfl⟩ hx
        obtain ⟨_, ⟨y', rfl⟩, γ', hγ', e⟩ := hx
        apply hg
        rw [Set.mem_singleton_iff] at hg'
        subst hg'
        have h1 : g' = (ι y)⁻¹ * (ι y' * γ') * γ⁻¹ := by
          rw [show ι y' * γ' = ι y * g' * γ from e]
          group
        refine ⟨ι (y⁻¹ * y'), ⟨_, rfl⟩, γ' * γ⁻¹, Γ.mul_mem hγ' (Γ.inv_mem hγ), ?_⟩
        rw [map_mul, map_inv]
        conv_rhs => rw [h1]
        group
      · exact (hι.isOpen_range.mul_right).mul_right
      · exact ⟨ι 1 * g, ⟨ι 1, ⟨1, rfl⟩, g, rfl, rfl⟩, 1, Γ.one_mem, by simp⟩
    have hScomp : IsCompact S := hSclosed.isCompact
    set U : G' → Set (G ⧸ Γ) := fun x =>
      (fun g : G => (g : G ⧸ Γ)) '' (ι '' ((x • interior V) ×ˢ (Set.univ : Set G''))) with hU
    have hUopen : ∀ x, IsOpen (U x) := fun x =>
      (QuotientGroup.isOpenMap_coe : IsOpenMap ((↑) : G → G ⧸ Γ)) _
        (hι.isOpenMap _ ((isOpen_interior.smul x).prod isOpen_univ))
    have hcover : S ⊆ ⋃ x, U x := by
      rintro _ ⟨⟨a, z⟩, rfl⟩
      refine Set.mem_iUnion.2 ⟨a, _, ⟨(a, z), ⟨?_, Set.mem_univ _⟩, rfl⟩, rfl⟩
      exact Set.mem_smul_set.2 ⟨1, hVi, mul_one a⟩
    obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover U hUopen hcover
    have hC : IsCompact (⋃ i ∈ t, i • V) := t.isCompact_biUnion fun i _ => hVc.smul i
    refine ⟨(hC.image (QuotientGroup.isQuotientMap_mk Γ').continuous).of_isClosed_subset
      isClosed_univ ?_⟩
    intro q _
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : ((ι (g, 1) : G) : G ⧸ Γ) ∈ S := ⟨(g, 1), rfl⟩
    obtain ⟨i, hi, _, ⟨⟨x, z⟩, ⟨hx, -⟩, rfl⟩, he⟩ := Set.mem_iUnion₂.1 (ht hg)
    have h1 := QuotientGroup.eq.1 he
    have h2 : ι (x⁻¹ * g, z⁻¹) = (ι (x, z))⁻¹ * ι (g, 1) := by
      rw [← map_inv, ← map_mul]
      simp
    have h3 : x⁻¹ * g ∈ Γ' := (hmem _).2 ⟨z⁻¹, by rw [h2]; exact h1⟩
    refine ⟨x, Set.mem_iUnion₂.2 ⟨i, hi, Set.smul_set_mono interior_subset hx⟩, ?_⟩
    exact QuotientGroup.eq.2 h3

end NumberFieldKB.WeilBNT
