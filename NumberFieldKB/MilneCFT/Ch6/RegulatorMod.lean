import NumberFieldKB.MilneCFT.Ch6.RayZeta
import NumberFieldKB.MilneCFT.Ch5RayClassOrder

/-!
# The regulator of $U_{\mathfrak m,1}$

$\mathrm{reg}(\mathfrak m)\,w_K = \mathrm{reg}(K)\,(U : U_{\mathfrak m,1})\,w_\mathfrak m$ (the corrected form of Milne,
*CFT*, VI, p. 189; see the erratum in `Ch6/RayZeta.lean`): the logarithmic image of $U_{\mathfrak m,1}$ has index
$(U : U_{\mathfrak m,1}\mu_K) = (U : U_{\mathfrak m,1})\,w_\mathfrak m / w_K$ in the unit lattice, and the covolume of a
sublattice is the covolume of the lattice times the index.
-/

open NumberField IsDedekindDomain NumberField.Units NumberField.Units.dirichletUnitTheorem

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

variable {K : Type} [Field K] [NumberField K]

open Submodule in
theorem span_logImage_toAddSubgroup (H : Subgroup (𝓞 K)ˣ) :
    (span ℤ ((fun u : (𝓞 K)ˣ => logEmbedding K (Additive.ofMul u)) '' (H : Set (𝓞 K)ˣ))).toAddSubgroup =
      AddSubgroup.map (logEmbedding K) H.toAddSubgroup := by
  rw [span_int_eq_addSubgroupClosure]
  conv_rhs => rw [← AddSubgroup.closure_eq (Subgroup.toAddSubgroup H), AddMonoidHom.map_closure]
  rfl

theorem unitsMod_relIndex_ne_zero (m : Modulus K) :
    (congruenceSubgroup m).relIndex (unitsK K) ≠ 0 := by
  intro h0
  obtain ⟨hf, he⟩ := theorem_1_7_card m
  have := Nat.card_pos (α := RayClassGroup m)
  rw [h0] at he
  simp at he
  omega

theorem unitLattice_toAddSubgroup_eq :
    (unitLattice K).toAddSubgroup =
      AddSubgroup.map (logEmbedding K) (⊤ : Subgroup (𝓞 K)ˣ).toAddSubgroup := by
  ext x
  simp [unitLattice]

open Submodule in
theorem span_logImage_relIndex (H : Subgroup (𝓞 K)ˣ) :
    (span ℤ ((fun u : (𝓞 K)ˣ => logEmbedding K (Additive.ofMul u)) '' (H : Set (𝓞 K)ˣ))).toAddSubgroup.relIndex
      (unitLattice K).toAddSubgroup = (H ⊔ torsion K).index := by
  rw [span_logImage_toAddSubgroup, unitLattice_toAddSubgroup_eq, AddSubgroup.relIndex_map_map,
    logEmbedding_ker, ← OrderIso.map_sup, ← OrderIso.map_sup, Subgroup.relIndex_toAddSubgroup,
    top_sup_eq, Subgroup.relIndex_top_right]

theorem unitsMod_index (m : Modulus K) :
    (unitsMod m).index = (congruenceSubgroup m).relIndex (unitsK K) := by
  rw [unitsMod, Subgroup.index_comap]
  rfl

theorem regulatorMod_eq (m : Modulus K) :
    regulatorMod m = regulator K * ((unitsMod m ⊔ torsion K).index : ℝ) := by
  classical
  set S : Submodule ℤ (logSpace K) := Submodule.span ℤ
    ((fun u : (𝓞 K)ˣ => logEmbedding K (Additive.ofMul u)) '' (unitsMod m : Set (𝓞 K)ˣ)) with hSdef
  have hle : S ≤ unitLattice K := by
    rw [hSdef, ← Submodule.toAddSubgroup_le, span_logImage_toAddSubgroup, unitLattice_toAddSubgroup_eq]
    exact AddSubgroup.map_mono (fun _ _ => trivial)
  have hdisc : DiscreteTopology S := by
    rw [← SetLike.isDiscrete_iff_discreteTopology]
    exact (inferInstance : DiscreteTopology (unitLattice K)).isDiscrete.mono hle
  have hidx0 : (unitsMod m ⊔ torsion K).index ≠ 0 := by
    have h1 : (unitsMod m).index ≠ 0 := by
      rw [unitsMod_index]; exact unitsMod_relIndex_ne_zero m
    have : (unitsMod m).FiniteIndex := ⟨h1⟩
    exact (Subgroup.finiteIndex_of_le (le_sup_left : unitsMod m ≤ unitsMod m ⊔ torsion K)).index_ne_zero
  have hrel := span_logImage_relIndex (K := K) (unitsMod m)
  have hrel' := hrel
  rw [← hSdef] at hrel'
  have : IsZLattice ℝ S := by
    refine ⟨?_⟩
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := unitLattice K)]
    refine Submodule.span_le.2 fun x hx => ?_
    have hx' : x ∈ (unitLattice K).toAddSubgroup := hx
    have hmem := AddSubgroup.nsmul_relIndex_mem S.toAddSubgroup hx'
    rw [hrel'] at hmem
    have hn : ((unitsMod m ⊔ torsion K).index : ℝ) ≠ 0 := by exact_mod_cast hidx0
    have hS' : ((unitsMod m ⊔ torsion K).index : ℝ) • x ∈ Submodule.span ℝ (S : Set (logSpace K)) :=
      Submodule.subset_span (by
        have : ((unitsMod m ⊔ torsion K).index) • x ∈ S.toAddSubgroup := hmem
        simpa [Nat.cast_smul_eq_nsmul] using this)
    have := Submodule.smul_mem _ (((unitsMod m ⊔ torsion K).index : ℝ)⁻¹) hS'
    simpa [smul_smul, inv_mul_cancel₀ hn] using this
  have h := ZLattice.covolume_div_covolume_eq_relIndex S (unitLattice K) hle
  rw [hrel] at h
  have hpos : 0 < regulator K := regulator_pos K
  unfold regulatorMod
  rw [← hSdef]
  have : ZLattice.covolume S = regulator K * ((unitsMod m ⊔ torsion K).index : ℝ) := by
    have hne : ZLattice.covolume (unitLattice K) ≠ 0 := hpos.ne'
    have := (div_eq_iff hne).1 h
    unfold regulator
    rw [this, mul_comm]
  exact this

theorem index_mul_card (m : Modulus K) :
    (unitsMod m).index * Nat.card (unitsMod m ⊓ torsion K : Subgroup (𝓞 K)ˣ) =
      (unitsMod m ⊔ torsion K).index * Nat.card (torsion K) := by
  have h1 := Subgroup.relIndex_mul_index (le_sup_left : unitsMod m ≤ unitsMod m ⊔ torsion K)
  have h2 : (unitsMod m).relIndex (unitsMod m ⊔ torsion K) = (unitsMod m).relIndex (torsion K) := by
    rw [sup_comm]; exact Subgroup.relIndex_sup_right _ _
  have h3 : (unitsMod m ⊓ torsion K).relIndex (torsion K) * Nat.card (unitsMod m ⊓ torsion K : Subgroup (𝓞 K)ˣ)
      = Nat.card (torsion K) := by
    rw [Subgroup.relIndex, mul_comm]
    have := Subgroup.card_mul_index ((unitsMod m ⊓ torsion K).subgroupOf (torsion K))
    rw [← this]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv.symm
  rw [← h1, h2, ← Subgroup.inf_relIndex_right, ← h3]
  ring

/-- **$\mathrm{reg}(\mathfrak m)\,w_K = \mathrm{reg}(K)\,(U : U_{\mathfrak m,1})\,w_\mathfrak m$.** -/
theorem regulatorMod_mul (m : Modulus K) :
    regulatorMod m * (torsionOrder K : ℝ) =
      regulator K * ((congruenceSubgroup m).relIndex (unitsK K) : ℝ) * (rootsOfUnityMod m : ℝ) := by
  rw [regulatorMod_eq, ← unitsMod_index]
  have h := index_mul_card m
  have h' : ((unitsMod m).index : ℝ) * (rootsOfUnityMod m : ℝ) =
      ((unitsMod m ⊔ torsion K).index : ℝ) * (torsionOrder K : ℝ) := by
    exact_mod_cast h
  calc regulator K * ((unitsMod m ⊔ torsion K).index : ℝ) * (torsionOrder K : ℝ)
      = regulator K * (((unitsMod m ⊔ torsion K).index : ℝ) * (torsionOrder K : ℝ)) := by ring
    _ = _ := by rw [← h']; ring

end NumberFieldKB.MilneCFT.Ch6
