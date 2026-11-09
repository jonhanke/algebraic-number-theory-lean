import NumberFieldKB.MilneCFT.LubinTate.FiltrationYamaguchi
import NumberFieldKB.MilneCFT.LubinTate.HerbrandTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.Consequences
import NumberFieldKB.MilneCFT.LocalCFT.TotallyRamifiedTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Norm.Surjectivity

open scoped ValuativeRel
noncomputable section
namespace NumberFieldKB.MilneCFT.LocalCFT

/-- Our unit filtration is Tau Ceti's. -/
theorem unitFiltration_eq_tauCeti {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : unitFiltration K n = TauCeti.unitFiltration K n := by
  ext x
  rw [TauCeti.mem_unitFiltration_iff_exists]
  constructor
  · rintro ⟨u, hu, w, hw, huw⟩
    have huw1 : u * w = 1 := by
      apply Subtype.val_injective
      simp [hu, hw]
    exact ⟨⟨u, w, huw1, by rw [mul_comm]; exact huw1⟩, huw, hu⟩
  · rintro ⟨u, h, hu⟩
    refine ⟨u, hu, (u⁻¹ : 𝒪[K]ˣ), ?_, h⟩
    have : ((u : 𝒪[K]) : K) * (((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) : K) = 1 := by
      rw [← Subring.coe_mul]; simp
    rw [hu] at this
    rw [Units.val_inv_eq_inv_val]
    exact (eq_inv_of_mul_eq_one_right this).symm.symm

/-- Our norm group is Tau Ceti's. -/
theorem normGroup_eq_tauCeti {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L] :
    normGroup L = TauCeti.normGroup K L := by
  ext x
  rw [TauCeti.mem_normGroup_iff]
  simp only [normGroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩; exact ⟨y, Units.ext hy⟩

/-- `U^{(n)} ⊆ Nm(K_{π,n}^×)` for `n ≥ 1` (Milne, *CFT*, I, proof of Theorem 4.8). -/
theorem unitFiltration_le_normGroup_ltField {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    unitFiltration K n ≤ normGroup (ltField Ω π n) := by
  have hG := ltField_isGalois (lubinTateExtensionTheorem K Ω) hπ hn
  obtain ⟨χ, hχ⟩ := (lubinTateExtensionTheorem K Ω).galois hπ n hn
  have hbot : upperRamificationGroup (ltField Ω π n) (n : ℝ) = ⊥ := by
    have := (lubinTateUpperFiltration K Ω).map_eq hπ n hn χ hχ n le_rfl
    rw [← this, unitFiltrationMod_self, Subgroup.map_bot]
  set L := ltField Ω π n with hL
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology K Ω L
  have : ValuativeExtension K L := TauCeti.finiteIntermediateField_valuativeExtension K Ω L
  have : IsNonarchimedeanLocalField L := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  rw [upperRamificationGroup_eq L (n : ℝ) (Nat.cast_nonneg n)] at hbot
  rw [unitFiltration_eq_tauCeti, normGroup_eq_tauCeti]
  exact TauCeti.unitFiltration_le_normGroup_of_upperRamificationGroup_eq_bot (K := K) (L := L) hbot

end NumberFieldKB.MilneCFT.LocalCFT
