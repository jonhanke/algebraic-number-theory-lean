import NumberFieldKB.MilneCFT.LocalCFT.Uniqueness
import NumberFieldKB.MilneCFT.LocalCFT.Consequences
import NumberFieldKB.MilneCFT.LubinTate.Extension

open scoped ValuativeRel
noncomputable section
namespace NumberFieldKB.MilneCFT.LocalCFT
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem unitFiltration_le_unitGroup (n : ℕ) : unitFiltration K n ≤ unitGroup K := by
  rintro x ⟨u, hu, w, hw, -⟩
  refine mem_unitGroup.2 ⟨⟨u, w, ?_, ?_⟩, ?_⟩
  · apply Subtype.val_injective
    have : (x : K) * (x⁻¹ : Kˣ) = 1 := by simp
    simp [hu, hw]
  · apply Subtype.val_injective
    have : (x⁻¹ : Kˣ) * (x : K) = 1 := by simp
    simp [hu, hw]
  · exact hu

/-- `⟨π⟩ U^{(n)} ∩ U = U^{(n)}`. -/
theorem zpowers_sup_unitFiltration_inf_unitGroup {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    (Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n) ⊓ unitGroup K ≤ unitFiltration K n := by
  rintro x ⟨hx, hxU⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hzU := unitFiltration_le_unitGroup n hz
  have : primeUnit hπ ^ k ∈ unitGroup K := by
    have := (unitGroup K).mul_mem hxU ((unitGroup K).inv_mem hzU)
    simpa using this
  have hk := zpow_primeUnit_mem_unitGroup hπ this
  subst hk
  simpa using hz

theorem units_map_mk_surjective' (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom) := by
  have : Nontrivial (𝒪[K] ⧸ 𝓂[K] ^ n) := by
    apply Ideal.Quotient.nontrivial_iff.2
    intro htop
    have : 𝓂[K] ^ n ≤ 𝓂[K] := Ideal.pow_le_self (by omega)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (htop ▸ this))
  exact IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)

/-- the inclusion `𝒪ˣ → Kˣ`. -/
def unitsToK : 𝒪[K]ˣ →* Kˣ :=
  Units.map ((Valuation.integer (ValuativeRel.valuation K)).subtype : 𝒪[K] →* K)

theorem unitsToK_mem_unitFiltration_iff (n : ℕ) (u : 𝒪[K]ˣ) :
    unitsToK u ∈ unitFiltration K n ↔ Ideal.Quotient.mk (𝓂[K] ^ n) (u : 𝒪[K]) = 1 := by
  rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ n)), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  constructor
  · rintro ⟨v, hv, w, hw, h⟩
    have : v = (u : 𝒪[K]) := Subtype.val_injective (by simpa [unitsToK] using hv)
    rwa [this] at h
  · intro h
    exact ⟨u, rfl, ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]), by rw [← map_inv]; rfl, h⟩

theorem index_zpowers_sup_unitFiltration {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    (Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n).index = (resCard K - 1) * resCard K ^ (n - 1) := by
  set H := Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n with hH
  let f : 𝒪[K]ˣ →* Kˣ ⧸ H := (QuotientGroup.mk' H).comp unitsToK
  let g : 𝒪[K]ˣ →* (𝒪[K] ⧸ 𝓂[K] ^ n)ˣ := Units.map (Ideal.Quotient.mk (𝓂[K] ^ n)).toMonoidHom
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨u, hu, k, rfl⟩ := exists_unit_zpow π hπ x
    obtain ⟨v, hv⟩ := mem_unitGroup.1 hu
    refine ⟨v, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    have : unitsToK v = u := Units.ext hv
    rw [this, QuotientGroup.eq]
    have : (u⁻¹ * (u * primeUnit hπ ^ k)) = primeUnit hπ ^ k := by group
    rw [this]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)
  have hker : f.ker = g.ker := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : f u = 1 ↔ unitsToK u ∈ H := by
      simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
      exact QuotientGroup.eq_one_iff _
    have h2 : g u = 1 ↔ Ideal.Quotient.mk (𝓂[K] ^ n) (u : 𝒪[K]) = 1 := by
      simp only [g]
      rw [Units.ext_iff]
      simp
    rw [h1, h2, ← unitsToK_mem_unitFiltration_iff]
    constructor
    · intro h
      exact zpowers_sup_unitFiltration_inf_unitGroup hπ n
        ⟨h, mem_unitGroup.2 ⟨u, rfl⟩⟩
    · intro h
      exact Subgroup.mem_sup_right h
  have e1 := QuotientGroup.quotientKerEquivOfSurjective f hf
  have e2 := QuotientGroup.quotientKerEquivOfSurjective g (units_map_mk_surjective' n hn)
  rw [← card_units_quot_maximalIdeal_pow n hn, ← Nat.card_congr e2.toEquiv, ← hker,
    Subgroup.index, Nat.card_congr e1.symm.toEquiv]

/-- A subgroup containing `π` and `U^{(n)}` with index `(q - 1) q^{n-1}` is `⟨π⟩ U^{(n)}`. -/
theorem eq_zpowers_sup_unitFiltration {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) (N : Subgroup Kˣ)
    (hπN : primeUnit hπ ∈ N) (hU : unitFiltration K n ≤ N)
    (hidx : N.index = (resCard K - 1) * resCard K ^ (n - 1)) :
    N = Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n := by
  have hle : Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n ≤ N :=
    sup_le ((Subgroup.zpowers_le).2 hπN) hU
  have hi := index_zpowers_sup_unitFiltration hπ n hn
  have hq : 2 ≤ resCard K := by
    have : Nontrivial 𝓀[K] := inferInstance
    have : Finite 𝓀[K] := inferInstance
    exact Finite.one_lt_card (α := 𝓀[K])
  have hne : (resCard K - 1) * resCard K ^ (n - 1) ≠ 0 := by
    have : 0 < resCard K - 1 := by omega
    positivity
  have h := Subgroup.relIndex_mul_index hle
  rw [hi, ← hidx] at h
  have h1 : (Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n).relIndex N = 1 := by
    have : N.index ≠ 0 := by rw [hidx]; exact hne
    exact (Nat.mul_eq_right this).1 h
  exact ((Subgroup.relIndex_eq_one.1 h1).antisymm hle)
end NumberFieldKB.MilneCFT.LocalCFT
