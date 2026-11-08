import NumberFieldKB.MilneCFT.LubinTate.LowerFiltrationYamaguchi
import NumberFieldKB.MilneCFT.LubinTate.HerbrandLubinTate
import NumberFieldKB.MilneCFT.LubinTate.RamificationQuotientTauCeti

/-!
# Propositions 4.1, 4.3 and Example 4.2 (Milne, *CFT*, I, §4), proved

* `lubinTateLowerFiltration`: Proposition 4.1 (`χ(U^{(i)}/U^{(n)}) = G_{q^i - 1}`, and `χ(u) ∉ G_{q^i}` for
  `u ∈ U^{(i)} \ U^{(i+1)}`), from `LubinTate/LowerFiltrationYamaguchi.lean`;
* `lubinTateHerbrand`: Example 4.2 (`φ(q^i - 1) = i`, `G^i = G_{q^i - 1}`), from Proposition 4.1 by
  `lubinTateHerbrand_of` (`LubinTate/HerbrandLubinTate.lean`) and the ramification quotient bounds
  (`ramificationQuotientBounds`, Tau Ceti);
* `lubinTateUpperFiltration`: Proposition 4.3 (`χ(U^{(i)}/U^{(n)}) = G^i`), by `lubinTateUpperFiltration_of`.

All for `K : Type` (Yamaguchi's local-field package).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Level

variable {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)

local notation "𝕃" => ltField Ω π (n + 1)

include hπ

theorem lowerFiltration_map_eq {χ : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ ≃* Gal(𝕃/K)}
    (hχ : ∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u) ⟨α, mem_ltField hα⟩ : 𝕃) : Ω) =
        ltAct hπ (n + 1) u α) (i : ℕ) (hi : i ≤ n + 1) :
    (unitFiltrationMod (n + 1) i).map χ.toMonoidHom = ramificationGroup 𝕃 (resCard K ^ i - 1) := by
  have hq : 1 ≤ resCard K ^ i := Nat.one_le_pow _ _ (resCard_pos hπ)
  ext σ
  constructor
  · rintro ⟨x, ⟨u, rfl, hu⟩, rfl⟩
    rw [MulEquiv.coe_toMonoidHom,
      mem_ramificationGroup_iff Ω hπ n _ _ _ (galRestrictInt_x0I_sub Ω hπ n hχ u).symm, Nat.sub_add_cancel hq]
    exact (principal_iff hπ n u i hi).2 hu
  · intro hσ
    obtain ⟨u, hu⟩ := units_map_mk_surjective (n + 1) (by omega) (χ.symm σ)
    have hσ' : σ = χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u) := by
      rw [hu, MulEquiv.apply_symm_apply]
    rw [hσ', mem_ramificationGroup_iff Ω hπ n _ _ _ (galRestrictInt_x0I_sub Ω hπ n hχ u).symm,
      Nat.sub_add_cancel hq, principal_iff hπ n u i hi] at hσ
    exact ⟨_, ⟨u, rfl, hσ⟩, hσ'.symm⟩

theorem lowerFiltration_not_mem {χ : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ ≃* Gal(𝕃/K)}
    (hχ : ∀ (u : 𝒪[K]ˣ) (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)),
      ((χ (Units.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))).toMonoidHom u) ⟨α, mem_ltField hα⟩ : 𝕃) : Ω) =
        ltAct hπ (n + 1) u α) (i : ℕ) (hi1 : 1 ≤ i) (hin : i < n + 1)
    (x : (𝒪[K] ⧸ 𝓂[K] ^ (n + 1))ˣ) (hx : x ∈ unitFiltrationMod (n + 1) i)
    (hx' : x ∉ unitFiltrationMod (n + 1) (i + 1)) :
    χ x ∉ ramificationGroup 𝕃 (resCard K ^ i) := by
  obtain ⟨u, rfl, -⟩ := hx
  intro hmem
  rw [mem_ramificationGroup_iff Ω hπ n _ _ _ (galRestrictInt_x0I_sub Ω hπ n hχ u).symm] at hmem
  have h := (principal_iff_interval hπ n u (i + 1) (by omega) (by omega)).1 (by simpa using hmem)
  exact hx' ⟨u, rfl, h⟩

end Level

variable (K) in
/-- **Proposition 4.1, proved** (Milne, *CFT*, I, Proposition 4.1), for `K : Type`. -/
@[kb "milne2020cft" "Ch. I, Proposition 4.1"]
theorem lubinTateLowerFiltration (h : LubinTateExtensionTheorem K Ω) : LubinTateLowerFiltration K Ω h where
  map_eq := fun {π} hπ n hn χ hχ i hi => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact lowerFiltration_map_eq Ω hπ m hχ i hi
  not_mem := fun {π} hπ n hn χ hχ i hi1 hin x hx hx' => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact lowerFiltration_not_mem Ω hπ m hχ i hi1 hin x hx hx'

variable (K) in
/-- **Proposition 4.1, proved**, for the isomorphism of Theorem 3.6 as proved here (no hypothesis). -/
@[kb "milne2020cft" "Ch. I, Proposition 4.1"]
theorem lubinTateLowerFiltration' : LubinTateLowerFiltration K Ω (lubinTateExtensionTheorem K Ω) :=
  lubinTateLowerFiltration K Ω _

variable (K) in
/-- **Example 4.2, proved** (Milne, *CFT*, I, Example 4.2), for `K : Type`. -/
@[kb "milne2020cft" "Ch. I, Example 4.2"]
theorem lubinTateHerbrand : LubinTateHerbrand K Ω :=
  lubinTateHerbrand_of (lubinTateExtensionTheorem K Ω) (lubinTateLowerFiltration K Ω _)
    (ramificationQuotientBounds K Ω)

variable (K) in
/-- **Proposition 4.3, proved** (Milne, *CFT*, I, Proposition 4.3), for `K : Type`. -/
@[kb "milne2020cft" "Ch. I, Proposition 4.3"]
theorem lubinTateUpperFiltration : LubinTateUpperFiltration K Ω :=
  lubinTateUpperFiltration_of (lubinTateExtensionTheorem K Ω) (lubinTateLowerFiltration K Ω _)
    (lubinTateHerbrand K Ω)

end NumberFieldKB.MilneCFT.LocalCFT
