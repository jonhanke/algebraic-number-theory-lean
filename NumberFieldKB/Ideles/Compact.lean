import NumberFieldKB.Ideles.Norm
import QuadFormsKB.Tamagawa.Measure.Weil.Fujisaki

/-!
# Compactness of the norm-one idele class group, on Mathlib's types

$F$ is a number field. Mathlib defines the idele class group $C_F$ = `IdeleClassGroup (𝓞 F) F` but not its norm-one
subgroup. Here:

* **`ideleGroupOne F`**: the ideles of norm one, $\mathbb A_F^1 = \{x : \|x\| = 1\}$ (Mathlib's norm, `mem_ideleGroupOne`),
  a closed subgroup containing the principal ideles;
* **`IdeleClassGroup.normOne F`**: its image $C_F^1 = \mathbb A_F^1/F^\times$ in Mathlib's idele class group;
* **`IdeleClassGroup.isCompact_normOne`**, **`IdeleClassGroup.compactSpace_normOne`**: $C_F^1$ is compact.

The proof transports QuadFormsKB's `exists_isCompact_ideleOne_mul_mem` (Fujisaki's argument from the adelic Minkowski
theorem, which gives `compactSpace_ideleClassOne`) through `ideleGroupEquiv F`; no new analysis. Independent proofs of
the same statement on Mathlib's types are in Tau Ceti (`IdeleClassGroup.compactSpace_normOne`) and in the class field
theory library port (`IdeleClassGroup.normOneSubgroup_isCompact`); neither is imported.
-/

open IsDedekindDomain NumberField
open QuadFormsKB.Tamagawa.Measure.Weil
open scoped NNReal

namespace NumberFieldKB.Ideles

noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- **The ideles of norm one** $\mathbb A_F^1$ in Mathlib's idele group. -/
def ideleGroupOne : Subgroup (IdeleGroup (𝓞 F) F) := (ideleGroupNorm F).ker

variable {F}

theorem mem_ideleGroupOne {x : IdeleGroup (𝓞 F) F} :
    x ∈ ideleGroupOne F ↔ ‖(x : AdeleRing (𝓞 F) F)‖ = 1 := by
  rw [ideleGroupOne, MonoidHom.mem_ker, ← coe_ideleGroupNorm, NNReal.coe_eq_one]

theorem isClosed_ideleGroupOne : IsClosed (ideleGroupOne F : Set (IdeleGroup (𝓞 F) F)) :=
  isClosed_eq continuous_ideleGroupNorm continuous_const

/-- `ideleGroupEquiv F` carries $\mathbb A_F^1$ (Mathlib's norm) onto QuadFormsKB's `ideleOne F`. -/
theorem mem_ideleGroupOne_iff_mem_ideleOne {x : IdeleGroup (𝓞 F) F} :
    x ∈ ideleGroupOne F ↔ ideleGroupEquiv F x ∈ ideleOne F := by
  rw [mem_ideleGroupOne, mem_ideleOne, norm_eq_ideleNorm]

theorem map_ideleGroupOne_ideleGroupEquiv :
    (ideleGroupOne F).map (ideleGroupEquiv F : IdeleGroup (𝓞 F) F →* (Adeles F)ˣ) = ideleOne F := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_ideleGroupOne_iff_mem_ideleOne.mp hx
  · intro hg
    refine ⟨(ideleGroupEquiv F).symm g, mem_ideleGroupOne_iff_mem_ideleOne.mpr ?_, ?_⟩
    · rwa [ContinuousMulEquiv.apply_symm_apply]
    · exact (ideleGroupEquiv F).apply_symm_apply g

theorem principalSubgroup_le_ideleGroupOne : IdeleGroup.principalSubgroup (𝓞 F) F ≤ ideleGroupOne F :=
  fun _ hx => ideleGroupNorm_eq_one_of_mem_principalSubgroup hx

variable (F) in
/-- **The norm-one idele class group** $C_F^1 = \mathbb A_F^1/F^\times\le C_F$, on Mathlib's `IdeleClassGroup`. -/
def IdeleClassGroup.normOne : Subgroup (IdeleClassGroup (𝓞 F) F) :=
  (ideleGroupOne F).map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F))

theorem IdeleClassGroup.mem_normOne_mk (x : IdeleGroup (𝓞 F) F) :
    (x : IdeleClassGroup (𝓞 F) F) ∈ IdeleClassGroup.normOne F ↔ x ∈ ideleGroupOne F := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have h := QuotientGroup.eq.mp hxy
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact mul_mem hy (principalSubgroup_le_ideleGroupOne h)
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- **$C_F^1$ is compact** (Mathlib's types), transported from QuadFormsKB's `exists_isCompact_ideleOne_mul_mem`. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §4.3 [unverified locator] (J⁰/k^× is compact)"]
theorem IdeleClassGroup.isCompact_normOne :
    IsCompact (IdeleClassGroup.normOne F : Set (IdeleClassGroup (𝓞 F) F)) := by
  obtain ⟨C, hC, hCx⟩ := exists_isCompact_ideleOne_mul_mem F
  set C' : Set (IdeleGroup (𝓞 F) F) := (ideleGroupEquiv F).symm '' (Subtype.val '' C)
  have hC' : IsCompact C' :=
    (hC.image continuous_subtype_val).image (ideleGroupEquiv F).symm.continuous
  have hset : (IdeleClassGroup.normOne F : Set (IdeleClassGroup (𝓞 F) F)) =
      (QuotientGroup.mk : IdeleGroup (𝓞 F) F → IdeleClassGroup (𝓞 F) F) '' C' := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [SetLike.mem_coe, IdeleClassGroup.mem_normOne_mk]
    constructor
    · intro hx
      have hg : ideleGroupEquiv F x ∈ ideleOne F := mem_ideleGroupOne_iff_mem_ideleOne.mp hx
      obtain ⟨γ, hγ, hmem⟩ := hCx ⟨_, hg⟩
      obtain ⟨ξ, hξ⟩ := (Subgroup.mem_subgroupOf.mp hγ : (γ : (Adeles F)ˣ) ∈ diagUnitsSub F)
      set z : (Adeles F)ˣ := ((γ⁻¹ * ⟨_, hg⟩ : ideleOne F) : (Adeles F)ˣ) with hz
      have hzC : z ∈ Subtype.val '' C := ⟨_, hmem, rfl⟩
      refine ⟨(ideleGroupEquiv F).symm z, Set.mem_image_of_mem _ hzC, ?_⟩
      rw [QuotientGroup.eq]
      refine ⟨ξ, (ideleGroupEquiv F).injective ?_⟩
      have hz' : z = (γ : (Adeles F)ˣ)⁻¹ * ideleGroupEquiv F x := rfl
      rw [ideleGroupEquiv_unitEmbedding, hξ, map_mul, map_inv, ContinuousMulEquiv.apply_symm_apply, hz',
        mul_inv_rev, inv_inv]
      rw [mul_comm _ (γ : (Adeles F)ˣ), mul_assoc, inv_mul_cancel, mul_one]
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨z, ⟨w, hw, hwz⟩, hzy⟩ := hy
      have hymem : y ∈ ideleGroupOne F := by
        rw [mem_ideleGroupOne_iff_mem_ideleOne, ← hzy, ContinuousMulEquiv.apply_symm_apply, ← hwz]
        exact w.2
      rw [← IdeleClassGroup.mem_normOne_mk, ← hyx, IdeleClassGroup.mem_normOne_mk]
      exact hymem
  rw [hset]
  exact hC'.image QuotientGroup.continuous_mk

instance IdeleClassGroup.compactSpace_normOne : CompactSpace (IdeleClassGroup.normOne F) :=
  isCompact_iff_compactSpace.mp IdeleClassGroup.isCompact_normOne

end

end NumberFieldKB.Ideles
