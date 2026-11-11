import NumberFieldKB.MilneCFT.LubinTate.LocalKroneckerWeberCFT
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Lemma 4.9 (Milne, *CFT*, I, §4), proved by norm groups

`lubinTateTotallyRamified`: the named statement `LubinTateTotallyRamified K Ω` (for `K Ω : Type`): an abelian
extension `L ⊇ K_π` all of whose finite subextensions are totally ramified is `K_π`.

Proof. Let `x ∈ L` and `M = K(x)` (abelian over `K`, `IsAbelianGalois.tower_bot`). Choose `n ≥ 1` with
`U^{(n)} ⊆ Nm(M^×)` and put `E = M K_{π,n} ⊆ L`, so `U^{(n)} ⊆ Nm(E^×) ⊆ Nm(K_{π,n}^×) = ⟨π⟩U^{(n)}`. As `E` is
totally ramified, some prime element `ϖ = π w` (`w ∈ 𝒪_K^×`) is a norm from `E` (Exercise 1.16); then
`w ∈ ⟨π⟩U^{(n)} ∩ U = U^{(n)}`, so `π ∈ Nm(E^×)` and `Nm(K_{π,n}^×) ⊆ Nm(E^×)`, i.e. `E ⊆ K_{π,n}`.
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable {K Ω} in
/-- The norm group of a finite abelian extension contains some `U^{(n)}`, `n ≥ 1`. -/
theorem exists_unitFiltration_le_normGroup_pos (L : FiniteAbelianExt K Ω) :
    ∃ n, 1 ≤ n ∧ unitFiltration K n ≤ normGroup L.toField := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : Algebra.IsSeparable K L.toField := Algebra.isSeparable_tower_bot_of_isSeparable K L.toField Ω
  obtain ⟨n, hn⟩ := TauCeti.exists_unitFiltration_le_normGroup (K := K) (L := L.toField)
  refine ⟨n + 1, by omega, (unitFiltration_succ_le K n).trans ?_⟩
  rw [unitFiltration_eq_tauCeti, normGroup_eq_tauCeti]
  exact hn

/-- **Lemma 4.9, proved** (Milne, *CFT*, I, Lemma 4.9), for `K Ω : Type`. -/
@[kb "milne2020cft" "Ch. I, Lemma 4.9"]
theorem lubinTateTotallyRamified : LubinTateTotallyRamified K Ω := by
  refine ⟨fun {π} hπ L hGal hcomm htot hle => le_antisymm ?_ hle⟩
  obtain ⟨φ, hφ⟩ := (localReciprocityExistence K Ω).exists_artin
  have hLT := lubinTateExtensionTheorem K Ω
  haveI : IsAbelianGalois K L := { hGal with is_comm := ⟨hcomm⟩ }
  intro x hx
  set M0 : IntermediateField K Ω := IntermediateField.adjoin K {x}
  have hM0L : M0 ≤ L := IntermediateField.adjoin_simple_le_iff.2 hx
  letI : Algebra M0 L := (IntermediateField.inclusion hM0L).toAlgebra
  haveI : IsScalarTower K M0 L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAbelianGalois K M0 := IsAbelianGalois.tower_bot K M0 L
  haveI : FiniteDimensional K M0 :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K) x)
  let M : FiniteAbelianExt K Ω := ⟨M0⟩
  obtain ⟨n, hn, hnM⟩ := exists_unitFiltration_le_normGroup_pos M
  let Ln := ltFieldExt hLT hπ hn
  let E := M.sup Ln
  have hEL : E.toField ≤ L := sup_le hM0L ((le_iSup (fun m => ltField Ω π m) n).trans hle)
  have hNE : normGroup E.toField = normGroup M.toField ⊓ normGroup Ln.toField := normGroup_sup hφ M Ln
  have hNLn : normGroup Ln.toField = Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n :=
    normGroup_ltField Ω hπ n hn
  have hUE : unitFiltration K n ≤ normGroup E.toField := by
    rw [hNE]; exact le_inf hnM (unitFiltration_le_normGroup_ltField Ω hπ n hn)
  obtain ⟨ϖ, hϖ, hϖN⟩ := ((totallyRamifiedNormInput K Ω).iff E.toField).1 (htot E.toField hEL inferInstance)
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hπ hϖ
  have hrel : primeUnit hϖ = primeUnit hπ * unitToK w := by
    ext
    simp only [coe_primeUnit, Units.val_mul, unitToK, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    rw [← hw]
    rfl
  have hwU : unitToK w ∈ unitGroup K := mem_unitGroup.2 ⟨w, rfl⟩
  have hwN : unitToK w ∈ Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n := by
    have h1 : primeUnit hϖ ∈ normGroup Ln.toField := (hNE ▸ hϖN).2
    have h2 : primeUnit hπ ∈ normGroup Ln.toField := hLT.isNorm hπ n
    rw [hNLn] at h1 h2
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h2) h1
    rwa [hrel, inv_mul_cancel_left] at this
  have hwUn : unitToK w ∈ unitFiltration K n := zpowers_sup_unitFiltration_inf_unitGroup hπ n ⟨hwN, hwU⟩
  have hπE : primeUnit hπ ∈ normGroup E.toField := by
    have := Subgroup.mul_mem _ hϖN (Subgroup.inv_mem _ (hUE hwUn))
    rwa [hrel, mul_inv_cancel_right] at this
  have hle' : normGroup Ln.toField ≤ normGroup E.toField := by
    rw [hNLn]
    exact sup_le ((Subgroup.zpowers_le).2 hπE) hUE
  have hEle : E.toField ≤ Ln.toField := (le_iff_normGroup_le hφ E Ln).2 hle'
  have hxE : x ∈ E.toField := le_sup_left (a := M0) (IntermediateField.mem_adjoin_simple_self K x)
  exact le_iSup (fun m => ltField Ω π m) n (hEle hxE)

end NumberFieldKB.MilneCFT.LocalCFT
