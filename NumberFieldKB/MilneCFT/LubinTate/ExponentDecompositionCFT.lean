import NumberFieldKB.MilneCFT.LubinTate.KroneckerWeber
import NumberFieldKB.MilneCFT.LocalCFT.UnconditionalYamaguchi
import NumberFieldKB.MilneCFT.LocalCFT.TotallyRamifiedTauCeti
import NumberFieldKB.MilneCFT.LocalCFT.UnramifiedTauCeti
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Lemma 4.11 (Milne, *CFT*, I, §4), proved by local class field theory

`exponentDecomposition`: the named statement `ExponentDecomposition K Ω` (for `K Ω : Type`).

Proof (norm groups instead of Milne's Lubin–Tate argument). Let `L/K` be finite abelian of exponent `m`, `K_m` the
unramified extension of degree `m`, `N = Nm(L^×)`. Every `a^m` lies in `N` (`K^×/N ≅ Gal(L/K)` has exponent `m`).
The subgroup `H = (N ∩ U_K)⟨π⟩` is open of finite index, hence `H = Nm(L_t^×)` for a finite abelian `L_t`
(existence theorem, `existsUnique_normGroup_eq_unconditional`), which is totally ramified since `π` is a norm
(Exercise 1.16, `totallyRamifiedNormInput`). Finally `Nm(K_m^×) ⊆ U_K⟨π^m⟩` (`normGroup_unramified_le`) gives
`N ∩ Nm(K_m^×) = H ∩ Nm(K_m^×)`, i.e. `Nm((L K_m)^×) = Nm((L_t K_m)^×)` (`normGroup_sup`), so `L K_m = L_t K_m`
(`normGroup_injective`).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Lemma 4.11, proved** (Milne, *CFT*, I, Lemma 4.11), by local class field theory, for `K Ω : Type`. -/
@[kb "milne2020cft" "Ch. I, Lemma 4.11"]
theorem exponentDecomposition : ExponentDecomposition K Ω := by
  refine ⟨fun L m hexp Km hKm hdeg => ?_⟩
  obtain ⟨φ, hφ⟩ := (localReciprocityExistence K Ω).exists_artin
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set N := normGroup L.toField with hN
  have hpow : ∀ a : Kˣ, a ^ m ∈ N := fun a => by
    rw [hN, ← hφ.ker_eq L, MonoidHom.mem_ker, map_pow, hexp]
  haveI : N.FiniteIndex := ⟨by rw [hN, index_normGroup hφ L]; exact Module.finrank_pos.ne'⟩
  set H := (N ⊓ unitGroup K) ⊔ Subgroup.zpowers (primeUnit hπ) with hH
  have hHfi : H.FiniteIndex := finiteIndex_inf_unitGroup_sup N hπ
  have hNo : IsOpen (N : Set Kˣ) := (normGroupOpenInput K Ω).isOpen L.toField inferInstance
  have hHo : IsOpen (H : Set Kˣ) :=
    Subgroup.isOpen_mono le_sup_left (by rw [Subgroup.coe_inf]; exact hNo.inter isOpen_unitGroup)
  obtain ⟨Lt, hLt, -⟩ := existsUnique_normGroup_eq_unconditional Ω H hHo hHfi
  refine ⟨Lt, ((totallyRamifiedNormInput K Ω).iff Lt.toField).2
    ⟨π, hπ, hLt ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩, ?_⟩
  apply normGroup_injective hφ (L := L.sup Km) (L' := Lt.sup Km)
  change normGroup (L.toField ⊔ Km.toField) = normGroup (Lt.toField ⊔ Km.toField)
  rw [normGroup_sup hφ, normGroup_sup hφ, hLt, ← hN]
  have hpm : ∀ j : ℤ, primeUnit hπ ^ ((Module.finrank K Km.toField : ℤ) * j) ∈ N := by
    intro j
    rw [hdeg, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ (hpow _) _
  ext x
  constructor
  · rintro ⟨hxN, hxK⟩
    refine ⟨?_, hxK⟩
    obtain ⟨u, hu, j, rfl⟩ := normGroup_unramified_le (unramifiedInput K Ω) hφ hπ Km hKm hxK
    have huN : u ∈ N := by
      have := N.mul_mem hxN (N.inv_mem (hpm j))
      simpa using this
    exact H.mul_mem (Subgroup.mem_sup_left ⟨huN, hu⟩) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))
  · rintro ⟨hxH, hxK⟩
    refine ⟨?_, hxK⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hxH
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨u, hu, j, hx⟩ := normGroup_unramified_le (unramifiedInput K Ω) hφ hπ Km hKm hxK
    have he : primeUnit hπ ^ (k - (Module.finrank K Km.toField : ℤ) * j) = y⁻¹ * u := by
      rw [zpow_sub, eq_comm, eq_mul_inv_iff_mul_eq, mul_assoc, ← hx, inv_mul_cancel_left]
    have hk := zpow_primeUnit_mem_unitGroup hπ (he ▸ (unitGroup K).mul_mem ((unitGroup K).inv_mem hy.2) hu)
    have hk' : k = (Module.finrank K Km.toField : ℤ) * j := by omega
    rw [hk']
    exact N.mul_mem hy.1 (hpm j)

end NumberFieldKB.MilneCFT.LocalCFT
