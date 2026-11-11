import NumberFieldKB.MilneCFT.LubinTate.NormGroupTauCeti
import NumberFieldKB.MilneCFT.LubinTate.ExponentDecompositionCFT
import NumberFieldKB.MilneCFT.LocalCFT.UnitFiltrationIndex
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Theorem 4.8 (local Kronecker–Weber) (Milne, *CFT*, I, §4), proved

`localKroneckerWeber`: the named statement `LocalKroneckerWeber K Ω` (for `K Ω : Type`): every finite abelian
extension `L/K` lies in `K_π K^{un}`.

Proof by norm groups. `Nm(K_{π,n}^×) = ⟨π⟩ U^{(n)}` (`normGroup_ltField`): it contains `π` (Theorem 3.6 (c)) and
`U^{(n)}` (`unitFiltration_le_normGroup_ltField`, from Proposition 4.3 and Tau Ceti's norm surjectivity above the upper
breaks), and has index `[K_{π,n} : K] = (q-1)q^{n-1}` (`index_normGroup`, `eq_zpowers_sup_unitFiltration`). Given
`L`, its norm group `N` contains some `U^{(n)}` (Tau Ceti `exists_unitFiltration_le_normGroup`) and `π^f`,
`f = (K^× : N)`. With `K_f` unramified of degree `f`, `Nm((K_{π,n} K_f)^×) = ⟨π⟩U^{(n)} ∩ Nm(K_f^×) ⊆ ⟨π^f⟩ U^{(n)}
⊆ N`, so `L ⊆ K_{π,n} K_f ⊆ K_π K^{un}` (`le_iff_normGroup_le`).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem unitFiltration_succ_le (n : ℕ) : unitFiltration K (n + 1) ≤ unitFiltration K n := by
  rintro x ⟨u, hu, w, hw, huw⟩
  exact ⟨u, hu, w, hw, Ideal.pow_le_pow_right (Nat.le_succ n) huw⟩

variable {K}

/-- **`Nm(K_{π,n}^×) = ⟨π⟩ U^{(n)}`** (`n ≥ 1`). -/
theorem normGroup_ltField {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    normGroup (ltField Ω π n) = Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n := by
  obtain ⟨φ, hφ⟩ := (localReciprocityExistence K Ω).exists_artin
  have h := lubinTateExtensionTheorem K Ω
  refine eq_zpowers_sup_unitFiltration hπ n hn _ (h.isNorm hπ n)
    (unitFiltration_le_normGroup_ltField Ω hπ n hn) ?_
  rw [show normGroup (ltField Ω π n) = normGroup (ltFieldExt h hπ hn).toField from rfl, index_normGroup hφ]
  exact h.finrank_eq hπ n hn

variable (K) in
/-- **Theorem 4.8 (local Kronecker–Weber), proved** (Milne, *CFT*, I, Theorem 4.8), for `K Ω : Type`. -/
@[kb "milne2020cft" "Ch. I, Theorem 4.8"]
theorem localKroneckerWeber : LocalKroneckerWeber K Ω := by
  refine ⟨fun {π} hπ L => ?_⟩
  obtain ⟨φ, hφ⟩ := (localReciprocityExistence K Ω).exists_artin
  have hLT := lubinTateExtensionTheorem K Ω
  set N := normGroup L.toField with hN
  haveI : N.FiniteIndex := ⟨by rw [hN, index_normGroup hφ L]; exact Module.finrank_pos.ne'⟩
  -- `U^{(n)} ⊆ N` for some `n ≥ 1`
  obtain ⟨n0, hn0⟩ : ∃ n, unitFiltration K n ≤ N := by
    have : Algebra.IsSeparable K Ω := IsSepClosure.separable
    have : Algebra.IsSeparable K L.toField := Algebra.isSeparable_tower_bot_of_isSeparable K L.toField Ω
    obtain ⟨n, hn⟩ := TauCeti.exists_unitFiltration_le_normGroup (K := K) (L := L.toField)
    exact ⟨n, by rw [unitFiltration_eq_tauCeti, hN, normGroup_eq_tauCeti]; exact hn⟩
  set n := n0 + 1
  have hn : 1 ≤ n := by omega
  have hUN : unitFiltration K n ≤ N := (unitFiltration_succ_le K n0).trans hn0
  -- `π^f ∈ N`
  set f := N.index
  have hf : 1 ≤ f := Nat.one_le_iff_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero
  have hπf : primeUnit hπ ^ f ∈ N := Subgroup.pow_index_mem N _
  obtain ⟨Kf, hKf, hdeg⟩ := (unramifiedInput K Ω).exists_unramified f hf
  let M := (ltFieldExt hLT hπ hn).sup Kf
  have hle : L.toField ≤ M.toField := by
    rw [le_iff_normGroup_le hφ L M]
    change normGroup (ltField Ω π n ⊔ Kf.toField) ≤ N
    rw [show normGroup (ltField Ω π n ⊔ Kf.toField) =
        normGroup ((ltFieldExt hLT hπ hn).toField ⊔ Kf.toField) from rfl, normGroup_sup hφ]
    rintro x ⟨hx1, hx2⟩
    change x ∈ normGroup (ltField Ω π n) at hx1
    rw [normGroup_ltField Ω hπ n hn] at hx1
    obtain ⟨u, hu, j, rfl⟩ := normGroup_unramified_le (unramifiedInput K Ω) hφ hπ Kf hKf hx2
    have hpj : primeUnit hπ ^ ((Module.finrank K Kf.toField : ℤ) * j) ∈
        Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n :=
      Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ _)
    have hu' : u ∈ (Subgroup.zpowers (primeUnit hπ) ⊔ unitFiltration K n) ⊓ unitGroup K := by
      refine ⟨?_, hu⟩
      have := Subgroup.mul_mem _ hx1 (Subgroup.inv_mem _ hpj)
      simpa using this
    have huN : u ∈ N := hUN (zpowers_sup_unitFiltration_inf_unitGroup hπ n hu')
    have hpN : primeUnit hπ ^ ((Module.finrank K Kf.toField : ℤ) * j) ∈ N := by
      rw [hdeg, zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ hπf _
    exact N.mul_mem huN hpN
  refine hle.trans (sup_le_sup ?_ ?_)
  · exact le_iSup (fun m => ltField Ω π m) n
  · exact le_iSup₂_of_le (f := fun (L : IntermediateField K Ω) (_ : FiniteDimensional K L ∧ IsUnramifiedExt L) => L)
      Kf.toField ⟨inferInstance, hKf⟩ le_rfl

end NumberFieldKB.MilneCFT.LocalCFT
