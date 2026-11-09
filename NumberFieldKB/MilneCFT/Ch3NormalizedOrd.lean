import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Invariant
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.GaloisAction
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.AlgebraicExtension.Basic

/-!
# Existence of the normalized valuation $\mathrm{ord}_M$ (Milne, *CFT*, III, §1, p. 99)

Tau Ceti's local-field structure on a finite extension $M/K$ gives the normalized valuation
`TauCeti.normalizedValuation M`; read additively it satisfies `IsNormalizedOrd`.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Existence of the normalized valuation $\mathrm{ord}_M$ (Milne, CFT, III, §1, p. 99). -/
theorem exists_isNormalizedOrd (M : IntermediateField K Ω) [FiniteDimensional K M] :
    ∃ v : Additive Mˣ →+ ℤ, IsNormalizedOrd M v := by
  let _ := TauCeti.algebraicExtensionValuativeRel K M
  let _ := TauCeti.algebraicExtensionNormedFieldTopology K M
  have := TauCeti.finiteExtension_isNonarchimedeanLocalField K M
  have := TauCeti.algebraicExtension_valuativeExtension K M
  have hmem : ∀ x : M, x ∈ integers M ↔ x ∈ 𝒪[M] := by
    intro x
    constructor
    · intro hx
      have h := (TauCeti.integerRingEquivIntegralClosure K M).symm ⟨x, hx⟩ |>.2
      rwa [TauCeti.coe_integerRingEquivIntegralClosure_symm_apply] at h
    · intro hx
      have h := (TauCeti.integerRingEquivIntegralClosure K M ⟨x, hx⟩).2
      rwa [TauCeti.coe_integerRingEquivIntegralClosure_apply] at h
  let v : Additive Mˣ →+ ℤ :=
    { toFun := fun x => (TauCeti.normalizedValuation M x.toMul).toAdd
      map_zero' := by simp
      map_add' := fun a b => by simp }
  have hv : ∀ x : Mˣ, v (Additive.ofMul x) = (TauCeti.normalizedValuation M x).toAdd := fun _ => rfl
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [hv, mem_unitsL, hmem, hmem, TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg,
      show ((x⁻¹ : Mˣ) : M) ∈ 𝒪[M] ↔ _ from
        TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg (x⁻¹), map_inv]
    simp only [toAdd_inv]
    omega
  · intro n
    obtain ⟨a, ha⟩ := TauCeti.normalizedValuation_surjective (K := M) (Multiplicative.ofAdd n)
    exact ⟨Additive.ofMul a, by rw [hv, ha]; rfl⟩
  · intro x hx
    rw [hv]
    exact (TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg x).1 ((hmem _).1 hx)
  · intro σ x
    rw [hv, hv]
    exact congrArg Multiplicative.toAdd
      (AlgEquiv.normalizedValuation_unitsMap (K := K) σ x)

end NumberFieldKB.MilneCFT.Ch3
