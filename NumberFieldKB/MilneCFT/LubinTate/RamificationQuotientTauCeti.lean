import NumberFieldKB.MilneCFT.LubinTate.Complements
import NumberFieldKB.MilneCFT.LubinTate.HerbrandTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.UnitFiltration.RamificationGroup
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.InertiaDegree

/-!
# The ramification quotients, from Tau Ceti (Milne, *CFT*, I, §4, p. 44)

The named statement `RamificationQuotientBounds` (Milne, *CFT*, I, §4, p. 44, recalled from *ANT* 7.57–7.58): for a
finite Galois extension $L/K$ of local fields with residue field $l$, $|l| = q^f$ with $f \ge 1$,
$(G_0 : G_1) \mid |l| - 1$, $(G_i : G_{i+1}) \mid |l|$ for $i \ge 1$, and $G_N = 1$ for $N$ large.

Proved from the ported Tau Ceti files (Apache 2.0, `NumberFieldKB/TauCetiPort/`), after installing Tau Ceti's
local-field structure on the intermediate field $L$ (`TauCeti.finiteIntermediateFieldValuativeRel`):

* $|l| = q^{f(L/K)}$: `TauCeti.natCard_residueField`, through the identification of our residue field
  `residueFieldL L` with `𝓀[L]` (`residueFieldLEquiv`, from `comap_maxIdealL` of `LubinTate/HerbrandTauCeti.lean`);
* our $G_i$ is Tau Ceti's (`ramificationGroup_eq_lowerRamificationGroup`), and the quotients embed in $l^\times$ and in
  $l$: `TauCeti.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one`,
  `TauCeti.ramificationGroupGradedToResidueField_injective`;
* eventual triviality: `TauCeti.LocalFieldsRamification.exists_forall_lowerRamificationGroup_natCast_eq_bot`.
-/

open scoped ValuativeRel

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Compatible

variable (L : IntermediateField K Ω) [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L]
  [ValuativeExtension K L] [IsNonarchimedeanLocalField L]

/-- `maxIdealL L` is the image of `𝓂[L]` under `𝒪[L] ≃ integers L`. -/
theorem maxIdealL_eq_map :
    maxIdealL L = (𝓂[L]).map ((TauCeti.integerRingEquivIntegralClosure K L).toRingEquiv :
      𝒪[L] →+* integers L) := by
  set f : 𝒪[L] ≃+* integers L := (TauCeti.integerRingEquivIntegralClosure K L).toRingEquiv
  rw [← comap_maxIdealL L]
  exact (Ideal.map_comap_of_surjective (f : 𝒪[L] →+* integers L) f.surjective _).symm

/-- Our residue field `residueFieldL L` is Tau Ceti's `𝓀[L]`. -/
def residueFieldLEquiv : 𝓀[L] ≃+* residueFieldL L :=
  Ideal.quotientEquiv _ _ (TauCeti.integerRingEquivIntegralClosure K L).toRingEquiv (maxIdealL_eq_map L)

theorem natCard_residueFieldL : Nat.card (residueFieldL L) = Nat.card 𝓀[L] :=
  (Nat.card_congr (residueFieldLEquiv L).toEquiv).symm

open TauCeti.LocalFieldsRamification in
theorem ramificationGroup_eq_tauCeti (i : ℕ) :
    ramificationGroup L i = TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] (i : ℤ) := by
  rw [ramificationGroup_eq_lowerRamificationGroup, lowerRamificationGroup_def]

theorem relIndex_ramificationGroup_eq (i : ℕ) :
    (ramificationGroup L (i + 1)).relIndex (ramificationGroup L i) =
      Nat.card (TauCeti.IsLocalRing.RamificationGroupGraded (L ≃ₐ[K] L) 𝒪[L] (i : ℤ)) := by
  rw [ramificationGroup_eq_tauCeti, ramificationGroup_eq_tauCeti]
  have h : (((i + 1 : ℕ) : ℤ)) = (i : ℤ) + 1 := by push_cast; rfl
  rw [h]
  rfl

end Compatible

/-- Install Tau Ceti's local-field structure on a finite intermediate field. -/
private theorem withLocal (L : IntermediateField K Ω) [FiniteDimensional K L] {P : Prop}
    (h : ∀ (_ : ValuativeRel L) (_ : TopologicalSpace L) (_ : ValuativeExtension K L)
      (_ : IsNonarchimedeanLocalField L), P) : P := by
  let _ : ValuativeRel L := TauCeti.finiteIntermediateFieldValuativeRel K Ω L
  let _ : TopologicalSpace L := TauCeti.finiteIntermediateFieldTopology K Ω L
  exact h _ _ (TauCeti.finiteIntermediateField_valuativeExtension K Ω L)
    (TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L)

variable (K Ω) in
/-- **The ramification quotients, proved** (Milne, *CFT*, I, §4, p. 44; *ANT* 7.57–7.58): the named statement
`RamificationQuotientBounds` holds, from Tau Ceti (see the module docstring). -/
@[kb "milne2020cft" "Ch. I, §4, p. 44 (ramification quotients)"]
theorem ramificationQuotientBounds : RamificationQuotientBounds K Ω := by
  refine ⟨fun L _ => ?_, fun L _ _ => ?_, fun L _ _ i hi => ?_, fun L _ _ => ?_⟩
  · refine withLocal L fun _ _ _ _ => ?_
    refine ⟨TauCeti.inertiaDegree K L, by rw [TauCeti.inertiaDegree_def]; exact Module.finrank_pos, ?_⟩
    rw [natCard_residueFieldL, TauCeti.natCard_residueField K L]
  · refine withLocal L fun _ _ _ _ => ?_
    have h := relIndex_ramificationGroup_eq L 0
    rw [Nat.zero_add, Nat.cast_zero] at h
    rw [h, natCard_residueFieldL]
    exact TauCeti.card_ramificationGroupGraded_zero_dvd_card_residueField_sub_one (G := L ≃ₐ[K] L) (L := L)
  · refine withLocal L fun _ _ _ _ => ?_
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    rw [relIndex_ramificationGroup_eq, natCard_residueFieldL]
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
    have hinj := TauCeti.ramificationGroupGradedToResidueField_injective (G := L ≃ₐ[K] L) (L := L) n π hπ
    have hdvd := AddSubgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_congr (Additive.toMul :
      Additive (TauCeti.IsLocalRing.RamificationGroupGraded (L ≃ₐ[K] L) 𝒪[L] ((n : ℤ) + 1)) ≃ _)] at hdvd
    push_cast
    exact hdvd
  · refine withLocal L fun _ _ _ _ => ?_
    obtain ⟨N, hN⟩ := TauCeti.LocalFieldsRamification.exists_forall_lowerRamificationGroup_natCast_eq_bot K L
    exact ⟨N, by rw [ramificationGroup_eq_lowerRamificationGroup]; exact hN N le_rfl⟩

end NumberFieldKB.MilneCFT.LocalCFT
