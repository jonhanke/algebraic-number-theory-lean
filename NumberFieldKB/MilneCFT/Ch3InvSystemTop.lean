import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3InvTauCeti
import NumberFieldKB.MilneCFT.Ch3Ramified

/-!
# Milne, *Class Field Theory*, Chapter III §2: the invariant maps $\mathrm{inv}_{M/K}$ from Tau Ceti's Brauer group

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

For a finite Galois $M/K$ inside $\Omega$ we define `tcInvK M : H^2(M/K) → ℚ/ℤ` as Tau Ceti's local invariant
`TauCeti.ClassFieldTheory.invMap K` of the class inflated into $\mathrm{Br}(K)$ (`TauCeti.ClassFieldTheory.relBrInfl`,
$M$ embedded in $K^{\mathrm{sep}}$ through a fixed $K$-isomorphism $\Omega \simeq K^{\mathrm{sep}}$). It is injective
with image $\frac1{[M:K]}\mathbb Z/\mathbb Z$, compatible with inflation, and equals the invariant map of §1 on
unramified extensions (`tcInvK_unramified`, from `invK_eq_unramifiedInv`).

**Uniqueness** (`InvariantSystem.invK_eq_tcInvK`): for every system of invariant maps `s` (Theorem 2.1),
`s.invK M = tcInvK M`. Milne's argument (p. 103–105): every class of $H^2(M/K)$ becomes, after inflation to a larger
finite Galois extension, inflated from the unramified extension of degree $[M:K]$ (Tau Ceti
`range_relBrInfl_eq_range_relBrInfl_unramifiedExtension`), where `s` is normalized.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K Ω) in
/-- The fixed $K$-isomorphism $\Omega \simeq K^{\mathrm{sep}}$ (`SeparableClosure K`). -/
noncomputable def sepEquiv : Ω ≃ₐ[K] SeparableClosure K := IsSepClosure.equiv K Ω (SeparableClosure K)

/-- $H^2(M/K) \to \mathrm{Br}(K)$: Tau Ceti's inflation, $M$ embedded in $K^{\mathrm{sep}}$ by `sepEquiv`. -/
noncomputable def toBr (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] : H2 M →+ Br K :=
  relBrInfl K M ((sepEquiv K Ω).toAlgHom.comp M.val)

/-- **The invariant map** $\mathrm{inv}_{M/K} = \mathrm{inv}_K \circ \mathrm{Inf}$ (Milne, p. 103, diagram (28)), with
Tau Ceti's $\mathrm{inv}_K : \mathrm{Br}(K) \simeq \mathbb Q/\mathbb Z$. -/
noncomputable def tcInvK (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] : H2 M →+ QZ :=
  (Ch4.addCircleEquivQZ.toAddMonoidHom.comp (invMap K).toAddMonoidHom).comp (toBr M)

theorem tcInvK_apply (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] (x : H2 M) :
    tcInvK M x = Ch4.addCircleEquivQZ (invMap K (toBr M x)) := rfl

theorem toBr_injective (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] :
    Function.Injective (toBr M) :=
  relBrInfl_injective K M _

theorem tcInvK_injective (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] :
    Function.Injective (tcInvK M) :=
  (Ch4.addCircleEquivQZ.injective.comp (invMap K).injective).comp (toBr_injective M)

theorem mem_qzOver_iff (n : ℕ) (hn : 0 < n) (y : QZ) : y ∈ qzOver n ↔ n • y = 0 := by
  refine ⟨fun hy => ?_, mem_qzOver_of_nsmul n hn y⟩
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
  rw [smul_comm, qz_nsmul, (qz_eq_zero_iff _).2 ⟨1, by push_cast; field_simp⟩, smul_zero]

theorem range_tcInvK (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M] :
    (tcInvK M).range = qzOver (Module.finrank K M) := by
  let _ := TauCeti.algebraicExtensionValuativeRel K M
  let _ := TauCeti.algebraicExtensionNormedFieldTopology K M
  have := TauCeti.finiteExtension_isNonarchimedeanLocalField K M
  have := TauCeti.algebraicExtension_valuativeExtension K M
  have hn : 0 < Module.finrank K M := Module.finrank_pos
  have h := range_invMap_comp_relBrInfl K M ((sepEquiv K Ω).toAlgHom.comp M.val)
  ext y
  rw [mem_qzOver_iff _ hn, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    have hx : invMap K (toBr M x) ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (Module.finrank K M) := by
      have : (invMap K ∘ relBrInfl K M ((sepEquiv K Ω).toAlgHom.comp M.val)) x ∈ Set.range
          (invMap K ∘ relBrInfl K M ((sepEquiv K Ω).toAlgHom.comp M.val)) := ⟨x, rfl⟩
      rw [h] at this
      exact this
    rw [AddSubgroup.torsionBy.nsmul_iff] at hx
    rw [tcInvK_apply, ← map_nsmul, hx, map_zero]
  · intro hy
    have ht : Ch4.addCircleEquivQZ.symm y ∈ Set.range
        (invMap K ∘ relBrInfl K M ((sepEquiv K Ω).toAlgHom.comp M.val)) := by
      rw [h]
      exact AddSubgroup.torsionBy.nsmul_iff.2 (by rw [← map_nsmul, hy, map_zero])
    obtain ⟨x, hx⟩ := ht
    have hx' : invMap K (toBr M x) = Ch4.addCircleEquivQZ.symm y := hx
    exact ⟨x, show Ch4.addCircleEquivQZ (invMap K (toBr M x)) = y by rw [hx', AddEquiv.apply_symm_apply]⟩

/-- **Inflation is compatible with $\mathrm{Inf}$ into $\mathrm{Br}(K)$.** -/
theorem toBr_inflK {M E : IntermediateField K Ω} [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional K E]
    [IsGalois K E] (h : M ≤ E) (x : H2 M) : toBr E ((inflK h).hom x) = toBr M x := by
  letI : Algebra M E := (IntermediateField.inclusion h).toAlgebra
  haveI : IsScalarTower K M E := .of_algebraMap_eq fun _ => rfl
  have e := relBrInfl_map K M E ((sepEquiv K Ω).toAlgHom.comp E.val) x
  have hτ : ((sepEquiv K Ω).toAlgHom.comp E.val).comp (IsScalarTower.toAlgHom K M E) =
      (sepEquiv K Ω).toAlgHom.comp M.val := AlgHom.ext fun _ => rfl
  rw [hτ] at e
  exact e

theorem tcInvK_inflK {M E : IntermediateField K Ω} [FiniteDimensional K M] [IsGalois K M] [FiniteDimensional K E]
    [IsGalois K E] (h : M ≤ E) (x : H2 M) : tcInvK E ((inflK h).hom x) = tcInvK M x := by
  rw [tcInvK_apply, tcInvK_apply, toBr_inflK]

/-- **Normalization on unramified extensions**: `tcInvK E` is the invariant map of §1. -/
theorem tcInvK_unramified (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (hE : IsUnramifiedExt E) {v : Additive Eˣ →+ ℤ} (hv : IsNormalizedOrd E v) {σ : Gal(E/K)}
    (hσ : IsFrobenius E σ) : tcInvK E = invK E hv σ := by
  let _ := TauCeti.algebraicExtensionValuativeRel K E
  let _ := TauCeti.algebraicExtensionNormedFieldTopology K E
  have := TauCeti.finiteExtension_isNonarchimedeanLocalField K E
  have := TauCeti.algebraicExtension_valuativeExtension K E
  have : TauCeti.IsUnramified K E := (isUnramified_iff_isUnramifiedExt E).2 hE
  ext x
  rw [tcInvK_apply, invK_eq_unramifiedInv E hv hσ x]
  congr 1
  exact invMap_relBrInfl_unramified K E _ x

/-- **Every class of $H^2(M/K)$ is split by an unramified extension** (Milne, *CFT*, III, Lemma 2.2 and Theorem 2.1,
p. 103–105; Tau Ceti `range_relBrInfl_eq_range_relBrInfl_unramifiedExtension`): its image in $\mathrm{Br}(K)$ is
inflated from a finite unramified Galois $U/K$ inside $\Omega$ (of degree $[M:K]$). -/
theorem exists_unramified_toBr_eq (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    (x : H2 M) : ∃ (U : IntermediateField K Ω) (_ : FiniteDimensional K U) (_ : IsGalois K U),
      IsUnramifiedExt U ∧ ∃ y : H2 U, toBr U y = toBr M x := by
  set τ := sepEquiv K Ω
  set b := toBr M x
  have hb : brBaseChange K M b = 0 :=
    (mem_range_relBrInfl_iff_brBaseChange_eq_zero K M (τ.toAlgHom.comp M.val) b).1 ⟨x, rfl⟩
  set E : IntermediateField K (SeparableClosure K) := M.map τ.toAlgHom
  let eE : M ≃ₐ[K] E := IntermediateField.equivMap M τ.toAlgHom
  have : FiniteDimensional K E := eE.toLinearEquiv.finiteDimensional
  have : Normal K E := Normal.of_algEquiv eE
  have hbE : brBaseChange K E b = 0 := brBaseChange_eq_zero_of_algHom eE.toAlgHom hb
  have h1 : b ∈ (relBrInfl K E E.val).range :=
    (mem_range_relBrInfl_iff_brBaseChange_eq_zero K E E.val b).2 hbE
  rw [range_relBrInfl_eq_range_relBrInfl_unramifiedExtension K E] at h1
  set m := Module.finrank K E
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hm : m ≠ 0 := Module.finrank_pos.ne'
  have hbU' := (mem_range_relBrInfl_iff_brBaseChange_eq_zero K _ _ b).1 h1
  set U : IntermediateField K Ω := TauCeti.unramifiedExtension K Ω m
  have hle := TauCeti.map_unramifiedExtension_le (K := K) m τ.symm.toAlgHom
  let f : TauCeti.unramifiedExtension K (SeparableClosure K) m →ₐ[K] U :=
    (IntermediateField.inclusion hle).comp
      (IntermediateField.equivMap (TauCeti.unramifiedExtension K (SeparableClosure K) m) τ.symm.toAlgHom).toAlgHom
  have hbU : brBaseChange K U b = 0 := brBaseChange_eq_zero_of_algHom f hbU'
  obtain ⟨y, hy⟩ := (mem_range_relBrInfl_iff_brBaseChange_eq_zero K U (τ.toAlgHom.comp U.val) b).2 hbU
  have hUnr : IsUnramifiedExt U := by
    let _ := TauCeti.algebraicExtensionValuativeRel K U
    let _ := TauCeti.algebraicExtensionNormedFieldTopology K U
    have := TauCeti.finiteExtension_isNonarchimedeanLocalField K U
    have := TauCeti.algebraicExtension_valuativeExtension K U
    exact (isUnramified_iff_isUnramifiedExt U).1 (TauCeti.isUnramified_unramifiedExtension hm)
  exact ⟨U, inferInstance, inferInstance, hUnr, y, hy⟩

/-- **Uniqueness of the invariant maps** (Milne, *CFT*, III, Theorem 2.1, "canonical", p. 103): every system of
invariant maps has `s.invK M = tcInvK M` for every finite Galois $M/K$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 2.1, uniqueness of inv_{L/K}, p. 103–105"]
theorem InvariantSystem.invK_eq_tcInvK (s : InvariantSystem K Ω) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] : s.invK M = tcInvK M := by
  ext x
  obtain ⟨U, _, _, hU, y, hy⟩ := exists_unramified_toBr_eq M x
  obtain ⟨v, hv⟩ := exists_isNormalizedOrd U
  obtain ⟨σ, hσ, -⟩ := (unramifiedCyclic K Ω).frob_generates U hU
  have hinj : (inflK (le_sup_left : M ≤ M ⊔ U)).hom x = (inflK (le_sup_right : U ≤ M ⊔ U)).hom y :=
    toBr_injective (M ⊔ U) (by rw [toBr_inflK, toBr_inflK, hy])
  calc s.invK M x = s.invK (M ⊔ U) ((inflK (le_sup_left : M ≤ M ⊔ U)).hom x) :=
        (s.infl_top M (M ⊔ U) le_sup_left x).symm
    _ = s.invK (M ⊔ U) ((inflK (le_sup_right : U ≤ M ⊔ U)).hom y) := by rw [hinj]
    _ = s.invK U y := s.infl_top U (M ⊔ U) le_sup_right y
    _ = Ch3.invK U hv σ y := by rw [s.unramified_top U hU hv hσ]
    _ = tcInvK U y := by rw [tcInvK_unramified U hU hv hσ]
    _ = tcInvK M x := by rw [tcInvK_apply, tcInvK_apply, hy]

end NumberFieldKB.MilneCFT.Ch3
