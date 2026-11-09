import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3InvSystemRel
import NumberFieldKB.MilneCFT.Ch3InvRelUnram

/-!
# Milne, *Class Field Theory*, Chapter III, Theorem 2.1: uniqueness of the relative invariant maps

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Every system of invariant maps `s` has `s.inv M H = tcInvRel M H` (`InvariantSystem.inv_eq_tcInvRel`): a class of
$H^2(M/M^H)$, inflated to a large enough $E \supseteq M$, is the restriction of a class of $H^2(E/K)$ (restriction
$\mathrm{Br}(K) \to \mathrm{Br}(M^H)$ is onto), where (29) and the uniqueness of `invK` apply.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory IntermediateField

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- **Every Brauer class of $K$ is inflated from a finite Galois $U/K$ inside $\Omega$.** -/
theorem exists_toBr_eq (b : Br K) : ∃ (U : IntermediateField K Ω) (_ : FiniteDimensional K U)
    (_ : IsGalois K U) (y : H2 U), toBr U y = b := by
  obtain ⟨E', _, _, w, rfl⟩ := exists_relBrInfl_eq b
  set τ := sepEquiv K Ω
  have hb : brBaseChange K E' (relBrInfl K E' E'.val w) = 0 :=
    (mem_range_relBrInfl_iff_brBaseChange_eq_zero K E' E'.val _).1 ⟨w, rfl⟩
  set U : IntermediateField K Ω := E'.map τ.symm.toAlgHom
  let eU : E' ≃ₐ[K] U := IntermediateField.equivMap E' τ.symm.toAlgHom
  have : FiniteDimensional K U := eU.toLinearEquiv.finiteDimensional
  have : Normal K U := Normal.of_algEquiv eU
  have : Algebra.IsSeparable K U := Algebra.IsSeparable.of_algHom K _ eU.symm.toAlgHom
  have : IsGalois K U := {}
  have hbU : brBaseChange K U (relBrInfl K E' E'.val w) = 0 := brBaseChange_eq_zero_of_algHom eU.toAlgHom hb
  obtain ⟨y, hy⟩ := (mem_range_relBrInfl_iff_brBaseChange_eq_zero K U (τ.toAlgHom.comp U.val) _).2 hbU
  exact ⟨U, inferInstance, inferInstance, y, hy⟩

/-- Every $q \in \frac1{|H|}\mathbb Z/\mathbb Z$ is $(G : H)\,t$ for some $t \in \frac1{[M:K]}\mathbb Z/\mathbb Z$. -/
theorem exists_index_nsmul_eq (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]
    (H : Subgroup Gal(M/K)) {q : QZ} (hq : q ∈ qzOver (Nat.card H)) :
    ∃ t ∈ qzOver (Module.finrank K M), H.index • t = q := by
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hq
  have hcard : Nat.card H * H.index = Module.finrank K M := by
    rw [H.card_mul_index, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]
  have hH : (Nat.card H : ℚ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hi : (H.index : ℚ) ≠ 0 := by exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := H))
  refine ⟨k • qz (1 / Module.finrank K M), AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples _) _, ?_⟩
  rw [smul_comm, qz_nsmul, ← hcard]
  congr 2
  push_cast
  field_simp

/-- **The Tau Ceti invariant maps form a system of invariant maps** (existence half of Milne, *CFT*, III,
Theorem 2.1, p. 103–105). -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 2.1, existence of the invariant maps, p. 103–105"]
noncomputable def tcInvariantSystem : InvariantSystem K Ω where
  invK M _ _ := tcInvK M
  inv M _ _ H := tcInvRel M H
  injective_top M _ _ := tcInvK_injective M
  range_top M _ _ := range_tcInvK M
  injective M _ _ H := tcInvRel_injective M H
  range M _ _ H := range_tcInvRel M H
  infl_top M E _ _ _ _ h x := tcInvK_inflK h x
  infl M E _ _ _ _ h H x := tcInvRel_inflRel M h H x
  res_top M _ _ H x := tcInvRel_resK M H x
  res M _ _ _ _ h x := tcInvRel_resRel M h x
  unramified_top M _ _ hM _ hv _ hσ := tcInvK_unramified M hM hv hσ
  unramified M _ _ H hH _ hv _ hσ := tcInvRel_unramified M H hH hv hσ

/-- **Uniqueness of the relative invariant maps** (Milne, *CFT*, III, Theorem 2.1, p. 103–105): restriction
$H^2(M/K) \to H^2(M/M^H)$ is onto (by (29) and the ranges), so (29) and `invK_eq_tcInvK` determine `s.inv M H`. -/
theorem InvariantSystem.inv_eq_tcInvRel (s : InvariantSystem K Ω) (M : IntermediateField K Ω)
    [FiniteDimensional K M] [IsGalois K M] (H : Subgroup Gal(M/K)) : s.inv M H = tcInvRel M H := by
  ext x
  have hq : tcInvRel M H x ∈ qzOver (Nat.card H) := by rw [← range_tcInvRel M H]; exact ⟨x, rfl⟩
  obtain ⟨t, ht, hidx⟩ := exists_index_nsmul_eq M H hq
  rw [← range_tcInvK M] at ht
  obtain ⟨y, rfl⟩ := ht
  have hx : (resK M H).hom y = x := tcInvRel_injective M H (by rw [tcInvRel_resK, hidx])
  rw [← hx, s.res_top, tcInvRel_resK, s.invK_eq_tcInvK]

/-- **Theorem 2.1** (Milne, *CFT*, III, p. 103), at finite level: there is exactly one system of invariant maps. -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 2.1, p. 103"]
theorem thm2_1 : Thm2_1 K Ω where
  exists_unique := ⟨⟨tcInvariantSystem⟩, fun s t =>
    ⟨fun M _ _ => by rw [s.invK_eq_tcInvK, t.invK_eq_tcInvK],
      fun M _ _ H => by rw [s.inv_eq_tcInvRel, t.inv_eq_tcInvRel]⟩⟩

end NumberFieldKB.MilneCFT.Ch3
