import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Special
import NumberFieldKB.MilneCFT.Ch4PeriodIndex

/-!
# Milne, Class Field Theory, Chapter IV, Remark 4.4 (c): splitting by fields of degree `n`

Base change of Brauer classes multiplies the local invariant by the degree, for arbitrary (possibly
inseparable) finite extensions of nonarchimedean local fields; hence an `n`-torsion class dies over
every field extension of degree `n`.
-/

open scoped TensorProduct ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

universe u

open TauCeti ClassFieldTheory IntermediateField

set_option linter.style.haveILetI false

set_option synthInstance.maxHeartbeats 400000 in
/-- **Base change multiplies the local invariant by the degree** (no separability needed). -/
theorem invMap_brBaseChange (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    (x : TauCeti.ClassFieldTheory.Br K) :
    invMap L (brBaseChange K L x) = Module.finrank K L • invMap K x := by
  obtain ⟨f, y, rfl⟩ := (mem_unramifiedBr_iff K).1 (unramifiedBr_eq_top K ▸ AddSubgroup.mem_top x)
  let ψ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  let U := unramifiedExtension K (SeparableClosure K) f
  let V := unramifiedExtension L (SeparableClosure L) f
  have hψ (e : U) : ψ (e : SeparableClosure K) ∈ V :=
    unramifiedExtension_le_restrictScalars_unramifiedExtension (K := K) L f
      (map_unramifiedExtension_le f ψ ((mem_map _).2 ⟨e, e.2, rfl⟩))
  let ι : U →ₐ[K] V :=
    (ψ.comp U.val).codRestrict (V.restrictScalars K).toSubalgebra hψ
  let _ : Algebra U V := ι.toAlgebra
  have : IsScalarTower K U V := .of_algebraMap_eq fun c => (ι.commutes c).symm
  let _ := algebraicExtensionValuativeRel K U
  let _ := algebraicExtensionNormedFieldTopology K U
  have := finiteExtension_isNonarchimedeanLocalField K U
  have := algebraicExtension_valuativeExtension K U
  have : IsUnramified K U := isUnramified_unramifiedExtension f.ne_zero
  let _ := algebraicExtensionValuativeRel L V
  let _ := algebraicExtensionNormedFieldTopology L V
  have := finiteExtension_isNonarchimedeanLocalField L V
  have := algebraicExtension_valuativeExtension L V
  have : IsUnramified L V := isUnramified_unramifiedExtension f.ne_zero
  have : ValuativeExtension K V := ValuativeExtension.trans K L V
  have : ValuativeExtension U V := ι.valuativeExtension
  rw [brBaseChange_relBrInfl K L U V U.val V.val y, invMap_relBrInfl,
    invMap_relBrInfl, unramifiedInv_map_baseChange]

set_option synthInstance.maxHeartbeats 400000 in
/-- An `n`-torsion class of `Br K` dies over every field extension of degree `n` (`n ≠ 0`), for
`K`, `L` in any universe. -/
theorem brBaseChange_eq_zero_of_finrank_eq
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (L : Type u) [Field L] [Algebra K L] (x : Br K) {n : ℕ} (hn : n ≠ 0)
    (hx : n • x = 0) (hL : Module.finrank K L = n) : brBaseChange K L x = 0 := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by omega)
  letI : Small.{0} K := LocalFieldTheory.nonarchimedeanLocalField_small K
  letI : ValuativeRel (Shrink.{0} K) := LocalFieldTheory.shrinkLocalFieldValuativeRel K
  haveI : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField K
  haveI : Small.{0} L := by
    let b := Module.finBasis K L
    exact small_of_injective b.equivFun.injective
  have hbijK : Function.Bijective (algebraMap K (Shrink.{0} K)) := by
    change Function.Bijective (Shrink.ringEquiv K).symm
    exact (Shrink.ringEquiv K).symm.bijective
  letI : Algebra (Shrink.{0} K) (Shrink.{0} L) :=
    ((Shrink.ringEquiv L).symm.toRingHom.comp
      ((algebraMap K L).comp (Shrink.ringEquiv K).toRingHom)).toAlgebra
  letI : Algebra (Shrink.{0} L) L := (Shrink.ringEquiv L).toRingHom.toAlgebra
  haveI : IsScalarTower K (Shrink.{0} K) (Shrink.{0} L) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change (Shrink.ringEquiv L).symm (algebraMap K L c) =
        (Shrink.ringEquiv L).symm (algebraMap K L ((Shrink.ringEquiv K) ((Shrink.ringEquiv K).symm c)))
      simp
  haveI : IsScalarTower K (Shrink.{0} L) L :=
    IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap K L c = (Shrink.ringEquiv L) ((Shrink.ringEquiv L).symm (algebraMap K L c))
      simp
  have hbijL : Function.Bijective (algebraMap (Shrink.{0} L) L) := (Shrink.ringEquiv L).bijective
  have hfr1 : Module.finrank (Shrink.{0} L) L = 1 := finrank_eq_one_of_bijective hbijL
  have hfrK : Module.finrank K (Shrink.{0} L) = n := by
    have := Module.finrank_mul_finrank K (Shrink.{0} L) L
    rw [hfr1, mul_one] at this
    rw [this, hL]
  haveI : FiniteDimensional K (Shrink.{0} L) := Module.finite_of_finrank_pos (by omega)
  have hfrK' : Module.finrank (Shrink.{0} K) (Shrink.{0} L) = n := by
    rw [← hfrK, ← Module.finrank_mul_finrank K (Shrink.{0} K) (Shrink.{0} L),
      finrank_eq_one_of_bijective hbijK, one_mul]
  haveI : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
    Module.finite_of_finrank_pos (by omega)
  letI := algebraicExtensionValuativeRel (Shrink.{0} K) (Shrink.{0} L)
  letI := algebraicExtensionNormedFieldTopology (Shrink.{0} K) (Shrink.{0} L)
  haveI := finiteExtension_isNonarchimedeanLocalField (Shrink.{0} K) (Shrink.{0} L)
  haveI := algebraicExtension_valuativeExtension (Shrink.{0} K) (Shrink.{0} L)
  let y : Br (Shrink.{0} K) := brBaseChange K (Shrink.{0} K) x
  have hy : n • y = 0 := by rw [← map_nsmul, hx, map_zero]
  have h0 : brBaseChange (Shrink.{0} K) (Shrink.{0} L) y = 0 := by
    apply (invMap (Shrink.{0} L)).injective
    rw [invMap_brBaseChange, hfrK', ← natCast_zsmul, ← map_zsmul, natCast_zsmul, hy,
      map_zero, map_zero]
  rw [← brBaseChange_brBaseChange K (Shrink.{0} L) L x,
    ← brBaseChange_brBaseChange K (Shrink.{0} K) (Shrink.{0} L) x]
  change brBaseChange (Shrink.{0} L) L (brBaseChange (Shrink.{0} K) (Shrink.{0} L) y) = 0
  rw [h0, map_zero]

/-- **Remark 4.4 (c) of Milne** (first assertion, unconditional): a central division algebra of
degree `n²` over a nonarchimedean local field is split by every field extension of degree `n`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(c), p. 141"]
theorem remark4_4c (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Remark4_4c K := by
  refine ⟨fun D _ _ _ _ _ hD L _ _ n hDn hLn => ?_⟩
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  have hn : n ≠ 0 := by
    rintro rfl
    have := Module.finrank_pos (R := K) (M := D)
    rw [hDn] at this
    simp at this
  have hord := (remark4_4b K).orderOf_eq (CSA.of K D) hD
  have hord' : orderOf (BrauerGroup.mk (CSA.of K D)) = n := by
    have : orderOf (BrauerGroup.mk (CSA.of K D)) ^ 2 = n ^ 2 := by
      exact hord.trans hDn
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
  have hx : n • brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk (CSA.of K D))) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, ← hord', pow_orderOf_eq_one, ofMul_one, map_zero]
  have hbc := brBaseChange_eq_zero_of_finrank_eq K L _ hn hx hLn
  have hker : BrauerGroup.baseChange K L (BrauerGroup.mk (CSA.of K D)) = 1 := by
    have e := BrauerBaseChange.brauerGroupEquivBr_baseChange K L (BrauerGroup.mk (CSA.of K D))
    rw [hbc] at e
    have := (brauerGroupEquivBr L).injective (e.trans (map_zero _).symm)
    exact Additive.ofMul.injective this
  exact (mk_mem_relBrauer_iff (K := K) (L := L) (CSA.of K D)).1
    (by rw [relBrauer, MonoidHom.mem_ker]; exact hker)

end NumberFieldKB.MilneCFT.Ch4
