import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch4Special
import NumberFieldKB.MilneCFT.Ch4ExponentDegree
import NumberFieldKB.MilneCFT.Ch4BrauerBaseChange
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Invariant
import NumberFieldKB.YamaguchiPort.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport

/-!
# Milne, Class Field Theory, Chapter IV, Remark 4.4 (b): period equals index over a local field

For a central division algebra `D` over a nonarchimedean local field `K` with `[D : K] = d²`, the
order of `[D]` in `Br(K)` is `d`.

Proof.  The order divides `d` by Cor. 3.17 (`exponentDividesDegree`).  Conversely, let `m` be the
order.  Tau Ceti's local invariant (`invMap`, defined for `K : Type`) shows that the unramified
extension of degree `m` kills every `m`-torsion class (`brBaseChange_eq_zero_of_dvd_finrank`).  To
reach a field `K : Type u` of any universe we transport along the small copy `Shrink K` (its
nonarchimedean local field structure is `LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField`),
and lift the resulting extension back to `Type u` with `ULift`.  Hence a field `L / K` of degree `m`
splits `D`; by Cor. 3.6 some `B ~ D` with `[B : K] = m²` contains `L`, and `B ≅ M_r(D)` (Wedderburn)
gives `m = r d`, so `d ∣ m`.
-/

open scoped TensorProduct ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch4

universe u

open TauCeti ClassFieldTheory

/-- A field extension whose structure map is bijective has degree one. -/
theorem finrank_eq_one_of_bijective {A B : Type*} [Field A] [Field B] [Algebra A B]
    (h : Function.Bijective (algebraMap A B)) : Module.finrank A B = 1 := by
  rw [← Module.finrank_self A]
  exact (AlgEquiv.ofBijective (Algebra.ofId A B) h).toLinearEquiv.finrank_eq.symm

/-- A copy of a `Type` in universe `u` (a plain definition, to keep the instances of `ULift` out of
the way). -/
def Up (E : Type) : Type u := ULift.{u} E

noncomputable instance (E : Type) [Field E] : Field (Up.{u} E) := inferInstanceAs (Field (ULift E))

/-- The ring equivalence `E ≃+* Up E`. -/
def upEquiv (E : Type) [Field E] : E ≃+* Up.{u} E := (ULift.ringEquiv (R := E)).symm

set_option synthInstance.maxHeartbeats 400000 in
/-- **Splitting a torsion Brauer class by a field of the order's degree**, over a nonarchimedean
local field of any universe: an `m`-torsion class of `Br K` (`m ≠ 0`) dies over some field extension
`L / K` of degree `m`. -/
theorem exists_field_finrank_eq_brBaseChange_eq_zero
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Br K) {m : ℕ} (hm : m ≠ 0) (hx : m • x = 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧ Module.finrank K L = m ∧ brBaseChange K L x = 0 := by
  letI : Small.{0} K := LocalFieldTheory.nonarchimedeanLocalField_small K
  letI : ValuativeRel (Shrink.{0} K) := LocalFieldTheory.shrinkLocalFieldValuativeRel K
  haveI : IsNonarchimedeanLocalField (Shrink.{0} K) :=
    LocalFieldTheory.shrinkLocalField_isNonarchimedeanLocalField K
  have hbij : Function.Bijective (algebraMap K (Shrink.{0} K)) := by
    change Function.Bijective (Shrink.ringEquiv K).symm
    exact (Shrink.ringEquiv K).symm.bijective
  let y : Br (Shrink.{0} K) := brBaseChange K (Shrink.{0} K) x
  have hy : m • y = 0 := by rw [← map_nsmul, hx, map_zero]
  let E := unramifiedExtension (Shrink.{0} K) (SeparableClosure (Shrink.{0} K)) m
  letI := algebraicExtensionValuativeRel (Shrink.{0} K) E
  letI := algebraicExtensionNormedFieldTopology (Shrink.{0} K) E
  haveI := finiteExtension_isNonarchimedeanLocalField (Shrink.{0} K) E
  haveI := algebraicExtension_valuativeExtension (Shrink.{0} K) E
  have hfr : Module.finrank (Shrink.{0} K) E = m := finrank_unramifiedExtension hm
  have hE : brBaseChange (Shrink.{0} K) E y = 0 :=
    brBaseChange_eq_zero_of_dvd_finrank (Shrink.{0} K) E hfr.symm.dvd y hy
  letI : Algebra E (Up.{u} E) := (upEquiv.{u} E).toRingHom.toAlgebra
  letI : Algebra (Shrink.{0} K) (Up.{u} E) :=
    ((algebraMap E (Up.{u} E)).comp (algebraMap (Shrink.{0} K) E)).toAlgebra
  haveI : IsScalarTower (Shrink.{0} K) E (Up.{u} E) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra K (Up.{u} E) :=
    ((algebraMap (Shrink.{0} K) (Up.{u} E)).comp (algebraMap K (Shrink.{0} K))).toAlgebra
  haveI : IsScalarTower K (Shrink.{0} K) (Up.{u} E) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hbij' : Function.Bijective (algebraMap E (Up.{u} E)) := (upEquiv.{u} E).bijective
  have hfr' : Module.finrank (Shrink.{0} K) (Up.{u} E) = m := by
    rw [← Module.finrank_mul_finrank (Shrink.{0} K) E (Up.{u} E), finrank_eq_one_of_bijective hbij',
      mul_one, hfr]
  have h2 : Module.finrank K (Up.{u} E) = m := by
    rw [← Module.finrank_mul_finrank K (Shrink.{0} K) (Up.{u} E), finrank_eq_one_of_bijective hbij,
      one_mul, hfr']
  have h1 : FiniteDimensional K (Up.{u} E) := Module.finite_of_finrank_pos (by omega)
  have h3 : brBaseChange K (Up.{u} E) x = 0 := by
    rw [← brBaseChange_brBaseChange K (Shrink.{0} K) (Up.{u} E) x,
      ← brBaseChange_brBaseChange (Shrink.{0} K) E (Up.{u} E)]
    change brBaseChange E (Up.{u} E) (brBaseChange (Shrink.{0} K) E y) = 0
    rw [hE, map_zero]
  exact ⟨Up.{u} E, inferInstance, inferInstance, h1, h2, h3⟩

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **Remark 4.4 (b) of Milne** (unconditional): for a central division algebra `D` over a
nonarchimedean local field `K`, the order of `[D]` in `Br(K)` is `√[D : K]`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Rem. 4.4(b), p. 141"]
theorem remark4_4b : Remark4_4b K := by
  refine ⟨fun D hD => ?_⟩
  letI : DivisionRing D := DivisionRing.ofIsUnitOrEqZero fun a => by
    by_cases h : a = 0
    · exact Or.inr h
    · exact Or.inl (hD a h)
  set d := TauCeti.Algebra.deg K (D : Type u) with hd
  have hdD : Module.finrank K D = d ^ 2 := (TauCeti.Algebra.deg_sq ..).symm
  have hdpos : d ≠ 0 := by
    intro h0
    have := Module.finrank_pos (R := K) (M := D)
    rw [hdD, h0] at this
    simp at this
  have hexp : BrauerGroup.mk D ^ d = 1 := (exponentDividesDegree K).pow_deg_eq_one D d hdD
  have hmd : orderOf (BrauerGroup.mk D) ∣ d := orderOf_dvd_of_pow_eq_one hexp
  have hm0 : orderOf (BrauerGroup.mk D) ≠ 0 := fun h => hdpos (by rw [h] at hmd; exact zero_dvd_iff.1 hmd)
  set m := orderOf (BrauerGroup.mk D) with hm
  suffices hdm : d ∣ m by
    rw [hdD]
    exact congrArg (· ^ 2) (Nat.dvd_antisymm hmd hdm)
  -- the class is killed by `m`
  have hx : m • brauerGroupEquivBr K (Additive.ofMul (BrauerGroup.mk D)) = 0 := by
    rw [← map_nsmul, ← ofMul_pow, hm, pow_orderOf_eq_one, ofMul_one, map_zero]
  obtain ⟨L, _, _, hfd, hLm, hbc⟩ :=
    exists_field_finrank_eq_brBaseChange_eq_zero K _ hm0 hx
  have hker : BrauerGroup.baseChange K L (BrauerGroup.mk D) = 1 := by
    have e := BrauerBaseChange.brauerGroupEquivBr_baseChange K L (BrauerGroup.mk D)
    rw [hbc] at e
    have := (brauerGroupEquivBr L).injective (e.trans (map_zero _).symm)
    exact Additive.ofMul.injective this
  have hsplit : IsSplitBy (K := K) L D :=
    (mk_mem_relBrauer_iff (K := K) (L := L) D).1 (by rw [relBrauer, MonoidHom.mem_ker]; exact hker)
  obtain ⟨B, hDB, ⟨φ⟩, hdim⟩ := (cor_3_6 D L).1 hsplit
  have hBD : IsBrauerEquivalent B D :=
    (BrauerGroup.mk_eq_mk_iff B D).1 ((BrauerGroup.mk_eq_mk_iff D B).2 hDB).symm
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨r, hr, D', _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  obtain ⟨g⟩ := remark_2_13a_matrix B D hBD D' D hr.out one_ne_zero f (BrauerGroup.matOne D).symm
  have hdD' : Module.finrank K D' = d ^ 2 := by
    rw [g.toLinearEquiv.finrank_eq, hdD]
  have h1 : Module.finrank K B = r * r * Module.finrank K D' := by
    rw [f.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  have hmrd : m = r * d := by
    have : m ^ 2 = (r * d) ^ 2 := by rw [← hLm, ← hdim, h1, hdD']; ring
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) this
  exact ⟨r, by rw [hmrd, mul_comm]⟩

end NumberFieldKB.MilneCFT.Ch4
