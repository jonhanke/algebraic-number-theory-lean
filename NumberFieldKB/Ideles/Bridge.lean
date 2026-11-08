import NumberFieldKB.Ideles.InfiniteAdeleRing
import QuadFormsKB.Tamagawa.Measure.Weil.Ideles
import NumberFieldKB.TauCetiPort.Topology.Algebra.Group.ClosedSubgroup

/-!
# Mathlib's adeles and ideles as QuadFormsKB's

$F$ is a number field. The public definitions of this library are Mathlib's adele ring
`AdeleRing (𝓞 F) F` $=\prod_{v\mid\infty}F_v\times\mathbb A_f$, its idele group `IdeleGroup (𝓞 F) F` (its units) and idele
class group `IdeleClassGroup (𝓞 F) F`. The analysis (Haar measures, the idele norm as a Haar modulus, compactness of the
norm-one idele class group, Poisson summation) lives in QuadFormsKB on `Adeles F` $=\mathbb R^{r_1}\times\mathbb C^{r_2}\times
\mathbb A_f$ and its units. This file identifies the two:

* **`adeleRingEquiv F`**: the ring isomorphism (Mathlib's `InfiniteAdeleRing.ringEquiv_mixedSpace` at the infinite places,
  the identity on the finite adeles), with **`adeleRingHomeomorph F`** the homeomorphism with the same underlying map, and
  **`adeleRingEquiv_algebraMap`**: it carries Mathlib's diagonal embedding of $F$ to QuadFormsKB's `diagRing F`;
* **`ideleGroupEquiv F`**: the induced isomorphism of topological groups `IdeleGroup (𝓞 F) F ≃ₜ* (Adeles F)ˣ`, with
  **`ideleGroupEquiv_unitEmbedding`** (it carries $F^\times$ to `diagUnits F`) and
  **`map_principalSubgroup_ideleGroupEquiv`** (principal ideles to `diagUnitsSub F`);
* **`ideleClassGroupEquiv F`**: the induced isomorphism of topological groups from Mathlib's idele class group to
  $\mathbb A_F^\times/F^\times$ in QuadFormsKB's model.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding
open QuadFormsKB.Tamagawa.Measure.Weil

namespace NumberFieldKB.Ideles

noncomputable section

variable (F : Type) [Field F] [NumberField F]

/-- **The adele ring of Mathlib is QuadFormsKB's**: `AdeleRing (𝓞 F) F ≃+* Adeles F`, Mathlib's
`InfiniteAdeleRing.ringEquiv_mixedSpace` on the infinite part and the identity on the finite adeles. -/
@[kb "weil1982" "§2.1 [unverified locator] (the adele ring of a number field, k_∞ × finite adeles)"]
def adeleRingEquiv : AdeleRing (𝓞 F) F ≃+* Adeles F :=
  RingEquiv.prodCongr (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) (RingEquiv.refl _)

@[simp] theorem adeleRingEquiv_apply (x : AdeleRing (𝓞 F) F) :
    adeleRingEquiv F x = (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2) := rfl

@[simp] theorem adeleRingEquiv_symm_apply (x : Adeles F) :
    (adeleRingEquiv F).symm x = ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm x.1, x.2) := rfl

/-- `adeleRingEquiv F` as a homeomorphism (`coe_adeleRingHomeomorph`). -/
def adeleRingHomeomorph : AdeleRing (𝓞 F) F ≃ₜ Adeles F :=
  (InfiniteAdeleRing.homeomorph_mixedSpace F).prodCongr (Homeomorph.refl _)

@[simp] theorem coe_adeleRingHomeomorph :
    (adeleRingHomeomorph F : AdeleRing (𝓞 F) F → Adeles F) = adeleRingEquiv F := rfl

@[simp] theorem coe_adeleRingHomeomorph_symm :
    ((adeleRingHomeomorph F).symm : Adeles F → AdeleRing (𝓞 F) F) = (adeleRingEquiv F).symm := rfl

/-- **The ring isomorphism `adeleRingEquiv F` is continuous.** -/
theorem continuous_adeleRingEquiv : Continuous (adeleRingEquiv F) := (adeleRingHomeomorph F).continuous

/-- **The inverse of `adeleRingEquiv F` is continuous.** -/
theorem continuous_adeleRingEquiv_symm : Continuous (adeleRingEquiv F).symm :=
  (adeleRingHomeomorph F).symm.continuous

/-- **Compatibility with the diagonal embedding**: Mathlib's `algebraMap F (AdeleRing (𝓞 F) F)` goes to QuadFormsKB's
`diagRing F` (= `diag F`). -/
theorem adeleRingEquiv_algebraMap (ξ : F) :
    adeleRingEquiv F (algebraMap F (AdeleRing (𝓞 F) F) ξ) = diagRing F ξ :=
  Prod.ext (NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm rfl

theorem adeleRingEquiv_comp_algebraMap :
    (adeleRingEquiv F : AdeleRing (𝓞 F) F →+* Adeles F).comp (algebraMap F (AdeleRing (𝓞 F) F)) = diagRing F :=
  RingHom.ext (adeleRingEquiv_algebraMap F)

/-! ### Ideles -/

/-- **The idele group of Mathlib is QuadFormsKB's**: `IdeleGroup (𝓞 F) F ≃ₜ* (Adeles F)ˣ`, the map induced on units by
`adeleRingEquiv F`; both sides carry the units topology $x\mapsto(x,x^{-1})$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §3.3 [unverified locator] (the idele group as the units of the adele ring)"]
def ideleGroupEquiv : ContinuousMulEquiv (IdeleGroup (𝓞 F) F) (Adeles F)ˣ where
  toMulEquiv := Units.mapEquiv (adeleRingEquiv F).toMulEquiv
  continuous_toFun := Units.continuous_iff.mpr
    ⟨(continuous_adeleRingEquiv F).comp Units.continuous_val,
      (continuous_adeleRingEquiv F).comp Units.continuous_coe_inv⟩
  continuous_invFun := Units.continuous_iff.mpr
    ⟨(continuous_adeleRingEquiv_symm F).comp Units.continuous_val,
      (continuous_adeleRingEquiv_symm F).comp Units.continuous_coe_inv⟩

@[simp] theorem val_ideleGroupEquiv (x : IdeleGroup (𝓞 F) F) :
    ((ideleGroupEquiv F x : (Adeles F)ˣ) : Adeles F) = adeleRingEquiv F x := rfl

@[simp] theorem val_inv_ideleGroupEquiv (x : IdeleGroup (𝓞 F) F) :
    (((ideleGroupEquiv F x)⁻¹ : (Adeles F)ˣ) : Adeles F) = adeleRingEquiv F ((x⁻¹ : IdeleGroup (𝓞 F) F) : _) := rfl

@[simp] theorem val_ideleGroupEquiv_symm (g : (Adeles F)ˣ) :
    (((ideleGroupEquiv F).symm g : IdeleGroup (𝓞 F) F) : AdeleRing (𝓞 F) F) = (adeleRingEquiv F).symm g := rfl

/-- **Compatibility with $F^\times$**: Mathlib's `IdeleGroup.unitEmbedding` goes to QuadFormsKB's `diagUnits F`. -/
theorem ideleGroupEquiv_unitEmbedding (ξ : Fˣ) :
    ideleGroupEquiv F (IdeleGroup.unitEmbedding (𝓞 F) F ξ) = diagUnits F ξ :=
  Units.ext (adeleRingEquiv_algebraMap F ξ)

theorem ideleGroupEquiv_comp_unitEmbedding :
    (ideleGroupEquiv F : IdeleGroup (𝓞 F) F →* (Adeles F)ˣ).comp (IdeleGroup.unitEmbedding (𝓞 F) F) = diagUnits F :=
  MonoidHom.ext (ideleGroupEquiv_unitEmbedding F)

/-- **Principal ideles correspond**: the image of Mathlib's `IdeleGroup.principalSubgroup` is `diagUnitsSub F`. -/
theorem map_principalSubgroup_ideleGroupEquiv :
    (IdeleGroup.principalSubgroup (𝓞 F) F).map (ideleGroupEquiv F : IdeleGroup (𝓞 F) F →* (Adeles F)ˣ) =
      diagUnitsSub F := by
  rw [IdeleGroup.principalSubgroup, MonoidHom.map_range, ideleGroupEquiv_comp_unitEmbedding, diagUnitsSub]

theorem comap_diagUnitsSub_ideleGroupEquiv :
    (diagUnitsSub F).comap (ideleGroupEquiv F : IdeleGroup (𝓞 F) F →* (Adeles F)ˣ) =
      IdeleGroup.principalSubgroup (𝓞 F) F := by
  rw [← map_principalSubgroup_ideleGroupEquiv]
  exact Subgroup.comap_map_eq_self_of_injective
    (f := (ideleGroupEquiv F : IdeleGroup (𝓞 F) F →* (Adeles F)ˣ)) (ideleGroupEquiv F).injective _

/-! ### Idele class groups -/

/-- **The idele class group of Mathlib is QuadFormsKB's $\mathbb A_F^\times/F^\times$**, as topological groups (both
carry the quotient topology). The quotient isomorphism is Tau Ceti's `ContinuousMulEquiv.quotientCongr` (ported,
`NumberFieldKB/TauCetiPort/Topology/Algebra/Group/ClosedSubgroup.lean`). -/
def ideleClassGroupEquiv : ContinuousMulEquiv (IdeleClassGroup (𝓞 F) F) ((Adeles F)ˣ ⧸ diagUnitsSub F) :=
  (ideleGroupEquiv F).quotientCongr _ _ (map_principalSubgroup_ideleGroupEquiv F)

@[simp] theorem ideleClassGroupEquiv_mk (x : IdeleGroup (𝓞 F) F) :
    ideleClassGroupEquiv F (x : IdeleClassGroup (𝓞 F) F) = ((ideleGroupEquiv F x : (Adeles F)ˣ) : _ ⧸ _) := rfl

end

end NumberFieldKB.Ideles
