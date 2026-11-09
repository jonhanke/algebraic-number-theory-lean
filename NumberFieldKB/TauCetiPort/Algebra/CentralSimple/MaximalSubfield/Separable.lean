/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Port of Tau Ceti `TauCeti/Algebra/CentralSimple/MaximalSubfield/Separable.lean` (Apache 2.0, Tau Ceti main,
-- shallow clone of 2026-11-05) together, in one file, with the parts of its import closure that are
-- missing from this port:
--   `TauCeti/FieldTheory/Separable/Adjoin.lean`, `TauCeti/FieldTheory/Separable/Tower.lean`,
--   `TauCeti/Algebra/Algebra/Subalgebra/Separable.lean`, `TauCeti/Algebra/Subalgebra/Centralizer.lean`,
--   `TauCeti/Algebra/Subalgebra/Center.lean` (only `Subalgebra.map_center_val`),
--   `TauCeti/Algebra/CentralSimple/Centralizer/Simple.lean`.
-- Declaration names and namespaces are unchanged.
public import NumberFieldKB.TauCetiPort.Algebra.CentralSimple.Subfield
public import NumberFieldKB.TauCetiPort.Algebra.CentralSimple.Centralizer.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.JacobsonNoether

/-!
# Separable maximal subfields of central division algebras

A finite-dimensional central division algebra over any field has a separable maximal
subfield. Its degree is the degree of the division algebra, and it splits the algebra
(Köthe–Noether). See the header comment for the Tau Ceti source files merged here.
-/

public section

open scoped IsMulCommutative

/-! ### `TauCeti/FieldTheory/Separable/Adjoin.lean` -/

namespace Set.Pairwise

variable {K A : Type*} [Field K] [Ring A] [IsDomain A] [Algebra K A]

/-- A pairwise commuting set in a domain generates a separable subalgebra if and only if
all of its generators are separable. The ambient domain need not be commutative or finite
dimensional. -/
theorem isSeparable_adjoin_iff {s : Set A} (hcomm : s.Pairwise Commute) :
    Algebra.IsSeparable K (Algebra.adjoin K s) ↔ ∀ x ∈ s, IsSeparable K x := by
  refine ⟨fun h x hx ↦ (Subalgebra.isSeparable_iff.mp h) x (Algebra.subset_adjoin hx), fun hsep ↦ ?_⟩
  have : IsMulCommutative (Algebra.adjoin K s) := Algebra.isMulCommutative_adjoin K hcomm
  have : Algebra.IsIntegral K (Algebra.adjoin K s) := ⟨fun x ↦ by
    obtain ⟨x, hx⟩ := x
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (isIntegral_algHom_iff (Algebra.adjoin K s).val Subtype.val_injective).mp
        (hsep x hx).isIntegral
    | algebraMap r => exact isIntegral_algebraMap
    | add x y hx hy ihx ihy => exact ihx.add ihy
    | mul x y hx hy ihx ihy => exact ihx.mul ihy⟩
  let _ : Field (Algebra.adjoin K s) := (isField_of_isIntegral_of_isField' (Field.toIsField K)).toField
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨x, hx⟩ := x
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    exact (isSeparable_map_iff (Algebra.adjoin K s).val Subtype.val_injective).mp (hsep x hx)
  | algebraMap r => exact isSeparable_algebraMap r
  | add x y hx hy ihx ihy => exact Field.isSeparable_add ihx ihy
  | mul x y hx hy ihx ihy => exact Field.isSeparable_mul ihx ihy

end Set.Pairwise

/-! ### `TauCeti/FieldTheory/Separable/Tower.lean` -/

namespace IsSeparable

variable {K L A : Type*} [Field K] [Field L] [Ring A] [IsDomain A]
  [Algebra K L] [Algebra K A] [Algebra L A] [IsScalarTower K L A]
  [Algebra.IsSeparable K L]

/-- An element of a possibly noncommutative domain that is separable over a separable field
extension is separable over the base field. -/
theorem restrictScalars {x : A} (hx : IsSeparable L x) : IsSeparable K x := by
  let M := Algebra.adjoin L ({x} : Set A)
  have : Module.Finite L M := Algebra.finite_adjoin_simple_of_isIntegral hx.isIntegral
  let : Field M := (IsField.of_isDomain_of_finite L M).toField
  let y : M := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  have hy : IsSeparable L y :=
    (isSeparable_map_iff M.val Subtype.val_injective).mp hx
  exact (IsSeparable.of_algebra_isSeparable_of_isSeparable K hy).map
    (M.val.restrictScalars K) Subtype.val_injective

end IsSeparable

/-! ### `TauCeti/Algebra/Algebra/Subalgebra/Separable.lean` -/

namespace TauCeti

variable (K A : Type*) [Field K] [Ring A] [Algebra K A] [FiniteDimensional K A]

/-- A finite-dimensional algebra has a separable commutative subalgebra whose dimension is
at least that of every separable commutative subalgebra. -/
theorem exists_isMulCommutative_isSeparable_forall_finrank_le :
    ∃ L : Subalgebra K A, IsMulCommutative L ∧ Algebra.IsSeparable K L ∧
      ∀ M : Subalgebra K A, IsMulCommutative M → Algebra.IsSeparable K M →
        Module.finrank K M ≤ Module.finrank K L := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ M : Subalgebra K A,
    IsMulCommutative M ∧ Algebra.IsSeparable K M ∧ Module.finrank K M = n
  have hcomm : IsMulCommutative (⊥ : Subalgebra K A) :=
    Algebra.adjoin_empty K A ▸ Algebra.isMulCommutative_adjoin K (by simp)
  have hsep : Algebra.IsSeparable K (⊥ : Subalgebra K A) := by
    apply Subalgebra.isSeparable_iff.mpr
    rintro x hx
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.mp hx
    exact isSeparable_algebraMap r
  have hle (M : Subalgebra K A) : Module.finrank K M ≤ Module.finrank K A :=
    Submodule.finrank_le M.toSubmodule
  have hstart : P (Module.finrank K (⊥ : Subalgebra K A)) := ⟨⊥, hcomm, hsep, rfl⟩
  obtain ⟨L, hLcomm, hLsep, hLn⟩ := Nat.findGreatest_spec (hle ⊥) hstart
  refine ⟨L, hLcomm, hLsep, fun M hMcomm hMsep ↦ ?_⟩
  rw [hLn]
  exact Nat.le_findGreatest (hle M) ⟨M, hMcomm, hMsep, rfl⟩

end TauCeti

namespace Subalgebra

variable {K A : Type*} [Field K] [Ring A] [IsDomain A] [Algebra K A]
  [FiniteDimensional K A]

/-- A separable commutative subalgebra of maximal dimension consists exactly of the separable
elements of its centralizer. -/
theorem mem_iff_isSeparable_and_mem_centralizer (L : Subalgebra K A)
    [IsMulCommutative L] [Algebra.IsSeparable K L]
    (hmax : ∀ M : Subalgebra K A, IsMulCommutative M → Algebra.IsSeparable K M →
      Module.finrank K M ≤ Module.finrank K L) (x : A) :
    x ∈ L ↔ IsSeparable K x ∧ x ∈ centralizer K (L : Set A) := by
  refine ⟨fun hx ↦ ⟨isSeparable_iff.mp inferInstance x hx,
    (mem_centralizer_iff K).mpr fun y hy ↦ setLike_mul_comm hy hx⟩, ?_⟩
  rintro ⟨hsep, hcent⟩
  have hcomm : (insert x (L : Set A)).Pairwise Commute := by
    apply Set.Pairwise.insert
    · exact fun a ha b hb _ ↦ setLike_mul_comm ha hb
    · intro y hy _
      exact ⟨((mem_centralizer_iff K).mp hcent y hy).symm,
        (mem_centralizer_iff K).mp hcent y hy⟩
  have hMcomm := Algebra.isMulCommutative_adjoin K hcomm
  have hMsep : Algebra.IsSeparable K (Algebra.adjoin K (insert x (L : Set A))) := by
    apply hcomm.isSeparable_adjoin_iff.mpr
    rintro y (rfl | hy)
    · exact hsep
    · exact isSeparable_iff.mp inferInstance y hy
  have hle : L ≤ Algebra.adjoin K (insert x (L : Set A)) := fun y hy ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)
  have heq := eq_of_le_of_finrank_le hle (hmax _ hMcomm hMsep)
  exact heq.symm ▸ Algebra.subset_adjoin (Set.mem_insert x (L : Set A))

end Subalgebra

/-! ### `TauCeti/Algebra/Subalgebra/Center.lean` (only `map_center_val`) -/

namespace Subalgebra

section Center

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- The center of a subalgebra, included in the ambient algebra, consists of its elements
which centralize the whole subalgebra. -/
@[simp]
theorem map_center_val (B : Subalgebra R A) :
    (center R B).map B.val = B ⊓ centralizer R (B : Set A) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.property, (mem_centralizer_iff R).mpr ?_⟩
    intro b hb
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨b, hb⟩)
  · rintro ⟨hx, hcomm⟩
    refine mem_map.mpr ⟨⟨x, hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro b
    exact Subtype.ext ((mem_centralizer_iff R).mp hcomm b b.property)

end Center

end Subalgebra

/-! ### `TauCeti/Algebra/Subalgebra/Centralizer.lean` -/

namespace Subalgebra

section CentralizerAlgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  (S : Subalgebra R A) [IsMulCommutative S]

/-- A commutative subalgebra acts on its centralizer by multiplication. -/
instance centralizerAlgebra : Algebra S (centralizer R (S : Set A)) :=
  (inclusion (fun _ hx ↦ (mem_centralizer_iff R).mpr fun _ hy ↦
    setLike_mul_comm hy hx)).toRingHom.toAlgebra' fun s c ↦
      Subtype.ext ((mem_centralizer_iff R).mp c.property s s.property)

/-- The structure map from a commutative subalgebra to its centralizer is inclusion. -/
@[simp]
theorem coe_algebraMap_centralizer (s : S) :
    (algebraMap S (centralizer R (S : Set A)) s : A) = s := (rfl)

/-- The scalar action on the centralizer is multiplication in the ambient algebra. -/
@[simp]
theorem coe_smul_centralizer (s : S) (c : centralizer R (S : Set A)) :
    ((s • c : centralizer R (S : Set A)) : A) = (s : A) * (c : A) := by
  simp [Algebra.smul_def]

/-- The centralizer's action by the commutative subalgebra extends its original base action. -/
instance isScalarTower_centralizerAlgebra :
    IsScalarTower R S (centralizer R (S : Set A)) :=
  IsScalarTower.of_algebraMap_eq fun r ↦ Subtype.ext (by simp)

/-- Subalgebras of a centralizer over its commutative scalar subalgebra correspond
to ambient subalgebras lying between the scalar subalgebra and its centralizer. -/
def centralizerSubalgebraOrderIso :
    Subalgebra S (centralizer R (S : Set A)) ≃o
      {T : Subalgebra R A // S ≤ T ∧ T ≤ centralizer R (S : Set A)} where
  toFun T := ⟨(T.restrictScalars R).map (centralizer R (S : Set A)).val, by
    constructor
    · intro s hs
      exact ⟨algebraMap S (centralizer R (S : Set A)) ⟨s, hs⟩,
        T.algebraMap_mem ⟨s, hs⟩, by simp⟩
    · rintro _ ⟨c, _, rfl⟩
      exact c.property⟩
  invFun T :=
    { (T.val.comap (centralizer R (S : Set A)).val).toSubsemiring with
      algebraMap_mem' := fun s ↦ by
        exact (by simpa only [coe_algebraMap_centralizer] using T.property.1 s.property :
          ((algebraMap S (centralizer R (S : Set A)) s) : A) ∈ T.val) }
  left_inv T := by
    ext c
    exact ⟨fun ⟨d, hd, hdc⟩ ↦ Subtype.ext hdc ▸ hd, fun hc ↦ ⟨c, hc, rfl⟩⟩
  right_inv T := by
    apply Subtype.ext
    ext a
    simp only [mem_map, mem_restrictScalars, val_apply]
    exact ⟨fun ⟨_, hc, hca⟩ ↦ hca ▸ hc,
      fun ha ↦ ⟨⟨a, T.property.2 ha⟩, ha, rfl⟩⟩
  map_rel_iff' := by
    intro T U
    constructor
    · intro h c hc
      obtain ⟨d, hd, hdc⟩ := h (mem_map.mpr ⟨c, hc, rfl⟩)
      exact Subtype.ext hdc ▸ hd
    · intro h a ha
      obtain ⟨c, hc, rfl⟩ := ha
      exact mem_map.mpr ⟨c, h hc, rfl⟩

/-- The forward correspondence restricts scalars and includes into the ambient algebra. -/
theorem centralizerSubalgebraOrderIso_apply
    (T : Subalgebra S (centralizer R (S : Set A))) :
    (S.centralizerSubalgebraOrderIso T).val =
      (T.restrictScalars R).map (centralizer R (S : Set A)).val := (rfl)

/-- The scalar subalgebra corresponds to the bottom subalgebra of the centralizer over `S`. -/
@[simp]
theorem centralizerSubalgebraOrderIso_bot :
    (S.centralizerSubalgebraOrderIso ⊥).val = S := by
  rw [centralizerSubalgebraOrderIso_apply]
  ext a
  simp only [mem_map, mem_restrictScalars, Algebra.mem_bot]
  constructor
  · rintro ⟨c, ⟨s, rfl⟩, rfl⟩
    simp
  · intro ha
    exact ⟨algebraMap S (centralizer R (S : Set A)) ⟨a, ha⟩,
      ⟨⟨a, ha⟩, rfl⟩, by simp⟩

/-- The whole centralizer corresponds to the top subalgebra over `S`. -/
@[simp]
theorem centralizerSubalgebraOrderIso_top :
    (S.centralizerSubalgebraOrderIso ⊤).val = centralizer R (S : Set A) := by
  rw [centralizerSubalgebraOrderIso_apply]
  ext a
  simp only [mem_map, mem_restrictScalars, Algebra.mem_top, true_and, val_apply]
  exact ⟨fun ⟨c, hca⟩ ↦ hca ▸ c.property, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩

end CentralizerAlgebra

end Subalgebra

/-! ### `TauCeti/Algebra/CentralSimple/Centralizer/Simple.lean` -/

namespace Subalgebra

open Module

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  (B : Subalgebra K A) [IsSimpleRing B]

/-- A simple subalgebra of a finite-dimensional central simple algebra is its own double
centralizer. In particular, this applies to subfields larger than the base field. -/
@[simp]
theorem centralizer_centralizer_of_isSimpleRing :
    centralizer K (Set.centralizer (B : Set A)) = B := by
  have := B.isSimpleRing_centralizer_of_isSimpleRing_tensorProduct
  have hC : 0 < finrank K ↥(centralizer K (B : Set A)) := Module.finrank_pos
  have hdim : finrank K B = finrank K ↥(centralizer K
      (centralizer K (B : Set A) : Set A)) := by
    apply Nat.eq_of_mul_eq_mul_left hC
    rw [TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite,
      ← TauCeti.finrank_mul_finrank_centralizer_of_isSimpleRing_tensorProduct_mulOpposite B,
      mul_comm]
  exact (eq_of_le_of_finrank_eq (le_centralizer_centralizer K) hdim).symm

open scoped IsMulCommutative in
/-- The centralizer of a commutative simple subalgebra is central over that subalgebra,
with its canonical action by inclusion. In particular, this applies to subfields. -/
theorem isCentral_centralizer [IsMulCommutative B] :
    Algebra.IsCentral B (centralizer K (B : Set A)) := by
  refine ⟨fun x hx ↦ ?_⟩
  have hxB : (x : A) ∈ centralizer K (Set.centralizer (B : Set A)) :=
    (mem_centralizer_iff K).mpr fun y hy ↦
      congrArg Subtype.val ((mem_center_iff.mp hx) ⟨y, hy⟩)
  rw [centralizer_centralizer_of_isSimpleRing] at hxB
  exact Algebra.mem_bot.mpr ⟨⟨x, hxB⟩, Subtype.ext (by simp)⟩

end Subalgebra

/-! ### `TauCeti/Algebra/CentralSimple/MaximalSubfield/Separable.lean` -/

namespace Subalgebra

variable {K D : Type*} [Field K] [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- In a central division algebra, a separable commutative subalgebra of maximal dimension
is its own centralizer, hence a maximal subfield. -/
theorem centralizer_eq_self_of_isSeparable_forall_finrank_le (L : Subalgebra K D)
    [IsMulCommutative L] [Algebra.IsSeparable K L]
    (hmax : ∀ M : Subalgebra K D, IsMulCommutative M → Algebra.IsSeparable K M →
      Module.finrank K M ≤ Module.finrank K L) :
    centralizer K (L : Set D) = L := by
  let : Field L := (IsField.of_isDomain_of_finite K L).toField
  let C := centralizer K (L : Set D)
  let : DivisionRing C := divisionRingOfFiniteDimensional K C
  let : Algebra.IsCentral L C := L.isCentral_centralizer
  let : Module.Finite L C := Module.Finite.of_restrictScalars_finite K L C
  have hbot : (⊥ : Subalgebra L C) = ⊤ := by
    by_contra hne
    obtain ⟨x, hx, hsep⟩ := JacobsonNoether.exists_separable_and_not_isCentral' hne
    have hxL : (x : D) ∈ L :=
      (L.mem_iff_isSeparable_and_mem_centralizer hmax x).mpr
        ⟨hsep.restrictScalars.map C.val Subtype.val_injective, x.property⟩
    exact hx (Algebra.mem_bot.mpr ⟨⟨x, hxL⟩, Subtype.ext (by simp [C])⟩)
  have heq := congrArg
    (fun T : Subalgebra L C ↦ (L.centralizerSubalgebraOrderIso T).val) hbot
  simpa only [C, centralizerSubalgebraOrderIso_bot, centralizerSubalgebraOrderIso_top]
    using heq.symm

end Subalgebra

namespace TauCeti.Algebra

universe u

variable (K : Type*) [Field K] (D : Type u) [DivisionRing D] [Algebra K D]
  [Algebra.IsCentral K D] [FiniteDimensional K D]

/-- A finite-dimensional central division algebra has a separable maximal subfield of
degree equal to its degree. The subfield is given as a subalgebra with a field structure. -/
theorem exists_subalgebra_isField_isSeparable_finrank_eq_deg :
    ∃ L : Subalgebra K D, IsField L ∧ _root_.Algebra.IsSeparable K L ∧
      Module.finrank K L = deg K D := by
  obtain ⟨L, hcomm, hsep, hmax⟩ :=
    exists_isMulCommutative_isSeparable_forall_finrank_le K D
  let := hcomm
  let := hsep
  have hfield : IsField L := IsField.of_isDomain_of_finite K L
  refine ⟨L, hfield, hsep, ?_⟩
  have hdim := finrank_mul_finrank_centralizer_of_isField L hfield
  rw [L.centralizer_eq_self_of_isSeparable_forall_finrank_le hmax] at hdim
  have hsq : Module.finrank K L ^ 2 = deg K D ^ 2 := by rw [sq, hdim, deg_sq]
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq

/-- A central division algebra is split by a finite separable subfield of degree equal to
its degree. The embedding records that the splitting field lies inside the algebra. -/
theorem exists_isSplittingField_isSeparable_finrank_eq_deg :
    ∃ (L : Type u) (_ : Field L) (_ : _root_.Algebra K L) (_ : L →ₐ[K] D),
      FiniteDimensional K L ∧ _root_.Algebra.IsSeparable K L ∧
        Module.finrank K L = deg K D ∧ IsSplittingField K D L := by
  obtain ⟨L, hfield, hsep, hdeg⟩ := exists_subalgebra_isField_isSeparable_finrank_eq_deg K D
  let : Field L := hfield.toField
  exact ⟨L, inferInstance, inferInstance, L.val, inferInstance, hsep, hdeg,
    isSplittingField_of_finrank_eq_deg L.val hdeg⟩

end TauCeti.Algebra
