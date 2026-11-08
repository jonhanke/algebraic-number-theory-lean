import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Delta

/-!
# Milne, *Class Field Theory*, Prop. A.11: the degree-0 part (partial)

Partial results toward `PropA_11`. Mathlib has `Functor.rightDerived` but no connecting morphism, no horseshoe
lemma and no long exact sequence for it, so only the parts not involving $\delta$ are proved here.
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Limits

variable {C : Type 1} [Category.{0} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type 1} [Category.{0} D] [Abelian D] (F : C ⥤ D) [F.Additive]

/-- Degree 0 of Prop. A.11: for left exact `F`, `R⁰F` takes monomorphisms to monomorphisms. -/
theorem rightDerived_zero_map_mono [PreservesFiniteLimits F] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono ((F.rightDerived 0).map f) := by
  have : Mono (F.map f) := inferInstance
  have h := F.rightDerivedZeroIsoSelf.hom.naturality f
  have : Mono ((F.rightDerived 0).map f ≫ F.rightDerivedZeroIsoSelf.hom.app Y) := by
    rw [h]; infer_instance
  exact @mono_of_mono _ _ _ _ _ ((F.rightDerived 0).map f) (F.rightDerivedZeroIsoSelf.hom.app Y) this

/-- Effaceability of the right derived functors, part of Prop. A.11 / Remark A.12 (b). -/
theorem rightDerived_effaceable (I : C) [Injective I] (n : ℕ) (hn : 0 < n) :
    IsZero ((F.rightDerived n).obj I) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact F.isZero_rightDerived_obj_injective_succ m I

end NumberFieldKB.MilneCFT
