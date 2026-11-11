import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Local

/-!
# Milne, *Class Field Theory*, Chapter III: stable submodules

Helpers for Chapter III: the $G$-module structure on a $G$-stable subgroup of a $G$-module (`stableRep`, used for
the open subgroups of Lemmas 2.3 and 2.4 and for the roots of unity $\mu_n$ in §4), the additive $G$-module $L$
(`addRep`), and subgroups of $L^\times$ as additive subgroups of the $G$-module $L^\times$ (`unitsSub`).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

/-- The $G$-module structure on a $G$-stable additive subgroup $W$ of a $G$-module $M$. -/
noncomputable def stableRep {G : Type} [Group G] (M : Rep ℤ G) (W : AddSubgroup M)
    (hW : ∀ (g : G), ∀ x ∈ W, M.ρ g x ∈ W) : Rep ℤ G :=
  Rep.of (X := W)
    { toFun := fun g => (AddMonoidHom.mk' (fun x : W => (⟨M.ρ g x, hW g x x.2⟩ : W))
          (fun x y => by ext; simp)).toIntLinearMap
      map_one' := by ext x; simp
      map_mul' := fun g h => by ext x; simp [Module.End.mul_apply] }

/-- The inclusion $W \to M$ of $G$-modules. -/
noncomputable def stableIncl {G : Type} [Group G] (M : Rep ℤ G) (W : AddSubgroup M)
    (hW : ∀ (g : G), ∀ x ∈ W, M.ρ g x ∈ W) : stableRep M W hW ⟶ M :=
  Rep.ofHom ⟨
    { toFun := fun x => (x : M)
      map_add' := fun _ _ => rfl
      map_smul' := fun c x => (int_smul_eq_zsmul M.hV2 c (x : M)).symm },
    fun _ => rfl⟩

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The $\operatorname{Gal}(L/K)$-module $L$ (additive group). -/
noncomputable abbrev addRep (L : IntermediateField K Ω) : Rep ℤ Gal(L/K) :=
  Rep.ofDistribMulAction ℤ Gal(L/K) L

/-- A subgroup $V$ of $L^\times$, as an additive subgroup of the $G$-module $L^\times$. -/
abbrev unitsSub (L : IntermediateField K Ω) (V : Subgroup Lˣ) : AddSubgroup (Rep.ofAlgebraAutOnUnits K L) :=
  show AddSubgroup (Additive Lˣ) from Subgroup.toAddSubgroup V

end NumberFieldKB.MilneCFT.Ch3
