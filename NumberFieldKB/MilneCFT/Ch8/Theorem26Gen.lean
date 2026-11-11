import NumberFieldKB.MilneCFT.Ch4Splitting
import NumberFieldKB.MilneCFT.Ch4Centralizer
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Central.Defs
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *CFT*, VIII, Theorem 2.6: generation of a cyclic algebra by a maximal subfield and one element

**Proved here** (`T26` namespace, `K` any field):
* `T26.isSimpleRing_subalgebra`: a subalgebra of a finite-dimensional division algebra is a division ring
  (`Ch4.inv_mem_of_finite`), hence simple.
* `T26.adjoin_eq_top`: let `L` be a subfield of a central division algebra `D` equal to its own centralizer, and `β ∈ D`
  such that the elements of `L` commuting with `β` lie in `K`. Then `L` and `β` generate `D`. Proof: `B = K[L, β]` is
  simple, so `[B : K] [C(B) : K] = [D : K]` (`Ch4.thm_3_1`); an element of `C(B)` commutes with `L`, so lies in `L`, and
  with `β`, so lies in `K`: `C(B) = K` and `B = D`.
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.T26

variable {K : Type} [Field K]

/-- A subalgebra of a finite-dimensional division algebra is simple. -/
theorem isSimpleRing_subalgebra {D : Type} [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    (B : Subalgebra K D) : IsSimpleRing B := by
  classical
  let dr : DivisionRing B :=
    { (inferInstance : Ring B) with
      inv := fun x => ⟨(x : D)⁻¹, if h : (x : D) = 0 then by rw [h, inv_zero]; exact B.zero_mem
        else Ch4.inv_mem_of_finite (K := K) B x.2 h⟩
      exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
      mul_inv_cancel := fun x hx => by
        have hx' : (x : D) ≠ 0 := fun h => hx (Subtype.ext h)
        exact Subtype.ext (by simp [hx'])
      inv_zero := Subtype.ext (by simp)
      nnqsmul := _
      nnqsmul_def := fun _ _ => rfl
      qsmul := _
      qsmul_def := fun _ _ => rfl }
  exact @DivisionRing.isSimpleRing B dr

/-- **Generation by a maximal subfield and one element.** -/
theorem adjoin_eq_top {D : Type} [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    (L : Subalgebra K D) (hL : Subalgebra.centralizer K (L : Set D) = L) (β : D)
    (hfix : ∀ x ∈ L, β * x = x * β → x ∈ (⊥ : Subalgebra K D)) :
    Algebra.adjoin K ((L : Set D) ∪ {β}) = ⊤ := by
  set B := Algebra.adjoin K ((L : Set D) ∪ {β}) with hB
  have : IsSimpleRing B := isSimpleRing_subalgebra B
  obtain ⟨-, -, hdim⟩ := Ch4.thm_3_1 (K := K) D B
  have hC : Subalgebra.centralizer K (B : Set D) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subalgebra.mem_centralizer_iff] at hx
    have hxL : ∀ y ∈ L, y * x = x * y := fun y hy =>
      hx y (Algebra.subset_adjoin (Or.inl hy))
    have hxL' : x ∈ L := by
      rw [← hL, Subalgebra.mem_centralizer_iff]
      intro y hy
      exact hxL y hy
    exact hfix x hxL' (hx β (Algebra.subset_adjoin (Or.inr rfl)))
  rw [hC, Subalgebra.finrank_bot, mul_one] at hdim
  exact Algebra.toSubmodule_eq_top.1 (Submodule.eq_top_of_finrank_eq (B.finrank_toSubmodule.trans hdim))

end NumberFieldKB.MilneCFT.Ch8.T26
