import NumberFieldKB.MilneCFT.Ch7.BrauerTauCeti
import NumberFieldKB.MilneCFT.Ch4Splitting
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.Restriction
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Milne, *CFT*, VIII, Theorem 2.6: period and index of a central division algebra over a number field

**Proved here** (`T26` namespace), for a central division algebra `D` of dimension `d^2` over a number field `K`:
* `T26.brClass_pow_eq_one`: `[D]^d = 1` in `Br(K)` (period divides index). Proof: `D` has a maximal subfield `F`
  (`Ch4.prop_3_8`), of degree `d` (`Ch4.cor_3_5`), which splits `D` (`Ch4.cor_3_6_subfield`); in Tau Ceti's Brauer group
  `brCor (brRes x) = [F : K] • x` (`TauCeti.ClassFieldTheory.brCor_brRes`) and `brRes x = brBaseChange x = 0`
  (`brBaseChange_eq_brRes`, `Ch7.splitsOver_iff_brBaseChange_eq_zero`).
* `T26.dvd_finrank_of_splitsOver`: if a finite extension `L/K` splits `D`, then `d ∣ [L : K]` (index divides the degree
  of a splitting field). Proof: `Ch4.cor_3_6` gives `B ∼ D` containing `L` with `[B : K] = [L : K]^2`; `B ≅ M_k(D)` since
  `D` is a division algebra Brauer equivalent to `B`, so `[L : K]^2 = k^2 d^2`.
-/

open IsDedekindDomain NumberField TauCeti.ClassFieldTheory
open scoped TensorProduct

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.T26

variable {K : Type} [Field K] [NumberField K]

/-- **Period divides index** for a central division algebra over a number field. -/
theorem brClass_pow_eq_one (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] {d : ℕ} (hd : Module.finrank K D = d ^ 2) :
    (Ch4.BrauerGroup.mk (⟨.of K D⟩ : CSA.{0, 0} K)) ^ d = 1 := by
  obtain ⟨F, hF, hmax, hsep⟩ := Ch4.prop_3_8 (K := K) D
  have hdim : Module.finrank K D = Module.finrank K F ^ 2 := (Ch4.cor_3_5 D F hF).1 hmax
  let _ : Field F := hF.toField
  have hsplit : Ch4.IsSplitBy (K := K) F D := Ch4.cor_3_6_subfield D F hF hdim
  have hS : Ch7.SplitsOver K D F := by
    obtain ⟨n, -, ⟨e⟩⟩ := hsplit
    exact ⟨n, ⟨e⟩⟩
  have hfd : Module.finrank K F = d := by
    have : Module.finrank K F ^ 2 = d ^ 2 := hdim.symm.trans hd
    exact Nat.pow_left_injective (by norm_num) this
  have h0 := (Ch7.splitsOver_iff_brBaseChange_eq_zero (K := K) D F).1 hS
  obtain ⟨σ⟩ : Nonempty (F →ₐ[K] SeparableClosure K) := ⟨IsSepClosed.lift⟩
  rw [brBaseChange_eq_brRes K F σ] at h0
  have h1 := brCor_brRes K F σ (brauerGroupEquivBr K (Additive.ofMul (Ch7.brClass (K := K) D)))
  rw [h0, map_zero, hfd] at h1
  have h2 : d • brauerGroupEquivBr K (Additive.ofMul (Ch7.brClass (K := K) D)) = 0 := h1.symm
  rw [← map_nsmul, ← ofMul_pow] at h2
  have h3 := (brauerGroupEquivBr K).injective (h2.trans (map_zero _).symm)
  exact Additive.ofMul.injective h3

/-- **Index divides the degree of a splitting field.** -/
theorem dvd_finrank_of_splitsOver (D : Type) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D] {d : ℕ} (hd : Module.finrank K D = d ^ 2) (L : Type) [Field L] [Algebra K L]
    [FiniteDimensional K L] (h : Ch7.SplitsOver K D L) : d ∣ Module.finrank K L := by
  let Dc : CSA.{0, 0} K := { toAlgCat := AlgCat.of K D }
  have hsplit : Ch4.IsSplitBy (K := K) L Dc := by
    obtain ⟨n, ⟨e⟩⟩ := h
    refine ⟨n, fun hn => ?_, ⟨e⟩⟩
    subst hn
    have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] D) :=
      Algebra.TensorProduct.includeLeft_injective (S := K) (FaithfulSMul.algebraMap_injective K D)
    have : Subsingleton (L ⊗[K] D) := e.toEquiv.subsingleton
    exact one_ne_zero (hinj (Subsingleton.elim _ _) : (1 : L) = 0)
  obtain ⟨B, hDB, ⟨φ⟩, hdim⟩ := (Ch4.cor_3_6 Dc L).1 hsplit
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨r, hr, D', _, _, _, ⟨f⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K B
  obtain ⟨g⟩ := Ch4.remark_2_13a_matrix Dc B hDB D D' one_ne_zero hr.out
    (Ch4.BrauerGroup.matOne D).symm f
  have hdimD' : Module.finrank K D' = d ^ 2 := by
    rw [← hd]
    exact g.symm.toLinearEquiv.finrank_eq
  have h1 : Module.finrank K B = r * r * Module.finrank K D' := by
    rw [f.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  rw [hdim, hdimD'] at h1
  have h2 : Module.finrank K L ^ 2 = (r * d) ^ 2 := by rw [h1]; ring
  have h3 : Module.finrank K L = r * d := Nat.pow_left_injective (by norm_num) h2
  exact ⟨r, by rw [h3]; ring⟩

end NumberFieldKB.MilneCFT.Ch8.T26
