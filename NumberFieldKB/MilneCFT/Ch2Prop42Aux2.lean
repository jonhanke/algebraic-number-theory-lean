import Mathlib
import NumberFieldKB.MilneCFT.Ch2Prop42Aux1

/-!
# Proposition 4.2, auxiliary file 2: inhomogeneous versus homogeneous cochains of a group

For an abstract group `Γ` and a `Γ`-module `M`, the inhomogeneous cochain `h : Γⁿ → M` corresponds
to the homogeneous cochain `x ↦ x₀ • h (x₀⁻¹x₁, …, xₙ₋₁⁻¹xₙ)` on `Γⁿ⁺¹`, and the differential of
Mathlib's inhomogeneous cochain complex corresponds to the alternating sum over omitted coordinates.
-/

open CategoryTheory

namespace NumberFieldKB.MilneCFT.Prop42

variable {Γ : Type} [Group Γ]

/-- The consecutive quotients `(x₀⁻¹x₁, …, xₙ₋₁⁻¹xₙ)` of a tuple. -/
def diffs {n : ℕ} (x : Fin (n + 1) → Γ) : Fin n → Γ :=
  fun k => (x (Fin.castSucc k))⁻¹ * x k.succ

theorem partialProd_diffs {n : ℕ} (x : Fin (n + 1) → Γ) (i : Fin (n + 1)) :
    Fin.partialProd (diffs x) i = (x 0)⁻¹ * x i := by
  refine Fin.induction ?_ (fun i ih => ?_) i
  · simp
  · rw [Fin.partialProd_succ, ih]
    simp [diffs, mul_assoc]

theorem diffs_comp_succAbove {n : ℕ} (x : Fin (n + 2) → Γ) (j : Fin (n + 1)) :
    diffs (fun i => x (j.succ.succAbove i)) = Fin.contractNth j (· * ·) (diffs x) := by
  funext k
  rw [← Fin.inv_partialProd_mul_eq_contractNth, partialProd_diffs, partialProd_diffs]
  simp [diffs, Fin.succ_succAbove_succ, mul_assoc]

theorem diffs_comp_succAbove_zero {n : ℕ} (x : Fin (n + 2) → Γ) :
    diffs (fun i => x ((0 : Fin (n + 2)).succAbove i)) = fun k => diffs x k.succ := by
  funext k
  simp [diffs]

/-- The homogeneous cochain attached to an inhomogeneous one. -/
def homG (M : Rep ℤ Γ) {n : ℕ} (h : (Fin n → Γ) → M) : (Fin (n + 1) → Γ) → M :=
  fun x => M.ρ (x 0) (h (diffs x))

theorem homG_d (M : Rep ℤ Γ) (n : ℕ) (h : (Fin n → Γ) → M) (x : Fin (n + 2) → Γ) :
    ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) • homG M h (fun i => x (j.succAbove i)) =
      homG M ((inhomogeneousCochains.d M n).hom h) x := by
  rw [Fin.sum_univ_succ]
  simp only [homG, inhomogeneousCochains.d_hom_apply, map_add, map_sum]
  congr 1
  · simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero]
    have e : (diffs fun i : Fin (n + 1) => x i.succ) = fun k => diffs x k.succ := rfl
    rw [e]
    have : (x 0) * diffs x 0 = x 1 := by simp [diffs]
    rw [← Module.End.mul_apply, ← map_mul, this, Fin.succ_zero_eq_one]
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_succ, Fin.succ_succAbove_zero, diffs_comp_succAbove]
    simp
    congr 2
    exact congrArg SMul.mk (funext fun n => funext fun v => (int_smul_eq_zsmul _ _ _).symm)

end NumberFieldKB.MilneCFT.Prop42
