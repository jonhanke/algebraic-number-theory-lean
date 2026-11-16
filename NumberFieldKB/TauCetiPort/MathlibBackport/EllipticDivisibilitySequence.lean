/-
Copyright (c) 2026 The Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Junyan Xu
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FinCases

/-!
# Backport from Mathlib: elliptic nets and normalised EDS

Mathlib commit `e8ba86fa` (Tau Ceti's pin), `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(authors David Kurniadi Angdinata, Junyan Xu) has about 170 more lines than Mathlib v4.35.0. This file
contains exactly the new declarations, in the same namespaces and with the same statements:
`IsEllipticNet.atom_mul_atomRel`, `IsEllipticNet.atomRel_perm`, `IsEllipticNet.atomRel_of_even_odd`,
`IsEllipticNet.of_even_odd`, `IsEllipticSequence.zero/neg/isEllipticNet/of_even_odd/ext`,
`normEDS_rel_even/odd`, `IsEllipticNet.normEDS`, `IsEllipticSequence.normEDS`,
`IsDvdSequence.normEDS`, `IsEllipticDvdSequence.normEDS`, `IsEllipticDvdSequence.eq_smul_normEDS`,
`normEDS_two_three_two`, `complEDS₂_two_three_two`, `complEDS'_two_three_two`,
`complEDS_two_three_two`, `normEDS_mul_complEDS`.
-/

@[expose] public section

namespace Tuple

variable {n : ℕ} {α : Type*} [LinearOrder α]

/-- `sortDesc f` is the permutation that orders `Fin n` according to the decreasing order of the
outputs of `f`. (Backport: Mathlib at `e8ba86fa` has `Tuple.sortDesc`, v4.35.0 does not.) -/
def sortDesc (f : Fin n → α) : Equiv.Perm (Fin n) :=
  sort (OrderDual.toDual ∘ f)

theorem antitone_sortDesc (f : Fin n → α) : Antitone (f ∘ sortDesc f) :=
  fun _ _ h ↦ monotone_sort (OrderDual.toDual ∘ f) h

end Tuple

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] (W : ℤ → R) {F : Type*} [FunLike F R S]

namespace IsEllipticNet

lemma atom_mul_atomRel (a b c d e f : ℤ) {u v w x y z : R} (h : u + v + w + x + y + z = 0) :
    (u + v) * atom W a b * atomRel W c d e f - (u + w) * atom W a c * atomRel W b d e f +
    (u + x) * atom W a d * atomRel W b c e f - (u + y) * atom W a e * atomRel W b c d f +
    (u + z) * atom W a f * atomRel W b c d e + (v + w) * atom W b c * atomRel W a d e f -
    (v + x) * atom W b d * atomRel W a c e f + (v + y) * atom W b e * atomRel W a c d f -
    (v + z) * atom W b f * atomRel W a c d e + (w + x) * atom W c d * atomRel W a b e f -
    (w + y) * atom W c e * atomRel W a b d f + (w + z) * atom W c f * atomRel W a b d e +
    (x + y) * atom W d e * atomRel W a b c f - (x + z) * atom W d f * atomRel W a b c e +
    (y + z) * atom W e f * atomRel W a b c d = 0 := by
  simp only [atomRel]
  grind only

variable {W} in
lemma atomRel_perm (odd : W.Odd) (σ : Equiv.Perm <| Fin 4) (a b c d : ℤ) :
    σ.sign • atomRel W (![a, b, c, d] <| σ 0) (![a, b, c, d] <| σ 1) (![a, b, c, d] <| σ 2)
      (![a, b, c, d] <| σ 3) = atomRel W a b c d := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap σ x y _ _ => fin_cases x <;> fin_cases y <;> simp [Equiv.swap_apply_def] <;>
      grind only [neg_atomRel₁₂, neg_atomRel₂₃, neg_atomRel₃₄, smul_neg]

variable {W} in
lemma atomRel_of_even_odd (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, atomRel W (2 * m + 2) (2 * m - 2) 2 0 = 0)
    (odd : ∀ m : ℤ, atomRel W (2 * m + 2) (2 * m) 2 0 = 0) {a b c d : ℤ}
    (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) : atomRel W a b c d = 0 := by
  wlog _ : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d generalizing a b c d with h
  · exact atomRel_abs neg .. ▸ h (parity.map _ <| by grind) <| by simp
  wlog _ : d ≤ c ∧ c ≤ b ∧ b ≤ a generalizing a b c d with h
  · rw [← atomRel_perm neg (Tuple.sortDesc ![a, b, c, d]) a b c d, smul_eq_zero_iff_eq]
    refine h (parity.perm (Equiv.Perm.ofFn_comp_perm _ ![a, b, c, d]).symm .symm) ?_ ?_
    · split_ands <;> apply (fun i ↦ by fin_cases i <;> simp <;> omega : 0 ≤ ![a, b, c, d])
    · split_ands <;> exact Tuple.antitone_sortDesc _ <| by decide
  wlog _ : d < c ∧ c < b ∧ b < a
  · rcases (by omega : a = b ∨ b = c ∨ c = d) with rfl | rfl | rfl <;>
      simp [pow_mem two 3 |>.right (W 0) <| by grind only [atomRel_same₂₃, atom, odd 1]]
  replace parity : a % 2 = b % 2 ∧ b % 2 = c % 2 ∧ c % 2 = d % 2 := by grind
  induction hn : 4 * a + b + c + d using @Int.strongRec 0 generalizing a b c d with
  | lt => omega
  | ge _ _ ih =>
    replace ih (a b c d : ℤ) := (@ih (4 * a + b + c + d) · a b c d)
    wlog _ : c = a % 2 + 2
    · have ha : atom W (a % 2 + 2) (a % 2) ∈ R⁰ := by grind only [atom, mul_mem]
      exact ha.left _ <| by grind (genLocal := 0) [atom_same, atomRel_same₃₄,
        atomRel.eq_def W a b c, @atom_mul_atomRel R _ W a b c (max d <| a % 2 + 2)
          (min d <| a % 2 + 2) (a % 2) 0 0 0 (-1) 0 1 <| by norm_num1, = (ih)]
    wlog _ : a = b + 2
    · grind (genLocal := 0) [=_ atomRel_neg₄, @atomRel_avg_sub R _ W a b c d <| by grind, = (ih)]
    grind [odd (b / 2), atomRel_neg₄ W a b c d, atomRel_avg_sub W (by simp) |>.trans (even (a / 2))]

/-- If a sequence satisfies the even and odd elliptic relations, then it is an elliptic net. -/
theorem of_even_odd {W : ℤ → R} (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, rel W (m + 1) (m - 1) 1 0 = 0) (odd : ∀ m : ℤ, rel W (m + 1) m 1 0 = 0) :
    IsEllipticNet W := fun _ _ _ _ ↦ by
  simp_rw [rel_eq] at *
  apply atomRel_of_even_odd <;> grind

end IsEllipticNet

namespace IsEllipticSequence

open IsEllipticNet

variable {W}

protected lemma zero (h : IsEllipticSequence W) (two : W 2 ∈ R⁰) : W 0 = 0 :=
  pow_mem two 3 |>.right _ <| by grind only [rel, h 1 1 2]

/-- An elliptic sequence is an odd function. -/
protected lemma neg (h : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) : W.Odd := by
  refine fun m ↦ eq_neg_of_add_eq_zero_left ?_
  rcases m.even_or_odd' with ⟨m, rfl | rfl⟩ <;> apply pow_mem (mul_mem one two) 3 |>.right <;>
  grind only [rel, h (1 - m) (1 + m) 2, h (1 + m) (1 - m) 2, h (-m) (m + 1) 1, h (1 + m) (-m) 1]

lemma isEllipticNet (h : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) :
    IsEllipticNet W :=
  of_even_odd (h.neg one two) one two (fun _ ↦ h ..) (fun _ ↦ h ..)

/-- If a sequence satisfies the even and odd elliptic relations, then it is an elliptic sequence. -/
theorem of_even_odd (neg : W.Odd) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (even : ∀ m : ℤ, rel W (m + 1) (m - 1) 1 0 = 0) (odd : ∀ m : ℤ, rel W (m + 1) m 1 0 = 0) :
    IsEllipticSequence W :=
  IsEllipticNet.of_even_odd neg one two even odd |>.isEllipticSequence

end IsEllipticSequence

variable (b c d : R)

lemma normEDS_rel_even (m : ℤ) : IsEllipticNet.rel (normEDS b c d) (m + 1) (m - 1) 1 0 = 0 := by
  simp [IsEllipticNet.rel_even, normEDS_even]

lemma normEDS_rel_odd (m : ℤ) : IsEllipticNet.rel (normEDS b c d) (m + 1) m 1 0 = 0 := by
  simp [IsEllipticNet.rel_odd, normEDS_odd]

variable {W} in
protected lemma IsEllipticSequence.ext {V : ℤ → R} (hW : IsEllipticSequence W)
    (hV : IsEllipticSequence V) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (h1 : W 1 = V 1) (h2 : W 2 = V 2)
    (h3 : W 3 = V 3) (h4 : W 4 = V 4) : W = V :=
  funext fun n ↦ by induction n using Int.negInduction with
  | nat n =>
    refine normEDSRec (by grind [hW.zero, hV.zero]) h1 h2 h3 h4 (fun m ↦ ?_) (fun m ↦ ?_) n <;>
      intros <;> refine sub_eq_zero.mp <| pow_mem (mul_mem one two) 3 |>.right _ ?_ <;>
        grind only [IsEllipticNet.rel, hW (m + 4) (m + 2) 1, hV (m + 4) (m + 2) 1,
          hW (m + 3) (m + 2) 1, hV (m + 3) (m + 2) 1]
  | neg hn n => rw [hW.neg one two, hV.neg (h1 ▸ one) (h2 ▸ two), hn]

open Polynomial in
/-- The canonical normalised EDS is an elliptic net. -/
theorem IsEllipticNet.normEDS : IsEllipticNet <| normEDS b c d := by
  suffices h : IsEllipticNet <| _root_.normEDS (X : R[X]) (C c) (C d) by
    convert h.comp <| evalRingHom b
    simp_rw [Function.comp_def, map_normEDS, coe_evalRingHom, eval_X, eval_C]
  exact of_even_odd (normEDS_neg X _ _) (by simp) (by simp [X_mem_nonZeroDivisors])
    (normEDS_rel_even _ _ _) (normEDS_rel_odd _ _ _)

/-- The canonical normalised EDS is an elliptic sequence. -/
theorem IsEllipticSequence.normEDS : IsEllipticSequence <| normEDS b c d :=
  IsEllipticNet.normEDS b c d |>.isEllipticSequence

variable {W} in
/-- An elliptic divisibility sequence is a scalar multiple of the canonical normalised EDS. -/
theorem IsEllipticDvdSequence.eq_smul_normEDS (h : IsEllipticDvdSequence W) (two : W 2 ∈ R⁰) :
    ∃ b c d : R, W = (W 1 • normEDS b c d ·) := by
  rcases h.right 1 2 ⟨2, by norm_num1⟩, h.right 1 3 ⟨3, by norm_num1⟩, h.right 2 4 ⟨2, by norm_num1⟩
    with ⟨⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
  exact ⟨b, c, d, h.left.ext (IsEllipticSequence.normEDS b c d |>.smul _)
    (mul_mem_nonZeroDivisors.mp <| hb ▸ two).left two (by simp) (by simp [hb]) (by simp [hc])
    (by rw [hd, hb, normEDS_four]; ring1)⟩

@[simp]
lemma normEDS_two_three_two (n : ℤ) : normEDS 2 3 2 n = n :=
  congrFun (g := id) (by apply IsEllipticSequence.ext <;>
    simp [IsEllipticSequence.normEDS, IsEllipticSequence.id]) n

@[simp]
lemma complEDS₂_two_three_two (n : ℤ) : complEDS₂ (2 : ℤ) 3 2 n = 2 := by
  grind only [complEDS₂_mul_b (2 : ℤ) 3 2 n, normEDS_two_three_two]

@[simp]
lemma complEDS'_two_three_two (k : ℤ) (n : ℕ) : complEDS' (2 : ℤ) 3 2 k n = n := by
  induction n using complEDSRec <;> simp <;>
    grind only [complEDS'_even, complEDS'_odd, complEDS₂_two_three_two, normEDS_two_three_two]

@[simp]
lemma complEDS_two_three_two (k n : ℤ) : complEDS 2 3 2 k n = n := by
  simpa [complEDS] using n.sign_mul_natAbs

open MvPolynomial in
lemma normEDS_mul_complEDS (m n : ℤ) :
    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) := by
  let N (m : ℤ) : MvPolynomial (Fin 3) ℤ := normEDS (X 0) (X 1) (X 2) m
  suffices hN : N m * complEDS (X 0) (X 1) (X 2) m n = N (n * m) by
    simpa [N] using congr(aeval ![b, c, d] $hN)
  by_cases hm : m = 0
  · simp [N, hm]
  induction n using Int.negInduction with
  | nat n => induction n using complEDSRec with
    | zero | one => simp [N]
    | even => rw [Nat.cast_mul, Nat.cast_ofNat, complEDS_even]; grind only [normEDS_mul_complEDS₂]
    | odd k ih₁ ih₂ =>
      apply mul_left_cancel₀ (a := N m) fun h ↦ hm <| by simpa [N] using congr(eval ![2, 3, 2] $h)
      grind [complEDS_odd _ _ _ m <| k + 1, normEDS_one, IsEllipticNet.rel,
        IsEllipticSequence.normEDS (@X ℤ _ _ (0 : Fin 3)) (X 1) (X 2) ((k + 2) * m) ((k + 1) * m) 1]
  | neg h n => simpa [N] using h n

/-- The canonical normalised EDS is a divisibility sequence. -/
theorem IsDvdSequence.normEDS : IsDvdSequence <| normEDS b c d :=
  fun _ _ ⟨_, h⟩ ↦ h ▸ ⟨complEDS .., by rw [normEDS_mul_complEDS, mul_comm]⟩

/-- The canonical normalised EDS is an elliptic divisibility sequence. -/
theorem IsEllipticDvdSequence.normEDS : IsEllipticDvdSequence <| normEDS b c d :=
  ⟨IsEllipticSequence.normEDS b c d, IsDvdSequence.normEDS b c d⟩
