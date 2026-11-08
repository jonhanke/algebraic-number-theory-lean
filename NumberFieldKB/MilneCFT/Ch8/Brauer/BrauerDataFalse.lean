/-
Copyright (c) 2026 Jonathan Hanke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NumberFieldKB.MilneCFT.Ch8.BrauerInductionUncond
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.RingTheory.IntegralDomain

/-!
# `BrauerData` is false as stated

`MilneCFT.Ch8.BrauerData` asks, for the trace `χ` of every representation `ρ` of a finite group `G`, for subgroups
`Hᵢ`, integers `mᵢ` and functions `φᵢ` on `Hᵢ` with `1 = ∑ mᵢ Ind_{Hᵢ} φᵢ` and `χ|_{Hᵢ} φᵢ` in the `ℤ`-span of the
*linear* characters of `Hᵢ` itself. Brauer's theorem only gives `χ|_{Hᵢ} φᵢ` as an integral combination of
characters *induced* from linear characters of subgroups of `Hᵢ` (elementary groups are monomial, not abelian), and
the stronger statement fails.

Counterexample (`not_brauerData`): `G` the quaternion group of order `8` (`QuaternionGroup 2`), `ρ` its
`2`-dimensional representation `quatRep` (`a k ↦ diag(iᵏ, i⁻ᵏ)`, `xa k ↦ !![0, -i⁻ᵏ; iᵏ, 0]`), whose trace `χ`
vanishes outside `{1, z}`, `z = a 2` central of order `2`, with `χ 1 = 2`. For a subgroup `H` and a function `φ` on
`H` with `f := χ|_H φ` in the `ℤ`-span of the linear characters of `H`:
* `∑_{h ∈ H} f h · μ(h)⁻¹ ∈ |H| ℤ` for every linear `μ` (orthogonality, `sum_mul_inv_mem`);
* `f` is supported on `H ∩ {1, z}`; so `2 f(1) ∈ |H| ℤ` (`two_mul_eval_one`): if `z ∉ H` use `μ = 1`; if some
  linear `μ` has `μ z ≠ 1` then `μ z = -1` and add the sums for `1` and `μ`; otherwise every linear character, hence
  `f`, takes the same value at `z` and at `1` (`eval_eq_eval_one`);
* hence `Ind_H φ (1) = [G : H] φ(1) = 4 f(1) / |H|` is an even integer, and `∑ mᵢ Ind_{Hᵢ} φᵢ (1)` cannot be `1`.

`BrauerInduction` itself is unconditional (`MilneCFT.Ch8.brauerInduction`, from the Tau Ceti port), and the
corrected elementary-subgroup datum is `MilneCFT.Ch8.brauerDataElementary`
(`NumberFieldKB/MilneCFT/Ch8/Brauer/BrauerDataElementary.lean`).
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.BrauerDataFalse

open Complex QuaternionGroup

/-! ### Linear characters: orthogonality and constancy -/

/-- For `f` in the `ℤ`-span of the linear characters of `H` and a linear character `μ`,
`∑_h f h · μ(h)⁻¹` is an integral multiple of `|H|`. -/
lemma sum_mul_inv_mem {H : Type} [Group H] [Fintype H] {f : H → ℂ}
    (hf : f ∈ Submodule.span ℤ (charSet H)) (μ : H →* ℂˣ) :
    ∃ k : ℤ, ∑ h, f h * ((μ h)⁻¹ : ℂˣ) = (Fintype.card H : ℂ) * k := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, rfl⟩ := hx
    by_cases hνμ : ν = μ
    · subst hνμ
      refine ⟨1, ?_⟩
      simp [Finset.card_univ]
    · refine ⟨0, ?_⟩
      have hne : (Units.coeHom ℂ).comp (ν * μ⁻¹) ≠ 1 := by
        intro h
        apply hνμ
        ext g
        have := congrArg (fun F : H →* ℂ => F g) h
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.mul_apply,
          MonoidHom.inv_apply, MonoidHom.one_apply] at this
        have h2 : ν g * (μ g)⁻¹ = 1 := Units.ext this
        exact congrArg Units.val (mul_inv_eq_one.mp h2)
      have := sum_hom_units_eq_zero _ hne
      simpa using this
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, ha, hb]
    push_cast; ring
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨c * a, ?_⟩
    simp only [Pi.smul_apply, zsmul_eq_mul, mul_assoc, ← Finset.mul_sum, ha]
    push_cast; ring

/-- If every linear character of `H` is `1` at `z`, so is every element of their `ℤ`-span: `f z = f 1`. -/
lemma eval_eq_eval_one {H : Type} [Group H] {f : H → ℂ} (hf : f ∈ Submodule.span ℤ (charSet H)) (z : H)
    (hz : ∀ μ : H →* ℂˣ, μ z = 1) : f z = f 1 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, rfl⟩ := hx
    simp [hz ν]
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

/-! ### The quaternion group and its `2`-dimensional representation -/

/-- `ζ k = iᵏ` on `ZMod 4`. -/
def ζ (k : ZMod (2 * 2)) : ℂ := I ^ k.val

lemma I_pow_mod (m : ℕ) : I ^ (m % 4) = I ^ m := by
  conv_rhs => rw [← Nat.mod_add_div m 4, pow_add, pow_mul, I_pow_four, one_pow, mul_one]

lemma ζ_add (a b : ZMod (2 * 2)) : ζ (a + b) = ζ a * ζ b := by
  unfold ζ
  rw [ZMod.val_add, I_pow_mod, pow_add]

lemma ζ_zero : ζ 0 = 1 := by simp [ζ]

lemma ζ_two : ζ ((2 : ℕ) : ZMod (2 * 2)) = -1 := by
  show I ^ 2 = -1
  exact I_sq

lemma ζ_neg_two : ζ (-((2 : ℕ) : ZMod (2 * 2))) = -1 := by
  rw [show -((2 : ℕ) : ZMod (2 * 2)) = (2 : ℕ) by decide]
  exact ζ_two

lemma ζ_neg_mul (a : ZMod (2 * 2)) : ζ (-a) * ζ a = 1 := by
  rw [← ζ_add, neg_add_cancel, ζ_zero]

/-- The matrices of the `2`-dimensional representation of the quaternion group. -/
def quatMat : QuaternionGroup 2 → Matrix (Fin 2) (Fin 2) ℂ
  | a k => !![ζ k, 0; 0, ζ (-k)]
  | xa k => !![0, -ζ (-k); ζ k, 0]

lemma quatMat_mul (g h : QuaternionGroup 2) : quatMat (g * h) = quatMat g * quatMat h := by
  rcases g with i | i <;> rcases h with j | j
  · rw [a_mul_a]
    simp only [quatMat]
    rw [Matrix.mul_fin_two, neg_add, ζ_add, ζ_add]
    simp
  · rw [a_mul_xa]
    simp only [quatMat]
    rw [Matrix.mul_fin_two, neg_sub, sub_eq_add_neg, sub_eq_add_neg, ζ_add, ζ_add]
    simp [mul_comm]
  · rw [xa_mul_a]
    simp only [quatMat]
    rw [Matrix.mul_fin_two, neg_add, ζ_add, ζ_add]
    simp
  · rw [xa_mul_xa]
    simp only [quatMat]
    rw [Matrix.mul_fin_two]
    have e1 : ((2 : ℕ) : ZMod (2 * 2)) + j - i = (2 : ℕ) + (j + -i) := by ring
    rw [e1, neg_add, ζ_add, ζ_add, ζ_add, ζ_two, ζ_neg_two, neg_add, neg_neg, ζ_add]
    ext r t
    fin_cases r <;> fin_cases t <;> simp <;> ring

/-- The `2`-dimensional representation of the quaternion group of order `8`. -/
def quatRep : QuaternionGroup 2 →* GL (Fin 2) ℂ :=
  MonoidHom.toHomUnits
    { toFun := quatMat
      map_one' := by
        rw [one_def]
        simp only [quatMat, neg_zero, ζ_zero]
        exact (Matrix.one_fin_two).symm
      map_mul' := quatMat_mul }

/-- The trace of `quatRep`. -/
def χ (g : QuaternionGroup 2) : ℂ := Matrix.trace ((quatRep g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)

lemma χ_eq (g : QuaternionGroup 2) : χ g = Matrix.trace (quatMat g) := rfl

/-- The central element of order `2`. -/
def z : QuaternionGroup 2 := a ((2 : ℕ) : ZMod (2 * 2))

lemma z_ne_one : z ≠ 1 := by decide

lemma z_mul_z : z * z = 1 := by decide

lemma χ_one : χ 1 = 2 := by
  rw [χ_eq, one_def]
  simp [quatMat, Matrix.trace_fin_two, ζ_zero]
  norm_num

lemma χ_eq_zero (g : QuaternionGroup 2) (h1 : g ≠ 1) (hz : g ≠ z) : χ g = 0 := by
  rw [χ_eq]
  rcases g with k | k
  · have hk : k = 1 ∨ k = 3 := by
      fin_cases k
      · exact absurd one_def.symm h1
      · left; rfl
      · exact absurd rfl hz
      · right; rfl
    have hI3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
    rcases hk with rfl | rfl
    · simp only [quatMat, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      show I ^ (1 : ZMod (2 * 2)).val + I ^ (-1 : ZMod (2 * 2)).val = 0
      rw [show (1 : ZMod (2 * 2)).val = 1 from rfl, show (-1 : ZMod (2 * 2)).val = 3 from rfl, hI3]
      ring
    · simp only [quatMat, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
      show I ^ (3 : ZMod (2 * 2)).val + I ^ (-3 : ZMod (2 * 2)).val = 0
      rw [show (3 : ZMod (2 * 2)).val = 3 from rfl, show (-3 : ZMod (2 * 2)).val = 1 from rfl, hI3]
      ring
  · simp [quatMat, Matrix.trace_fin_two]

/-! ### The parity argument -/

open scoped Classical

/-- The key lemma: `2 f(1) ∈ |H| ℤ` for `f = χ|_H φ` in the `ℤ`-span of linear characters of `H`. -/
lemma two_mul_eval_one (H : Subgroup (QuaternionGroup 2)) (φ : H → ℂ)
    (hf : (fun h : H => χ (h : QuaternionGroup 2) * φ h) ∈ Submodule.span ℤ (charSet H)) :
    ∃ k : ℤ, 2 * (χ 1 * φ 1) = (Fintype.card H : ℂ) * k := by
  set f : H → ℂ := fun h : H => χ (h : QuaternionGroup 2) * φ h with hfdef
  have hsupp : ∀ h : H, (h : QuaternionGroup 2) ≠ 1 → (h : QuaternionGroup 2) ≠ z → f h = 0 := by
    intro h h1 hz
    simp [hfdef, χ_eq_zero _ h1 hz]
  have hf1 : f 1 = χ 1 * φ 1 := by simp [hfdef]
  rw [← hf1]
  by_cases hzH : z ∈ H
  · set zH : H := ⟨z, hzH⟩
    have hzne : zH ≠ 1 := fun h => z_ne_one (congrArg Subtype.val h)
    have hsum : ∀ g : H → ℂ, (∀ h : H, h ≠ 1 → h ≠ zH → g h = 0) → ∑ h, g h = g 1 + g zH := by
      intro g hg
      exact Fintype.sum_eq_add 1 zH hzne.symm fun x hx => hg x hx.1 hx.2
    have hvan : ∀ h : H, h ≠ 1 → h ≠ zH → f h = 0 := by
      intro h h1 hz
      exact hsupp h (fun e => h1 (Subtype.ext e)) (fun e => hz (Subtype.ext e))
    obtain ⟨k₁, hk₁⟩ := sum_mul_inv_mem hf 1
    rw [hsum _ (fun h h1 hz => by simp [hvan h h1 hz])] at hk₁
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, mul_one] at hk₁
    by_cases hμ : ∃ μ : H →* ℂˣ, μ zH ≠ 1
    · obtain ⟨μ, hμ⟩ := hμ
      have hsq : (μ zH : ℂ) * μ zH = 1 := by
        rw [← Units.val_mul, ← map_mul]
        have : zH * zH = 1 := Subtype.ext z_mul_z
        rw [this, map_one, Units.val_one]
      have hμz : (μ zH : ℂ) = -1 := by
        have hne : (μ zH : ℂ) ≠ 1 := fun e => hμ (Units.ext e)
        have : ((μ zH : ℂ) - 1) * ((μ zH : ℂ) + 1) = 0 := by ring_nf; rw [sq, hsq]; ring
        rcases mul_eq_zero.mp this with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact eq_neg_of_add_eq_zero_left h
      obtain ⟨k₂, hk₂⟩ := sum_mul_inv_mem hf μ
      rw [hsum _ (fun h h1 hz => by simp [hvan h h1 hz])] at hk₂
      have hinv : (((μ zH)⁻¹ : ℂˣ) : ℂ) = -1 := by
        rw [Units.val_inv_eq_inv_val, hμz]; norm_num
      rw [hinv, map_one, inv_one, Units.val_one] at hk₂
      refine ⟨k₁ + k₂, ?_⟩
      push_cast
      linear_combination hk₁ + hk₂
    · push Not at hμ
      have := eval_eq_eval_one hf zH hμ
      refine ⟨k₁, ?_⟩
      rw [← hk₁, this]; ring
  · obtain ⟨k₁, hk₁⟩ := sum_mul_inv_mem hf 1
    rw [Fintype.sum_eq_single 1 (fun h h1 => by
      simp [hsupp h (fun e => h1 (Subtype.ext e)) (fun e => hzH (e ▸ h.2))])] at hk₁
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, mul_one] at hk₁
    exact ⟨2 * k₁, by rw [hk₁]; push_cast; ring⟩

/-- `Ind_H φ (1)` is an even integer under the hypothesis of `two_mul_eval_one`. -/
lemma indFun_one_even (H : Subgroup (QuaternionGroup 2)) (φ : H → ℂ)
    (hf : (fun h : H => χ (h : QuaternionGroup 2) * φ h) ∈ Submodule.span ℤ (charSet H)) :
    ∃ k : ℤ, indFun H φ 1 = 2 * k := by
  obtain ⟨k, hk⟩ := two_mul_eval_one H φ hf
  refine ⟨k, ?_⟩
  have hcard : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hG : (Fintype.card (QuaternionGroup 2) : ℂ) = 8 := by rw [QuaternionGroup.card]; norm_num
  have hind : indFun H φ 1 = (Fintype.card H : ℂ)⁻¹ * (8 * φ 1) := by
    unfold indFun
    rw [Nat.card_eq_fintype_card]
    congr 1
    have : ∀ x : QuaternionGroup 2, x * 1 * x⁻¹ = 1 := fun x => by group
    simp only [this, dite_eq_left (one_mem H)]
    trans ∑ _x : QuaternionGroup 2, φ 1
    · rfl
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hG]
  rw [hind]
  rw [χ_one] at hk
  field_simp
  linear_combination 2 * hk

end NumberFieldKB.MilneCFT.Ch8.BrauerDataFalse

namespace NumberFieldKB.MilneCFT.Ch8

open scoped Classical
open BrauerDataFalse

/-- **`BrauerData` is false** (counterexample: the `2`-dimensional representation of the quaternion group of
order `8`). -/
@[kb "milne2020cft" "Ch. VIII, §10, p. 262 (BrauerData as stated fails; erratum)"]
theorem not_brauerData : ¬ BrauerData := by
  intro hB
  obtain ⟨ι, s, H, m, φ, h1, hmem⟩ := hB.data (QuaternionGroup 2) 2 quatRep
  have hev : ∀ i ∈ s, ∃ k : ℤ, indFun (H i) (φ i) 1 = 2 * k := fun i hi =>
    indFun_one_even (H i) (φ i) (hmem i hi)
  choose! k hk using hev
  have := h1 1
  rw [Finset.sum_congr rfl fun i hi => by rw [hk i hi]] at this
  have hz : ((2 * ∑ i ∈ s, m i * k i : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
    push_cast
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have := Int.cast_injective hz
  omega

end NumberFieldKB.MilneCFT.Ch8
