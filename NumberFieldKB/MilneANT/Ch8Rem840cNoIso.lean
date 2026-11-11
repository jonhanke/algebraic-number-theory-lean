import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Rem840cDiscr

/-!
# Milne, *Algebraic Number Theory*, Remark 8.40(c): `ℚ(⁸√3) ≇ ℚ(⁸√48)`

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 8.40(c), p. 150; bib key `milne2020ant`.
If `φ : ℚ(⁸√48) ≃ ℚ(⁸√3)`, then `z = φ(⁸√48)/⁸√3` satisfies `z⁸ = 16`; a real embedding forces `z² = 2`, so
`z` is an algebraic integer of `ℤ[⁸√3]`. Reducing modulo `(⁸√3)` (the ring hom `ℤ[⁸√3] → 𝔽₃`, `θ ↦ 0`) gives
a square root of `2` in `𝔽₃`, which does not exist.
-/

open Polynomial NumberField

namespace NumberFieldKB.MilneANT.Rem840c

/-- The ring hom `𝓞 L = ℤ[θ] → 𝔽₃` sending `θ ↦ 0`. -/
theorem exists_hom_zmod_three : ∃ ψ : 𝓞 L →+* ZMod 3, ψ (theta 3) = 0 := by
  have hy : aeval (0 : ZMod 3) (minpoly ℤ intPB.gen) = 0 := by
    rw [intPB_gen, minpoly_theta]
    simp only [polyZ, map_sub, map_pow, aeval_X, aeval_C]
    decide
  refine ⟨(intPB.lift (0 : ZMod 3) hy : 𝓞 L →ₐ[ℤ] ZMod 3), ?_⟩
  have := intPB.lift_gen (0 : ZMod 3) hy
  rw [intPB_gen] at this
  exact this

/-- A real embedding of `L` sending `θ` to a real eighth root of `3`. -/
theorem exists_real_embedding : ∃ ρ : L →+* ℝ, ρ (AdjoinRoot.root (polyQ 3)) ^ 8 = 3 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r ^ 8 = 3 := by
    refine ⟨(3 : ℝ) ^ ((1 : ℝ) / 8), ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h : (polyQ 3).eval₂ (algebraMap ℚ ℝ) r = 0 := by
    simp [polyQ, hr]
  refine ⟨AdjoinRoot.lift (algebraMap ℚ ℝ) _ h, ?_⟩
  rw [AdjoinRoot.lift_root]
  exact hr

@[kb "milne2020ant" "v3.08, Rem. 8.40(c), p. 150"]
theorem isEmpty_ringEquiv : IsEmpty (M ≃+* L) := by
  refine ⟨fun φ => ?_⟩
  have hθ : (AdjoinRoot.root (polyQ 3)) ^ 8 = (3 : L) := by
    have := root_pow_eight 3
    exact_mod_cast this
  have hy : (φ (AdjoinRoot.root (polyQ 48))) ^ 8 = 48 := by
    have := root_pow_eight 48
    rw [← map_pow, this]
    simp only [Int.cast_ofNat]
    exact map_ofNat φ 48
  have hθ0 : AdjoinRoot.root (polyQ 3) ≠ 0 := by
    intro h
    rw [h] at hθ
    norm_num at hθ
  set z : L := φ (AdjoinRoot.root (polyQ 48)) / AdjoinRoot.root (polyQ 3) with hzdef
  have hz8 : z ^ 8 = 16 := by
    rw [hzdef, div_pow, hy, hθ]
    norm_num
  obtain ⟨ρ, hρ⟩ := exists_real_embedding
  have ht : ρ z ^ 2 = 2 := by
    have h8 : (ρ z) ^ 8 = 16 := by
      rw [← map_pow, hz8]; exact map_ofNat ρ 16
    have h4 : ((ρ z) ^ 2) ^ 4 = (2 : ℝ) ^ 4 := by
      rw [← pow_mul]; norm_num [h8]
    exact (pow_left_inj₀ (sq_nonneg _) (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)).1 h4
  have hz2 : z ^ 2 = 2 := by
    apply ρ.injective
    rw [map_pow, ht]; exact (map_ofNat ρ 2).symm
  have hzint : IsIntegral ℤ z := by
    refine ⟨X ^ 2 - C 2, monic_X_pow_sub_C 2 (by norm_num), ?_⟩
    simp [hz2]
  let w : 𝓞 L := ⟨z, hzint⟩
  have hw : w ^ 2 = 2 := by
    apply Subtype.ext
    exact hz2
  obtain ⟨ψ, -⟩ := exists_hom_zmod_three
  have h := congrArg ψ hw
  rw [map_pow, map_ofNat] at h
  revert h
  generalize ψ w = x
  revert x
  decide

theorem isEmpty_ringEquiv' : IsEmpty (L ≃+* M) :=
  ⟨fun φ => isEmpty_ringEquiv.false φ.symm⟩

end NumberFieldKB.MilneANT.Rem840c
