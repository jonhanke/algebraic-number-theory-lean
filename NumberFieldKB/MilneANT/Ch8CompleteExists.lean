import NumberFieldKB.MilneANT.Ch7LocalFields
import NumberFieldKB.MilneANT.Ch7AbsoluteValues
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Extension of an absolute value from a complete field to a finite extension

Milne, Theorem 7.38 (existence) and Theorem 7.39, used in the proof of Proposition 8.1 (p. 135).
-/

namespace NumberFieldKB.MilneANT

/-- A power $|\cdot|^s$ with $0 < s \le 1$ of an absolute value is an absolute value. -/
noncomputable def absoluteValueRpow {F : Type*} [Field F] (v : AbsoluteValue F ℝ) (s : ℝ) (hs : 0 < s)
    (hs1 : s ≤ 1) : AbsoluteValue F ℝ where
  toFun x := v x ^ s
  map_mul' x y := by simp [Real.mul_rpow (v.nonneg x) (v.nonneg y)]
  nonneg' x := Real.rpow_nonneg (v.nonneg x) s
  eq_zero' x := by
    rw [Real.rpow_eq_zero (v.nonneg x) hs.ne']
    exact v.eq_zero
  add_le' x y := by
    calc v (x + y) ^ s ≤ (v x + v y) ^ s :=
          Real.rpow_le_rpow (v.nonneg _) (v.add_le x y) hs.le
      _ ≤ v x ^ s + v y ^ s := Real.rpow_add_le_add_rpow (v.nonneg x) (v.nonneg y) hs.le hs1

/-- Completeness of a normed field transfers to the type synonym `WithAbs` of its own absolute value. -/
theorem completeSpace_withAbs_toAbsoluteValue {E : Type*} [NormedField E] [CompleteSpace E] :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue E)) := by
  have hiso : Isometry (WithAbs.equiv (NormedField.toAbsoluteValue E)) :=
    AddMonoidHomClass.isometry_of_norm _ fun x => rfl
  exact (hiso.isUniformInducing.completeSpace_congr
    (WithAbs.equiv (NormedField.toAbsoluteValue E)).surjective).2 inferInstance

/-- Trivial case. -/
theorem exists_absoluteValue_extension_of_trivial {E F : Type*} [NormedField E] [Field F] [Algebra E F]
    (h : ∀ c : E, c ≠ 0 → ‖c‖ = 1) :
    ∃ w : AbsoluteValue F ℝ, ∀ c : E, w (algebraMap E F c) = ‖c‖ := by
  classical
  refine ⟨AbsoluteValue.trivial, fun c => ?_⟩
  by_cases hc : c = 0
  · simp [hc]
  · have : algebraMap E F c ≠ 0 := (map_ne_zero_iff _ (algebraMap E F).injective).2 hc
    simp [AbsoluteValue.trivial, this, h c hc]

private theorem exists_ext_nontrivial {E F : Type*} [NontriviallyNormedField E] [CompleteSpace E]
    [IsUltrametricDist E] [Field F] [Algebra E F] [FiniteDimensional E F] :
    ∃ w : AbsoluteValue F ℝ, ∀ c : E, w (algebraMap E F c) = ‖c‖ := by
  let N := spectralMulAlgNorm E F
  refine ⟨{ toFun := fun x => N x
            map_mul' := fun x y => map_mul N x y
            nonneg' := fun x => apply_nonneg N x
            eq_zero' := fun x => map_eq_zero_iff_eq_zero N
            add_le' := fun x y => map_add_le_add N x y }, fun c => ?_⟩
  exact spectralNorm_extends c

/-- **Theorem 7.38 (existence), nonarchimedean case**: an absolute value on a complete nonarchimedean field
extends to every finite extension. -/
@[kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"]
theorem exists_absoluteValue_extension_of_nonarch {E F : Type*} [NormedField E] [CompleteSpace E]
    [IsUltrametricDist E] [Field F] [Algebra E F] [FiniteDimensional E F] :
    ∃ w : AbsoluteValue F ℝ, ∀ c : E, w (algebraMap E F c) = ‖c‖ := by
  by_cases h : ∃ x : E, x ≠ 0 ∧ ‖x‖ ≠ 1
  · letI : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne h
    exact exists_ext_nontrivial
  · push_neg at h
    exact exists_absoluteValue_extension_of_trivial h

private theorem exists_ext_of_embedding {E F : Type*} [NormedField E] [Field F] [Algebra E F]
    [FiniteDimensional E F] (ψ : E →+* ℂ) (s : ℝ) (hs : 0 < s) (h : ∀ c : E, ‖c‖ = ‖ψ c‖ ^ s) :
    ∃ w : AbsoluteValue F ℝ, ∀ c : E, w (algebraMap E F c) = ‖c‖ := by
  letI : Algebra E ℂ := ψ.toAlgebra
  have hs1 : s ≤ 1 := by
    have h2 : ‖(2 : E)‖ ≤ 2 := by
      have : (2 : E) = 1 + 1 := by norm_num
      calc ‖(2 : E)‖ = ‖(1 : E) + 1‖ := by rw [← this]
        _ ≤ ‖(1 : E)‖ + ‖(1 : E)‖ := norm_add_le _ _
        _ = 2 := by simp; norm_num
    have h3 : ‖(2 : E)‖ = 2 ^ s := by
      rw [h 2, map_ofNat, Complex.norm_ofNat]
    rw [h3] at h2
    have : (2 : ℝ) ^ s ≤ 2 ^ (1 : ℝ) := by simpa using h2
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 this
  let φ : F →ₐ[E] ℂ := IsAlgClosed.lift (M := ℂ)
  let v : AbsoluteValue F ℝ := (NormedField.toAbsoluteValue ℂ).comp (f := φ.toRingHom) φ.toRingHom.injective
  refine ⟨absoluteValueRpow v s hs hs1, fun c => ?_⟩
  show ‖φ (algebraMap E F c)‖ ^ s = ‖c‖
  rw [h c]
  congr 2
  exact φ.commutes c

/-- **Theorem 7.38 (existence)** (conditional on Ostrowski's theorem `Remark7_49a` in the archimedean case):
an absolute value on a complete field extends to every finite extension. -/
@[kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"]
theorem exists_absoluteValue_extension_of_remark_7_49a (h : Remark7_49a) {E F : Type} [NormedField E]
    [CompleteSpace E] [Field F] [Algebra E F] [FiniteDimensional E F] :
    ∃ w : AbsoluteValue F ℝ, ∀ c : E, w (algebraMap E F c) = ‖c‖ := by
  by_cases hna : IsNonarchimedean (NormedField.toAbsoluteValue E)
  · haveI : IsUltrametricDist E := IsUltrametricDist.isUltrametricDist_iff_isNonarchimedean_norm.2 hna
    exact exists_absoluteValue_extension_of_nonarch
  · have hc := completeSpace_withAbs_toAbsoluteValue (E := E)
    rcases h.real_or_complex E (NormedField.toAbsoluteValue E) hna hc with ⟨e, he⟩ | ⟨e, he⟩
    · obtain ⟨s, hs, hse⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
      refine exists_ext_of_embedding ((algebraMap ℝ ℂ).comp e.toRingHom) (1 / s) (by positivity) fun c => ?_
      have := congrFun hse c
      simp at this ⊢
      rw [← this, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hs.ne', Real.rpow_one]
    · obtain ⟨s, hs, hse⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
      refine exists_ext_of_embedding e.toRingHom (1 / s) (by positivity) fun c => ?_
      have := congrFun hse c
      simp at this ⊢
      rw [← this, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hs.ne', Real.rpow_one]

end NumberFieldKB.MilneANT
