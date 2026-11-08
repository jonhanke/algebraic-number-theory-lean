import NumberFieldKB.MilneANT.Ch7LocalFields
import NumberFieldKB.MilneANT.Ch7Places

open NumberField

namespace NumberFieldKB.MilneANT

/-- The completion of a field at an absolute value is complete for the absolute value coming from its norm. -/
theorem completeSpace_withAbs_toAbsoluteValue_completion {K : Type} [Field K] (v : AbsoluteValue K ℝ) :
    CompleteSpace (WithAbs (NormedField.toAbsoluteValue v.Completion)) := by
  have hiso : Isometry (WithAbs.equiv (NormedField.toAbsoluteValue v.Completion)) :=
    AddMonoidHomClass.isometry_of_norm _ fun x => rfl
  exact (hiso.isUniformInducing.completeSpace_congr
    (WithAbs.equiv (NormedField.toAbsoluteValue v.Completion)).surjective).2 inferInstance

/-- **Theorem 7.14, infinite primes** (conditional on Ostrowski's theorem `Remark7_49a`): every archimedean
absolute value on a number field is equivalent to the absolute value of an infinite place. Milne's argument:
complete the number field at the absolute value, identify the completion with the real or complex numbers, and
restrict the resulting embedding to the number field. -/
@[kb "milne2020ant" "v3.08, Thm. 7.14, p. 111"]
theorem exists_infinitePlace_isEquiv_of_remark_7_49a (h : Remark7_49a) {K : Type} [Field K] [NumberField K]
    (v : AbsoluteValue K ℝ) (hna : ¬ IsNonarchimedean v) : ∃ w : InfinitePlace K, v.IsEquiv w.1 := by
  let ι : K →+* v.Completion :=
    (UniformSpace.Completion.coeRingHom (α := WithAbs v)).comp (WithAbs.equiv v).symm.toRingHom
  have hι : ∀ x : K, NormedField.toAbsoluteValue v.Completion (ι x) = v x := fun x => by
    show ‖((WithAbs.toAbs v x : WithAbs v) : v.Completion)‖ = v x
    rw [UniformSpace.Completion.norm_coe]; rfl
  have hna' : ¬ IsNonarchimedean (NormedField.toAbsoluteValue v.Completion) := by
    intro hn
    apply hna
    intro x y
    have := hn (ι x) (ι y)
    rw [← map_add, hι, hι, hι] at this
    exact this
  have hc := completeSpace_withAbs_toAbsoluteValue_completion v
  rcases h.real_or_complex v.Completion _ hna' hc with ⟨e, he⟩ | ⟨e, he⟩
  · let σ : K →+* ℂ := (algebraMap ℝ ℂ).comp (e.toRingHom.comp ι)
    refine ⟨InfinitePlace.mk σ, fun x y => ?_⟩
    rw [← hι x, ← hι y, he (ι x) (ι y)]
    change _ ↔ ‖σ x‖ ≤ ‖σ y‖
    simp [σ]
  · let σ : K →+* ℂ := e.toRingHom.comp ι
    refine ⟨InfinitePlace.mk σ, fun x y => ?_⟩
    rw [← hι x, ← hι y, he (ι x) (ι y)]
    change _ ↔ ‖σ x‖ ≤ ‖σ y‖
    simp [σ]

end NumberFieldKB.MilneANT
