import NumberFieldKB.MilneCFT.LubinTate.Example413Proof
import NumberFieldKB.MilneCFT.LocalCFT.ArtinMapTransport

/-!
# Example 4.13 for a separable closure in any universe

Milne, *CFT*, I, Example 4.13. `example413` is proved for `Ω : Type`; here it is transported along
`IsSepClosure.equiv` to a separable closure of `ℚ_[5]` in any universe.
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

section

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω Ω' : Type*} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra K Ω']

/-- Total ramification is invariant under $K$-isomorphism. -/
theorem isTotallyRamifiedExt_of_equiv {L : IntermediateField K Ω} {L' : IntermediateField K Ω'}
    (g : L ≃ₐ[K] L') (h : IsTotallyRamifiedExt L) : IsTotallyRamifiedExt L' := by
  obtain ⟨P, hP, he⟩ := h
  let f : integers L ≃+* integers L' := (integersEquiv g).toRingEquiv
  refine ⟨P.map f, ?_, ?_⟩
  · exact Ideal.map_isMaximal_of_equiv f
  · rw [← LinearEquiv.finrank_eq g.toLinearEquiv, ← Ideal.map_pow, ← he]
    have := integersEquiv_comp g
    change _ = Ideal.map (f : integers L →+* integers L') _
    rw [Ideal.map_map]
    have h2 : (f : integers L →+* integers L').comp (algebraMap 𝒪[K] (integers L)) =
      algebraMap 𝒪[K] (integers L') := this
    rw [h2]

end

/-- **Example 4.13, any universe** (Milne, *CFT*, I, Example 4.13): `example413` for a separable closure `Ω` of
`ℚ_[5]` in any universe, transported from `SeparableClosure ℚ_[5]` along `IsSepClosure.equiv`. -/
@[kb "milne2020cft" "Ch. I, Example 4.13"]
theorem example413_univ (Ω : Type*) [Field Ω] [Algebra ℚ_[5] Ω] [IsSepClosure ℚ_[5] Ω] : Example413 Ω := by
  refine ⟨fun ζ hζ => ?_⟩
  let e : SeparableClosure ℚ_[5] ≃ₐ[ℚ_[5]] Ω := IsSepClosure.equiv ℚ_[5] (SeparableClosure ℚ_[5]) Ω
  have hζ' : IsPrimitiveRoot (e.symm ζ) 3120 := hζ.map_of_injective e.symm.injective
  obtain ⟨L', hle, hrk, hcyc, hnot⟩ := example413.exists_not_compositum (e.symm ζ) hζ'
  refine ⟨L'.mapEquiv e, ?_, ?_, ?_, ?_⟩
  · change L'.toField.map (e : SeparableClosure ℚ_[5] →ₐ[ℚ_[5]] Ω) ≤ _
    refine (IntermediateField.map_mono _ hle).trans ?_
    rw [IntermediateField.adjoin_map]
    simp
  · rw [← hrk]
    exact (FiniteAbelianExt.equivMapEquiv e L').symm.toLinearEquiv.finrank_eq
  · exact (MulEquiv.isCyclic (FiniteAbelianExt.equivMapEquiv e L').autCongr).1 hcyc
  · rintro ⟨Lt, Lu, hLt, hLu, htr, hun, hsup⟩
    apply hnot
    let gt : Lt ≃ₐ[ℚ_[5]] Lt.map (e.symm : Ω →ₐ[ℚ_[5]] SeparableClosure ℚ_[5]) :=
      IntermediateField.equivMap Lt _
    let gu : Lu ≃ₐ[ℚ_[5]] Lu.map (e.symm : Ω →ₐ[ℚ_[5]] SeparableClosure ℚ_[5]) :=
      IntermediateField.equivMap Lu _
    refine ⟨Lt.map (e.symm : Ω →ₐ[ℚ_[5]] SeparableClosure ℚ_[5]),
      Lu.map (e.symm : Ω →ₐ[ℚ_[5]] SeparableClosure ℚ_[5]),
      LinearEquiv.finiteDimensional gt.toLinearEquiv, LinearEquiv.finiteDimensional gu.toLinearEquiv,
      isTotallyRamifiedExt_of_equiv gt htr, isUnramifiedExt_of_equiv gu hun, ?_⟩
    rw [← IntermediateField.map_sup, ← hsup]
    change L'.toField = (L'.toField.map (e : SeparableClosure ℚ_[5] →ₐ[ℚ_[5]] Ω)).map
      (e.symm : Ω →ₐ[ℚ_[5]] SeparableClosure ℚ_[5])
    rw [IntermediateField.map_map]
    ext x
    simp

end NumberFieldKB.MilneCFT.LocalCFT
