import NumberFieldKB.MilneCFT.LocalCFT.Basic
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.LocalExistence.Existence

/-!
# The local existence theorem in characteristic zero, from Tau Ceti (Milne, *CFT*, I, Theorem 1.4)

Tau Ceti proves that for a nonarchimedean local field $K$ (in `Type`) of characteristic zero, every subgroup of finite
index of $K^\times$ is the norm group of a finite abelian extension
(`TauCeti.ClassFieldTheory.localAbelianExistence`, ported under `NumberFieldKB/TauCetiPort/` from Tau Ceti main
`85f3eb55`, Apache 2.0; the extension is the class field `classField K V` inside `SeparableClosure K`). This file
carries that field into our separable closure $\Omega$ along a $K$-isomorphism `IsSepClosure.equiv` (norm groups are
invariant under $K$-isomorphisms) and proves the named statement `LocalExistenceInput` for $K$ of characteristic zero
(`localExistenceInput`). In positive characteristic Tau Ceti proves only the index-prime-to-$p$ case; the named statement
stays open there.
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

open TauCeti TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The norm group of a finite extension is invariant under $K$-isomorphisms. -/
theorem normGroup_eq_of_algEquiv {E : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]
    (L : IntermediateField K Ω) [FiniteDimensional K L] (ψ : E ≃ₐ[K] L) :
    normGroup L = TauCeti.normGroup K E := by
  ext a
  rw [TauCeti.mem_normGroup_iff]
  simp only [normGroup, MonoidHom.mem_range, Units.ext_iff, Units.coe_map]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.map ψ.symm.toRingEquiv.toMonoidHom y, ?_⟩
    rw [← hy]
    exact Algebra.norm_eq_of_algEquiv ψ.symm (y : L)
  · rintro ⟨y, hy⟩
    refine ⟨Units.map ψ.toRingEquiv.toMonoidHom y, ?_⟩
    rw [← hy]
    exact Algebra.norm_eq_of_algEquiv ψ (y : E)

variable (K Ω) in
/-- **The local existence theorem in characteristic zero, proved** (Milne, *CFT*, I, Theorem 1.4, hard half, for $K$ of
characteristic zero): the named statement `LocalExistenceInput` holds. From Tau Ceti's `localAbelianExistence`
(ported), which needs no openness hypothesis. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4 (characteristic zero)"]
theorem localExistenceInput [CharZero K] : LocalExistenceInput K Ω := by
  refine ⟨fun H _ hfi => ?_⟩
  have := hfi
  obtain ⟨V, hV, hN⟩ := localAbelianExistence H
  have hab : IsAbelianGalois K (classField K V) := isAbelianGalois_classField_iff.2 hV
  let φ : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  let L : IntermediateField K Ω := (classField K V).map φ.toAlgHom
  let ψ : classField K V ≃ₐ[K] L := IntermediateField.equivMap (classField K V) φ.toAlgHom
  have : FiniteDimensional K L := LinearEquiv.finiteDimensional ψ.toLinearEquiv
  have : IsGalois K L := IsGalois.of_algEquiv ψ
  have : IsMulCommutative Gal(L/K) := by
    have := hab.toIsMulCommutative
    exact (AlgEquiv.autCongr ψ).surjective.isMulCommutative
  have : IsAbelianGalois K L := ⟨⟩
  refine ⟨⟨L⟩, ?_⟩
  change normGroup L = H
  rw [normGroup_eq_of_algEquiv L ψ, ← hN]
  rfl

end NumberFieldKB.MilneCFT.LocalCFT
