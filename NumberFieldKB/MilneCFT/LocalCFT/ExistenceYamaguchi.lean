import NumberFieldKB.MilneCFT.LocalCFT.Basic
import NumberFieldKB.YamaguchiPort.ClassFieldTheory.Theorems.LocalClassFieldTheory.FiniteAbelianLocalExistenceOrderIso

/-!
# The local existence theorem in every characteristic, from Yamaguchi (Milne, *CFT*, I, Theorem 1.4)

Yamaguchi's class field theory library proves that for every nonarchimedean local field $K$ (any universe, any
characteristic) the finite abelian extensions of $K$ inside `SeparableClosure K` correspond, order-reversingly, to the
open subgroups of finite index of $K^\times$, an extension going to its norm subgroup
(`ClassFieldTheory.finiteAbelianLocalExistence_orderIso`, ported under `NumberFieldKB/YamaguchiPort/` from Yamaguchi main
`fbd320cd`, Apache 2.0). This file carries the extension attached to an open subgroup of finite index into our
separable closure $\Omega$ along a $K$-isomorphism (`IsSepClosure.equiv`) and proves the named statement
`LocalExistenceInput` with no restriction on the characteristic or the universe (`localExistenceInput_yamaguchi`).

**Comparison lemmas.** Yamaguchi's `fieldNormSubgroup K E` is the range of `Units.map (Algebra.norm K)`, the same
formula as our `normGroup` (`normGroup_eq_fieldNormSubgroup`, by `rfl` for an intermediate field of $\Omega$), and norm
groups are invariant under $K$-isomorphisms (`fieldNormSubgroup_eq_of_algEquiv`). Yamaguchi's
`FiniteAbelianLocalExtension K` is our `FiniteAbelianExt K (SeparableClosure K)` as a subtype
(`finiteAbelianExtOfYamaguchi`).
-/

noncomputable section

namespace NumberFieldKB.MilneCFT.LocalCFT

universe u v

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type v} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- Our norm group of an intermediate field of $\Omega$ is Yamaguchi's field-norm subgroup of the same field. -/
theorem normGroup_eq_fieldNormSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    normGroup L = ClassFieldTheory.fieldNormSubgroup K L :=
  rfl

/-- Yamaguchi's field-norm subgroup is invariant under $K$-isomorphisms. -/
theorem fieldNormSubgroup_eq_of_algEquiv {E F : Type*} [Field E] [Algebra K E] [FiniteDimensional K E]
    [Field F] [Algebra K F] [FiniteDimensional K F] (ψ : E ≃ₐ[K] F) :
    ClassFieldTheory.fieldNormSubgroup K E = ClassFieldTheory.fieldNormSubgroup K F := by
  ext a
  simp only [ClassFieldTheory.fieldNormSubgroup, ClassFieldTheory.fieldNormHom, MonoidHom.mem_range,
    Units.ext_iff, Units.coe_map]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Units.map ψ.toRingEquiv.toMonoidHom y, ?_⟩
    rw [← hy]
    exact Algebra.norm_eq_of_algEquiv ψ (y : E)
  · rintro ⟨y, hy⟩
    refine ⟨Units.map ψ.symm.toRingEquiv.toMonoidHom y, ?_⟩
    rw [← hy]
    exact Algebra.norm_eq_of_algEquiv ψ.symm (y : F)

variable (K Ω) in
/-- **The local existence theorem, proved in every characteristic** (Milne, *CFT*, I, Theorem 1.4, hard half): the
named statement `LocalExistenceInput` holds for every nonarchimedean local field $K$ and every separable closure
$\Omega$, from Yamaguchi's `ClassFieldTheory.finiteAbelianLocalExistence_orderIso` (ported). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4"]
theorem localExistenceInput_yamaguchi : LocalExistenceInput K Ω := by
  refine ⟨fun H hopen hfi => ?_⟩
  obtain ⟨e, he⟩ := ClassFieldTheory.finiteAbelianLocalExistence_orderIso K
  let E : ClassFieldTheory.FiniteAbelianLocalExtension K := e.symm (OrderDual.toDual ⟨H, hopen, hfi⟩)
  have hE : E.normSubgroup = H := by
    rw [← he E]
    simp [E]
  let φ : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  let L : IntermediateField K Ω := E.1.map φ.toAlgHom
  let ψ : E.1 ≃ₐ[K] L := IntermediateField.equivMap E.1 φ.toAlgHom
  have : FiniteDimensional K L := LinearEquiv.finiteDimensional ψ.toLinearEquiv
  have : IsGalois K L := IsGalois.of_algEquiv ψ
  have : IsMulCommutative Gal(L/K) := by
    have := (inferInstance : IsAbelianGalois K E.1).toIsMulCommutative
    exact (AlgEquiv.autCongr ψ).surjective.isMulCommutative
  have : IsAbelianGalois K L := ⟨⟩
  refine ⟨⟨L⟩, ?_⟩
  change normGroup L = H
  rw [normGroup_eq_fieldNormSubgroup, ← fieldNormSubgroup_eq_of_algEquiv ψ, ← hE]
  rfl

end NumberFieldKB.MilneCFT.LocalCFT
