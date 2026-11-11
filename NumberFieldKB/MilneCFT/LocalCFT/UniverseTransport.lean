import NumberFieldKB.MilneCFT.LocalCFT.UnconditionalYamaguchi
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Norm.Basic

/-!
# Local class field theory for a separable closure in any universe

Tau Ceti's local reciprocity (`localReciprocityExistence`) and hence `isLocalArtinMap_unique_unconditional` are
stated for $K$ and $\Omega$ in `Type`. Norm groups do not depend on the choice of separable closure: a
$K$-isomorphism $e : \Omega \simeq \Omega'$ carries finite abelian extensions to finite abelian extensions with the same
norm group (`normGroup_map`). So the local existence theorem (Milne, *CFT*, I, Theorem 1.4) and the uniqueness of the
local Artin map (Theorem 1.13) hold for a separable closure $\Omega$ in any universe (`isNormGroup_iff_univ`,
`isLocalArtinMap_unique_univ`), by comparison with `SeparableClosure K`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω Ω' : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [Field Ω'] [Algebra K Ω']
  [IsSepClosure K Ω']

/-- The image of a finite abelian extension under a $K$-isomorphism of separable closures. -/
def FiniteAbelianExt.mapEquiv (e : Ω ≃ₐ[K] Ω') (L : FiniteAbelianExt K Ω) : FiniteAbelianExt K Ω' :=
  let g : L.toField ≃ₐ[K] L.toField.map (e : Ω →ₐ[K] Ω') := IntermediateField.equivMap L.toField (e : Ω →ₐ[K] Ω')
  haveI : FiniteDimensional K (L.toField.map (e : Ω →ₐ[K] Ω')) := Module.Finite.equiv g.toLinearEquiv
  haveI : IsAbelianGalois K (L.toField.map (e : Ω →ₐ[K] Ω')) := IsAbelianGalois.of_algHom g.symm.toAlgHom
  { toField := L.toField.map (e : Ω →ₐ[K] Ω') }

/-- Norm groups are invariant under $K$-isomorphisms of the ambient separable closure. -/
theorem normGroup_map (e : Ω ≃ₐ[K] Ω') (L : IntermediateField K Ω) [FiniteDimensional K L]
    [FiniteDimensional K (L.map (e : Ω →ₐ[K] Ω'))] :
    normGroup (L.map (e : Ω →ₐ[K] Ω')) = normGroup L := by
  let g : L ≃ₐ[K] L.map (e : Ω →ₐ[K] Ω') := IntermediateField.equivMap L (e : Ω →ₐ[K] Ω')
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map (g.symm : _ →* _) y, Units.ext ?_⟩
    change Algebra.norm K (g.symm (y : L.map (e : Ω →ₐ[K] Ω'))) = Algebra.norm K (y : L.map (e : Ω →ₐ[K] Ω'))
    exact Algebra.norm_eq_of_algEquiv g.symm _
  · rintro ⟨x, rfl⟩
    refine ⟨Units.map (g : _ →* _) x, Units.ext ?_⟩
    change Algebra.norm K (g (x : L)) = Algebra.norm K (x : L)
    exact Algebra.norm_eq_of_algEquiv g _

theorem isNormGroup_of_equiv (e : Ω ≃ₐ[K] Ω') {H : Subgroup Kˣ} (h : IsNormGroup K Ω H) : IsNormGroup K Ω' H := by
  obtain ⟨L, rfl⟩ := h
  have : FiniteDimensional K (L.toField.map (e : Ω →ₐ[K] Ω')) := (L.mapEquiv e).finiteDimensional
  exact ⟨L.mapEquiv e, normGroup_map e L.toField⟩

theorem isNormGroup_iff_of_equiv (e : Ω ≃ₐ[K] Ω') (H : Subgroup Kˣ) : IsNormGroup K Ω H ↔ IsNormGroup K Ω' H :=
  ⟨isNormGroup_of_equiv e, isNormGroup_of_equiv e.symm⟩

variable (Ω) in
/-- **Theorem 1.4 (local existence), for a separable closure in any universe** (Milne, *CFT*, I, Theorem 1.4): the
norm groups are exactly the open subgroups of finite index. -/
@[kb "milne2020cft" "Ch. I, Theorem 1.4"]
theorem isNormGroup_iff_univ (H : Subgroup Kˣ) : IsNormGroup K Ω H ↔ IsOpen (H : Set Kˣ) ∧ H.FiniteIndex :=
  (isNormGroup_iff_of_equiv (IsSepClosure.equiv K Ω (SeparableClosure K)) H).trans
    (isNormGroup_iff_unconditional (SeparableClosure K) H)

/-- **Theorem 1.13 (uniqueness of the local Artin map), for a separable closure in any universe** (Milne, *CFT*, I,
p. 33). -/
@[kb "milne2020cft" "Ch. I, Theorem 1.13"]
theorem isLocalArtinMap_unique_univ {φ ψ : ∀ L : FiniteAbelianExt K Ω, Kˣ →* Gal(L.toField/K)}
    (hφ : IsLocalArtinMap φ) (hψ : IsLocalArtinMap ψ) : φ = ψ :=
  isLocalArtinMap_unique (isNormGroup_iff_univ Ω) (unramifiedInput K Ω) hφ hψ

end NumberFieldKB.MilneCFT.LocalCFT
