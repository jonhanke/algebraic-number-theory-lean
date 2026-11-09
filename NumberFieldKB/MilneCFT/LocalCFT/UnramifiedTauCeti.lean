import NumberFieldKB.MilneCFT.LubinTate.HerbrandTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.Unramified.Existence
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.ResidueCorrespondence

/-!
# Unramified extensions from Tau Ceti (Milne, *CFT*, I, §1, p. 20)

Our unramifiedness `IsUnramifiedExt L` ($\mathfrak m_K\mathcal O_L$ is maximal) is Tau Ceti's `TauCeti.IsUnramified K L`
for any local-field structure on $L$ extending $K$'s (`isUnramified_iff_isUnramifiedExt`), and our Frobenius
condition `IsFrobenius` ($\sigma x\equiv x^q$ modulo $\mathfrak m_K\mathcal O_L$) characterizes Tau Ceti's
`frobeniusAlgEquiv` (`eq_frobeniusAlgEquiv_of_isFrobenius`, from `eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one`).
With Tau Ceti's unramified extension of each degree inside $\Omega$ (`TauCeti.unramifiedExtension`, ported from Tau Ceti
main `85f3eb55`, Apache 2.0), this proves the named statement `UnramifiedInput` (`unramifiedInput`).
-/

open scoped ValuativeRel

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Compatible

variable (E : IntermediateField K Ω) [FiniteDimensional K E] [ValuativeRel E] [TopologicalSpace E]
  [ValuativeExtension K E] [IsNonarchimedeanLocalField E]

omit [FiniteDimensional K E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
theorem map_maximalIdeal_integerRingEquiv :
    (𝓂[K].map (algebraMap 𝒪[K] 𝒪[E])).map
        ((TauCeti.integerRingEquivIntegralClosure K E : 𝒪[E] →+* integers E)) =
      𝓂[K].map (algebraMap 𝒪[K] (integers E)) := by
  have he : ((TauCeti.integerRingEquivIntegralClosure K E : 𝒪[E] →+* integers E)).comp
      (algebraMap 𝒪[K] 𝒪[E]) = algebraMap 𝒪[K] (integers E) :=
    RingHom.ext fun x => (TauCeti.integerRingEquivIntegralClosure K E).commutes x
  rw [Ideal.map_map, he]

/-- **Our unramifiedness is Tau Ceti's.** -/
theorem isUnramified_iff_isUnramifiedExt : TauCeti.IsUnramified K E ↔ IsUnramifiedExt E := by
  rw [TauCeti.isUnramified_iff_map_maximalIdeal_eq]
  set e := TauCeti.integerRingEquivIntegralClosure K E
  constructor
  · intro h
    have hmax : ((𝓂[E]).comap ((e.toRingEquiv.symm : integers E →+* 𝒪[E]))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ e.toRingEquiv.symm.surjective
    have heq : (𝓂[E]).map (e : 𝒪[E] →+* integers E) =
        (𝓂[E]).comap (e.toRingEquiv.symm : integers E →+* 𝒪[E]) :=
      Ideal.map_comap_of_equiv e.toRingEquiv
    unfold IsUnramifiedExt
    rw [← map_maximalIdeal_integerRingEquiv E, h, heq]
    exact hmax
  · intro hE
    have hmap := map_maximalIdeal_integerRingEquiv E
    have hmax : (𝓂[K].map (algebraMap 𝒪[K] 𝒪[E])).IsMaximal := by
      have h1 : (((𝓂[K].map (algebraMap 𝒪[K] 𝒪[E])).map (e : 𝒪[E] →+* integers E)).comap
          (e : 𝒪[E] →+* integers E)).IsMaximal := by
        rw [hmap]
        exact Ideal.comap_isMaximal_of_surjective _ e.surjective (H := hE)
      rwa [Ideal.comap_map_of_bijective (e : 𝒪[E] →+* integers E) e.bijective] at h1
    exact IsLocalRing.eq_maximalIdeal hmax

/-- **Our Frobenius condition characterizes Tau Ceti's Frobenius**: in an unramified $E/K$, an automorphism with
$\sigma x - x^q\in\mathfrak m_K\mathcal O_E$ for all $x\in\mathcal O_E$ is `frobeniusAlgEquiv`. -/
theorem eq_frobeniusAlgEquiv_of_isFrobenius [IsGalois K E] [TauCeti.IsUnramified K E] (σ : Gal(E/K))
    (hσ : IsFrobenius E σ) : σ = TauCeti.frobeniusAlgEquiv (K := K) (L := E) := by
  apply TauCeti.eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one
  intro y
  set e := TauCeti.integerRingEquivIntegralClosure K E
  have hy : (y : E) ∈ integers E := by
    rw [← TauCeti.coe_integerRingEquivIntegralClosure_apply (K := K) y]
    exact (e y).2
  obtain ⟨b, hb, hby⟩ := hσ (y : E) hy
  have hb1 : b ∈ maxIdealL E ^ 1 := by
    rw [pow_one]
    exact Ideal.le_radical hb
  have hm := (mem_maxIdealL_pow_iff E 1 b).1 hb1
  rw [pow_one] at hm
  have hv := (Valuation.mem_maximalIdeal_iff (v := ValuativeRel.valuation E)).1 hm
  rw [TauCeti.coe_integerRingEquivIntegralClosure_symm_apply, hby] at hv
  exact hv

end Compatible

variable (K Ω) in
/-- **Finite unramified extensions, proved** (Milne, *CFT*, I, §1, p. 20, and *ANT* 7.54): the named statement
`UnramifiedInput` holds. For $m\ge1$ Tau Ceti's `unramifiedExtension K Ω m` is unramified of degree $m$ with cyclic
Galois group (`isUnramified_unramifiedExtension`, `finrank_unramifiedExtension`, `isCyclic_algEquiv`); and an
automorphism satisfying our Frobenius condition is Tau Ceti's `frobeniusAlgEquiv` (`eq_frobeniusAlgEquiv_of_isFrobenius`),
hence unique. -/
@[kb "milne2020cft" "Ch. I, §1, p. 20 (unramified extensions)"]
theorem unramifiedInput : UnramifiedInput K Ω := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine ⟨fun m hm => ?_, fun L hL σ τ hσ hτ => ?_⟩
  · have hm0 : m ≠ 0 := by omega
    let E := TauCeti.unramifiedExtension K Ω m
    let _ : ValuativeRel E := TauCeti.finiteIntermediateFieldValuativeRel K Ω E
    let _ : TopologicalSpace E := TauCeti.finiteIntermediateFieldTopology K Ω E
    have : ValuativeExtension K E := TauCeti.finiteIntermediateField_valuativeExtension K Ω E
    have : IsNonarchimedeanLocalField E := TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω E
    have hU : TauCeti.IsUnramified K E := TauCeti.isUnramified_unramifiedExtension hm0
    have : IsCyclic Gal(E/K) := TauCeti.isCyclic_algEquiv
    have : IsMulCommutative Gal(E/K) := ⟨⟨IsCyclic.commGroup.mul_comm⟩⟩
    have : IsAbelianGalois K E := ⟨⟩
    exact ⟨⟨E⟩, (isUnramified_iff_isUnramifiedExt E).1 hU, TauCeti.finrank_unramifiedExtension hm0⟩
  · let _ : ValuativeRel L.toField := TauCeti.finiteIntermediateFieldValuativeRel K Ω L.toField
    let _ : TopologicalSpace L.toField := TauCeti.finiteIntermediateFieldTopology K Ω L.toField
    have : ValuativeExtension K L.toField := TauCeti.finiteIntermediateField_valuativeExtension K Ω L.toField
    have : IsNonarchimedeanLocalField L.toField :=
      TauCeti.finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toField
    have : TauCeti.IsUnramified K L.toField := (isUnramified_iff_isUnramifiedExt L.toField).2 hL
    rw [eq_frobeniusAlgEquiv_of_isFrobenius L.toField σ hσ, eq_frobeniusAlgEquiv_of_isFrobenius L.toField τ hτ]

end NumberFieldKB.MilneCFT.LocalCFT
