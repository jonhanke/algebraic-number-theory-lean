import NumberFieldKB.MilneCFT.Ch7.TateZero
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.GroupTheory.QuotientGroup.Simple
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Auxiliary results for Milne, *CFT*, Chapter VII, Lemma 4.5

Helpers: the tower law for `adeleMap`, equivariance of `ideleIncl`, and the inclusion
$\mathrm{Nm}_{L/K}\mathbb I_L\subseteq\mathrm{Nm}_{K'/K}\mathbb I_{K'}$ for $K\subseteq K'\subseteq L$ with $K'/K$ and
$L/K$ Galois.
-/

open IsDedekindDomain NumberField NumberField.mixedEmbedding
open QuadFormsKB.Tamagawa.Measure.Weil NumberFieldKB.Ideles

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7.Lemma45Aux

section Tower

variable {k F L : Type} [Field k] [NumberField k] [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]

theorem infMap_comp : (infMap F L).comp (infMap k F) = infMap k L := by
  refine (latticeBasis k).ext fun i => ?_
  simp only [LinearMap.comp_apply, latticeBasis_apply, infMap_mixedEmbedding]
  rw [← IsScalarTower.algebraMap_apply]

theorem finMap_comp (t : FiniteAdeleRing (𝓞 k) k) : finMap F L (finMap k F t) = finMap k L t := by
  have hc1 : Continuous fun t : FiniteAdeleRing (𝓞 k) k => finMap F L (finMap k F t) :=
    continuous_finMap.comp continuous_finMap
  have := (denseRange_algebraMap_finiteAdele (F := k)).equalizer hc1 continuous_finMap
    (funext fun x => by
      simp only [Function.comp_apply, finMap_algebraMap, ← IsScalarTower.algebraMap_apply])
  exact congrFun this t

theorem adeleMap_comp (t : Adeles k) : adeleMap F L (adeleMap k F t) = adeleMap k L t := by
  refine Prod.ext ?_ ?_
  · simp only [adeleMap_fst]
    have := LinearMap.congr_fun (infMap_comp (k := k) (F := F) (L := L)) t.1
    exact this
  · simp only [adeleMap_snd]
    exact finMap_comp t.2

theorem ideleIncl_comp (x : IdeleGroup (𝓞 k) k) :
    ideleIncl F L (ideleIncl k F x) = ideleIncl k L x := by
  apply (ideleGroupEquiv L).injective
  rw [ideleGroupEquiv_ideleIncl, ideleGroupEquiv_ideleIncl, ideleGroupEquiv_ideleIncl]
  refine Units.ext ?_
  simp only [Units.coe_map]
  exact adeleMap_comp _

/-- Expansion of `galAdeleFun` on sums of the form `∑ diag(c_j) * ι(t_j)`. -/
theorem galAdeleFun_expansion (σ : L ≃ₐ[F] L) {ι : Type} (s : Finset ι) (c : ι → L) (t : ι → Adeles F) :
    galAdeleFun σ (∑ j ∈ s, diagRing L (c j) * adeleMap F L (t j)) =
      ∑ j ∈ s, diagRing L (σ (c j)) * adeleMap F L (t j) := by
  rw [galAdeleFun_sum]
  exact Finset.sum_congr rfl fun j _ => galAdeleFun_diag_mul_adeleMap σ _ _

/-- The action of `Gal(L/F)` on `𝔸_L` is the restriction of the action of `Gal(L/K)`. -/
theorem galAdeleFun_restrictScalars (σ : L ≃ₐ[F] L) (y : Adeles L) :
    galAdeleFun (σ.restrictScalars k) y = galAdeleFun σ y := by
  rw [galAdeleFun_eq]
  have h : y = ∑ j, diagRing L (Module.finBasis k L j) *
      adeleMap F L (adeleMap k F ((adeleBaseChange (Module.finBasis k L)).symm y j)) := by
    simp only [adeleMap_comp]
    exact adele_expand k y
  conv_rhs => rw [h]
  rw [galAdeleFun_expansion]
  simp only [adeleMap_comp]
  rfl

/-- **Equivariance of `adeleMap`**: if `σ ∈ Gal(L/K)` restricts to `τ ∈ Gal(F/K)` then
`ι(τ t) = σ ι(t)`. -/
theorem adeleMap_galAdeleFun (σ : L ≃ₐ[k] L) (τ : F ≃ₐ[k] F)
    (hστ : ∀ f : F, σ (algebraMap F L f) = algebraMap F L (τ f)) (t : Adeles F) :
    adeleMap F L (galAdeleFun τ t) = galAdeleFun σ (adeleMap F L t) := by
  have h : t = ∑ j, diagRing F (Module.finBasis k F j) *
      adeleMap k F ((adeleBaseChange (Module.finBasis k F)).symm t j) := adele_expand k t
  have h1 : adeleMap F L t = ∑ j, diagRing L (algebraMap F L (Module.finBasis k F j)) *
      adeleMap k L ((adeleBaseChange (Module.finBasis k F)).symm t j) := by
    conv_lhs => rw [h]
    simp only [map_sum, map_mul, adeleMap_diagRing, adeleMap_comp]
  rw [galAdeleFun_eq τ t, h1, galAdeleFun_sum]
  simp only [map_sum, map_mul, adeleMap_diagRing, adeleMap_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [galAdeleFun_diag_mul_adeleMap, hστ]

/-- **Equivariance of `ideleIncl`**. -/
theorem ideleIncl_smul (σ : L ≃ₐ[k] L) (τ : F ≃ₐ[k] F)
    (hστ : ∀ f : F, σ (algebraMap F L f) = algebraMap F L (τ f)) (y : IdeleGroup (𝓞 F) F) :
    ideleIncl F L (τ • y) = σ • ideleIncl F L y := by
  refine Units.ext ((adeleRingEquiv L).injective ?_)
  change adeleRingEquiv L ((adeleRingEquiv L).symm (adeleMap F L (adeleRingEquiv F (τ • (y : AdeleRing (𝓞 F) F))))) =
    adeleRingEquiv L (σ • (adeleRingEquiv L).symm (adeleMap F L (adeleRingEquiv F y)))
  rw [adeleRingEquiv_smul, adeleRingEquiv_smul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  exact adeleMap_galAdeleFun σ τ hστ _

section Norm

variable [IsGalois k L] [IsGalois k F] [IsGalois F L]

/-- The bijection `Gal(F/k) × Gal(L/F) ≃ Gal(L/k)`, as a function. -/
def prodMap (p : (F ≃ₐ[k] F) × (L ≃ₐ[F] L)) : L ≃ₐ[k] L :=
  p.1.liftNormal L * p.2.restrictScalars k

theorem prodMap_algebraMap (p : (F ≃ₐ[k] F) × (L ≃ₐ[F] L)) (f : F) :
    prodMap p (algebraMap F L f) = algebraMap F L (p.1 f) := by
  change (p.1.liftNormal L) (p.2 (algebraMap F L f)) = _
  rw [AlgEquiv.commutes, AlgEquiv.liftNormal_commutes]

theorem prodMap_bijective : Function.Bijective (prodMap (k := k) (F := F) (L := L)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, h⟩ ⟨τ', h'⟩ he
    have hτ : τ = τ' := by
      ext f
      apply (algebraMap F L).injective
      rw [← prodMap_algebraMap ⟨τ, h⟩, he, prodMap_algebraMap ⟨τ', h'⟩]
    subst hτ
    have : h.restrictScalars k = h'.restrictScalars k := mul_left_cancel he
    refine Prod.ext rfl (AlgEquiv.ext fun x => ?_)
    exact congrArg (fun g : L ≃ₐ[k] L => g x) this
  · rw [Fintype.card_prod]
    simp only [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact Module.finrank_mul_finrank k F L

/-- **Norm transitivity (inclusion)**: for a tower `k ⊆ F ⊆ L` of Galois extensions of number fields,
`Nm_{L/k} 𝕀_L ⊆ Nm_{F/k} 𝕀_F` (indeed `Nm_{L/k} = Nm_{F/k} ∘ Nm_{L/F}`). -/
theorem ideleNorm_comp (x : IdeleGroup (𝓞 L) L) :
    ideleNorm k F (ideleNorm F L x) = ideleNorm k L x := by
  apply (prop_2_5a k L).1
  rw [← ideleIncl_comp (F := F), ideleIncl_ideleNorm k F, ideleIncl_ideleNorm k L, map_prod]
  have hF := ideleIncl_ideleNorm F L x
  have hres : ∀ (h : L ≃ₐ[F] L) (z : IdeleGroup (𝓞 L) L), (h.restrictScalars k) • z = h • z := by
    intro h z
    refine Units.ext ((adeleRingEquiv L).injective ?_)
    change adeleRingEquiv L (galAdeleFun _ (adeleRingEquiv L (z : AdeleRing (𝓞 L) L)) |> (adeleRingEquiv L).symm) =
      adeleRingEquiv L (galAdeleFun _ (adeleRingEquiv L (z : AdeleRing (𝓞 L) L)) |> (adeleRingEquiv L).symm)
    rw [galAdeleFun_restrictScalars]
  have h1 : ∀ τ : F ≃ₐ[k] F, ideleIncl F L (τ • ideleNorm F L x) =
      τ.liftNormal L • ∏ h : L ≃ₐ[F] L, h • x := by
    intro τ
    rw [ideleIncl_smul (τ.liftNormal L) τ (fun f => AlgEquiv.liftNormal_commutes τ L f), hF]
  refine Eq.trans ?_ (Fintype.prod_bijective _ (prodMap_bijective (k := k) (F := F) (L := L))
    (fun p => p.1.liftNormal L • p.2 • x) (fun g => g • x) (fun p => ?_))
  · simp only [h1]
    rw [Fintype.prod_prod_type (f := fun p : (F ≃ₐ[k] F) × (L ≃ₐ[F] L) => p.1.liftNormal L • p.2 • x)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact map_prod (MulDistribMulAction.toMonoidHom (IdeleGroup (𝓞 L) L) (τ.liftNormal L)) _ _
  · change _ = (p.1.liftNormal L * p.2.restrictScalars k) • x
    rw [mul_smul, hres]

end Norm

end Tower

/-- A nontrivial finite solvable group has a proper normal subgroup with cyclic quotient (of prime order). -/
theorem exists_normal_cyclic_quotient (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] [Nontrivial G] :
    ∃ (H : Subgroup G) (_ : H.Normal), H ≠ ⊤ ∧ IsCyclic (G ⧸ H) := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator G)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne
  haveI : M.Normal := Subgroup.Normal.of_commutator_le (G := G) hle
  haveI : IsSimpleGroup (G ⧸ M) := Group.isSimpleGroup_of_isCoatom hM
  haveI : IsMulCommutative (G ⧸ M) := Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hle
  letI : CommGroup (G ⧸ M) :=
    { (inferInstance : Group (G ⧸ M)) with mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  exact ⟨M, inferInstance, hM.1, IsSimpleGroup.isCyclic⟩

end NumberFieldKB.MilneCFT.Ch7.Lemma45Aux
