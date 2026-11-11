import NumberFieldKB.MilneCFT.Ch7.BrauerTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.RelativeBrauerLocalization
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Milne, *Class Field Theory*, Chapter VII, Theorem 7.1 from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
Theorem 7.1, p. 219.

The named statement `Theorem7_1` has two parts. The concrete form (`splits`) is `theorem7_1_splits`
(`BrauerTauCeti.lean`). The cohomological form (`injective`): a $2$-cocycle $f$ of $G = \mathrm{Gal}(L/K)$ with values
in $L^\times$ that becomes a coboundary in $(L\otimes_KK_v)^\times$ for every place $v$ is a coboundary. Proof, from Tau
Ceti's global class field theory (ported, Apache 2.0, the Tau Ceti contributors):

* the hypothesis at $v$ says that the image of the class $[f]$ in $H^2(G,(K_v\otimes_KL)^\times)$ vanishes (the
  factors are swapped by `Algebra.TensorProduct.comm`, which intertwines the two Galois actions);
* by `map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero` (and its infinite analogue) the
  Brauer class `relBrInfl K L σ [f]` is then locally trivial everywhere;
* by the Hasse principle `brLocalization_injective` it is trivial, and inflation `relBrInfl` is injective.
-/

open IsDedekindDomain NumberField CategoryTheory TauCeti.ClassFieldTheory groupCohomology
open scoped TensorProduct AdicCompletionExtension

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- Swapping the tensor factors, on units: $(L\otimes_KF)^\times\simeq(F\otimes_KL)^\times$. -/
abbrev swapUnits (F : Type) [Field F] [Algebra K F] : (L ⊗[K] F)ˣ ≃* (F ⊗[K] L)ˣ :=
  Units.mapEquiv (Algebra.TensorProduct.comm K L F).toMulEquiv

omit [NumberField K] [NumberField L] in
theorem swapUnits_smul (F : Type) [Field F] [Algebra K F] (σ : L ≃ₐ[K] L) (u : (L ⊗[K] F)ˣ) :
    swapUnits F (σ • u) = TauCeti.Algebra.TensorProduct.baseChangeAutHom F L σ • swapUnits F u := by
  apply Units.ext
  change Algebra.TensorProduct.comm K L F (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K F) (u : L ⊗[K] F)) =
    Algebra.TensorProduct.congr AlgEquiv.refl σ (Algebra.TensorProduct.comm K L F (u : L ⊗[K] F))
  induction (u : L ⊗[K] F) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField K] [NumberField L] in
theorem coe_swapUnits_unitsToTensor (F : Type) [Field F] [Algebra K F] (a : Lˣ) :
    ((swapUnits F (unitsToTensor K L F a) : (F ⊗[K] L)ˣ) : F ⊗[K] L) = 1 ⊗ₜ[K] (a : L) :=
  rfl

omit [NumberField K] [NumberField L] in
/-- A cocycle that is a coboundary in $(L\otimes_KF)^\times$ gives, after swapping the factors, a coboundary of
Tau Ceti's representation on $(F\otimes_KL)^\times$. -/
theorem mem_coboundaries₂_swap (F : Type) [Field F] [Algebra K F] (f : Gal(L/K) × Gal(L/K) → Lˣ)
    (hf : IsMulCoboundary₂ (fun g => unitsToTensor K L F (f g)))
    (c : Gal(L/K) × Gal(L/K) → Additive (F ⊗[K] L)ˣ)
    (hc : ∀ g, ((Additive.toMul (c g) : (F ⊗[K] L)ˣ) : F ⊗[K] L) = 1 ⊗ₜ[K] ((f g : Lˣ) : L)) :
    c ∈ coboundaries₂ (Rep.res (TauCeti.Algebra.TensorProduct.baseChangeAutHom F L)
      (Rep.ofAlgebraAutOnUnits F (F ⊗[K] L))) := by
  obtain ⟨x, hx⟩ := hf
  refine ⟨fun g => Additive.ofMul (swapUnits F (x g)), funext fun ⟨g₁, g₂⟩ => ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  refine Eq.trans ?_ (hc (g₁, g₂)).symm
  change (((TauCeti.Algebra.TensorProduct.baseChangeAutHom F L g₁ • swapUnits F (x g₂)) /
      swapUnits F (x (g₁ * g₂)) * swapUnits F (x g₁) : (F ⊗[K] L)ˣ) : F ⊗[K] L) =
    ((swapUnits F (unitsToTensor K L F (f (g₁, g₂))) : (F ⊗[K] L)ˣ) : F ⊗[K] L)
  rw [← swapUnits_smul, ← map_div, ← map_mul, hx g₁ g₂]

omit [NumberField L] in
/-- The semi-local component at a finite place $v$ of the principal idèle of $a\in L^\times$ is $1\otimes a$ (as in
Tau Ceti's private lemma of `RelativeBrauerLocalization.lean`). -/
theorem coe_unitsToIdeles_idelesToSemilocalUnits (v : HeightOneSpectrum (𝓞 K)) [NumberField L]
    (a : Additive Lˣ) :
    ((Additive.toMul (α := (v.adicCompletion K ⊗[K] L)ˣ)
      ((unitsToIdeles K L ≫ idelesToSemilocalUnits L v).hom a) : (v.adicCompletion K ⊗[K] L)ˣ) :
        v.adicCompletion K ⊗[K] L) = 1 ⊗ₜ[K] ((Additive.toMul a : Lˣ) : L) := by
  have h : (unitsToIdeles K L ≫ idelesToSemilocalUnits L v).hom a =
      Additive.ofMul (TauCeti.finiteIdeleSemilocalHom L v
        (FiniteAdeleRing.unitEmbedding (𝓞 L) L (Additive.toMul a))) :=
    (congrArg (idelesToSemilocalUnits L v).hom (unitsToIdeles_hom_apply (K := K) L a)).trans
      ((idelesToSemilocalUnits_hom_apply L v _).trans
        (congrArg (fun z ↦ Additive.ofMul (TauCeti.finiteIdeleSemilocalHom L v z))
          (IdeleGroup.toFiniteIdele_unitEmbedding (𝓞 L) L _)))
  rw [h, toMul_ofMul, TauCeti.coe_finiteIdeleSemilocalHom, FiniteAdeleRing.unitEmbedding_apply,
    TauCeti.finiteAdeleSemilocalHom_algebraMap]

/-- The semi-local component at an infinite place $w$ of the principal idèle of $a\in L^\times$ is $1\otimes a$. -/
theorem coe_unitsToIdeles_idelesToInfiniteSemilocalUnits (w : InfinitePlace K) (a : Additive Lˣ) :
    ((Additive.toMul (α := (w.Completion ⊗[K] L)ˣ)
      ((unitsToIdeles K L ≫ idelesToInfiniteSemilocalUnits L w).hom a) : (w.Completion ⊗[K] L)ˣ) :
        w.Completion ⊗[K] L) = 1 ⊗ₜ[K] ((Additive.toMul a : Lˣ) : L) :=
  (coe_idelesToInfiniteSemilocalUnits_hom_apply L w _).trans <|
    (congrArg (fun z : Additive (IdeleGroup (𝓞 L) L) ↦
      TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom L w ((Additive.toMul z : IdeleGroup (𝓞 L) L) : AdeleRing (𝓞 L) L).1)
      (unitsToIdeles_hom_apply (K := K) L a)).trans
    (TauCeti.GlobalNumberFields.infiniteAdeleSemilocalHom_algebraMap (L := L) (v := w) _)

/-- **Theorem 7.1, cohomological form** (Milne, *CFT*, Chapter VII, p. 219): a $2$-cocycle of $\mathrm{Gal}(L/K)$
in $L^\times$ that is a coboundary in $(L\otimes_KK_v)^\times$ for every place $v$ is a coboundary. -/
theorem theorem7_1_injective [IsGalois K L] (f : Gal(L/K) × Gal(L/K) → Lˣ) (hf : IsMulCocycle₂ f)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), IsMulCoboundary₂
      (fun g : Gal(L/K) × Gal(L/K) => unitsToTensor K L (v.adicCompletion K) (f g)))
    (hinf : ∀ w : InfinitePlace K, IsMulCoboundary₂
      (fun g : Gal(L/K) × Gal(L/K) => unitsToTensor K L w.Completion (f g))) :
    IsMulCoboundary₂ f := by
  let z := cocyclesOfIsMulCocycle₂ hf
  let x := H2π (Rep.ofMulDistribMulAction Gal(L/K) Lˣ) z
  let σ : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have hv (v : HeightOneSpectrum (𝓞 K)) :
      brBaseChange K (v.adicCompletion K) (relBrInfl K L σ x) = 0 := by
    rw [← map_unitsToIdeles_idelesToSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero σ x,
      H2π_comp_map_apply, H2π_eq_zero_iff]
    exact mem_coboundaries₂_swap _ f (hfin v) _
      (fun g => coe_unitsToIdeles_idelesToSemilocalUnits v (Additive.ofMul (f g)))
  have hw (w : InfinitePlace K) : brBaseChange K w.Completion (relBrInfl K L σ x) = 0 := by
    rw [← map_unitsToIdeles_idelesToInfiniteSemilocalUnits_eq_zero_iff_brBaseChange_eq_zero σ x,
      H2π_comp_map_apply, H2π_eq_zero_iff]
    exact mem_coboundaries₂_swap _ f (hinf w) _
      (fun g => coe_unitsToIdeles_idelesToInfiniteSemilocalUnits w (Additive.ofMul (f g)))
  have hloc : brLocalization K (relBrInfl K L σ x) = 0 :=
    Prod.ext (DFinsupp.ext fun v => (brLocalization_fst_apply K _ v).trans (hv v))
      (funext fun w => (brLocalization_snd_apply K _ w).trans (hw w))
  have hx : x = 0 := (injective_iff_map_eq_zero (relBrInfl K L σ)).1 (relBrInfl_injective K L σ) _
    ((injective_iff_map_eq_zero (brLocalization K)).1 (brLocalization_injective K) _ hloc)
  rw [H2π_eq_zero_iff] at hx
  exact isMulCoboundary₂_of_mem_coboundaries₂ _ hx

/-- **Theorem 7.1, unconditional** (Milne, *CFT*, Chapter VII, p. 219): $H^2(L/K)\to\bigoplus_vH^2(L_v/K_v)$ is
injective (cocycle form, `theorem7_1_injective`), and a central simple algebra over $K$ split by every completion is
split (`theorem7_1_splits`). From Tau Ceti's Hasse principle for the Brauer group. -/
@[kb "milne2020cft" "Ch. VII, Thm. 7.1"]
theorem theorem7_1 (K : Type) [Field K] [NumberField K] : Theorem7_1 K where
  injective _ _ _ _ _ f hf hfin hinf := theorem7_1_injective f hf hfin hinf
  splits A _ _ _ _ _ hfin hinf := theorem7_1_splits A hfin hinf

end NumberFieldKB.MilneCFT.Ch7
