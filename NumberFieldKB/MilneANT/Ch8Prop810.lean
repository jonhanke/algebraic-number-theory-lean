import NumberFieldKB.MilneANT.Ch8Prop81
import NumberFieldKB.MilneANT.Ch8Decomposition

/-!
# Milne, *Algebraic Number Theory*, Proposition 8.10: $G_w \cong \mathrm{Gal}(L_w/K_v)$

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, p. 139.

Proof outline, following Milne:

1. An element $\sigma$ of the decomposition group $G_w$ is an isometry of $(L, w)$, so it extends (by
   `exists_completion_lift`, `Prop810.exists_ext`) to a norm-preserving automorphism of $L_w$ over $K_v$
   (`Prop810.exists_equiv`). Such automorphisms are determined by their values on $L$ (`Prop810.ext_L`), whence a
   group homomorphism `Prop810.extHom` $G_w \to \mathrm{Gal}(L_w/K_v)$.
2. It is injective since $L \to L_w$ is injective.
3. It is surjective: $L_w$ is finite over $K_v$ (`Prop81.hMap_bijective`), so any $\tau \in \mathrm{Gal}(L_w/K_v)$ is an
   isometry (uniqueness of the extension of the absolute value, `absoluteValue_eq_of_complete`); as $L/K$ is normal,
   $\tau$ restricts to an automorphism $\sigma$ of $L$ (`AlgEquiv.restrictNormal`), which lies in $G_w$ because $\tau$ is
   an isometry, and extends to $\tau$.
-/

open NumberField

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneANT
noncomputable section

namespace Prop810

open Prop81

section

variable {K L : Type} [Field K] [Field L] [Algebra K L] (v : AbsoluteValue K ℝ)
  (w : AbsoluteValue L ℝ) [w.LiesOver v]

theorem completeSpace_toAbs : CompleteSpace (WithAbs (NormedField.toAbsoluteValue w.Completion)) := by
  have hiso : Isometry (WithAbs.equiv (NormedField.toAbsoluteValue w.Completion)) :=
    AddMonoidHomClass.isometry_iff_norm _ |>.2 (fun x => rfl)
  refine (completeSpace_iff_isComplete_range hiso.isUniformInducing).2 ?_
  rw [(WithAbs.equiv (NormedField.toAbsoluteValue w.Completion)).surjective.range_eq]
  exact isComplete_univ

theorem exists_ext [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
    [ContinuousSMul v.Completion w.Completion]
    (σ : L ≃ₐ[K] L) (hσ : ∀ x, w (σ x) = w x) :
    ∃ J : w.Completion →ₐ[v.Completion] w.Completion,
      (∀ a : L, J (a : w.Completion) = ((σ a : L) : w.Completion)) ∧ ∀ x, ‖J x‖ = ‖x‖ := by
  have h := AbsoluteValue.Completion.algebra_eq v w
  subst h
  let _ := AbsoluteValue.Completion.algebraOfLiesOver v w
  let W : Extensions L v := ⟨w, inferInstance⟩
  have := completeSpace_toAbs w
  obtain ⟨J, h1, h2, h3⟩ := exists_completion_lift v W (M := w.Completion)
    (NormedField.toAbsoluteValue w.Completion) (norm_algebraMap_ext v W)
    ((coeAlgHom (K := K) w).comp σ.toAlgHom)
    (fun a => by
      show ‖((σ a : L) : w.Completion)‖ = _
      rw [norm_coe_completion, hσ])
  exact ⟨{ J with commutes' := h3 }, h1, h2⟩

theorem norm_algebraMap' [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
    [ContinuousSMul v.Completion w.Completion] (c : v.Completion) :
    ‖algebraMap v.Completion w.Completion c‖ = ‖c‖ := by
  have h := AbsoluteValue.Completion.algebra_eq v w
  subst h
  let W : Extensions L v := ⟨w, inferInstance⟩
  exact norm_algebraMap_ext v W c

theorem ext_L {f g : w.Completion → w.Completion} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ a : L, f a = g a) : f = g :=
  UniformSpace.Completion.ext hf hg fun a => h (WithAbs.ofAbs a)

theorem coe_inj {a b : L} (h : (a : w.Completion) = (b : w.Completion)) : a = b :=
  congrArg WithAbs.ofAbs (UniformSpace.Completion.coe_injective (WithAbs w) h)

variable [Algebra v.Completion w.Completion] [IsScalarTower K v.Completion w.Completion]
  [ContinuousSMul v.Completion w.Completion]

theorem exists_equiv (σ : L ≃ₐ[K] L) (hσ : ∀ x, w (σ x) = w x) :
    ∃ τ : w.Completion ≃ₐ[v.Completion] w.Completion,
      (∀ a : L, τ (a : w.Completion) = ((σ a : L) : w.Completion)) ∧ ∀ x, ‖τ x‖ = ‖x‖ := by
  obtain ⟨J, hJ1, hJ2⟩ := exists_ext v w σ hσ
  obtain ⟨J', hJ1', hJ2'⟩ := exists_ext v w σ.symm (fun x => by
    have := hσ (σ.symm x)
    rw [AlgEquiv.apply_symm_apply] at this
    exact this.symm)
  have cJ : Continuous J := ((AddMonoidHomClass.isometry_iff_norm J).2 hJ2).continuous
  have cJ' : Continuous J' := ((AddMonoidHomClass.isometry_iff_norm J').2 hJ2').continuous
  have e1 : ∀ x, J (J' x) = x := fun x => by
    have := ext_L w (f := fun x => J (J' x)) (g := id) (cJ.comp cJ') continuous_id (fun a => by
      show J (J' (a : w.Completion)) = _
      rw [hJ1', hJ1]
      simp)
    exact congrFun this x
  have e2 : ∀ x, J' (J x) = x := fun x => by
    have := ext_L w (f := fun x => J' (J x)) (g := id) (cJ'.comp cJ) continuous_id (fun a => by
      show J' (J (a : w.Completion)) = _
      rw [hJ1, hJ1']
      simp)
    exact congrFun this x
  exact ⟨AlgEquiv.ofAlgHom J J' (AlgHom.ext e1) (AlgHom.ext e2), hJ1, hJ2⟩

theorem alg_ext {τ τ' : w.Completion ≃ₐ[v.Completion] w.Completion} (hτ : ∀ x, ‖τ x‖ = ‖x‖)
    (hτ' : ∀ x, ‖τ' x‖ = ‖x‖) (h : ∀ a : L, τ (a : w.Completion) = τ' (a : w.Completion)) :
    τ = τ' := by
  have c1 : Continuous τ := ((AddMonoidHomClass.isometry_iff_norm τ).2 hτ).continuous
  have c2 : Continuous τ' := ((AddMonoidHomClass.isometry_iff_norm τ').2 hτ').continuous
  exact AlgEquiv.ext fun x => congrFun (ext_L w c1 c2 h) x

theorem iso_of_mem {σ : L ≃ₐ[K] L} (h : σ ∈ decompGroupAbv (K := K) w) (x : L) : w (σ x) = w x := by
  change conjAbv σ w = w at h
  have := DFunLike.congr_fun h (σ x)
  rw [conjAbv_apply, AlgEquiv.symm_apply_apply] at this
  exact this.symm

/-- The extension of an element of the decomposition group to the completion. -/
def extEquiv (σ : decompGroupAbv (K := K) w) : w.Completion ≃ₐ[v.Completion] w.Completion :=
  Classical.choose (exists_equiv v w σ.1 (iso_of_mem w σ.2))

theorem extEquiv_apply (σ : decompGroupAbv (K := K) w) (a : L) :
    extEquiv v w σ (a : w.Completion) = ((σ.1 a : L) : w.Completion) :=
  (Classical.choose_spec (exists_equiv v w σ.1 (iso_of_mem w σ.2))).1 a

theorem extEquiv_norm (σ : decompGroupAbv (K := K) w) (x : w.Completion) :
    ‖extEquiv v w σ x‖ = ‖x‖ :=
  (Classical.choose_spec (exists_equiv v w σ.1 (iso_of_mem w σ.2))).2 x

/-- The homomorphism $G_w \to \mathrm{Gal}(L_w/K_v)$. -/
def extHom : decompGroupAbv (K := K) w →* (w.Completion ≃ₐ[v.Completion] w.Completion) where
  toFun := extEquiv v w
  map_one' := alg_ext v w (extEquiv_norm v w 1) (fun x => rfl) (fun a => by
    rw [extEquiv_apply]
    rfl)
  map_mul' σ τ := alg_ext v w (extEquiv_norm v w _)
    (fun x => by
      show ‖extEquiv v w σ (extEquiv v w τ x)‖ = _
      rw [extEquiv_norm, extEquiv_norm])
    (fun a => by
      rw [extEquiv_apply]
      show _ = extEquiv v w σ (extEquiv v w τ (a : w.Completion))
      rw [extEquiv_apply, extEquiv_apply]
      rfl)

theorem extHom_apply (σ : decompGroupAbv (K := K) w) (a : L) :
    extHom v w σ (a : w.Completion) = ((σ.1 a : L) : w.Completion) :=
  extEquiv_apply v w σ a

theorem extHom_injective : Function.Injective (extHom (K := K) v w) := by
  intro σ σ' h
  refine Subtype.ext (AlgEquiv.ext fun a => coe_inj w ?_)
  rw [← extHom_apply v w σ, ← extHom_apply v w σ', h]

theorem finiteDimensional [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    FiniteDimensional v.Completion w.Completion := by
  have h := AbsoluteValue.Completion.algebra_eq v w
  subst h
  let W : Extensions L v := ⟨w, inferInstance⟩
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  let _ := extAlgebra v W
  exact LinearEquiv.finiteDimensional
    (AlgEquiv.ofBijective (hMap v W α) (hMap_bijective v hα W)).toLinearEquiv

theorem norm_equiv [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (τ : w.Completion ≃ₐ[v.Completion] w.Completion) (x : w.Completion) : ‖τ x‖ = ‖x‖ := by
  have := finiteDimensional v w
  have h := absoluteValue_eq_of_complete (E := v.Completion) (F := w.Completion)
    (NormedField.toAbsoluteValue w.Completion)
    ((NormedField.toAbsoluteValue w.Completion).comp (f := (τ : w.Completion ≃+* w.Completion).toRingHom)
      τ.injective)
    (fun c => norm_algebraMap' v w c)
    (fun c => by
      show ‖τ (algebraMap v.Completion w.Completion c)‖ = _
      rw [AlgEquiv.commutes]
      exact norm_algebraMap' v w c)
  exact (DFunLike.congr_fun h x).symm

theorem extHom_surjective [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (extHom (K := K) v w) := by
  intro τ
  have hn := norm_equiv v w τ
  let σ : L ≃ₐ[K] L := (τ.restrictScalars K).restrictNormal L
  have hσ : ∀ a : L, ((σ a : L) : w.Completion) = τ (a : w.Completion) := fun a =>
    AlgEquiv.restrictNormal_commutes (τ.restrictScalars K) L a
  have hmem : σ ∈ decompGroupAbv (K := K) w := by
    change conjAbv σ w = w
    ext x
    show w (σ.symm x) = w x
    have h1 := hσ (σ.symm x)
    rw [AlgEquiv.apply_symm_apply] at h1
    rw [← norm_coe_completion w (σ.symm x), ← norm_coe_completion w x, ← hn, ← h1]
  refine ⟨⟨σ, hmem⟩, alg_ext v w (extEquiv_norm v w _) hn (fun a => ?_)⟩
  show extEquiv v w ⟨σ, hmem⟩ (a : w.Completion) = _
  rw [extEquiv_apply, hσ]

end

end Prop810

open Prop810 in
/-- **Proposition 8.10** (Milne, p. 139): $G_w \cong \mathrm{Gal}(L_w/K_v)$, via the extension of each
$\sigma \in G_w$ to the completion. -/
@[kb "milne2020ant" "v3.08, Prop. 8.10, p. 139"]
theorem prop_8_10 : Prop8_10 := by
  refine ⟨fun K L _ _ _ _ _ _ w => ?_⟩
  let _ := AbsoluteValue.Completion.algebraOfLiesOver (w.under K) w
  exact ⟨MulEquiv.ofBijective (extHom (w.under K) w)
    ⟨extHom_injective (w.under K) w, extHom_surjective (w.under K) w⟩,
    fun σ x => extHom_apply (w.under K) w σ x⟩

end

end NumberFieldKB.MilneANT
