import NumberFieldKB.MilneANT.Ch7LocalFields
import NumberFieldKB.MilneANT.Ch7Artin
import NumberFieldKB.MilneANT.Ch7AbsoluteValues

namespace NumberFieldKB.MilneANT

open Filter Topology

/-- Completeness is invariant under equivalence of absolute values: the identity map between the two
topologies is a uniform isomorphism, since it is an additive homeomorphism. -/
theorem completeSpace_withAbs_of_isEquiv {K : Type*} [Field K] {v w : AbsoluteValue K ℝ}
    (h : v.IsEquiv w) (hc : CompleteSpace (WithAbs v)) : CompleteSpace (WithAbs w) := by
  have h1 : IsHomeomorph (WithAbs.congr v w (RingEquiv.refl K)) :=
    (AbsoluteValue.isEquiv_iff_isHomeomorph v w).1 h
  let ψ : WithAbs v ≃+* WithAbs w := WithAbs.congr v w (RingEquiv.refl K)
  have hψ : Continuous ψ := h1.continuous
  have hψ' : Continuous ψ.symm :=
    ((AbsoluteValue.isEquiv_iff_isHomeomorph w v).1 h.symm).continuous
  let e : WithAbs v ≃ᵤ WithAbs w :=
    { toEquiv := ψ.toEquiv
      uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous
        (f := ψ.toRingHom.toAddMonoidHom) hψ
      uniformContinuous_invFun := uniformContinuous_addMonoidHom_of_continuous
        (f := ψ.symm.toRingHom.toAddMonoidHom) hψ' }
  exact (completeSpace_congr e.isUniformEmbedding).1 hc

/-- A complete normed field in which the natural numbers have their usual norm contains a copy of
`ℝ` (the closure of the rational numbers) on which the norm is the absolute value. -/
theorem exists_real_embedding (F : Type*) [NormedField F] [CompleteSpace F]
    (hn : ∀ n : ℕ, ‖(n : F)‖ = n) : ∃ φ : ℝ →+* F, ∀ r, ‖φ r‖ = |r| := by
  have hq : ∀ q : ℚ, ‖(q : F)‖ = |(q : ℝ)| := by
    intro q
    have hz : ∀ z : ℤ, ‖(z : F)‖ = |(z : ℝ)| := by
      intro z
      rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩ <;> simp [hn]
    rw [Rat.cast_def, norm_div, hz, ← Int.cast_natCast, hz]
    rw [Rat.cast_def (K := ℝ) q, abs_div]; simp
  have : CharZero F := ⟨fun a b hab => by
    have := congrArg norm hab
    rw [hn, hn] at this
    exact_mod_cast this⟩
  have hiso : Isometry (Rat.castHom F) := by
    apply AddMonoidHomClass.isometry_of_norm
    intro q
    show ‖(q : F)‖ = ‖q‖
    rw [hq, ← Rat.norm_cast_real, Real.norm_eq_abs]
  have ue : IsUniformInducing (Rat.castHom ℝ) := Rat.isUniformEmbedding_coe_real.isUniformInducing
  have dr : DenseRange (Rat.castHom ℝ) := Rat.denseRange_cast
  have hf : UniformContinuous (Rat.castHom F) := hiso.uniformContinuous
  refine ⟨IsDenseInducing.extendRingHom ue dr hf, fun r => ?_⟩
  have hcont : Continuous (IsDenseInducing.extendRingHom ue dr hf) :=
    (uniformContinuous_uniformly_extend ue dr hf).continuous
  refine dr.induction_on r (isClosed_eq (by fun_prop) (by fun_prop)) (fun q => ?_)
  have : IsDenseInducing.extendRingHom ue dr hf (Rat.castHom ℝ q) = Rat.castHom F q :=
    IsDenseInducing.extend_eq (ue.isDenseInducing dr) hf.continuous q
  rw [this]
  simpa using hq q

/-- Gelfand–Mazur step: a complete normed field `F` in which the natural numbers have their usual norm
is isomorphic to `ℝ` or `ℂ`, by a field isomorphism preserving the norm. -/
theorem exists_normPreserving_equiv_real_or_complex (F : Type*) [NormedField F] [CompleteSpace F]
    (hn : ∀ n : ℕ, ‖(n : F)‖ = n) :
    (∃ e : F ≃+* ℝ, ∀ x, ‖x‖ = ‖e x‖) ∨ (∃ e : F ≃+* ℂ, ∀ x, ‖x‖ = ‖e x‖) := by
  obtain ⟨φ, hφ⟩ := exists_real_embedding F hn
  let _ : Algebra ℝ F := φ.toAlgebra
  let _ : NormedAlgebra ℝ F :=
    { (inferInstance : Algebra ℝ F) with
      norm_smul_le := fun r x => by
        rw [Algebra.smul_def, norm_mul]
        show ‖φ r‖ * ‖x‖ ≤ ‖r‖ * ‖x‖
        rw [hφ, Real.norm_eq_abs] }
  rcases NormedAlgebra.Real.nonempty_algEquiv_or F with h | h
  · left
    obtain ⟨e⟩ := h
    refine ⟨e.toRingEquiv, fun x => ?_⟩
    have h1 : ∀ r : ℝ, e.symm r = φ r := fun r => by
      have h := e.symm.commutes r
      rw [Algebra.algebraMap_self_apply] at h
      exact h
    calc ‖x‖ = ‖e.symm (e x)‖ := by rw [AlgEquiv.symm_apply_apply]
      _ = ‖e x‖ := by rw [h1, hφ, Real.norm_eq_abs]
  · right
    obtain ⟨e⟩ := h
    refine ⟨e.toRingEquiv, fun x => ?_⟩
    let T : ℂ →L[ℝ] F := LinearMap.toContinuousLinearMap e.symm.toLinearMap
    have hT : ∀ z, T z = e.symm z := fun z => rfl
    have hC : ∀ z : ℂ, ‖e.symm z‖ ≤ ‖T‖ * ‖z‖ := fun z => by
      rw [← hT]; exact T.le_opNorm z
    have hle : ∀ z : ℂ, ‖e.symm z‖ ≤ ‖z‖ := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      by_contra hlt
      push Not at hlt
      have hb : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hr : 1 < ‖e.symm z‖ / ‖z‖ := (one_lt_div hb).2 hlt
      obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt ‖T‖ hr
      have h2 : ‖e.symm z‖ ^ n ≤ ‖T‖ * ‖z‖ ^ n := by
        have := hC (z ^ n)
        rwa [map_pow, norm_pow, norm_pow] at this
      have h3 : (‖e.symm z‖ / ‖z‖) ^ n * ‖z‖ ^ n ≤ ‖T‖ * ‖z‖ ^ n := by
        rwa [← mul_pow, div_mul_cancel₀ _ hb.ne']
      have := le_of_mul_le_mul_right h3 (pow_pos hb n)
      linarith
    have hge : ∀ z : ℂ, ‖z‖ ≤ ‖e.symm z‖ := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      have hb : 0 < ‖z‖ := norm_pos_iff.2 hz
      have := hle z⁻¹
      rw [map_inv₀, norm_inv, norm_inv] at this
      have hpos : 0 < ‖e.symm z‖ := norm_pos_iff.2 (by simpa using hz)
      exact (inv_le_inv₀ hpos hb).1 this
    calc ‖x‖ = ‖e.symm (e x)‖ := by rw [AlgEquiv.symm_apply_apply]
      _ = ‖e x‖ := le_antisymm (hle _) (hge _)

/-- **Remark 7.49(a)** (Ostrowski; proof via Artin's lemma and the Gelfand-Mazur theorem): a field that is
complete for an archimedean absolute value is isomorphic to the real or the complex numbers, and the absolute
value is equivalent to the usual one. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
theorem remark_7_49a : Remark7_49a := by
  refine ⟨fun K _ v hna hcv => ?_⟩
  have hub : ¬ ∀ n : ℕ, v (n : K) ≤ 1 := fun h => hna (isNonarchimedean_of_natCast_le_one v h)
  have hchar : ringChar K = 0 := by
    by_contra h
    exact hna (cor_7_3 h v)
  haveI : CharP K 0 := ringChar.eq_iff.1 hchar
  haveI : CharZero K := CharP.charP_to_charZero K
  let u : AbsoluteValue ℚ ℝ := v.comp (f := algebraMap ℚ K) (algebraMap ℚ K).injective
  have hu : ¬ ∀ n : ℕ, u n ≤ 1 := by simpa [u] using hub
  have h1 : u.IsEquiv Rat.AbsoluteValue.real := Rat.AbsoluteValue.equiv_real_of_unbounded hu
  obtain ⟨c, hc0, hc⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 h1.symm
  have hv : ∀ n : ℕ, v (n : K) = (n : ℝ) ^ c := fun n => by
    have := congrFun hc (n : ℚ)
    simpa [u] using this.symm
  obtain ⟨w, hw, hwv⟩ := AbsoluteValue.exists_rpow_inv_isEquiv v hc0 hv
  have hwn : ∀ n : ℕ, w (n : K) = n := fun n => by
    rw [hw, hv, ← Real.rpow_mul (Nat.cast_nonneg _), mul_inv_cancel₀ hc0.ne', Real.rpow_one]
  have hcw : CompleteSpace (WithAbs w) := completeSpace_withAbs_of_isEquiv hwv.symm hcv
  have hn : ∀ n : ℕ, ‖(n : WithAbs w)‖ = n := fun n => by
    rw [WithAbs.norm_eq_apply_ofAbs]; exact hwn n
  rcases exists_normPreserving_equiv_real_or_complex (WithAbs w) hn with ⟨e, he⟩ | ⟨e, he⟩
  · left
    refine ⟨(WithAbs.equiv w).symm.trans e, ?_⟩
    have key : (NormedField.toAbsoluteValue ℝ).comp (f := ((WithAbs.equiv w).symm.trans e).toRingHom)
        ((WithAbs.equiv w).symm.trans e).injective = w :=
      AbsoluteValue.ext fun x => (he (WithAbs.toAbs w x)).symm
    rw [key]; exact hwv.symm
  · right
    refine ⟨(WithAbs.equiv w).symm.trans e, ?_⟩
    have key : (NormedField.toAbsoluteValue ℂ).comp (f := ((WithAbs.equiv w).symm.trans e).toRingHom)
        ((WithAbs.equiv w).symm.trans e).injective = w :=
      AbsoluteValue.ext fun x => (he (WithAbs.toAbs w x)).symm
    rw [key]; exact hwv.symm

end NumberFieldKB.MilneANT
