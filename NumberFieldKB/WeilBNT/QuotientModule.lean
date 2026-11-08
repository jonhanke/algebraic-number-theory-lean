import Mathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Topology.Algebra.Group.Quotient
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, I.§2, Lemma 2: the module is multiplicative on quotients

$G$ is a locally compact (Hausdorff) commutative group, written additively, $G'$ a closed subgroup, $G''=G/G'$.
The module $\operatorname{mod}_G(A)$ of an automorphism $A$ of $G$ (Weil I.§2 (2): $\alpha(A(X))=\operatorname{mod}_G(A)\,
\alpha(X)$ for a Haar measure $\alpha$) is Mathlib's `addEquivAddHaarChar A`
(`MeasureTheory.addEquivAddHaarChar_smul_preimage`: $c\,\mu(A^{-1}X)=\mu(X)$, the same convention).

* **`weil_I_2_lemma2`**: if $A$ maps $G'$ onto itself, inducing $A'$ on $G'$ and $A''$ on $G''$, then
  $\operatorname{mod}_G(A)=\operatorname{mod}_{G'}(A')\operatorname{mod}_{G''}(A'')$.

*Proof* (Weil's): the Haar measure on $G$ is built from those on $G'$ and $G''$ by
$\int_Gf\,d\alpha=\int_{G''}\big(\int_{G'}f(x+y)\,d\alpha'(y)\big)d\alpha''(\dot x)$ (Mathlib's
`TopologicalAddGroup.IsSES.inducedMeasure` for the extension `IsSES.ofClosedAddSubgroup`, with
`integral_inducedMeasure`), and one applies $A$ to both sides.
-/

open MeasureTheory Measure Topology
open scoped NNReal

noncomputable section

namespace NumberFieldKB.WeilBNT.QuotientModule

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : AddSubgroup G) [hH : IsClosed (H : Set G)]
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

instance : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- Change of variables for an additive Haar measure: `∫ F (e x) dμ = mod(e)⁻¹ ∫ F dμ`. -/
lemma integral_comp_addEquiv {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K] (e : K ≃ₜ+ K) (μ : Measure K)
    [μ.IsAddHaarMeasure] [μ.Regular] (F : K → ℝ) :
    ∫ x, F (e x) ∂μ = ((addEquivAddHaarChar e : ℝ≥0) : ℝ)⁻¹ * ∫ x, F x ∂μ := by
  have h := addEquivAddHaarChar_smul_integral_map (f := F) μ e
  have hm : ∫ x, F x ∂(μ.map e) = ∫ x, F (e x) ∂μ :=
    integral_map_equiv e.toHomeomorph.toMeasurableEquiv F
  rw [hm] at h
  have hp : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) ≠ 0 := by
    have := addEquivAddHaarChar_pos e
    exact_mod_cast this.ne'
  rw [← h, NNReal.smul_def, smul_eq_mul]
  field_simp

/-- A compactly supported continuous function with nonzero integral against a Haar measure. -/
lemma exists_integral_ne_zero {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [LocallyCompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
    [μ.IsAddHaarMeasure] :
    ∃ f : CompactlySupportedContinuousMap K ℝ, ∫ x, f x ∂μ ≠ 0 := by
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen (isCompact_singleton (x := (0 : K)))
      isOpen_univ (Set.subset_univ _)
  refine ⟨⟨f, hf2⟩, ?_⟩
  exact (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hf2
    (fun x => (hf4 x).1) (x := 0) (by simp [hf1 (Set.mem_singleton (0 : K))])).ne'

/-- **Weil, I.§2, Lemma 2.** Let $G'$ be a closed subgroup of $G$ and $A$ an automorphism of $G$ inducing an
automorphism $A'$ of $G'$ (`hA'`: $A'(y)=A(y)$ for $y\in G'$) and an automorphism $A''$ of $G/G'$ (`hA''`:
$A''(\dot x)=\dot{\overline{A(x)}}$). Then $\operatorname{mod}_G(A)=\operatorname{mod}_{G'}(A')\operatorname{mod}_{G/G'}(A'')$. -/
@[kb "weil1973bnt" "Ch. I, §2, Lemma 2"]
theorem weil_I_2_lemma2 (A : G ≃ₜ+ G) (A' : H ≃ₜ+ H) (A'' : (G ⧸ H) ≃ₜ+ (G ⧸ H))
    (hA' : ∀ y : H, ((A' y : H) : G) = A y)
    (hA'' : ∀ x : G, A'' (QuotientAddGroup.mk x) = QuotientAddGroup.mk (A x)) :
    addEquivAddHaarChar A = addEquivAddHaarChar A' * addEquivAddHaarChar A'' := by
  let S := TopologicalAddGroup.IsSES.ofClosedAddSubgroup H hH
  let μH : Measure H := addHaar
  let μQ : Measure (G ⧸ H) := addHaar
  let μ : Measure G := S.inducedMeasure μH μQ
  obtain ⟨f, hf⟩ := exists_integral_ne_zero μ
  let fA : CompactlySupportedContinuousMap G ℝ := f.comp A.toHomeomorph.toCocompactMap
  have h1 : ∫ x, fA x ∂μ = ((addEquivAddHaarChar A : ℝ≥0) : ℝ)⁻¹ * ∫ x, f x ∂μ :=
    integral_comp_addEquiv A μ f
  have h2 : ∫ x, fA x ∂μ = ((addEquivAddHaarChar A' : ℝ≥0) : ℝ)⁻¹ *
      (((addEquivAddHaarChar A'' : ℝ≥0) : ℝ)⁻¹ * ∫ x, f x ∂μ) := by
    rw [TopologicalAddGroup.IsSES.integral_inducedMeasure, TopologicalAddGroup.IsSES.integral_inducedMeasure,
      TopologicalAddGroup.IsSES.integrate_apply, TopologicalAddGroup.IsSES.integrate_apply]
    have key : ∀ c : G ⧸ H, S.pushforward μH fA c =
        ((addEquivAddHaarChar A' : ℝ≥0) : ℝ)⁻¹ * S.pushforward μH f (A'' c) := by
      intro c
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective c
      have e1 : S.pushforward μH fA (QuotientAddGroup.mk b) = ∫ y : H, f (A b + A' y) ∂μH := by
        refine (TopologicalAddGroup.IsSES.pushforward_apply_apply S μH fA b).trans ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [TopologicalAddGroup.IsSES.pullback_def, fA, hA' y, map_add]
        rfl
      have e2 : S.pushforward μH f (A'' (QuotientAddGroup.mk b)) = ∫ y : H, f (A b + y) ∂μH := by
        rw [hA'' b]
        exact (TopologicalAddGroup.IsSES.pushforward_apply_apply S μH f (A b)).trans
          (integral_congr_ae (Filter.Eventually.of_forall fun y => by
            simp [TopologicalAddGroup.IsSES.pullback_def]))
      rw [e1, e2]
      exact integral_comp_addEquiv A' μH (fun y : H => f (A b + (y : G)))
    simp_rw [key]
    rw [integral_const_mul]
    congr 1
    exact integral_comp_addEquiv A'' μQ (S.pushforward μH f)
  have hne : ((addEquivAddHaarChar A : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (addEquivAddHaarChar_pos A).ne'
  have hne' : ((addEquivAddHaarChar A' : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (addEquivAddHaarChar_pos A').ne'
  have hne'' : ((addEquivAddHaarChar A'' : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (addEquivAddHaarChar_pos A'').ne'
  have h3 := h1.symm.trans h2
  have h4 : ((addEquivAddHaarChar A : ℝ≥0) : ℝ) =
      ((addEquivAddHaarChar A' : ℝ≥0) : ℝ) * ((addEquivAddHaarChar A'' : ℝ≥0) : ℝ) := by
    have h5 : ((addEquivAddHaarChar A : ℝ≥0) : ℝ)⁻¹ =
        ((addEquivAddHaarChar A' : ℝ≥0) : ℝ)⁻¹ * ((addEquivAddHaarChar A'' : ℝ≥0) : ℝ)⁻¹ :=
      mul_right_cancel₀ hf (by rw [h3]; ring)
    calc ((addEquivAddHaarChar A : ℝ≥0) : ℝ) = (((addEquivAddHaarChar A : ℝ≥0) : ℝ)⁻¹)⁻¹ :=
          (inv_inv _).symm
      _ = _ := by rw [h5]; simp [mul_comm]
  exact_mod_cast h4

end NumberFieldKB.WeilBNT.QuotientModule
