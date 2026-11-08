import NumberFieldKB.Pontryagin.Annihilator
import NumberFieldKB.WeilBNT.AbstractFourier
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Fourier inversion and dual measures for compact and discrete groups (Weil VII.§2, p. 105)

Weil's Fourier transform is `NumberFieldKB.WeilBNT.AbstractFourier.fourierLCA α Φ`,
$\Phi^*(g^*)=\int_G\Phi(g)\langle g,g^*\rangle\,d\alpha(g)$, and "admissible" is `AbstractFourier.IsAdmissible`.

* `IsDualMeasure α β`: $\beta$ is the dual measure of $\alpha$ (Weil, p. 105): for every admissible $\Phi$,
  $\Phi(g)=\int_{G^*}\Phi^*(g^*)\langle -g,g^*\rangle\,d\beta(g^*)$.
* **`isDualMeasure_count_of_compact`** (Weil, p. 105: "if $G$ is compact, and $\alpha(G)=1$, the dual measure is the
  measure on the discrete group $G^*$ for which each point has measure $1$"): given the Peter–Weyl theorem.
* **`isDualMeasure_of_discrete`** (the dual statement: for $G$ discrete with counting measure, the dual measure is
  the normalized Haar measure of the compact group $G^*$): unconditional.

Two general facts are proved on the way: the integral for the counting measure is the sum
(`integral_count_eq_tsum`, any index type), and the interchange of an absolutely summable series of uniformly bounded
functions with a finite integral (`integral_tsum_mul`, any index type, by restricting to the countable support).
-/

open MeasureTheory Topology

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

open NumberFieldKB.WeilBNT.AbstractFourier

section General

/-- The integral for the counting measure of an integrable function is its sum (any index type). -/
lemma integral_count_eq_tsum {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {f : X → ℂ}
    (hf : Integrable f Measure.count) : ∫ x, f x ∂Measure.count = ∑' x, f x := by
  have hs : (Function.support f).Countable := by
    have := (integrable_count_iff.mp hf).of_norm.countable_support
    exact this
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Function.support f)
    (fun x hx => Function.notMem_support.mp hx)]
  rw [setIntegral_countable _ hs hf.integrableOn]
  rw [← tsum_subtype_eq_of_support_subset (s := Function.support f) subset_rfl]
  congr 1 with x
  simp [measureReal_def]

/-- Interchange of an absolutely summable series of uniformly bounded functions with the integral for a finite
measure (any index type). -/
lemma integral_tsum_mul {ι X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (a : ι → ℂ) (ha : Summable fun i => ‖a i‖) (f : ι → X → ℂ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : ∀ i x, ‖f i x‖ ≤ 1) :
    ∫ x, ∑' i, a i * f i x ∂μ = ∑' i, a i * ∫ x, f i x ∂μ := by
  set s := Function.support a
  have hs : s.Countable := ha.of_norm.countable_support
  have : Countable s := hs.to_subtype
  have hsupp : ∀ x, Function.support (fun i => a i * f i x) ⊆ s := fun x i hi h0 => hi (by simp [h0])
  have hsupp' : Function.support (fun i => a i * ∫ x, f i x ∂μ) ⊆ s := fun i hi h0 => hi (by simp [h0])
  simp_rw [← tsum_subtype_eq_of_support_subset (hsupp _), ← tsum_subtype_eq_of_support_subset hsupp']
  have hsum : ∀ x, Summable fun j : s => a j * f j x := by
    intro x
    refine Summable.of_norm_bounded (ha.subtype s) fun j => ?_
    rw [norm_mul]
    calc ‖a j‖ * ‖f j x‖ ≤ ‖a j‖ * 1 := by gcongr; exact hb _ _
      _ = ‖a j‖ := mul_one _
  have h := hasSum_integral_of_dominated_convergence (μ := μ) (F := fun (j : s) x => a j * f j x)
    (f := fun x => ∑' j : s, a j * f j x) (fun j _ => ‖a j‖)
    (fun j => (hf j).const_mul _) (fun j => Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      calc ‖a j‖ * ‖f j x‖ ≤ ‖a j‖ * 1 := by gcongr; exact hb _ _
        _ = ‖a j‖ := mul_one _)
    (Filter.Eventually.of_forall fun _ => ha.subtype s) (integrable_const _)
    (Filter.Eventually.of_forall fun x => (hsum x).hasSum)
  rw [← h.tsum_eq]
  congr 1 with j
  exact integral_const_mul _ _

end General

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- **Weil VII.§2, p. 105**: `β` is the **dual measure** of `α`: Fourier inversion
$\Phi(g)=\int\Phi^*(g^*)\langle-g,g^*\rangle\,d\beta(g^*)$ holds for every function admissible for $G$. -/
def IsDualMeasure (α : Measure G) [MeasurableSpace (PontryaginDual G)] (β : Measure (PontryaginDual G)) : Prop :=
  ∀ Φ : G → ℂ, IsAdmissible α β Φ → ∀ g : G,
    Φ g = ∫ χ, fourierLCA α Φ χ * ((χ g⁻¹ : Circle) : ℂ) ∂β

section CompactCase

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- **Weil VII.§2, p. 105, compact groups**: if $G$ is compact, its characters separate points and $\alpha(G)=1$,
the dual measure is the counting measure on the discrete group $G^*$. -/
theorem isDualMeasure_count_of_compact_of_separates (hS : CharactersSeparate G) (α : Measure G)
    [α.IsHaarMeasure] [IsProbabilityMeasure α] [MeasurableSpace (PontryaginDual G)]
    [MeasurableSingletonClass (PontryaginDual G)] :
    IsDualMeasure α (Measure.count : Measure (PontryaginDual G)) := by
  classical
  rintro Φ ⟨hΦc, -, hΦ⟩ g
  set a : PontryaginDual G → ℂ := fourierLCA α Φ
  have ha : Summable fun χ => ‖a χ‖ := integrable_count_iff.mp hΦ
  -- the right-hand side is a sum
  have hint : Integrable (fun χ : PontryaginDual G => a χ * ((χ g⁻¹ : Circle) : ℂ)) Measure.count := by
    rw [integrable_count_iff]; simp only [norm_mul, Circle.norm_coe, mul_one]; exact ha
  rw [integral_count_eq_tsum hint]
  -- `Ψ`, the sum of the Fourier series, is continuous and has the same Fourier coefficients as `Φ`
  set Ψ : G → ℂ := fun x => ∑' χ, a χ * ((χ x⁻¹ : Circle) : ℂ)
  have hΨc : Continuous Ψ := by
    refine continuous_tsum (u := fun χ => ‖a χ‖) (fun χ => ?_) ha
      (fun χ x => by rw [norm_mul, Circle.norm_coe, mul_one])
    exact continuous_const.mul (continuous_subtype_val.comp (χ.continuous.comp continuous_inv))
  have hcoef : ∀ ψ : PontryaginDual G, ∫ x, ((ψ x : Circle) : ℂ) * Ψ x ∂α = a ψ := by
    intro ψ
    have hswap := integral_tsum_mul α a ha
      (fun χ x => ((χ x⁻¹ : Circle) : ℂ) * ((ψ x : Circle) : ℂ))
      (fun χ => ((continuous_subtype_val.comp (χ.continuous.comp continuous_inv)).mul
        (continuous_subtype_val.comp ψ.continuous)).aestronglyMeasurable) (fun χ x => by simp)
    have heq : ∀ x, ((ψ x : Circle) : ℂ) * Ψ x =
        ∑' χ, a χ * (((χ x⁻¹ : Circle) : ℂ) * ((ψ x : Circle) : ℂ)) := by
      intro x
      simp only [Ψ]
      rw [← tsum_mul_left]
      congr 1 with χ
      ring
    simp_rw [heq]
    rw [hswap]
    have horth : ∀ χ : PontryaginDual G,
        ∫ x, ((χ x⁻¹ : Circle) : ℂ) * ((ψ x : Circle) : ℂ) ∂α = if χ = ψ then 1 else 0 := by
      intro χ
      have hfun : (fun x => ((χ x⁻¹ : Circle) : ℂ) * ((ψ x : Circle) : ℂ)) =
          fun x => (((χ⁻¹ * ψ) x : Circle) : ℂ) := by
        funext x; simp [map_inv]
      rw [hfun]
      split_ifs with h
      · subst h; simp
      · exact integral_char_eq_zero α (by
          intro h1; apply h; exact (inv_mul_eq_one.mp h1))
    simp_rw [horth]
    simp
  -- hence `Φ - Ψ` is orthogonal to every character, so it vanishes
  have hsep : ∀ x y : G, x ≠ y → ∃ χ ∈ (⊤ : Subgroup (PontryaginDual G)), χ x ≠ χ y := by
    intro x y hxy
    obtain ⟨χ, hχ⟩ := hS (x * y⁻¹) (by
      intro h; exact hxy (mul_inv_eq_one.mp h))
    refine ⟨χ, trivial, fun h => hχ ?_⟩
    rw [map_mul, map_inv, h, mul_inv_cancel]
  set F : G → ℂ := fun x => Φ x - Ψ x
  have hFc : Continuous F := hΦc.sub hΨc
  have hF : ∀ χ ∈ (⊤ : Subgroup (PontryaginDual G)), ∫ x, ((χ x : Circle) : ℂ) * F x ∂α = 0 := by
    intro χ _
    have i1 : Integrable (fun x => ((χ x : Circle) : ℂ) * Φ x) α :=
      integrable_of_continuous α ((continuous_subtype_val.comp χ.continuous).mul hΦc)
    have i2 : Integrable (fun x => ((χ x : Circle) : ℂ) * Ψ x) α :=
      integrable_of_continuous α ((continuous_subtype_val.comp χ.continuous).mul hΨc)
    simp only [F, mul_sub]
    rw [integral_sub i1 i2, hcoef]
    simp only [a, fourierLCA]
    rw [sub_eq_zero]
    congr 1 with x
    ring
  have h0 := integral_mul_eq_zero_of_separates α ⊤ hsep hFc hF (star ⟨F, hFc⟩)
  have hnorm : ∀ x, (star (⟨F, hFc⟩ : C(G, ℂ))) x * F x = ((‖F x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    simp only [ContinuousMap.star_apply, ContinuousMap.coe_mk]
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    rfl
  simp_rw [hnorm, integral_complex_ofReal] at h0
  have h1 : ∫ x, ‖F x‖ ^ 2 ∂α = 0 := by exact_mod_cast h0
  have hae : (fun x => ‖F x‖ ^ 2) =ᵐ[α] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      (integrable_of_continuous α (hFc.norm.pow 2))).mp h1
  have hall : (fun x => ‖F x‖ ^ 2) = 0 :=
    (hFc.norm.pow 2).ae_eq_iff_eq α continuous_const |>.mp hae
  have hg := congrFun hall g
  simp only [Pi.zero_apply, pow_eq_zero_iff (two_ne_zero), norm_eq_zero, F, sub_eq_zero] at hg
  exact hg

/-- **Weil VII.§2, p. 105, compact groups**: if $G$ is compact and $\alpha(G)=1$, the dual measure is the counting
measure on the discrete group $G^*$ (given the Peter–Weyl theorem, which supplies the completeness of the
characters; the unconditional form is `NumberFieldKB.Pontryagin.Unconditional.isDualMeasure_count_of_compact`). -/
theorem isDualMeasure_count_of_compact (hPW : PeterWeylTheorem.{u}) (α : Measure G) [α.IsHaarMeasure]
    [IsProbabilityMeasure α] [MeasurableSpace (PontryaginDual G)]
    [MeasurableSingletonClass (PontryaginDual G)] :
    IsDualMeasure α (Measure.count : Measure (PontryaginDual G)) :=
  isDualMeasure_count_of_compact_of_separates (charactersSeparate_of_compact hPW) α

end CompactCase

section DiscreteCase

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] [MeasurableSpace G]
  [BorelSpace G]

/-- **The dual statement of Weil VII.§2, p. 105**: for a discrete group with the counting measure, the dual measure
is the normalized Haar measure of the compact group $G^*$. Unconditional. -/
theorem isDualMeasure_of_discrete [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (β : Measure (PontryaginDual G)) [IsProbabilityMeasure β] [β.IsMulLeftInvariant] :
    IsDualMeasure (Measure.count : Measure G) β := by
  classical
  have : MeasurableSingletonClass G := ⟨fun _ => (isOpen_discrete _).measurableSet⟩
  rintro Φ ⟨-, hΦ, -⟩ g
  have ha : Summable fun h => ‖Φ h‖ := integrable_count_iff.mp hΦ
  have hfour : ∀ χ : PontryaginDual G, fourierLCA Measure.count Φ χ = ∑' h, Φ h * ((χ h : Circle) : ℂ) := by
    intro χ
    apply integral_count_eq_tsum
    rw [integrable_count_iff]; simp only [norm_mul, Circle.norm_coe, mul_one]; exact ha
  simp_rw [hfour]
  have heq : ∀ χ : PontryaginDual G, (∑' h, Φ h * ((χ h : Circle) : ℂ)) * ((χ g⁻¹ : Circle) : ℂ) =
      ∑' h, Φ h * ((dualEval G (h * g⁻¹) χ : Circle) : ℂ) := by
    intro χ
    rw [← tsum_mul_right]
    congr 1 with h
    simp [map_mul, mul_assoc]
  simp_rw [heq]
  rw [integral_tsum_mul β Φ ha (fun h χ => ((dualEval G (h * g⁻¹) χ : Circle) : ℂ))
    (fun h => (continuous_subtype_val.comp (dualEval G (h * g⁻¹)).continuous).aestronglyMeasurable)
    (fun h χ => by simp)]
  have horth : ∀ h : G, ∫ χ, ((dualEval G (h * g⁻¹) χ : Circle) : ℂ) ∂β = if h = g then 1 else 0 := by
    intro h
    split_ifs with hh
    · subst hh; simp
    · apply integral_char_eq_zero β
      intro h1
      apply hh
      have := (dualEval_injective_iff.mpr charactersSeparate_of_discrete) (h1.trans (map_one _).symm)
      exact mul_inv_eq_one.mp this
  simp_rw [horth]
  simp

end DiscreteCase

end NumberFieldKB.Pontryagin
