import NumberFieldKB.Pontryagin.ComplexUniqueness
import NumberFieldKB.Pontryagin.Correspondences
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# The Pontryagin duality theorem, given Bochner

$G$ is a locally compact commutative Hausdorff group, $\Gamma=G^*$, and $\delta:G\to\Gamma^*=G^{**}$ the canonical map,
a closed embedding (`isClosedEmbedding_dualEval`). Here $\delta$ is shown to be onto, which gives
**`pontryaginDuality`**: $G\cong G^{**}$ for every locally compact commutative Hausdorff group (given Bochner).

The argument uses Fourier inversion on $G$ and on $\Gamma$ (`NumberFieldKB.Pontryagin.FourierInversion`), and no
Plancherel theorem. Let $f=u\star\tilde u$ for a bump function $u\ge0$ and $F=\hat f$ on $\Gamma$: $F$ is continuous and
integrable for the dual Haar measure, and $F(\xi)=\int_G\overline{\xi(y)}f(y)\,dy$ is the transform of the finite
inner regular measure $M=\delta^{-1}_*(f\,dy)$ on $\Gamma^*$, carried by the closed subgroup $\Phi=\delta(G)$.

* `fhat_eq_zero_of_notMem_range`: $\hat F=0$ off $\Phi$. For $g$ in the inversion class of $\Gamma$ the
  measures $\hat g\,M$ and $\hat F\,\mu_g$ have the same transform, so they agree
  (`measureReal_eq_setIntegral_of_fourierStieltjes`); $M$ vanishes off $\Phi$, hence so does $\hat F\hat g$ (as
  $\mu_g=\hat g\lambda$ with $\lambda$ a Haar measure), and $\hat g>0$ at any given point for a suitable $g$.
* `dualEval_surjective`: if $\omega_0\notin\Phi$, the complex density $F\bar\omega_0$ on $\Gamma$ has transform
  $x\mapsto\hat F(\delta(x)^{-1}\omega_0)=0$ on $G$, so it vanishes, contradicting $F(1)=\int f>0$.

Compare Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Theorem 4.32, where the last step uses
Plancherel.
-/

open MeasureTheory Topology Filter ComplexConjugate

noncomputable section

namespace NumberFieldKB.Pontryagin

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G]

/-- **Step 1**: the transform of $F$ on $G^{**}$ vanishes off the image of $G$. -/
theorem fhat_eq_zero_of_notMem_range (hB : BochnerTheorem.{u}) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] [MeasurableSpace (PontryaginDual G)]
    [BorelSpace (PontryaginDual G)] [MeasurableSpace (PontryaginDual (PontryaginDual G))]
    [BorelSpace (PontryaginDual (PontryaginDual G))]
    (M : Measure (PontryaginDual (PontryaginDual G))) [IsFiniteMeasure M] [M.InnerRegular]
    (hM : M (Set.range (dualEval G))ᶜ = 0) {F : PontryaginDual G → ℂ} (hFc : Continuous F)
    (hFi : Integrable F (dualHaar μ hB)) (hFM : ∀ ξ, fourierStieltjes M ξ = F ξ)
    {ω : PontryaginDual (PontryaginDual G)} (hω : ω ∉ Set.range (dualEval G)) :
    fhat (dualHaar μ hB) F ω = 0 := by
  set lamG := dualHaar μ hB
  have : lamG.IsHaarMeasure := isHaarMeasure_dualHaar
  obtain ⟨g, hg, hgω⟩ := exists_isInvClass_pos (μ := lamG) ω
  have := hg.withDensity_finite M
  have := hg.withDensity_innerRegular M
  set ν := M.withDensity fun ξ => (fhatNN lamG g ξ : ENNReal)
  set ρ := bochnerMeasure hB hg
  set h := fhat lamG F
  have hhc : Continuous h := continuous_fhat lamG hFi
  have hFconj : ∀ η, conj (F η) = F η⁻¹ := fun η => by
    rw [← hFM, ← hFM, conj_fourierStieltjes]
  -- the transforms of `ĝ M` and `F̂ μ_g` agree
  have hFS : ∀ ξ, fourierStieltjes ν ξ = ∫ ω', ((ω' ξ : Circle) : ℂ) * h ω' ∂ρ := by
    intro ξ
    rw [fourierStieltjes_withDensity_fhat M hg ξ]
    have hc : Continuous fun η => F (ξ * η) := hFc.comp (continuous_const.mul continuous_id)
    have htr : ∀ ω', ((ω' ξ : Circle) : ℂ) * h ω' = fhat lamG (fun η => F (ξ * η)) ω' := fun ω' => by
      rw [fhat_translate]
    rw [integral_congr_ae (Eventually.of_forall htr), integral_fhat ρ hc (hFi.comp_mul_left ξ)]
    simp only [ρ, fourierStieltjes_bochnerMeasure, hFM]
    rw [← integral_mul_left_eq_self _ ξ⁻¹, ← integral_inv_eq_self]
    congr 1 with y
    rw [hFconj, show ξ * (ξ⁻¹ * y⁻¹) = y⁻¹ by group,
      show (ξ⁻¹ * y⁻¹)⁻¹ = ξ * y by rw [mul_inv_rev, inv_inv, inv_inv, mul_comm], ← hg.conj_eq hB, mul_comm]
  have hb : ∀ ω', ‖h ω'‖ ≤ ∫ η, ‖F η‖ ∂lamG := fun ω' => norm_fhat_le lamG F ω'
  have hhi : Integrable h ρ :=
    Integrable.of_bound hhc.aestronglyMeasurable _ (Eventually.of_forall hb)
  have huniq := fun (A : Set (PontryaginDual (PontryaginDual G))) (hA : MeasurableSet A) =>
    measureReal_eq_setIntegral_of_fourierStieltjes hB ν ρ hhc.measurable hb hhi hFS hA
  -- `F̂ = 0` almost everywhere on the complement `W` of the image, for `μ_g`
  set W := (Set.range (dualEval G))ᶜ
  have hWo : IsOpen W := (isClosedEmbedding_dualEval hB).isClosed_range.isOpen_compl
  have hae : h =ᵐ[ρ.restrict W] 0 := by
    refine Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero (hhi.restrict (s := W)) fun s hs _ => ?_
    rw [Measure.restrict_restrict hs, ← huniq _ (hs.inter hWo.measurableSet)]
    have : ν (s ∩ W) = 0 :=
      withDensity_absolutelyContinuous M _ (measure_mono_null Set.inter_subset_right hM)
    simp [Measure.real, this]
  -- transfer to the Haar measure `λ'` of `G**`, using `μ_g = ĝ λ'`
  set lam' := dualHaar lamG hB
  have : lam'.IsHaarMeasure := isHaarMeasure_dualHaar
  have hρ : ρ = lam'.withDensity fun ω' => ENNReal.ofReal (fhat lamG g ω').re := bochnerMeasure_eq_withDensity hg
  have hdm : Measurable fun ω' => ENNReal.ofReal (fhat lamG g ω').re :=
    ENNReal.measurable_ofReal.comp (Complex.continuous_re.comp hg.continuous_fhat).measurable
  rw [hρ, restrict_withDensity hWo.measurableSet, EventuallyEq, ae_withDensity_iff hdm] at hae
  set k : PontryaginDual (PontryaginDual G) → ℂ := fun ω' => ((fhat lamG g ω').re : ℂ) * h ω'
  have hk : k =ᵐ[lam'.restrict W] 0 := by
    filter_upwards [hae] with ω' hω'
    by_cases hz : ENNReal.ofReal (fhat lamG g ω').re = 0
    · have h0 : (fhat lamG g ω').re = 0 :=
        le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (hg.re_nonneg ω')
      simp [k, h0]
    · simp [k, hω' hz]
  have hkc : Continuous k := (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hg.continuous_fhat)).mul hhc
  have := Measure.eqOn_open_of_ae_eq hk hWo hkc.continuousOn continuousOn_const hω
  simp only [k, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero] at this
  exact this.resolve_left hgω.ne'

/-- **Step 2: the canonical map $G\to G^{**}$ is onto** (given Bochner). -/
theorem dualEval_surjective (hB : BochnerTheorem.{u}) : Function.Surjective (dualEval G) := by
  intro ω₀
  by_contra hω₀
  have hω₀' : ω₀ ∉ Set.range (dualEval G) := fun h => hω₀ h
  let _ : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  let _ : MeasurableSpace (PontryaginDual G) := borel _
  have : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let _ : MeasurableSpace (PontryaginDual (PontryaginDual G)) := borel _
  have : BorelSpace (PontryaginDual (PontryaginDual G)) := ⟨rfl⟩
  let μ : Measure G := Measure.haar
  -- `f = u ⋆ ũ` for a real bump function `u ≥ 0`; `f` is real and non-negative
  obtain ⟨b, hbc, hb0, hb1⟩ := exists_continuous_nonneg_pos (1 : G)
  set u : G → ℂ := fun y => ((b y : ℝ) : ℂ) with hu
  have huc : Continuous u := Complex.continuous_ofReal.comp b.continuous
  have hus : HasCompactSupport u :=
    HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hbc Complex.ofReal_zero
  have hf : IsInvClass μ (autocorr μ u) := isInvClass_autocorr huc hus
  set f := autocorr μ u with hfdef
  set fr : G → ℝ := fun y => ∫ z, b z * b (y⁻¹ * z) ∂μ with hfr
  have hf_eq : ∀ y, f y = (fr y : ℂ) := by
    intro y
    rw [hfr, ← integral_complex_ofReal, hfdef]
    unfold autocorr
    congr 1 with z
    simp [hu, Complex.conj_ofReal]
  have hfr_re : fr = fun y => (f y).re := funext fun y => by rw [hf_eq]; simp
  have hfr0 : ∀ y, 0 ≤ fr y := fun y => integral_nonneg fun z => mul_nonneg (hb0 z) (hb0 _)
  have hfrc : Continuous fr := by rw [hfr_re]; exact Complex.continuous_re.comp hf.continuous
  have hfrs : HasCompactSupport fr := by
    rw [hfr_re]; exact hf.hasCompactSupport.comp_left Complex.zero_re
  have hfri : Integrable fr μ := hfrc.integrable_of_hasCompactSupport hfrs
  have hfr1 : 0 < fr 1 := by
    have : fr 1 = ∫ z, b z * b z ∂μ := by simp [hfr]
    rw [this]
    exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (b.continuous.mul b.continuous) hbc.mul_left (fun y => mul_self_nonneg _) (mul_ne_zero hb1 hb1)
  have hfrpos : 0 < ∫ y, fr y ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfrc hfrs hfr0 hfr1.ne'
  -- `F = f̂` on `Γ = G*`
  set lamG := dualHaar μ hB
  have : lamG.IsHaarMeasure := isHaarMeasure_dualHaar
  set F := fhat μ f
  obtain ⟨hFi, -⟩ := inversion_isInvClass (hB := hB) hf
  have hFc : Continuous F := hf.continuous_fhat
  -- `M`, the image of `f dy` under `y ↦ δ(y)⁻¹`
  obtain ⟨C, hC⟩ := hfrc.bounded_above_of_compact_support hfrs
  have hdm : Measurable fun y => ((fr y).toNNReal : ENNReal) :=
    measurable_coe_nnreal_ennreal.comp hfrc.measurable.real_toNNReal
  set m₀ := μ.withDensity fun y => ((fr y).toNNReal : ENNReal)
  have hlt : ∫⁻ y, ((fr y).toNNReal : ENNReal) ∂μ ≠ ⊤ := hfri.lintegral_lt_top.ne
  have : IsFiniteMeasure m₀ := isFiniteMeasure_withDensity hlt
  have : m₀.InnerRegular := innerRegular_withDensity μ hdm ENNReal.ofReal_ne_top
    (fun y => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC y))) hlt
  set φ : G → PontryaginDual (PontryaginDual G) := fun y => (dualEval G y)⁻¹
  have hφc : Continuous φ := (dualEval G).continuous.inv
  set M := m₀.map φ
  have : M.InnerRegular := Measure.InnerRegular.map_of_continuous hφc
  have hM : M (Set.range (dualEval G))ᶜ = 0 := by
    rw [Measure.map_apply hφc.measurable
      (isClosedEmbedding_dualEval hB).isClosed_range.isOpen_compl.measurableSet]
    have : φ ⁻¹' (Set.range (dualEval G))ᶜ = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨y⁻¹, by simp [φ, map_inv]⟩
    rw [this, measure_empty]
  have hFM : ∀ ξ, fourierStieltjes M ξ = F ξ := by
    intro ξ
    unfold fourierStieltjes
    rw [integral_map hφc.aemeasurable (continuous_apply_dual ξ).aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hfrc.measurable.real_toNNReal]
    simp only [F, fhat]
    congr 1 with y
    rw [hf_eq, NNReal.smul_def, Real.coe_toNNReal _ (hfr0 y), Complex.real_smul]
    simp only [φ, dual_inv_apply, dualEval_apply, Circle.coe_inv_eq_conj]
  -- step 1: `F̂ = 0` off the image
  have hA : ∀ ω ∉ Set.range (dualEval G), fhat lamG F ω = 0 := fun ω hω =>
    fhat_eq_zero_of_notMem_range hB μ M hM hFc hFi hFM hω
  -- step 2: the density `F ω̄₀` has vanishing transform on `G`
  set k : PontryaginDual G → ℂ := fun ξ => F ξ * conj ((ω₀ ξ : Circle) : ℂ)
  have hkc : Continuous k :=
    hFc.mul (Complex.continuous_conj.comp (continuous_subtype_val.comp ω₀.continuous))
  have hkF : ∀ ξ, ‖k ξ‖ = ‖F ξ‖ := fun ξ => by simp [k]
  have hkb : ∀ ξ, ‖k ξ‖ ≤ ∫ x, ‖f x‖ ∂μ := fun ξ => (hkF ξ).le.trans (norm_fhat_le μ f ξ)
  have hki : Integrable k lamG :=
    hFi.norm.mono' hkc.aestronglyMeasurable (Eventually.of_forall fun ξ => (hkF ξ).le)
  have hkFS : ∀ x : G, fourierStieltjes (0 : Measure (PontryaginDual G)) x =
      ∫ ξ, ((ξ x : Circle) : ℂ) * k ξ ∂lamG := by
    intro x
    have hnot : (dualEval G x)⁻¹ * ω₀ ∉ Set.range (dualEval G) := by
      rintro ⟨y, hy⟩
      apply hω₀'
      exact ⟨x * y, by rw [map_mul, hy, mul_inv_cancel_left]⟩
    rw [show fourierStieltjes (0 : Measure (PontryaginDual G)) x = 0 by simp [fourierStieltjes],
      ← hA _ hnot]
    unfold fhat
    congr 1 with ξ
    simp only [k, dual_mul_apply, dual_inv_apply, dualEval_apply, Circle.coe_mul, Circle.coe_inv_eq_conj,
      map_mul, Complex.conj_conj]
    ring
  have hzero := fun (A : Set (PontryaginDual G)) (hA : MeasurableSet A) =>
    measureReal_eq_setIntegral_of_fourierStieltjes hB (H := G) 0 lamG hkc.measurable hkb hki hkFS hA
  have hk0 : k =ᵐ[lamG] 0 :=
    hki.ae_eq_zero_of_forall_setIntegral_eq_zero fun s hs _ => by rw [← hzero s hs]; simp
  have hk1 := congrFun ((hkc.ae_eq_iff_eq lamG continuous_const).mp hk0) 1
  have hF1 : F 1 = ((∫ y, fr y ∂μ : ℝ) : ℂ) := by
    simp only [F, fhat]
    rw [← integral_complex_ofReal]
    congr 1 with y
    simp [hf_eq]
  simp only [k, hF1, map_one, Circle.coe_one, map_one, mul_one, Pi.zero_apply] at hk1
  have := congrArg Complex.re hk1
  simp only [Complex.ofReal_re, Complex.zero_re] at this
  linarith

/-- **The Pontryagin duality theorem** (Weil II.§5, p. 38; Folland, Theorem 4.32), given Bochner's theorem: for
every locally compact commutative Hausdorff group $G$, the canonical map $G\to G^{**}$ is an isomorphism of
topological groups. -/
theorem pontryaginDuality (hB : BochnerTheorem.{u}) : PontryaginDualityStatement G :=
  pontryaginDualityStatement_of_denseRange hB (dualEval_surjective hB).denseRange

end NumberFieldKB.Pontryagin
