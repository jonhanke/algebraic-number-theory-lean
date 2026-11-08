import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Fubini's theorem and regularity for continuous integrands on locally compact spaces

No countability assumption: on a locally compact Hausdorff space that is not second countable, the Borel σ-algebra of
a product is larger than the product σ-algebra, so the usual Fubini theorem does not apply to continuous integrands.
The results below replace it by approximation with compactly supported functions (Mathlib's
`MeasureTheory.integral_integral_swap_of_hasCompactSupport`) and inner regularity.

* `exists_isCompact_integral_compl_le`: an integrable function is concentrated on a compact set up to `ε`, for a
  measure inner regular on sets of finite measure.
* `continuous_integral_of_dominated`: $x\mapsto\int F(x,y)\,d\nu(y)$ is continuous when $F$ is continuous and
  $\|F(x,y)\|\le a(x)b(y)$ with $a$ continuous and $b$ integrable.
* `integral_integral_swap_of_dominated`: $\int\!\int F\,d\nu\,d\mu=\int\!\int F\,d\mu\,d\nu$ for $F$ continuous with
  $\|F(x,y)\|\le a(x)b(y)$, $a,b$ continuous, non-negative and integrable.
* `innerRegular_withDensity`: a finite measure with bounded density with respect to a measure inner regular on sets
  of finite measure is inner regular.
* `eq_withDensity_of_integral_eq`: a finite inner regular measure $\nu$ with $\int\psi\,d\nu=\int\psi p\,d\lambda$ for
  every $\psi\in C_c$ ($\lambda$ regular, $p\ge0$ continuous and bounded) is $p\,\lambda$.

References: G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., §2.3 (Radon products) and §4.2;
N. Bourbaki, *Intégration*, Ch. V.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace NumberFieldKB.Pontryagin

variable {X Y E : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Tightness with a compact set of finite measure (auxiliary form of `exists_isCompact_integral_compl_le`). -/
theorem exists_isCompact_integral_compl_le_aux (ν : Measure Y) [ν.InnerRegularCompactLTTop] {b : Y → ℝ}
    (hb : Integrable b ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set Y, IsCompact L ∧ ν L ≠ ⊤ ∧ ∫ y in Lᶜ, ‖b y‖ ∂ν ≤ ε := by
  obtain ⟨s, hs, hsm⟩ := (memLp_one_iff_integrable.2 hb).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ε := ENNReal.ofReal (ε / 2)) (by simp [hε])
  have hsi : Integrable s ν := memLp_one_iff_integrable.1 hsm
  obtain ⟨R, hR⟩ := s.exists_forall_norm_le
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set S : Set Y := Function.support s with hS
  have hSm : MeasurableSet S := s.measurableSet_support
  have hSf : ν S ≠ ⊤ := (s.measure_support_lt_top_of_integrable hsi).ne
  obtain ⟨K, hKS, hK, hSK⟩ := hSm.exists_isCompact_sdiff_lt hSf
    (ε := ENNReal.ofReal (ε / (2 * (R' + 1)))) (by simp [hε]; positivity)
  refine ⟨K, hK, ((measure_mono hKS).trans_lt hSf.lt_top).ne, ?_⟩
  rw [← integral_indicator hK.isClosed.measurableSet.compl]
  have hdiff : Integrable (fun g => b g - s g) ν := hb.sub hsi
  have hint : ∫ g, ‖b g - s g‖ ∂ν ≤ ε / 2 := by
    have hm : AEStronglyMeasurable (b - ⇑s) ν := hdiff.aestronglyMeasurable
    rw [integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable]
    rw [eLpNorm_one_eq_lintegral_enorm hm] at hs
    have : ∫⁻ g, ‖b g - s g‖ₑ ∂ν < ENNReal.ofReal (ε / 2) := hs
    exact (ENNReal.toReal_lt_of_lt_ofReal this).le
  have hKm : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hSDm : MeasurableSet (S \ K) := hSm.diff hK.isClosed.measurableSet
  have hSDfin : ν (S \ K) ≠ ⊤ := ((measure_mono Set.sdiff_subset).trans_lt hSf.lt_top).ne
  have hI : Integrable ((S \ K).indicator fun _ => R') ν :=
    (integrable_indicator_iff hSDm).2 (integrableOn_const hSDfin)
  calc ∫ g, Kᶜ.indicator (fun g => ‖b g‖) g ∂ν
      ≤ ∫ g, (‖b g - s g‖ + (S \ K).indicator (fun _ => R') g) ∂ν := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g => ?_) ?_
          (Filter.Eventually.of_forall fun g => ?_)
        · exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) g
        · exact hdiff.norm.add hI
        · beta_reduce
          by_cases hg : g ∈ K
          · rw [Set.indicator_of_notMem (by simpa using hg)]
            exact add_nonneg (norm_nonneg _) (Set.indicator_nonneg (fun _ _ => hR'0) g)
          · have hgc : g ∈ Kᶜ := hg
            rw [Set.indicator_of_mem hgc]
            by_cases hgS : g ∈ S
            · rw [Set.indicator_of_mem (show g ∈ S \ K from ⟨hgS, hg⟩)]
              have h1 : ‖b g‖ ≤ ‖b g - s g‖ + ‖s g‖ := by
                have := norm_add_le (b g - s g) (s g)
                simpa using this
              have h2 : ‖s g‖ ≤ R' := (hR g).trans (le_max_left _ _)
              linarith
            · have : s g = 0 := by simpa [hS] using hgS
              rw [Set.indicator_of_notMem (show g ∉ S \ K from fun h => hgS h.1)]
              simp [this]
    _ = ∫ g, ‖b g - s g‖ ∂ν + R' * ν.real (S \ K) := by
        rw [integral_add hdiff.norm hI]
        rw [integral_indicator_const _ hSDm]
        simp [mul_comm]
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        have h1 : ν.real (S \ K) ≤ ε / (2 * (R' + 1)) := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSK.le
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
        calc R' * ν.real (S \ K) ≤ R' * (ε / (2 * (R' + 1))) := by gcongr
          _ ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    _ = ε := by ring

/-- **Tightness**: an integrable function is concentrated, up to `ε`, on a compact set. -/
theorem exists_isCompact_integral_compl_le (ν : Measure Y) [ν.InnerRegularCompactLTTop] {b : Y → ℝ}
    (hb : Integrable b ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Set Y, IsCompact L ∧ ∫ y in Lᶜ, ‖b y‖ ∂ν ≤ ε := by
  obtain ⟨L, hL, -, h⟩ := exists_isCompact_integral_compl_le_aux ν hb hε
  exact ⟨L, hL, h⟩

/-- A continuous function dominated by an integrable function is a.e. strongly measurable, for a measure inner
regular on sets of finite measure (no second countability needed). -/
theorem aestronglyMeasurable_of_continuous_of_norm_le (ν : Measure Y) [ν.InnerRegularCompactLTTop]
    {f : Y → E} (hf : Continuous f) {b : Y → ℝ} (hb : Integrable b ν) (hfb : ∀ y, ‖f y‖ ≤ b y) :
    AEStronglyMeasurable f ν := by
  have hb0 : ∀ y, 0 ≤ b y := fun y => (norm_nonneg _).trans (hfb y)
  choose K hKc hKt using fun n : ℕ =>
    exists_isCompact_integral_compl_le ν hb (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  set T : Set Y := ⋃ n, K n with hT
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun n => (hKc n).isClosed.measurableSet
  have h1 : AEStronglyMeasurable f (ν.restrict T) := by
    rw [hT, aestronglyMeasurable_iUnion_iff]
    intro n
    exact hf.continuousOn.aestronglyMeasurable_of_isCompact (hKc n) (hKc n).isClosed.measurableSet
  have h2 : ∫ y in Tᶜ, ‖b y‖ ∂ν ≤ 0 := by
    refine le_of_forall_pos_le_add fun e he => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt he
    have : ∫ y in Tᶜ, ‖b y‖ ∂ν ≤ ∫ y in (K n)ᶜ, ‖b y‖ ∂ν := by
      refine setIntegral_mono_set hb.norm.integrableOn
        (Filter.Eventually.of_forall fun _ => norm_nonneg _) (Filter.Eventually.of_forall ?_)
      exact Set.compl_subset_compl.2 (Set.subset_iUnion _ n)
    linarith [hKt n]
  have h3 : (fun y => ‖b y‖) =ᵐ[ν.restrict Tᶜ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hb.norm.integrableOn).1 ?_
    exact le_antisymm h2 (integral_nonneg fun _ => norm_nonneg _)
  have h4 : AEStronglyMeasurable f (ν.restrict Tᶜ) := by
    refine aestronglyMeasurable_zero.congr ?_
    filter_upwards [h3] with y hy
    have hy' : ‖b y‖ = 0 := hy
    have : ‖f y‖ ≤ 0 := (hfb y).trans (by rw [← Real.norm_of_nonneg (hb0 y)]; exact hy'.le)
    exact (norm_le_zero_iff.1 this).symm
  rw [← Measure.restrict_add_restrict_compl (μ := ν) hTm]
  exact h1.add_measure h4

/-- **Continuity of a dominated parametric integral** (no countability assumption). -/
theorem continuous_integral_of_dominated (ν : Measure Y) [ν.InnerRegularCompactLTTop] {F : X → Y → E}
    (hF : Continuous (Function.uncurry F)) {a : X → ℝ} (ha : Continuous a) (ha0 : 0 ≤ a) {b : Y → ℝ}
    (hb0 : 0 ≤ b) (hb : Integrable b ν) (hFab : ∀ x y, ‖F x y‖ ≤ a x * b y) :
    Continuous fun x => ∫ y, F x y ∂ν := by
  have hFx : ∀ x, Continuous (F x) := fun x => hF.comp (continuous_const.prodMk continuous_id)
  have hFi : ∀ x, Integrable (F x) ν := fun x =>
    (hb.const_mul (a x)).mono'
      (aestronglyMeasurable_of_continuous_of_norm_le ν (hFx x) (hb.const_mul (a x)) fun y => hFab x y)
      (Filter.Eventually.of_forall (hFab x))
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hUc.exists_bound_of_continuousOn ha.continuousOn
  have hM0 : 0 ≤ M :=
    (ha0 x₀).trans ((Real.le_norm_self _).trans (hM x₀ (mem_of_mem_nhds hU)))
  obtain ⟨L, hLc, hLf, hLt⟩ :=
    exists_isCompact_integral_compl_le_aux ν hb (ε := ε / (8 * (M + 1))) (by positivity)
  have hδ : 0 < ε / (4 * (ν.real L + 1)) := by
    have : 0 ≤ ν.real L := ENNReal.toReal_nonneg
    positivity
  have hcont : Continuous (ContinuousMap.curry (⟨Function.uncurry F, hF⟩ : C(X × Y, E))) :=
    map_continuous _
  have hT := hcont.tendsto x₀
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at hT
  have h2 := Metric.tendstoUniformlyOn_iff.1 (hT L hLc) _ hδ
  filter_upwards [h2, hU] with x hx hxU
  have hLm : MeasurableSet L := hLc.isClosed.measurableSet
  have hLi : Integrable (L.indicator fun _ => ε / (4 * (ν.real L + 1))) ν :=
    (integrable_indicator_iff hLm).2 (integrableOn_const hLf)
  have hI : Integrable (Lᶜ.indicator fun y => ‖b y‖) ν := hb.norm.indicator hLm.compl
  have hax : a x ≤ M := (Real.le_norm_self _).trans (hM x hxU)
  have hax₀ : a x₀ ≤ M := (Real.le_norm_self _).trans (hM x₀ (mem_of_mem_nhds hU))
  rw [dist_eq_norm, ← integral_sub (hFi x) (hFi x₀)]
  refine lt_of_le_of_lt (norm_integral_le_integral_norm _) (lt_of_le_of_lt ?_ (half_lt_self hε))
  have hint := ((hFi x).sub (hFi x₀)).norm
  calc ∫ y, ‖F x y - F x₀ y‖ ∂ν
      ≤ ∫ y, (L.indicator (fun _ => ε / (4 * (ν.real L + 1))) y
          + 2 * M * Lᶜ.indicator (fun y => ‖b y‖) y) ∂ν := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hLi.add (hI.const_mul _)) (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce
        have hn : 0 ≤ Lᶜ.indicator (fun y => ‖b y‖) y := Set.indicator_nonneg (fun _ _ => norm_nonneg _) y
        have hn' : 0 ≤ L.indicator (fun _ => ε / (4 * (ν.real L + 1))) y :=
          Set.indicator_nonneg (fun _ _ => hδ.le) y
        by_cases hy : y ∈ L
        · rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (by simpa using hy)]
          have := hx y hy
          rw [dist_eq_norm, norm_sub_rev] at this
          have h' : ‖F x y - F x₀ y‖ ≤ ε / (4 * (ν.real L + 1)) := this.le
          linarith
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_mem (show y ∈ Lᶜ from hy), Real.norm_of_nonneg (hb0 y)]
          have h1 : ‖F x y - F x₀ y‖ ≤ ‖F x y‖ + ‖F x₀ y‖ := norm_sub_le _ _
          have h2 := hFab x y
          have h3 := hFab x₀ y
          have h4 : a x * b y ≤ M * b y := mul_le_mul_of_nonneg_right hax (hb0 y)
          have h5 : a x₀ * b y ≤ M * b y := mul_le_mul_of_nonneg_right hax₀ (hb0 y)
          linarith
    _ = ε / (4 * (ν.real L + 1)) * ν.real L + 2 * M * ∫ y in Lᶜ, ‖b y‖ ∂ν := by
        rw [integral_add hLi (hI.const_mul _), integral_const_mul, integral_indicator_const _ hLm,
          integral_indicator hLm.compl]
        simp [mul_comm]
    _ ≤ ε / 4 + 2 * M * (ε / (8 * (M + 1))) := by
        gcongr
        · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have : 0 ≤ ν.real L := ENNReal.toReal_nonneg
          nlinarith
    _ ≤ ε / 2 := by
        have : 2 * M * (ε / (8 * (M + 1))) ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        linarith

/-- A compactly supported continuous bump function with values in `[0,1]`, equal to `1` on a given compact set. -/
theorem exists_bump {Z : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z] {K : Set Z}
    (hK : IsCompact K) :
    ∃ χ : Z → ℝ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ ∀ z ∈ K, χ z = 1 := by
  obtain ⟨f, hf1, hf2, -, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ
    (Set.subset_univ K)
  exact ⟨f, f.continuous, hf2, fun z => ⟨(hf3 z).1, (hf3 z).2⟩, fun z hz => by simpa using hf1 hz⟩

/-- The partial integral of a dominated continuous integrand is integrable. -/
theorem integrable_integral_of_dominated (μ : Measure X) [μ.InnerRegularCompactLTTop] (ν : Measure Y)
    [ν.InnerRegularCompactLTTop] {F : X → Y → E} (hF : Continuous (Function.uncurry F)) {a : X → ℝ}
    (ha : Continuous a) (ha0 : 0 ≤ a) (hai : Integrable a μ) {b : Y → ℝ} (hb0 : 0 ≤ b)
    (hbi : Integrable b ν) (hFab : ∀ x y, ‖F x y‖ ≤ a x * b y) :
    Integrable (fun x => ∫ y, F x y ∂ν) μ := by
  have hc := continuous_integral_of_dominated ν hF ha ha0 hb0 hbi hFab
  have hbd : ∀ x, ‖∫ y, F x y ∂ν‖ ≤ a x * ∫ y, b y ∂ν := fun x => by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le (hbi.const_mul _) (Filter.Eventually.of_forall (hFab x))
  exact (hai.mul_const _).mono'
    (aestronglyMeasurable_of_continuous_of_norm_le μ hc (hai.mul_const _) hbd)
    (Filter.Eventually.of_forall hbd)

/-- Replacing `F` by its cutoff `χ ⊗ ω • F` changes the iterated integral by at most the tail integrals. -/
theorem integral_integral_sub_cutoff_le (μ : Measure X) [μ.InnerRegularCompactLTTop] (ν : Measure Y)
    [ν.InnerRegularCompactLTTop] {F : X → Y → E} (hF : Continuous (Function.uncurry F)) {a : X → ℝ}
    (ha : Continuous a) (ha0 : 0 ≤ a) (hai : Integrable a μ) {b : Y → ℝ} (hb0 : 0 ≤ b)
    (hbi : Integrable b ν) (hFab : ∀ x y, ‖F x y‖ ≤ a x * b y) {K : Set X} {L : Set Y}
    (hK : IsCompact K) (hL : IsCompact L) {χ : X → ℝ} (hχ : Continuous χ) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχK : ∀ x ∈ K, χ x = 1) {ω : Y → ℝ} (hω : Continuous ω) (hω01 : ∀ y, 0 ≤ ω y ∧ ω y ≤ 1)
    (hωL : ∀ y ∈ L, ω y = 1) :
    ‖∫ x, ∫ y, F x y ∂ν ∂μ - ∫ x, ∫ y, (χ x * ω y) • F x y ∂ν ∂μ‖ ≤
      (∫ x in Kᶜ, a x ∂μ) * ∫ y, b y ∂ν + (∫ x, a x ∂μ) * ∫ y in Lᶜ, b y ∂ν := by
  have hΦ : Continuous (Function.uncurry fun x y => (χ x * ω y) • F x y) :=
    ((hχ.comp continuous_fst).mul (hω.comp continuous_snd)).smul hF
  have hΦab : ∀ x y, ‖(χ x * ω y) • F x y‖ ≤ a x * b y := fun x y => by
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (hχ01 x).1 (hω01 y).1)]
    calc χ x * ω y * ‖F x y‖ ≤ 1 * (a x * b y) := by
          apply mul_le_mul _ (hFab x y) (norm_nonneg _) zero_le_one
          nlinarith [(hχ01 x).1, (hχ01 x).2, (hω01 y).1, (hω01 y).2]
      _ = a x * b y := one_mul _
  have hKm : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hLm : MeasurableSet Lᶜ := hL.isClosed.measurableSet.compl
  have hFx : ∀ x, Integrable (F x) ν := fun x =>
    (hbi.const_mul (a x)).mono'
      (aestronglyMeasurable_of_continuous_of_norm_le ν (hF.comp (continuous_const.prodMk continuous_id))
        (hbi.const_mul (a x)) fun y => hFab x y)
      (Filter.Eventually.of_forall (hFab x))
  have hΦx : ∀ x, Integrable (fun y => (χ x * ω y) • F x y) ν := fun x =>
    (hbi.const_mul (a x)).mono'
      (aestronglyMeasurable_of_continuous_of_norm_le ν (hΦ.comp (continuous_const.prodMk continuous_id))
        (hbi.const_mul (a x)) fun y => hΦab x y)
      (Filter.Eventually.of_forall (hΦab x))
  have IG := integrable_integral_of_dominated μ ν hF ha ha0 hai hb0 hbi hFab
  have IΦ := integrable_integral_of_dominated μ ν hΦ ha ha0 hai hb0 hbi hΦab
  have hg : Integrable (fun x => Kᶜ.indicator a x * ∫ y, b y ∂ν + a x * ∫ y in Lᶜ, b y ∂ν) μ :=
    ((hai.indicator hKm).mul_const _).add (hai.mul_const _)
  have hpt : ∀ x, ‖∫ y, F x y ∂ν - ∫ y, (χ x * ω y) • F x y ∂ν‖ ≤
      Kᶜ.indicator a x * ∫ y, b y ∂ν + a x * ∫ y in Lᶜ, b y ∂ν := by
    intro x
    have hI : Integrable (Lᶜ.indicator b) ν := hbi.indicator hLm
    rw [← integral_sub (hFx x) (hΦx x)]
    have hgi : Integrable (fun y => Kᶜ.indicator a x * b y + a x * Lᶜ.indicator b y) ν :=
      (hbi.const_mul (Kᶜ.indicator a x)).add (hI.const_mul (a x))
    have := norm_integral_le_of_norm_le hgi
      (Filter.Eventually.of_forall fun y => ?_) (f := fun y => F x y - (χ x * ω y) • F x y)
    · rw [integral_add (hbi.const_mul _) (hI.const_mul _), integral_const_mul, integral_const_mul,
        integral_indicator hLm] at this
      exact this
    · beta_reduce
      have e : F x y - (χ x * ω y) • F x y = (1 - χ x * ω y) • F x y := by rw [sub_smul, one_smul]
      have h0 : 0 ≤ 1 - χ x * ω y := by nlinarith [(hχ01 x).1, (hχ01 x).2, (hω01 y).1, (hω01 y).2]
      have h1 : 1 - χ x * ω y ≤ 1 := by nlinarith [(hχ01 x).1, (hω01 y).1]
      have hn : ‖F x y - (χ x * ω y) • F x y‖ ≤ (1 - χ x * ω y) * (a x * b y) := by
        rw [e, norm_smul, Real.norm_of_nonneg h0]
        exact mul_le_mul_of_nonneg_left (hFab x y) h0
      have hab : 0 ≤ a x * b y := mul_nonneg (ha0 x) (hb0 y)
      have n1 : 0 ≤ Kᶜ.indicator a x * b y := mul_nonneg (Set.indicator_nonneg (fun _ _ => ha0 _) x) (hb0 y)
      have n2 : 0 ≤ a x * Lᶜ.indicator b y := mul_nonneg (ha0 x) (Set.indicator_nonneg (fun _ _ => hb0 _) y)
      by_cases hx : x ∈ K
      · by_cases hy : y ∈ L
        · have h0' : 1 - χ x * ω y = 0 := by rw [hχK x hx, hωL y hy]; ring
          rw [h0', zero_mul] at hn
          rw [Set.indicator_of_notMem (by simpa using hx)] at n1 ⊢
          linarith
        · rw [Set.indicator_of_mem (show y ∈ Lᶜ from hy)]
          rw [Set.indicator_of_notMem (by simpa using hx)] at n1 ⊢
          have : (1 - χ x * ω y) * (a x * b y) ≤ a x * b y := by nlinarith
          simp only [zero_mul, zero_add]
          linarith
      · rw [Set.indicator_of_mem (show x ∈ Kᶜ from hx)] at n1 ⊢
        have : (1 - χ x * ω y) * (a x * b y) ≤ a x * b y := by nlinarith
        linarith
  have := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hpt)
  rw [← integral_sub IG IΦ]
  refine this.trans (le_of_eq ?_)
  rw [integral_add ((hai.indicator hKm).mul_const _) (hai.mul_const _), integral_mul_const,
    integral_mul_const, integral_indicator hKm]

/-- **Fubini's theorem for a continuous integrand dominated by a product of integrable functions** (no countability
or σ-finiteness assumption). -/
theorem integral_integral_swap_of_dominated (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    [μ.InnerRegularCompactLTTop] (ν : Measure Y) [IsFiniteMeasureOnCompacts ν] [ν.InnerRegularCompactLTTop]
    {F : X → Y → E} (hF : Continuous (Function.uncurry F)) {a : X → ℝ} (ha : Continuous a) (ha0 : 0 ≤ a)
    (hai : Integrable a μ) {b : Y → ℝ} (hb : Continuous b) (hb0 : 0 ≤ b) (hbi : Integrable b ν)
    (hFab : ∀ x y, ‖F x y‖ ≤ a x * b y) :
    ∫ x, ∫ y, F x y ∂ν ∂μ = ∫ y, ∫ x, F x y ∂μ ∂ν := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  set A : ℝ := ∫ x, a x ∂μ with hA
  set B : ℝ := ∫ y, b y ∂ν with hB
  have hA0 : 0 ≤ A := integral_nonneg ha0
  have hB0 : 0 ≤ B := integral_nonneg hb0
  have hε' : 0 < ε / (4 * (A + B + 1)) := by positivity
  set e : ℝ := ε / (4 * (A + B + 1)) with he
  obtain ⟨K, hKc, hKt⟩ := exists_isCompact_integral_compl_le μ hai hε'
  obtain ⟨L, hLc, hLt⟩ := exists_isCompact_integral_compl_le ν hbi hε'
  have ea : ∀ x, ‖a x‖ = a x := fun x => Real.norm_of_nonneg (ha0 x)
  have eb : ∀ y, ‖b y‖ = b y := fun y => Real.norm_of_nonneg (hb0 y)
  simp only [ea] at hKt
  simp only [eb] at hLt
  obtain ⟨χ, hχ, hχc, hχ01, hχK⟩ := exists_bump hKc
  obtain ⟨ω, hω, hωc, hω01, hωL⟩ := exists_bump hLc
  have h1 := integral_integral_sub_cutoff_le μ ν hF ha ha0 hai hb0 hbi hFab hKc hLc hχ hχ01 hχK hω hω01 hωL
  -- the swapped version
  have hF' : Continuous (Function.uncurry fun y x => F x y) := hF.comp continuous_swap
  have h2 := integral_integral_sub_cutoff_le ν μ hF' hb hb0 hbi ha0 hai (fun y x => by
    rw [mul_comm]; exact hFab x y) hLc hKc hω hω01 hωL hχ hχ01 hχK
  have hΦ : Continuous (Function.uncurry fun x y => (χ x * ω y) • F x y) :=
    ((hχ.comp continuous_fst).mul (hω.comp continuous_snd)).smul hF
  have hcs : HasCompactSupport (Function.uncurry fun x y => (χ x * ω y) • F x y) := by
    refine HasCompactSupport.intro (hχc.isCompact.prod hωc.isCompact) fun p hp => ?_
    simp only [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hp]
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hp]
  have hsw := integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := ν) hΦ hcs
  have e2 : ∀ y x, (ω y * χ x) • F x y = (χ x * ω y) • F x y := fun y x => by rw [mul_comm]
  simp only [e2] at h2
  rw [dist_eq_norm]
  have hlt : (∫ x in Kᶜ, a x ∂μ) * B + A * (∫ y in Lᶜ, b y ∂ν) ≤ ε / 4 := by
    have hKt0 : 0 ≤ ∫ x in Kᶜ, a x ∂μ := setIntegral_nonneg hKc.isClosed.measurableSet.compl fun x _ => ha0 x
    have hLt0 : 0 ≤ ∫ y in Lᶜ, b y ∂ν := setIntegral_nonneg hLc.isClosed.measurableSet.compl fun x _ => hb0 x
    calc _ ≤ e * B + A * e := by gcongr
      _ ≤ e * (A + B + 1) := by nlinarith
      _ = ε / 4 := by rw [he]; field_simp
  have n1 := norm_sub_le_norm_sub_add_norm_sub
    (∫ x, ∫ y, F x y ∂ν ∂μ) (∫ x, ∫ y, (χ x * ω y) • F x y ∂ν ∂μ) (∫ y, ∫ x, F x y ∂μ ∂ν)
  rw [hsw] at n1 h1
  have h2' : ‖∫ y, ∫ x, (χ x * ω y) • F x y ∂μ ∂ν - ∫ y, ∫ x, F x y ∂μ ∂ν‖ ≤
      (∫ y in Lᶜ, b y ∂ν) * A + B * ∫ x in Kᶜ, a x ∂μ := by
    rw [norm_sub_rev]; exact h2
  have hq : (∫ y in Lᶜ, b y ∂ν) * A + B * (∫ x in Kᶜ, a x ∂μ) =
      (∫ x in Kᶜ, a x ∂μ) * B + A * (∫ y in Lᶜ, b y ∂ν) := by ring
  linarith

/-- A measure with bounded density and finite total mass, with respect to a measure inner regular on sets of
finite measure, is inner regular. -/
theorem innerRegular_withDensity (ν : Measure Y) [ν.InnerRegularCompactLTTop] {p : Y → ENNReal}
    (hp : Measurable p) {C : ENNReal} (hC : C ≠ ⊤) (hpC : ∀ y, p y ≤ C) (hfin : ∫⁻ y, p y ∂ν ≠ ⊤) :
    (ν.withDensity p).InnerRegular := by
  refine ⟨fun A hA r hr => ?_⟩
  set ρ := ν.withDensity p with hρdef
  have hρ : ∀ S, MeasurableSet S → ρ S = ∫⁻ y in S, p y ∂ν := fun S hS => withDensity_apply _ hS
  set A' : ℕ → Set Y := fun n => A ∩ {y | ((n : ENNReal) + 1)⁻¹ ≤ p y} with hA'
  have hA'm : ∀ n, MeasurableSet (A' n) := fun n => hA.inter (measurableSet_le measurable_const hp)
  have hmono : Monotone A' := fun n m hnm y hy => by
    refine ⟨hy.1, le_trans ?_ (show ((n : ENNReal) + 1)⁻¹ ≤ p y from hy.2)⟩
    refine ENNReal.inv_le_inv.2 ?_
    gcongr
  have hzero : ρ (A ∩ {y | p y = 0}) = 0 := by
    rw [hρ _ (hA.inter (measurableSet_eq_fun hp measurable_const))]
    rw [setLIntegral_congr_fun (hA.inter (measurableSet_eq_fun hp measurable_const))
      (g := fun _ => 0) (fun y hy => hy.2)]
    simp
  have hcover : A ⊆ (⋃ n, A' n) ∪ (A ∩ {y | p y = 0}) := by
    intro y hy
    by_cases h0 : p y = 0
    · exact Or.inr ⟨hy, h0⟩
    · left
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h0
      refine Set.mem_iUnion.2 ⟨n, hy, le_trans ?_ hn.le⟩
      exact ENNReal.inv_le_inv.2 le_self_add
  have hρA : ρ A ≤ ⨆ n, ρ (A' n) := by
    calc ρ A ≤ ρ ((⋃ n, A' n) ∪ (A ∩ {y | p y = 0})) := measure_mono hcover
      _ ≤ ρ (⋃ n, A' n) + ρ (A ∩ {y | p y = 0}) := measure_union_le _ _
      _ = ⨆ n, ρ (A' n) := by rw [hzero, add_zero, hmono.measure_iUnion]
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 (hr.trans_le hρA)
  have hνfin : ν (A' n) ≠ ⊤ := by
    have h1 := mul_meas_ge_le_lintegral hp (((n : ENNReal) + 1)⁻¹) (μ := ν)
    have h2 : ν (A' n) ≤ ν {y | ((n : ENNReal) + 1)⁻¹ ≤ p y} := measure_mono Set.inter_subset_right
    refine ne_top_of_le_ne_top ?_ h2
    intro htop
    rw [htop] at h1
    simp at h1
    exact hfin h1
  have hρfin : ρ (A' n) ≠ ⊤ := by
    rw [hρ _ (hA'm n)]
    exact ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)
  set d := ρ (A' n) - r with hd
  have hd0 : d ≠ 0 := (tsub_pos_of_lt hn).ne'
  obtain ⟨e, he0, hCe⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hd0
  obtain ⟨K, hKA, hKc, hK⟩ := (hA'm n).exists_isCompact_lt_add hνfin (ε := e) (by exact_mod_cast he0.ne')
  refine ⟨K, hKA.trans Set.inter_subset_left, hKc, ?_⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hνK : ν K ≠ ⊤ := ne_top_of_le_ne_top hνfin (measure_mono hKA)
  have hdiff : ν (A' n \ K) ≤ e := by
    rw [measure_diff hKA hKm.nullMeasurableSet hνK]
    exact tsub_le_iff_left.2 hK.le
  have hsplit : ρ K + ρ (A' n \ K) = ρ (A' n) := by
    rw [measure_add_diff hKm.nullMeasurableSet, Set.union_eq_self_of_subset_left hKA]
  have hdm : MeasurableSet (A' n \ K) := (hA'm n).diff hKm
  have hρd : ρ (A' n \ K) < d := by
    rw [hρ _ hdm]
    calc ∫⁻ y in A' n \ K, p y ∂ν ≤ ∫⁻ y in A' n \ K, C ∂ν := lintegral_mono fun y => hpC y
      _ = C * ν (A' n \ K) := by rw [setLIntegral_const, mul_comm]
      _ ≤ C * e := by gcongr
      _ < d := by rw [mul_comm]; exact hCe
  by_contra hle
  push_neg at hle
  have : ρ (A' n) < ρ (A' n) := by
    calc ρ (A' n) = ρ K + ρ (A' n \ K) := hsplit.symm
      _ ≤ r + ρ (A' n \ K) := by gcongr
      _ < r + d := ENNReal.add_lt_add_left (ne_top_of_lt hn) hρd
      _ = ρ (A' n) := by rw [hd, add_tsub_cancel_of_le hn.le]
  exact lt_irrefl _ this

/-- Comparison of measures on compact sets from comparison of integrals of `C_c` functions, when the larger measure
is outer regular at compact sets (a variant of `RealRMK.measure_le_of_isCompact_of_integral`). -/
theorem measure_le_of_isCompact_of_integral_of_approx {m1 m2 : Measure Y} [IsFiniteMeasureOnCompacts m1]
    [IsFiniteMeasureOnCompacts m2]
    (hreg : ∀ K : Set Y, IsCompact K → ∀ ε : ENNReal, ε ≠ 0 → ∃ V, K ⊆ V ∧ IsOpen V ∧ m2 V ≤ m2 K + ε)
    (hμν : ∀ f : CompactlySupportedContinuousMap Y ℝ, ∫ x, f x ∂m1 ≤ ∫ x, f x ∂m2)
    ⦃K : Set Y⦄ (hK : IsCompact K) : m1 K ≤ m2 K := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hν ↦ ?_
  have hνK : m2 K ≠ ⊤ := hν.ne
  have hμK : m1 K ≠ ⊤ := hK.measure_lt_top.ne
  obtain ⟨V, pV1, pV2, pV3⟩ : ∃ V ⊇ K, IsOpen V ∧ m2 V ≤ m2 K + ε :=
    hreg K hK ε (ne_of_gt (ENNReal.coe_lt_coe.mpr hε))
  suffices m1.real K ≤ m2.real K + ε by
    rwa [← ENNReal.toReal_le_toReal, ENNReal.toReal_add, ENNReal.coe_toReal]
    all_goals finiteness
  have VltTop : m2 V < ⊤ := pV3.trans_lt <| by finiteness
  obtain ⟨f, pf1, pf2, pf3⟩ :
      ∃ f : CompactlySupportedContinuousMap Y ℝ, Set.EqOn (⇑f) 1 K ∧ tsupport ⇑f ⊆ V ∧
        ∀ (x : Y), f x ∈ Set.Icc 0 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK pV2 pV1
    exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf1, hf3⟩
  have hfV (x : Y) : f x ≤ V.indicator 1 x := by
    by_cases hx : x ∈ tsupport f
    · simp [(pf2 hx), (pf3 x).2]
    · simp [image_eq_zero_of_notMem_tsupport hx, Set.indicator_nonneg]
  have hfK (x : Y) : K.indicator 1 x ≤ f x := by
    by_cases hx : x ∈ K
    · simp [hx, pf1 hx]
    · simp [hx, (pf3 x).1]
  calc
    m1.real K = ∫ x, K.indicator 1 x ∂m1 := integral_indicator_one hK.measurableSet |>.symm
    _ ≤ ∫ x, f x ∂m1 := by
      refine integral_mono ?_ f.integrable hfK
      exact (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
    _ ≤ ∫ x, f x ∂m2 := hμν f
    _ ≤ ∫ x, V.indicator 1 x ∂m2 := by
      refine integral_mono f.integrable ?_ hfV
      exact IntegrableOn.integrable_indicator integrableOn_const pV2.measurableSet
    _ ≤ (m2 K).toReal + ↑ε := by
      rwa [integral_indicator_one pV2.measurableSet, measureReal_def,
        ← ENNReal.coe_toReal, ← ENNReal.toReal_add, ENNReal.toReal_le_toReal]
      all_goals finiteness

/-- **Identification of a density**: if a finite inner regular measure `ν` integrates every compactly supported
continuous function as `p • λ` does ($\lambda$ regular, $p\ge0$ continuous and bounded), then $\nu=p\,\lambda$. -/
theorem eq_withDensity_of_integral_eq (lam : Measure Y) [lam.Regular] (ν : Measure Y) [IsFiniteMeasure ν]
    [ν.InnerRegular] {p : Y → ℝ} (hp : Continuous p) (hp0 : 0 ≤ p) {C : ℝ} (hpC : ∀ y, p y ≤ C)
    (h : ∀ ψ : CompactlySupportedContinuousMap Y ℝ, ∫ y, ψ y ∂ν = ∫ y, ψ y * p y ∂lam) :
    ν = lam.withDensity fun y => ENNReal.ofReal (p y) := by
  set ρ := lam.withDensity fun y => ENNReal.ofReal (p y) with hρdef
  have hpm : Measurable fun y => ENNReal.ofReal (p y) := ENNReal.measurable_ofReal.comp hp.measurable
  have hρ : ∀ S, MeasurableSet S → ρ S = ∫⁻ y in S, ENNReal.ofReal (p y) ∂lam :=
    fun S hS => withDensity_apply _ hS
  have hρint : ∀ g : Y → ℝ, ∫ y, g y ∂ρ = ∫ y, g y * p y ∂lam := by
    intro g
    rw [integral_withDensity_eq_integral_toReal_smul hpm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [ENNReal.toReal_ofReal (hp0 y), mul_comm]
  have hρle : ∀ S, MeasurableSet S → ρ S ≤ ENNReal.ofReal C * lam S := by
    intro S hS
    rw [hρ S hS]
    calc ∫⁻ y in S, ENNReal.ofReal (p y) ∂lam ≤ ∫⁻ y in S, ENNReal.ofReal C ∂lam :=
          lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpC y)
      _ = ENNReal.ofReal C * lam S := by rw [setLIntegral_const, mul_comm]
  have hρfinK : ∀ K, IsCompact K → ρ K ≠ ⊤ := fun K hK =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK.measure_lt_top.ne)
      (hρle K hK.isClosed.measurableSet)
  haveI : IsFiniteMeasureOnCompacts ρ := ⟨fun K hK => lt_top_iff_ne_top.2 (hρfinK K hK)⟩
  have hdiff : ∀ (A K : Set Y) (n : ENNReal), MeasurableSet A → IsCompact K → K ⊆ A →
      lam A ≤ lam K + n → ρ A ≤ ρ K + ENNReal.ofReal C * n := by
    intro A K n hA hK hKA hn
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have h1 : ρ K + ρ (A \ K) = ρ A := by
      rw [measure_add_sdiff hKm.nullMeasurableSet, Set.union_eq_self_of_subset_left hKA]
    have h2 : lam (A \ K) ≤ n := by
      rw [measure_sdiff hKA hKm.nullMeasurableSet hK.measure_lt_top.ne]
      exact tsub_le_iff_left.2 hn
    rw [← h1]
    gcongr
    exact (hρle _ (hA.diff hKm)).trans (by gcongr)
  have hρreg : ∀ K : Set Y, IsCompact K → ∀ ε : ENNReal, ε ≠ 0 →
      ∃ V, K ⊆ V ∧ IsOpen V ∧ ρ V ≤ ρ K + ε := by
    intro K hK ε hε
    obtain ⟨n, hn0, hn⟩ := ENNReal.exists_nnreal_pos_mul_lt (ENNReal.ofReal_ne_top (r := C)) hε
    obtain ⟨V, hKV, hVo, hV⟩ := K.exists_isOpen_le_add lam (ε := n) (by exact_mod_cast hn0.ne')
    refine ⟨V, hKV, hVo, ?_⟩
    refine (hdiff V K n hVo.measurableSet hK hKV hV).trans ?_
    rw [mul_comm]
    gcongr
  have hKeq : ∀ K : Set Y, IsCompact K → ν K = ρ K := by
    intro K hK
    refine le_antisymm ?_ ?_
    · refine measure_le_of_isCompact_of_integral_of_approx hρreg (fun f => ?_) hK
      rw [h f, hρint]
    · refine measure_le_of_isCompact_of_integral_of_approx
        (fun K hK ε hε => Set.exists_isOpen_le_add K ν hε) (fun f => ?_) hK
      rw [h f, hρint]
  have hle : ν ≤ ρ := by
    refine Measure.le_iff.2 fun s hs => ?_
    refine le_of_forall_lt fun r hr => ?_
    obtain ⟨K, hKs, hK, hrK⟩ := hs.exists_lt_isCompact hr
    rw [hKeq K hK] at hrK
    exact hrK.trans_le (measure_mono hKs)
  -- finiteness of ρ
  set U : ℕ → Set Y := fun n => {y | ((n : ENNReal) + 1)⁻¹ < ENNReal.ofReal (p y)} with hU
  have hUo : ∀ n, IsOpen (U n) := fun n =>
    isOpen_lt continuous_const (ENNReal.continuous_ofReal.comp hp)
  have hUmono : Monotone U := fun n m hnm y hy => by
    refine lt_of_le_of_lt (ENNReal.inv_le_inv.2 ?_) (show ((n : ENNReal) + 1)⁻¹ < _ from hy)
    gcongr
  have hUρ : ∀ n, ρ (U n) ≤ ν Set.univ := by
    intro n
    set t : ENNReal := ((n : ENNReal) + 1)⁻¹ with ht
    have ht0 : t ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
    have htop : t ≠ ⊤ := ENNReal.inv_ne_top.2 (by simp)
    have hK1 : ∀ K, K ⊆ U n → IsCompact K → t * lam K ≤ ν Set.univ := by
      intro K hKU hK
      calc t * lam K = ∫⁻ y in K, t ∂lam := by rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ y in K, ENNReal.ofReal (p y) ∂lam :=
          setLIntegral_mono' hK.isClosed.measurableSet fun y hy => (hKU hy).le
        _ = ρ K := (hρ K hK.isClosed.measurableSet).symm
        _ = ν K := (hKeq K hK).symm
        _ ≤ ν Set.univ := measure_mono (Set.subset_univ _)
    have hlamfin : lam (U n) ≠ ⊤ := by
      intro htopU
      have hr : t⁻¹ * ν Set.univ < lam (U n) := by
        rw [htopU]
        exact lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ht0) (measure_ne_top _ _))
      obtain ⟨K, hKU, hK, hrK⟩ := (hUo n).exists_lt_isCompact hr
      have h1 := hK1 K hKU hK
      have h2 : t * (t⁻¹ * ν Set.univ) < t * lam K := (ENNReal.mul_lt_mul_iff_right ht0 htop).2 hrK
      rw [← mul_assoc, ENNReal.mul_inv_cancel ht0 htop, one_mul] at h2
      exact lt_irrefl _ (h2.trans_le h1)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨m, hm0, hm⟩ := ENNReal.exists_nnreal_pos_mul_lt (ENNReal.ofReal_ne_top (r := C))
      (show (ε : ENNReal) ≠ 0 by exact_mod_cast hε.ne')
    obtain ⟨K, hKU, hK, hKl⟩ := (hUo n).measurableSet.exists_isCompact_lt_add hlamfin
      (ε := m) (by exact_mod_cast hm0.ne')
    calc ρ (U n) ≤ ρ K + ENNReal.ofReal C * m :=
          hdiff _ K m (hUo n).measurableSet hK hKU hKl.le
      _ ≤ ν Set.univ + ε := by
          rw [← hKeq K hK, mul_comm]
          exact add_le_add (measure_mono (Set.subset_univ _)) hm.le
  have hρuniv : ρ Set.univ ≤ ν Set.univ := by
    have hz : ρ {y | ENNReal.ofReal (p y) = 0} = 0 := by
      have hm : MeasurableSet {y | ENNReal.ofReal (p y) = 0} := measurableSet_eq_fun hpm measurable_const
      rw [hρ _ hm, setLIntegral_congr_fun hm (g := fun _ => 0) (fun y hy => hy)]
      simp
    have hcover : (Set.univ : Set Y) ⊆ (⋃ n, U n) ∪ {y | ENNReal.ofReal (p y) = 0} := by
      intro y _
      by_cases h0 : ENNReal.ofReal (p y) = 0
      · exact Or.inr h0
      · left
        obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h0
        exact Set.mem_iUnion.2 ⟨n, lt_of_le_of_lt (ENNReal.inv_le_inv.2 le_self_add) hn⟩
    calc ρ Set.univ ≤ ρ ((⋃ n, U n) ∪ {y | ENNReal.ofReal (p y) = 0}) := measure_mono hcover
      _ ≤ ρ (⋃ n, U n) + ρ {y | ENNReal.ofReal (p y) = 0} := measure_union_le _ _
      _ = ⨆ n, ρ (U n) := by rw [hz, add_zero, hUmono.measure_iUnion]
      _ ≤ ν Set.univ := iSup_le hUρ
  haveI : IsFiniteMeasure ρ := ⟨lt_of_le_of_lt hρuniv (measure_lt_top _ _)⟩
  exact Measure.eq_of_le_of_measure_univ_eq hle (le_antisymm (hle Set.univ) hρuniv)

end NumberFieldKB.Pontryagin
