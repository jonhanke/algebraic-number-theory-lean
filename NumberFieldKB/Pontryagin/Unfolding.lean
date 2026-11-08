import NumberFieldKB.Pontryagin.Bruhat
import NumberFieldKB.Pontryagin.Fubini
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Unfolding an integral over $G$ along a discrete cocompact subgroup

$G$ is a locally compact commutative Hausdorff group with a regular Haar measure $\alpha$, $\Gamma\subset G$ a
discrete subgroup and $h$ a Bruhat function for $\Gamma$ (`NumberFieldKB.Pontryagin.IsBruhat`). For a continuous
integrable $F$ whose periodization $\sum_{\gamma}F(g\gamma)$ converges uniformly on the support of $h$,
$$\int_GF\,d\alpha=\int_Gh(g)\sum_{\gamma\in\Gamma}F(g\gamma)\,d\alpha(g)$$
(`integral_eq_integral_mul_tsum`). This is the "unfolding" step of the Poisson summation formula (A. Weil,
*Basic Number Theory*, VII.§2, p. 106; G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., Theorem 2.49).
No countability of $\Gamma$ is assumed: the interchanges of sum and integral are done by uniform convergence on a
compact set and by tightness of $F$ (`NumberFieldKB.Pontryagin.exists_isCompact_integral_compl_le`), not by
dominated convergence along a sequence.
-/

open MeasureTheory Topology Filter Set

noncomputable section

namespace NumberFieldKB.Pontryagin

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (α : Measure G) [α.IsHaarMeasure]


/-- The partial sum $\sum_{\gamma\in s}h(g\gamma^{-1})$ of translates of a Bruhat function. -/
def bruhatPartialSum (h : G → ℝ) (s : Finset Γ) (g : G) : ℝ := ∑ γ ∈ s, h (g * (γ : G)⁻¹)

omit [LocallyCompactSpace G] [CommGroup G] [IsTopologicalGroup G] [T2Space G] in
/-- A bounded continuous function times an integrable one is integrable. -/
theorem integrable_mul_of_bdd (μ : Measure G) {ψ F : G → ℂ}
    (hψ : Continuous ψ) {M : ℝ} (hM : ∀ g, ‖ψ g‖ ≤ M) (hFi : Integrable F μ) :
    Integrable (fun g => ψ g * F g) μ := by
  refine (hFi.norm.const_mul M).mono' (hψ.aestronglyMeasurable.mul hFi.aestronglyMeasurable) ?_
  filter_upwards with g
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM g) (norm_nonneg _)

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [IsTopologicalGroup G] [DiscreteTopology
  Γ] in
/-- $\sum_\gamma h(g\gamma^{-1})=1$. -/
theorem tsum_mul_inv_eq {h : G → ℝ} (hh : IsBruhat Γ h) (g : G) :
    ∑' γ : Γ, h (g * (γ : G)⁻¹) = 1 := by
  have := (Equiv.inv Γ).tsum_eq (fun γ : Γ => h (g * (γ : G)))
  simpa [hh.tsum_eq_one g] using this

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in
/-- Summability of $\gamma\mapsto h(g\gamma^{-1})$. -/
theorem summable_mul_inv {h : G → ℝ} (hh : IsBruhat Γ h) (g : G) :
    Summable fun γ : Γ => h (g * (γ : G)⁻¹) := by
  have hs : Summable fun γ : Γ => h (g * (γ : G)) :=
    summable_of_ne_finset_zero (s := (finite_support_mul Γ hh.hasCompactSupport g).toFinset) fun γ hγ => by
      simpa using hγ
  exact (Equiv.summable_iff (Equiv.inv Γ)).2 hs

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [IsTopologicalGroup G] [DiscreteTopology
  Γ] in
theorem bruhatPartialSum_nonneg {h : G → ℝ} (hh : IsBruhat Γ h) (s : Finset Γ) (g : G) : 0 ≤ bruhatPartialSum Γ h s g :=
  Finset.sum_nonneg fun _ _ => hh.nonneg _

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] in
theorem bruhatPartialSum_le_one {h : G → ℝ} (hh : IsBruhat Γ h) (s : Finset Γ) (g : G) : bruhatPartialSum Γ h s g ≤ 1
  := by
  have := (summable_mul_inv Γ hh g).sum_le_tsum s (fun _ _ => hh.nonneg _)
  rwa [tsum_mul_inv_eq Γ hh g] at this

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [IsTopologicalGroup G] [DiscreteTopology
  Γ] in
theorem bruhatPartialSum_eq_one {h : G → ℝ} (hh : IsBruhat Γ h) {s : Finset Γ} {L : Set G} {g : G} (hg : g ∈ L)
    (hs : ∀ γ : Γ, (∃ k ∈ tsupport h, k * (γ : G) ∈ L) → γ ∈ s) : bruhatPartialSum Γ h s g = 1 := by
  rw [← tsum_mul_inv_eq Γ hh g, bruhatPartialSum]
  refine (tsum_eq_sum fun γ hγ => ?_).symm
  by_contra hne
  refine hγ (hs γ ⟨g * (γ : G)⁻¹, subset_tsupport _ hne, by simpa using hg⟩)

omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
theorem continuous_bruhatPartialSum {h : G → ℝ} (hc : Continuous h) (s : Finset Γ) : Continuous (bruhatPartialSum Γ h
  s) :=
  continuous_finsetSum _ fun _ _ => hc.comp (continuous_id.mul continuous_const)

omit [LocallyCompactSpace G] [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace
  G] [BorelSpace G] in
private theorem indicator_one_le (K : Set G) (g : G) : K.indicator (fun _ => (1 : ℝ)) g ≤ 1 := by
  by_cases hg : g ∈ K <;> simp [hg]

/-- **Unfolding**: for a continuous integrable $F$ whose periodization $\sum_\gamma F(g\gamma)$ converges uniformly on
the support of the Bruhat function $h$, $\int_GF\,d\alpha=\int_Gh(g)\sum_\gamma F(g\gamma)\,d\alpha(g)$. -/
theorem integral_eq_integral_mul_tsum [α.Regular] {h : G → ℝ} (hh : IsBruhat Γ h) {F : G → ℂ}
    (hFc : Continuous F) (hFi : Integrable F α)
    (hF : TendstoUniformlyOn (fun (s : Finset Γ) (g : G) => ∑ γ ∈ s, F (g * γ))
      (fun g => ∑' γ : Γ, F (g * γ)) atTop (tsupport h)) :
    ∫ g, F g ∂α = ∫ g, (h g : ℂ) * ∑' γ : Γ, F (g * γ) ∂α := by
  classical
  have hK : IsCompact (tsupport h) := hh.hasCompactSupport
  have hKm : MeasurableSet (tsupport h) := hK.isClosed.measurableSet
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ g, ‖h g‖ ≤ M := hh.continuous.bounded_above_of_compact_support hh.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  have hhc : Continuous fun g => (h g : ℂ) := Complex.continuous_ofReal.comp hh.continuous
  have hhb : ∀ g, ‖(h g : ℂ)‖ ≤ M := fun g => by simpa using hM g
  have hh0 : ∀ g, g ∉ tsupport h → h g = 0 := fun g hg => image_eq_zero_of_notMem_tsupport hg
  set f : Finset Γ → G → ℂ := fun s g => (h g : ℂ) * ∑ γ ∈ s, F (g * γ) with hf
  set φ : G → ℂ := fun g => (h g : ℂ) * ∑' γ : Γ, F (g * γ) with hφ
  have key : ∀ δ > 0, ∀ᶠ s in atTop, ∀ g, ‖f s g - φ g‖ ≤ δ * (tsupport h).indicator (fun _ => (1 : ℝ)) g := by
    intro δ hδ
    have := Metric.tendstoUniformlyOn_iff.1 hF (δ / (M + 1)) (by positivity)
    filter_upwards [this] with s hs g
    by_cases hg : g ∈ tsupport h
    · have h1 := hs g hg
      rw [dist_eq_norm, norm_sub_rev] at h1
      have e : f s g - φ g = (h g : ℂ) * ((∑ γ ∈ s, F (g * γ)) - ∑' γ : Γ, F (g * γ)) := by
        simp only [hf, hφ]; ring
      rw [Set.indicator_of_mem hg, mul_one, e, norm_mul]
      calc ‖(h g : ℂ)‖ * ‖(∑ γ ∈ s, F (g * γ)) - ∑' γ : Γ, F (g * γ)‖ ≤ M * (δ / (M + 1)) :=
            mul_le_mul (hhb g) h1.le (norm_nonneg _) hM0
        _ ≤ δ := by
            rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
    · have h0 := hh0 g hg
      simp [hf, hφ, h0, hg]
  have hfc : ∀ s, Continuous (f s) := fun s =>
    hhc.mul (continuous_finsetSum _ fun γ _ => hFc.comp (continuous_id.mul continuous_const))
  have hfcs : ∀ s, HasCompactSupport (f s) := fun s =>
    HasCompactSupport.intro hK fun g hg => by simp [hf, hh0 g hg]
  have hTU : TendstoUniformly f φ atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [key (ε / 2) (by positivity)] with s hs g
    rw [dist_eq_norm, norm_sub_rev]
    calc ‖f s g - φ g‖ ≤ ε / 2 * (tsupport h).indicator (fun _ => (1 : ℝ)) g := hs g
      _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left (indicator_one_le _ g) (by positivity)
      _ < ε := by linarith
  have hφc : Continuous φ := hTU.continuous (Filter.Eventually.of_forall hfc).frequently
  have hφcs : HasCompactSupport φ :=
    HasCompactSupport.intro hK fun g hg => by simp [hφ, hh0 g hg]
  have hφi : Integrable φ α := hφc.integrable_of_hasCompactSupport hφcs
  have hfi : ∀ s, Integrable (f s) α := fun s => (hfc s).integrable_of_hasCompactSupport (hfcs s)
  -- (a)
  have hA : Tendsto (fun s => ∫ g, f s g ∂α) atTop (𝓝 (∫ g, φ g ∂α)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c : ℝ := α.real (tsupport h) with hc
    have hc0 : 0 ≤ c := measureReal_nonneg
    have hbi : Integrable (fun g => (tsupport h).indicator (fun _ => (1 : ℝ)) g) α :=
      (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
    filter_upwards [key (ε / (c + 1)) (by positivity)] with s hs
    rw [dist_eq_norm, ← integral_sub (hfi s) hφi]
    calc ‖∫ g, (f s g - φ g) ∂α‖
        ≤ ∫ g, ε / (c + 1) * (tsupport h).indicator (fun _ => (1 : ℝ)) g ∂α :=
          norm_integral_le_of_norm_le (hbi.const_mul _) (Filter.Eventually.of_forall hs)
      _ = ε / (c + 1) * c := by
          rw [integral_const_mul, integral_indicator_const _ hKm]; simp [hc]
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  -- (b)
  have hterm : ∀ γ : Γ, ∫ g, (h g : ℂ) * F (g * γ) ∂α = ∫ g, (h (g * (γ : G)⁻¹) : ℂ) * F g ∂α := by
    intro γ
    have := integral_mul_right_eq_self (μ := α) (fun x => (h (x * (γ : G)⁻¹) : ℂ) * F x) (γ : G)
    simpa using this
  have hAB : ∀ s : Finset Γ, ∫ g, f s g ∂α = ∫ g, ((bruhatPartialSum Γ h s g : ℝ) : ℂ) * F g ∂α := by
    intro s
    have e1 : ∀ g, f s g = ∑ γ ∈ s, (h g : ℂ) * F (g * γ) := fun g => by simp [hf, Finset.mul_sum]
    have e2 : ∀ g, ((bruhatPartialSum Γ h s g : ℝ) : ℂ) * F g = ∑ γ ∈ s, (h (g * (γ : G)⁻¹) : ℂ) * F g := fun g => by
      simp [bruhatPartialSum, Finset.sum_mul]
    simp_rw [e1, e2]
    have i1 : ∀ γ ∈ s, Integrable (fun g => (h g : ℂ) * F (g * (γ : G))) α := fun γ _ =>
      integrable_mul_of_bdd α hhc hhb (hFi.comp_mul_right (γ : G))
    have i2 : ∀ γ ∈ s, Integrable (fun g => (h (g * (γ : G)⁻¹) : ℂ) * F g) α := fun γ _ =>
      integrable_mul_of_bdd α (hhc.comp (continuous_id.mul continuous_const)) (fun g => hhb _) hFi
    rw [integral_finsetSum s i1, integral_finsetSum s i2]
    exact Finset.sum_congr rfl fun γ _ => hterm γ
  -- (c)
  have hψc : ∀ s, Continuous fun g => ((bruhatPartialSum Γ h s g : ℝ) : ℂ) := fun s =>
    Complex.continuous_ofReal.comp (continuous_bruhatPartialSum Γ hh.continuous s)
  have hψb : ∀ s g, ‖((bruhatPartialSum Γ h s g : ℝ) : ℂ)‖ ≤ 1 := fun s g => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bruhatPartialSum_nonneg Γ hh s g)]
    exact bruhatPartialSum_le_one Γ hh s g
  have hB : Tendsto (fun s => ∫ g, ((bruhatPartialSum Γ h s g : ℝ) : ℂ) * F g ∂α) atTop (𝓝 (∫ g, F g ∂α)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨L, hLc, hL⟩ := exists_isCompact_integral_compl_le α hFi.norm (ε := ε / 2) (by positivity)
    have hL' : ∫ y in Lᶜ, ‖F y‖ ∂α ≤ ε / 2 := by simpa using hL
    have hLm : MeasurableSet L := hLc.isClosed.measurableSet
    have hfin := finite_setOf_mul_mem Γ hK hLc
    filter_upwards [eventually_ge_atTop hfin.toFinset] with s hs
    have hsL : ∀ γ : Γ, (∃ k ∈ tsupport h, k * (γ : G) ∈ L) → γ ∈ s := fun γ hγ =>
      hs (by simpa using hγ)
    rw [dist_comm, dist_eq_norm, ← integral_sub hFi
      (integrable_mul_of_bdd α (hψc s) (hψb s) hFi)]
    have hbi : Integrable (Lᶜ.indicator fun g => ‖F g‖) α := hFi.norm.indicator hLm.compl
    calc ‖∫ g, (F g - ((bruhatPartialSum Γ h s g : ℝ) : ℂ) * F g) ∂α‖
        ≤ ∫ g, Lᶜ.indicator (fun g => ‖F g‖) g ∂α := by
          refine norm_integral_le_of_norm_le hbi (Filter.Eventually.of_forall fun g => ?_)
          by_cases hg : g ∈ L
          · simp [bruhatPartialSum_eq_one Γ hh hg hsL, hg]
          · rw [Set.indicator_of_mem (show g ∈ Lᶜ from hg)]
            have e : F g - ((bruhatPartialSum Γ h s g : ℝ) : ℂ) * F g = ((1 - bruhatPartialSum Γ h s g : ℝ) : ℂ) * F
              g := by
              push_cast; ring
            rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (by linarith [bruhatPartialSum_le_one Γ hh s g])]
            exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [bruhatPartialSum_nonneg Γ hh s g])
      _ = ∫ y in Lᶜ, ‖F y‖ ∂α := integral_indicator hLm.compl
      _ < ε := by linarith
  have := tendsto_nhds_unique hB (hA.congr hAB)
  exact this

end NumberFieldKB.Pontryagin
