import NumberFieldKB.Pontryagin.Unfolding
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The quotient measure on $G/\Gamma$ (Weil VII.§2, p. 105)

$G$ is a locally compact commutative Hausdorff group with a Haar measure $\alpha$, and $\Gamma\subset G$ a discrete
subgroup with $G/\Gamma$ compact. Weil (*Basic Number Theory*, VII.§2, p. 105) writes $\alpha(G/\Gamma)$ for the
measure of $G/\Gamma$ under the quotient of $\alpha$ by the counting measure of $\Gamma$, i.e. the measure on $G/\Gamma$
with
$$\int_G f\,d\alpha=\int_{G/\Gamma}\sum_{\gamma\in\Gamma}f(g\gamma)\,d\bar\alpha(\dot g)$$
for continuous compactly supported $f$ (Weil, *L'intégration dans les groupes topologiques*, §9; Folland, *A Course in
Abstract Harmonic Analysis*, 2nd ed., Theorem 2.49).

Here `quotientMeasure Γ α` is built from a Bruhat function $h$ (`NumberFieldKB.Pontryagin.bruhat`) as the image of
$h\,\alpha$ under $G\to G/\Gamma$. It does not depend on $h$ (`quotientMeasure_eq`), it is a Haar measure on
$G/\Gamma$, it satisfies Weil's formula (`integral_eq_integral_periodize`), and $\bar\alpha(G/\Gamma)=\int_G h\,d\alpha$
(`quotientMeasure_univ`). No countability of $\Gamma$ and no fundamental domain are needed (Mathlib's
`MeasureTheory.Measure.IsMulLeftInvariant` quotient theory assumes a fundamental domain and a countable $\Gamma$).

## Main declarations
* `lintegral_mul_eq_of_isBruhat`: $\int h_1P\,d\alpha=\int h_2P\,d\alpha$ for Bruhat functions $h_1,h_2$ and
  $\Gamma$-periodic $P\ge0$.
* `quotientMeasure`, `quotientMeasure_eq`, `quotientMeasure_univ`, instance `IsHaarMeasure`.
* `integral_quotientMeasure`: $\int_{G/\Gamma}P\,d\bar\alpha=\int_G h\,(P\circ\pi)\,d\alpha$.
* `integral_eq_integral_mul_tsum` (unfolding): $\int_GF\,d\alpha=\int_G h(g)\sum_\gamma F(g\gamma)\,d\alpha(g)$ for
  continuous integrable $F$ whose periodization converges uniformly on the support of $h$.
* `integral_eq_integral_periodize`: Weil's formula above.
-/

open MeasureTheory Topology Filter Set

noncomputable section

namespace NumberFieldKB.Pontryagin

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (α : Measure G) [α.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] in
/-- Translates of a Bruhat function are Bruhat functions. -/
theorem IsBruhat.translate {h : G → ℝ} (hh : IsBruhat Γ h) (x : G) : IsBruhat Γ (fun g => h (x * g)) where
  continuous := hh.continuous.comp (continuous_const.mul continuous_id)
  hasCompactSupport := hh.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft x)
  nonneg g := hh.nonneg _
  tsum_eq_one g := by simpa only [mul_assoc] using hh.tsum_eq_one (x * g)

/-- If a nonnegative family sums to $1$ and is supported in the finset `S`, then
$a=\sum_{\gamma\in S}a\,\varphi(\gamma)$ in `ℝ≥0∞`. -/
theorem ofReal_eq_sum_mul {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (hφ : ∀ i, 0 ≤ φ i) (hsum : ∑' i, φ i = 1)
    (hS : ∀ i, φ i ≠ 0 → i ∈ S) (a : ENNReal) :
    a = ∑ i ∈ S, a * ENNReal.ofReal (φ i) := by
  have h1 : ∑' i, φ i = ∑ i ∈ S, φ i := tsum_eq_sum fun i hi => by
    by_contra hne; exact hi (hS i hne)
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun i _ => hφ i, ← h1, hsum]
  simp

omit [LocallyCompactSpace G] in
/-- **Independence of the Bruhat function**: for Bruhat functions $h_1,h_2$ and a measurable $\Gamma$-periodic
$P\ge0$, $\int h_1P\,d\alpha=\int h_2P\,d\alpha$. -/
theorem lintegral_mul_eq_of_isBruhat {h₁ h₂ : G → ℝ} (hh₁ : IsBruhat Γ h₁) (hh₂ : IsBruhat Γ h₂)
    {P : G → ENNReal} (hP : Measurable P) (hper : ∀ (g : G) (γ : Γ), P (g * γ) = P g) :
    ∫⁻ g, ENNReal.ofReal (h₁ g) * P g ∂α = ∫⁻ g, ENNReal.ofReal (h₂ g) * P g ∂α := by
  have hfin := finite_setOf_mul_mem Γ hh₁.hasCompactSupport.isCompact hh₂.hasCompactSupport.isCompact
  set S := hfin.toFinset with hSdef
  have hSmem : ∀ γ : Γ, (∃ k ∈ tsupport h₁, k * (γ : G) ∈ tsupport h₂) → γ ∈ S := fun γ hγ => by
    simpa [hSdef] using hγ
  have hA : ∀ g, ENNReal.ofReal (h₁ g) = ∑ γ ∈ S, ENNReal.ofReal (h₁ g) * ENNReal.ofReal (h₂ (g * γ)) := by
    intro g
    by_cases h0 : h₁ g = 0
    · simp [h0]
    refine ofReal_eq_sum_mul S (fun γ : Γ => h₂ (g * γ)) (fun γ => hh₂.nonneg _) (hh₂.tsum_eq_one g) ?_ _
    intro γ hγ
    exact hSmem γ ⟨g, subset_tsupport _ h0, subset_tsupport _ hγ⟩
  have hB : ∀ g, ENNReal.ofReal (h₂ g) = ∑ γ ∈ S, ENNReal.ofReal (h₂ g) * ENNReal.ofReal (h₁ (g * (γ : G)⁻¹)) := by
    intro g
    by_cases h0 : h₂ g = 0
    · simp [h0]
    refine ofReal_eq_sum_mul S (fun γ : Γ => h₁ (g * (γ : G)⁻¹)) (fun γ => hh₁.nonneg _) ?_ ?_ _
    · rw [← hh₁.tsum_eq_one g]
      exact (Equiv.inv Γ).tsum_eq (fun γ : Γ => h₁ (g * (γ : G))) |>.symm ▸ rfl
    intro γ hγ
    exact hSmem γ ⟨g * (γ : G)⁻¹, subset_tsupport _ hγ, by simpa using subset_tsupport _ h0⟩
  have m₁ : Measurable fun g => ENNReal.ofReal (h₁ g) := ENNReal.measurable_ofReal.comp hh₁.continuous.measurable
  have m₂ : Measurable fun g => ENNReal.ofReal (h₂ g) := ENNReal.measurable_ofReal.comp hh₂.continuous.measurable
  have m₁' : ∀ γ : G, Measurable fun g => ENNReal.ofReal (h₁ (g * γ)) := fun γ =>
    ENNReal.measurable_ofReal.comp (hh₁.continuous.comp (continuous_id.mul continuous_const)).measurable
  have m₂' : ∀ γ : G, Measurable fun g => ENNReal.ofReal (h₂ (g * γ)) := fun γ =>
    ENNReal.measurable_ofReal.comp (hh₂.continuous.comp (continuous_id.mul continuous_const)).measurable
  have e₁ : ∫⁻ g, ENNReal.ofReal (h₁ g) * P g ∂α =
      ∑ γ ∈ S, ∫⁻ g, ENNReal.ofReal (h₁ g) * ENNReal.ofReal (h₂ (g * γ)) * P g ∂α := by
    rw [← lintegral_finsetSum S (f := fun (γ : Γ) g => ENNReal.ofReal (h₁ g) * ENNReal.ofReal (h₂ (g * γ)) * P g)
      fun γ _ => (m₁.mul (m₂' _)).mul hP]
    refine lintegral_congr fun g => ?_
    rw [← Finset.sum_mul, ← hA g]
  have e₂ : ∫⁻ g, ENNReal.ofReal (h₂ g) * P g ∂α =
      ∑ γ ∈ S, ∫⁻ g, ENNReal.ofReal (h₂ g) * ENNReal.ofReal (h₁ (g * (γ : G)⁻¹)) * P g ∂α := by
    rw [← lintegral_finsetSum S
      (f := fun (γ : Γ) g => ENNReal.ofReal (h₂ g) * ENNReal.ofReal (h₁ (g * (γ : G)⁻¹)) * P g)
      fun γ _ => (m₂.mul (m₁' _)).mul hP]
    refine lintegral_congr fun g => ?_
    rw [← Finset.sum_mul, ← hB g]
  rw [e₁, e₂]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← lintegral_mul_right_eq_self (fun g => ENNReal.ofReal (h₁ g) * ENNReal.ofReal (h₂ (g * γ)) * P g) (γ : G)⁻¹]
  refine lintegral_congr fun g => ?_
  have h1 : P (g * (γ : G)⁻¹) = P g := by simpa using (hper (g * (γ : G)⁻¹) γ).symm
  show ENNReal.ofReal (h₁ (g * (γ : G)⁻¹)) * ENNReal.ofReal (h₂ (g * (γ : G)⁻¹ * γ)) * P (g * (γ : G)⁻¹) = _
  rw [h1, inv_mul_cancel_right]
  ring

variable [CompactSpace (G ⧸ Γ)] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

omit [CompactSpace (G ⧸ Γ)] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
/-- The quotient map is measurable. -/
theorem measurable_mk' : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := by
  have hc : Continuous (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quot_mk
  exact hc.measurable

omit [CompactSpace (G ⧸ Γ)] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
/-- Preimages of measurable sets under the quotient map are measurable. -/
theorem measurable_mk {E : Set (G ⧸ Γ)} (hE : MeasurableSet E) :
    MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E) :=
  measurable_mk' Γ hE

omit [CompactSpace (G ⧸ Γ)] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [DiscreteTopology Γ] in
/-- Indicators of preimages of measurable sets are measurable. -/
theorem indicator_measurable {E : Set (G ⧸ Γ)} (hE : MeasurableSet E) :
    Measurable (((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator (1 : G → ENNReal)) :=
  measurable_one.indicator (measurable_mk Γ hE)

omit [CompactSpace (G ⧸ Γ)] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] in
/-- Indicators of preimages of sets of $G/\Gamma$ are $\Gamma$-periodic. -/
theorem indicator_periodic (E : Set (G ⧸ Γ)) (g : G) (γ : Γ) :
    ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator (1 : G → ENNReal) (g * γ) =
      ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator (1 : G → ENNReal) g := by
  have : ((g * γ : G) : G ⧸ Γ) = g := QuotientGroup.mk_mul_of_mem g γ.2
  have key : g * (γ : G) ∈ (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E ↔ g ∈ (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E := by
    simp only [Set.mem_preimage]; rw [this]
  by_cases hg : g ∈ (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E
  · simp [Set.indicator, hg, key.2 hg]
  · simp [Set.indicator, hg, mt key.1 hg]

/-- **The quotient measure** $\bar\alpha$ on $G/\Gamma$: the image of $h\,\alpha$ under $G\to G/\Gamma$, for the
chosen Bruhat function $h$ (independent of the choice, `quotientMeasure_eq`). -/
def quotientMeasure : Measure (G ⧸ Γ) :=
  (α.withDensity fun g => ENNReal.ofReal (bruhat Γ g)).map (QuotientGroup.mk : G → G ⧸ Γ)

omit [α.IsHaarMeasure] [CompactSpace (G ⧸ Γ)] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [DiscreteTopology Γ] in
/-- The image of $h\,\alpha$ on a measurable set $E$ of $G/\Gamma$. -/
theorem map_apply_eq {h : G → ℝ} (_hh : IsBruhat Γ h) {E : Set (G ⧸ Γ)} (hE : MeasurableSet E) :
    ((α.withDensity fun g => ENNReal.ofReal (h g)).map (QuotientGroup.mk : G → G ⧸ Γ)) E =
      ∫⁻ g, ENNReal.ofReal (h g) * ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator 1 g ∂α := by
  have hs : MeasurableSet ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E) := measurable_mk Γ hE
  rw [Measure.map_apply (measurable_mk' Γ) hE, withDensity_apply _ hs, ← lintegral_indicator hs]
  refine lintegral_congr fun g => ?_
  by_cases hg : g ∈ (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E <;> simp [hg]

/-- The quotient measure does not depend on the Bruhat function. -/
theorem quotientMeasure_eq {h : G → ℝ} (hh : IsBruhat Γ h) :
    quotientMeasure Γ α = (α.withDensity fun g => ENNReal.ofReal (h g)).map (QuotientGroup.mk : G → G ⧸ Γ) := by
  refine Measure.ext fun E hE => ?_
  unfold quotientMeasure
  rw [map_apply_eq Γ α (isBruhat_bruhat Γ) hE, map_apply_eq Γ α hh hE]
  exact lintegral_mul_eq_of_isBruhat Γ α (isBruhat_bruhat Γ) hh (indicator_measurable Γ hE)
    (indicator_periodic Γ E)

/-- $\bar\alpha(G/\Gamma)=\int_G h\,d\alpha$ for every Bruhat function $h$. -/
theorem quotientMeasure_univ {h : G → ℝ} (hh : IsBruhat Γ h) :
    quotientMeasure Γ α univ = ∫⁻ g, ENNReal.ofReal (h g) ∂α := by
  rw [quotientMeasure_eq Γ α hh, Measure.map_apply (measurable_mk' Γ) MeasurableSet.univ, preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

instance : IsFiniteMeasure (quotientMeasure Γ α) := by
  have hh := isBruhat_bruhat Γ
  refine ⟨?_⟩
  rw [quotientMeasure_univ Γ α hh]
  exact (hh.continuous.integrable_of_hasCompactSupport hh.hasCompactSupport).lintegral_lt_top

/-- $\bar\alpha(E)=\int h\cdot 1_{\pi^{-1}E}\,d\alpha$ for measurable $E$. -/
theorem quotientMeasure_apply {h : G → ℝ} (hh : IsBruhat Γ h) {E : Set (G ⧸ Γ)} (hE : MeasurableSet E) :
    quotientMeasure Γ α E = ∫⁻ g, ENNReal.ofReal (h g) * ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator 1 g ∂α := by
  rw [quotientMeasure_eq Γ α hh, map_apply_eq Γ α hh hE]

instance : (quotientMeasure Γ α).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  have hh := isBruhat_bruhat Γ
  refine Measure.ext fun E hE => ?_
  have hE' : MeasurableSet ((fun y : G ⧸ Γ => (x : G ⧸ Γ) * y) ⁻¹' E) := (measurable_const_mul _) hE
  rw [Measure.map_apply (measurable_const_mul _) hE, quotientMeasure_apply Γ α hh hE',
    quotientMeasure_apply Γ α hh hE]
  have hind : ∀ g : G, ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' ((fun y : G ⧸ Γ => (x : G ⧸ Γ) * y) ⁻¹' E)).indicator
      (1 : G → ENNReal) g = ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator (1 : G → ENNReal) (x * g) := by
    intro g
    rfl
  simp only [hind]
  have hT := lintegral_mul_eq_of_isBruhat Γ α (hh.translate Γ x⁻¹) hh (indicator_measurable Γ hE)
    (indicator_periodic Γ E)
  rw [← lintegral_mul_left_eq_self (fun g => ENNReal.ofReal (bruhat Γ g) *
    ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' E).indicator 1 (x * g)) x⁻¹]
  simpa using hT

instance : (quotientMeasure Γ α).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  have hh := isBruhat_bruhat Γ
  set h := bruhat Γ
  have hV : IsOpen ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U) := hU.preimage continuous_quot_mk
  obtain ⟨y, hg⟩ := hne
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hex : ∃ γ : Γ, h (g * γ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hh.tsum_eq_one g
    simp [hcon] at this
  obtain ⟨γ, hγ⟩ := hex
  have hmem : g * (γ : G) ∈ (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U := by
    simpa [QuotientGroup.mk_mul_of_mem g γ.2] using hg
  have hW : IsOpen ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U ∩ {y | 0 < h y}) :=
    hV.inter (isOpen_lt continuous_const hh.continuous)
  have hWpos : 0 < α ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U ∩ {y | 0 < h y}) :=
    hW.measure_pos α ⟨g * γ, hmem, lt_of_le_of_ne (hh.nonneg _) (Ne.symm hγ)⟩
  rw [quotientMeasure_eq Γ α hh, Measure.map_apply (measurable_mk' Γ) hU.measurableSet,
    withDensity_apply _ hV.measurableSet]
  refine ((lintegral_pos_iff_support (ENNReal.measurable_ofReal.comp hh.continuous.measurable)).2 ?_).ne'
  have hsub : (QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U ∩ {y | 0 < h y} ⊆
      Function.support fun y => ENNReal.ofReal (h y) := fun y hy => by
    simpa [Function.mem_support] using hy.2
  calc (0 : ENNReal) < α ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U ∩ {y | 0 < h y}) := hWpos
    _ = (α.restrict ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U))
          ((QuotientGroup.mk : G → G ⧸ Γ) ⁻¹' U ∩ {y | 0 < h y}) := by
        rw [Measure.restrict_apply hW.measurableSet, inter_eq_left.2 inter_subset_left]
    _ ≤ _ := measure_mono hsub

instance : (quotientMeasure Γ α).IsHaarMeasure := {}

/-- Integration against the quotient measure: $\int_{G/\Gamma}P\,d\bar\alpha=\int_Gh(g)P(\Gamma g)\,d\alpha(g)$ for
continuous $P$ and every Bruhat function $h$. -/
theorem integral_quotientMeasure {h : G → ℝ} (hh : IsBruhat Γ h) {P : G ⧸ Γ → ℂ} (hP : Continuous P) :
    ∫ x, P x ∂(quotientMeasure Γ α) = ∫ g, (h g : ℂ) * P (g : G ⧸ Γ) ∂α := by
  have hm : Measurable fun g => (h g).toNNReal := hh.continuous.measurable.real_toNNReal
  rw [quotientMeasure_eq Γ α hh, integral_map (measurable_mk' Γ).aemeasurable hP.aestronglyMeasurable]
  refine (integral_withDensity_eq_integral_smul hm (fun g => P (g : G ⧸ Γ))).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hh.nonneg g), Complex.real_smul]

/-- **Weil's formula for the quotient measure**: for continuous compactly supported $f$ on $G$,
$\int_Gf\,d\alpha=\int_{G/\Gamma}\sum_{\gamma\in\Gamma}f(g\gamma)\,d\bar\alpha$. -/
theorem integral_eq_integral_periodize [α.Regular] {f : G → ℂ} (hfc : Continuous f) (hf : HasCompactSupport f) :
    ∫ g, f g ∂α = ∫ x, periodize Γ f x ∂(quotientMeasure Γ α) := by
  rw [integral_quotientMeasure Γ α (isBruhat_bruhat Γ) (continuous_periodize Γ hfc hf)]
  exact integral_eq_integral_mul_tsum Γ α (isBruhat_bruhat Γ) hfc (hfc.integrable_of_hasCompactSupport hf)
    (tendstoUniformlyOn_sum_of_hasCompactSupport Γ hf (isBruhat_bruhat Γ).hasCompactSupport)

end NumberFieldKB.Pontryagin
