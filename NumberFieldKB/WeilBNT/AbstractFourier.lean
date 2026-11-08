import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.UniformSpace.CompactConvergence
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, VII.§2, text p. 104–105: the Fourier transform on a locally compact abelian group

$G$ is a locally compact commutative Hausdorff group (written multiplicatively here; Weil writes it additively),
$\alpha$ a Haar measure on $G$, $G^*$ = Mathlib's `PontryaginDual G` (continuous homomorphisms $G\to\mathbb T$, with the
compact-open topology), and $\langle g,g^*\rangle=g^*(g)$.

* `fourierLCA α Φ` $=\Phi^*$, $\Phi^*(g^*)=\int_G\Phi(g)\langle g,g^*\rangle\,d\alpha(g)$ (Weil's formula, no complex
  conjugation).
* **`weil_VII_2_text104_continuous`**: for $\Phi$ integrable, $\Phi^*$ is continuous on $G^*$ (Weil states it for
  $\Phi$ continuous and integrable). The Haar measure is assumed regular (`[α.Regular]`): Weil's Haar measures are
  Radon measures, while Mathlib's `IsHaarMeasure` does not include regularity (Mathlib's `Measure.haar` is regular).
* `IsAdmissible α Φ` (Weil's "admissible for $G$", p. 105): $\Phi$ is continuous and integrable and $\Phi^*$ is
  integrable for a Haar measure on $G^*$ (`β`, any Haar measure: integrability does not depend on the choice).

The dual measure, Fourier inversion and the compact-group normalization (VII.§2 texts p. 105) are in
`NumberFieldKB/Pontryagin/Inversion.lean` (`NumberFieldKB.Pontryagin.IsDualMeasure`, for compact and discrete groups).
-/

open MeasureTheory Topology

noncomputable section

namespace NumberFieldKB.WeilBNT.AbstractFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Weil's Fourier transform $\Phi^*(g^*)=\int_G\Phi(g)\langle g,g^*\rangle\,d\alpha(g)$. -/
def fourierLCA (α : Measure G) (Φ : G → ℂ) (χ : PontryaginDual G) : ℂ := ∫ g, Φ g * (χ g : ℂ) ∂α

open Filter in
/-- Near a character, all characters are uniformly close to it on a given compact set (compact-open topology). -/
lemma eventually_close (χ₀ : PontryaginDual G) {K : Set G} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ χ in 𝓝 χ₀, ∀ g ∈ K, ‖(χ g : ℂ) - (χ₀ g : ℂ)‖ < δ := by
  have h : Tendsto (fun χ : PontryaginDual G => (χ.toContinuousMap : C(G, Circle))) (𝓝 χ₀)
      (𝓝 χ₀.toContinuousMap) :=
    (continuous_induced_dom (f := fun χ : PontryaginDual G => χ.toContinuousMap)).tendsto χ₀
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at h
  have h2 := Metric.tendstoUniformlyOn_iff.1 (h K hK) δ hδ
  filter_upwards [h2] with χ hχ g hg
  have := hχ g hg
  have h3 : dist (χ₀ g) (χ g) < δ := this
  rw [dist_comm] at h3
  change dist (χ g : ℂ) (χ₀ g : ℂ) < δ at h3
  rwa [dist_eq_norm] at h3

/-- The integrand of the Fourier transform is integrable. -/
lemma integrable_mul_char (α : Measure G) {Φ : G → ℂ} (hΦ : Integrable Φ α) (χ : PontryaginDual G) :
    Integrable (fun g => Φ g * (χ g : ℂ)) α := by
  refine hΦ.norm.mono' (hΦ.aestronglyMeasurable.mul ?_) (Filter.Eventually.of_forall fun g => ?_)
  · exact (continuous_subtype_val.comp (map_continuous χ)).aestronglyMeasurable
  · simp

/-- Tightness of an integrable function for a measure that is inner regular for compact sets. -/
lemma exists_isCompact_tight (α : Measure G) [α.InnerRegularCompactLTTop] {Φ : G → ℂ}
    (hΦ : Integrable Φ α) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set G, IsCompact C ∧ ∫ g, Cᶜ.indicator (fun g => ‖Φ g‖) g ∂α ≤ ε := by
  obtain ⟨s, hs, hsm⟩ := (memLp_one_iff_integrable.2 hΦ).exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.one_ne_top (ε := ENNReal.ofReal (ε / 2)) (by simp [hε])
  have hsi : Integrable s α := memLp_one_iff_integrable.1 hsm
  obtain ⟨R, hR⟩ := s.exists_forall_norm_le
  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _
  set S : Set G := Function.support s with hS
  have hSm : MeasurableSet S := s.measurableSet_support
  have hSf : α S ≠ ⊤ := (s.measure_support_lt_top_of_integrable hsi).ne
  obtain ⟨K, hKS, hK, hSK⟩ := hSm.exists_isCompact_sdiff_lt hSf
    (ε := ENNReal.ofReal (ε / (2 * (R' + 1)))) (by simp [hε]; positivity)
  refine ⟨K, hK, ?_⟩
  have hdiff : Integrable (fun g => Φ g - s g) α := hΦ.sub hsi
  have hint : ∫ g, ‖Φ g - s g‖ ∂α ≤ ε / 2 := by
    have hm : AEStronglyMeasurable (Φ - ⇑s) α := hdiff.aestronglyMeasurable
    rw [integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable]
    rw [eLpNorm_one_eq_lintegral_enorm hm] at hs
    have : ∫⁻ g, ‖Φ g - s g‖ₑ ∂α < ENNReal.ofReal (ε / 2) := hs
    exact (ENNReal.toReal_lt_of_lt_ofReal this).le
  have hKm : MeasurableSet Kᶜ := hK.isClosed.measurableSet.compl
  have hSDm : MeasurableSet (S \ K) := hSm.diff hK.isClosed.measurableSet
  have hSDfin : α (S \ K) ≠ ⊤ := ((measure_mono Set.sdiff_subset).trans_lt hSf.lt_top).ne
  have hI : Integrable ((S \ K).indicator fun _ => R') α :=
    (integrable_indicator_iff hSDm).2 (integrableOn_const hSDfin)
  calc ∫ g, Kᶜ.indicator (fun g => ‖Φ g‖) g ∂α
      ≤ ∫ g, (‖Φ g - s g‖ + (S \ K).indicator (fun _ => R') g) ∂α := by
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
              have h1 : ‖Φ g‖ ≤ ‖Φ g - s g‖ + ‖s g‖ := by
                have := norm_add_le (Φ g - s g) (s g)
                simpa using this
              have h2 : ‖s g‖ ≤ R' := (hR g).trans (le_max_left _ _)
              linarith
            · have : s g = 0 := by simpa [hS] using hgS
              rw [Set.indicator_of_notMem (show g ∉ S \ K from fun h => hgS h.1)]
              simp [this]
    _ = ∫ g, ‖Φ g - s g‖ ∂α + R' * α.real (S \ K) := by
        rw [integral_add hdiff.norm hI]
        rw [integral_indicator_const _ hSDm]
        simp [mul_comm]
    _ ≤ ε / 2 + ε / 2 := by
        gcongr
        have h1 : α.real (S \ K) ≤ ε / (2 * (R' + 1)) := by
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hSK.le
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
        calc R' * α.real (S \ K) ≤ R' * (ε / (2 * (R' + 1))) := by gcongr
          _ ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
    _ = ε := by ring

open Filter in
/-- The Fourier transform of an integrable function is continuous on $G^*$ when the measure is inner regular
for compact sets (finite-measure sets are approximated from inside by compact sets). -/
lemma continuous_fourierLCA_of_innerRegular (α : Measure G) [α.InnerRegularCompactLTTop] {Φ : G → ℂ}
    (hΦ : Integrable Φ α) : Continuous (fourierLCA α Φ) := by
  rw [continuous_iff_continuousAt]
  intro χ₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨C, hC, hCε⟩ := exists_isCompact_tight α hΦ (ε := ε / 4) (by positivity)
  set M : ℝ := ∫ g, ‖Φ g‖ ∂α with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  have hδ : 0 < ε / (4 * (M + 1)) := by positivity
  filter_upwards [eventually_close χ₀ hC hδ] with χ hχ
  have hCm : MeasurableSet Cᶜ := hC.isClosed.measurableSet.compl
  have hI : Integrable (Cᶜ.indicator fun g => ‖Φ g‖) α := hΦ.norm.indicator hCm
  have hb : ‖fourierLCA α Φ χ - fourierLCA α Φ χ₀‖ ≤
      ε / (4 * (M + 1)) * M + 2 * ∫ g, Cᶜ.indicator (fun g => ‖Φ g‖) g ∂α := by
    unfold fourierLCA
    rw [← integral_sub (integrable_mul_char α hΦ χ) (integrable_mul_char α hΦ χ₀)]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ g, ‖Φ g * (χ g : ℂ) - Φ g * (χ₀ g : ℂ)‖ ∂α
        ≤ ∫ g, (ε / (4 * (M + 1)) * ‖Φ g‖ + 2 * Cᶜ.indicator (fun g => ‖Φ g‖) g) ∂α := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hΦ.norm.const_mul _).add (hI.const_mul _)) (Filter.Eventually.of_forall fun g => ?_)
          beta_reduce
          rw [← mul_sub, norm_mul]
          by_cases hg : g ∈ C
          · rw [Set.indicator_of_notMem (by simpa using hg)]
            have := (hχ g hg).le
            nlinarith [norm_nonneg (Φ g)]
          · rw [Set.indicator_of_mem (show g ∈ Cᶜ from hg)]
            have h1 : ‖(χ g : ℂ) - (χ₀ g : ℂ)‖ ≤ 2 := by
              calc ‖(χ g : ℂ) - (χ₀ g : ℂ)‖ ≤ ‖(χ g : ℂ)‖ + ‖(χ₀ g : ℂ)‖ := norm_sub_le _ _
                _ = 2 := by simp; norm_num
            nlinarith [norm_nonneg (Φ g), norm_nonneg ((χ g : ℂ) - (χ₀ g : ℂ)),
              mul_nonneg (norm_nonneg (Φ g)) hδ.le]
      _ = ε / (4 * (M + 1)) * M + 2 * ∫ g, Cᶜ.indicator (fun g => ‖Φ g‖) g ∂α := by
          rw [integral_add (hΦ.norm.const_mul _) (hI.const_mul _), integral_const_mul,
            integral_const_mul]
  have h3 : ε / (4 * (M + 1)) * M ≤ ε / 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [dist_eq_norm]
  linarith

/-- **Weil, VII.§2, text p. 104**: the Fourier transform of an integrable function is continuous on $G^*$. -/
@[kb "weil1973bnt" "Ch. VII, §2, text p.104-105 (the Fourier transform is continuous on the dual group)"]
theorem weil_VII_2_text104_continuous (α : Measure G) [α.IsHaarMeasure] [α.Regular] {Φ : G → ℂ}
    (hΦ : Integrable Φ α) : Continuous (fourierLCA α Φ) :=
  continuous_fourierLCA_of_innerRegular α hΦ

/-- Weil's "admissible for $G$" (VII.§2, p. 105): $\Phi$ continuous, integrable, with $\Phi^*$ integrable for the Haar
measure `β` on $G^*$. -/
def IsAdmissible (α : Measure G) [MeasurableSpace (PontryaginDual G)] (β : Measure (PontryaginDual G))
    (Φ : G → ℂ) : Prop :=
  Continuous Φ ∧ Integrable Φ α ∧ Integrable (fourierLCA α Φ) β

end NumberFieldKB.WeilBNT.AbstractFourier
