import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Milne, *Algebraic Number Theory*, Lemma 4.23: auxiliary results for Dirichlet's integral

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), p. 78; bib key `milne2020ant`.

The proof follows Milne's: the integral $F(t)$ over $Z(t)$ scales as $F(t) = t^{\sum a_i + m}F(1)$, and integrating
$F(t)e^{-t}$ over $t > 0$ (Tonelli) gives $\prod_i \Gamma(a_i + 1) = F(1)\,\Gamma(\sum a_i + m + 1)$.
The tagged statement is `NumberFieldKB.MilneANT.lemma_4_23` in `Ch4.lean`.
-/

open MeasureTheory Set ENNReal
open scoped ENNReal

namespace NumberFieldKB.MilneANT.Dirichlet4

def S4 (m : ℕ) : Set (Fin m → ℝ) := {x | ∀ i, 0 ≤ x i}
def Z4 (m : ℕ) (t : ℝ) : Set (Fin m → ℝ) := S4 m ∩ {x | ∑ i, x i ≤ t}
noncomputable def g4 {m : ℕ} (a : Fin m → ℝ) (x : Fin m → ℝ) : ℝ≥0∞ := ∏ i, ENNReal.ofReal (x i ^ a i)
noncomputable def F4 {m : ℕ} (a : Fin m → ℝ) (t : ℝ) : ℝ≥0∞ := ∫⁻ x in Z4 m t, g4 a x

lemma measurableSet_S4 (m : ℕ) : MeasurableSet (S4 m) := by
  have : S4 m = ⋂ i, {x : Fin m → ℝ | 0 ≤ x i} := by ext x; simp [S4]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)

lemma measurableSet_Z4 (m : ℕ) (t : ℝ) : MeasurableSet (Z4 m t) :=
  (measurableSet_S4 m).inter (measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
    measurable_const)

lemma measurable_g4 {m : ℕ} (a : Fin m → ℝ) : Measurable (g4 a) := by
  unfold g4
  refine Finset.measurable_prod _ fun i _ => ?_
  exact ENNReal.measurable_ofReal.comp ((measurable_pi_apply i).pow_const _)

lemma g4_smul {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 < t) {y : Fin m → ℝ}
    (hy : y ∈ S4 m) : g4 a (t • y) = ENNReal.ofReal (t ^ (∑ i, a i)) * g4 a y := by
  unfold g4
  have : ∀ i, ENNReal.ofReal ((t • y) i ^ a i) = ENNReal.ofReal (t ^ a i) * ENNReal.ofReal (y i ^ a i) := by
    intro i
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    simp [Real.mul_rpow ht.le (hy i)]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Real.rpow_sum_of_pos ht, ENNReal.ofReal_prod_of_nonneg]
  intro i _
  exact Real.rpow_nonneg ht.le _

lemma F4_scale {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 < t) :
    F4 a t = ENNReal.ofReal (t ^ (∑ i, a i + m)) * F4 a 1 := by
  have h1 := setLIntegral_map (μ := (volume : Measure (Fin m → ℝ))) (measurableSet_Z4 m t)
    (measurable_g4 a) (measurable_const_smul t)
  rw [Measure.map_addHaar_smul volume ht.ne', Measure.restrict_smul, lintegral_smul_measure] at h1
  have hpre : (fun y : Fin m → ℝ => t • y) ⁻¹' Z4 m t = Z4 m 1 := by
    ext y
    simp only [Z4, S4, mem_preimage, mem_inter_iff, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · have := h1 i
        exact nonneg_of_mul_nonneg_right this ht
      · rw [← Finset.mul_sum] at h2
        nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => mul_nonneg ht.le (h1 i), ?_⟩
      rw [← Finset.mul_sum]
      nlinarith
  rw [hpre] at h1
  have h2 : ∫⁻ x in Z4 m 1, g4 a (t • x) = ENNReal.ofReal (t ^ (∑ i, a i)) * F4 a 1 := by
    rw [F4, ← lintegral_const_mul _ (measurable_g4 a)]
    refine setLIntegral_congr_fun (measurableSet_Z4 m 1) fun y hy => ?_
    exact g4_smul a ha ht hy.1
  rw [h2, smul_eq_mul] at h1
  have hfin : (Module.finrank ℝ (Fin m → ℝ)) = m := by simp
  rw [hfin] at h1
  have hc : ENNReal.ofReal |(t ^ m)⁻¹| ≠ 0 := by
    simp [ht.ne']
  have hc' : ENNReal.ofReal |(t ^ m)⁻¹| ≠ ⊤ := ENNReal.ofReal_ne_top
  have : F4 a t = ENNReal.ofReal (t ^ m) * (ENNReal.ofReal (t ^ (∑ i, a i)) * F4 a 1) := by
    rw [← h1]
    unfold F4
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity)]
    simp
  rw [this, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm (t ^ m),
    ← Real.rpow_natCast, ← Real.rpow_add ht]

lemma S4_eq_pi (m : ℕ) : S4 m = Set.pi univ (fun _ : Fin m => Ici (0 : ℝ)) := by
  ext x
  constructor
  · intro h i _; exact h i
  · intro h i; exact h i (mem_univ i)

lemma gamma_integrableOn (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ (s - 1)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact Real.GammaIntegral_convergent hs

lemma lintegral_D {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∫⁻ x in S4 m, g4 a x * ENNReal.ofReal (Real.exp (-∑ i, x i)) =
      ∏ i, ENNReal.ofReal (Real.Gamma (a i + 1)) := by
  set h : Fin m → ℝ → ℝ := fun i y => Real.exp (-y) * y ^ (a i + 1 - 1) with hh
  have hint : ∀ i, Integrable (h i) (volume.restrict (Ici (0 : ℝ))) :=
    fun i => gamma_integrableOn (a i + 1) (by linarith [ha i])
  have hν : (volume : Measure (Fin m → ℝ)).restrict (S4 m) =
      Measure.pi (fun _ : Fin m => (volume : Measure ℝ).restrict (Ici 0)) := by
    rw [S4_eq_pi, volume_pi, Measure.restrict_pi_pi]
  have hcongr : ∫⁻ x in S4 m, g4 a x * ENNReal.ofReal (Real.exp (-∑ i, x i)) =
      ∫⁻ x in S4 m, ENNReal.ofReal (∏ i, h i (x i)) := by
    refine setLIntegral_congr_fun (measurableSet_S4 m) fun x hx => ?_
    unfold g4
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => by
      simp only [hh]; exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (hx i) _))]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hx i) _)]
    rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx i) _)]
    congr 1
    have : Real.exp (-∑ i, x i) = ∏ i, Real.exp (-x i) := by
      rw [← Finset.sum_neg_distrib, Real.exp_sum]
    rw [this, ← Finset.prod_mul_distrib]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
      mul_nonneg (Real.rpow_nonneg (hx i) _) (Real.exp_nonneg _))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [hh, add_sub_cancel_right]
    rw [mul_comm]
  have hnn : ∀ i, ∀ y : ℝ, 0 ≤ y → 0 ≤ h i y := fun i y hy =>
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hy _)
  have hI0 := Integrable.fintype_prod (μ := fun _ : Fin m => (volume : Measure ℝ).restrict (Ici 0)) hint
  have hI : Integrable (fun x : Fin m → ℝ => ∏ i, h i (x i)) ((volume : Measure (Fin m → ℝ)).restrict (S4 m)) := by
    rw [hν]; exact hI0
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hI
    ((ae_restrict_mem (measurableSet_S4 m)).mono fun x hx =>
      Finset.prod_nonneg fun i _ => hnn i _ (hx i))]
  rw [hν, integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    rw [Real.Gamma_eq_integral (by linarith [ha i]), integral_Ici_eq_integral_Ioi]
  · intro i _
    exact integral_nonneg_of_ae ((ae_restrict_mem measurableSet_Ici).mono fun y hy => hnn i y hy)

lemma lintegral_exp_Ici (c : ℝ) :
    ∫⁻ s, (Ici c).indicator (fun s : ℝ => ENNReal.ofReal (Real.exp (-s))) s =
      ENNReal.ofReal (Real.exp (-c)) := by
  rw [lintegral_indicator measurableSet_Ici, ← setLIntegral_congr Ioi_ae_eq_Ici,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi c)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun _ _ => (Real.exp_pos _).le)),
    integral_exp_neg_Ioi]

noncomputable def f4 {m : ℕ} (a : Fin m → ℝ) (x : Fin m → ℝ) (s : ℝ) : ℝ≥0∞ :=
  if ∑ i, x i ≤ s then g4 a x * ENNReal.ofReal (Real.exp (-s)) else 0

lemma measurable_f4 {m : ℕ} (a : Fin m → ℝ) : Measurable (Function.uncurry (f4 a)) := by
  unfold f4 Function.uncurry
  refine Measurable.ite (measurableSet_le ?_ measurable_snd) ?_ measurable_const
  · exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp measurable_fst
  · exact ((measurable_g4 a).comp measurable_fst).mul
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_snd.neg))

lemma tonelli4 {m : ℕ} (a : Fin m → ℝ) :
    ∫⁻ x in S4 m, g4 a x * ENNReal.ofReal (Real.exp (-∑ i, x i)) =
      ∫⁻ s, ENNReal.ofReal (Real.exp (-s)) * F4 a s := by
  have h1 : ∫⁻ x in S4 m, g4 a x * ENNReal.ofReal (Real.exp (-∑ i, x i)) =
      ∫⁻ x in S4 m, ∫⁻ s, f4 a x s := by
    refine lintegral_congr (fun x => ?_)
    have : ∀ s, f4 a x s = g4 a x * (Ici (∑ i, x i)).indicator
        (fun s : ℝ => ENNReal.ofReal (Real.exp (-s))) s := by
      intro s
      unfold f4
      by_cases h : ∑ i, x i ≤ s
      · simp [h, indicator]
      · simp [h, indicator]
    simp_rw [this]
    have hm : Measurable ((Ici (∑ i, x i)).indicator
        (fun s : ℝ => ENNReal.ofReal (Real.exp (-s)))) :=
      (show Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-s))) from
        ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)).indicator
        measurableSet_Ici
    rw [lintegral_const_mul _ hm, lintegral_exp_Ici]
  rw [h1, lintegral_lintegral_swap (measurable_f4 a).aemeasurable]
  refine lintegral_congr (fun s => ?_)
  have : ∀ x, f4 a x s = {x : Fin m → ℝ | ∑ i, x i ≤ s}.indicator
      (fun x => g4 a x * ENNReal.ofReal (Real.exp (-s))) x := by
    intro x
    simp [f4, indicator]
  simp_rw [this]
  rw [lintegral_indicator (measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
    measurable_const), Measure.restrict_restrict (measurableSet_le
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const),
    lintegral_mul_const _ (measurable_g4 a), mul_comm, F4, Z4, inter_comm]

lemma F4_neg {m : ℕ} (a : Fin m → ℝ) {s : ℝ} (hs : s < 0) : F4 a s = 0 := by
  have : Z4 m s = ∅ := by
    ext x
    simp only [Z4, S4, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    exact lt_of_lt_of_le hs (Finset.sum_nonneg fun i _ => hx i)
  rw [F4, this]; simp

lemma key4 {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    F4 a 1 * ENNReal.ofReal (Real.Gamma (∑ i, a i + m + 1)) = ∏ i, ENNReal.ofReal (Real.Gamma (a i + 1)) := by
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  rw [← lintegral_D a ha, tonelli4]
  have h1 : ∫⁻ s, ENNReal.ofReal (Real.exp (-s)) * F4 a s =
      ∫⁻ s, (Ioi (0 : ℝ)).indicator (fun s => ENNReal.ofReal (Real.exp (-s)) *
        (ENNReal.ofReal (s ^ (∑ i, a i + m)) * F4 a 1)) s := by
    refine lintegral_congr_ae ?_
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with s hs
    have hs' : s ≠ 0 := hs
    rcases lt_or_gt_of_ne hs' with h | h
    · simp [F4_neg a h, indicator, not_lt.2 h.le]
    · simp [indicator, h, F4_scale a ha h]
  set p : ℝ := ∑ i, a i + m with hp
  have hp0 : 0 ≤ p := by positivity
  have h2 : ∀ s : ℝ, ENNReal.ofReal (Real.exp (-s)) * (ENNReal.ofReal (s ^ p) * F4 a 1) =
      ENNReal.ofReal (Real.exp (-s) * s ^ p) * F4 a 1 := by
    intro s
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hmeas : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-s) * s ^ p)) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp measurable_neg).mul
      (measurable_id.pow_const _))
  rw [h1, lintegral_indicator measurableSet_Ioi]
  simp_rw [h2]
  rw [lintegral_mul_const _ hmeas]
  have hG : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-s) * s ^ p) =
      ENNReal.ofReal (Real.Gamma (p + 1)) := by
    have hint : IntegrableOn (fun s : ℝ => Real.exp (-s) * s ^ p) (Ioi 0) := by
      have := Real.GammaIntegral_convergent (s := p + 1) (by linarith)
      simpa using this
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun s hs =>
        mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (le_of_lt hs) _))),
      Real.Gamma_eq_integral (by linarith)]
    simp
  rw [hG, mul_comm]

lemma lemma_4_23_aux (m : ℕ) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (t : ℝ) (ht : 0 < t) :
    ∫ x in {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t}, ∏ i, x i ^ a i =
      t ^ (∑ i, a i + m) * (∏ i, Real.Gamma (a i + 1)) / Real.Gamma (∑ i, a i + m + 1) := by
  have hset : {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ t} = Z4 m t := rfl
  have hA : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  have hGpos : ∀ i, 0 < Real.Gamma (a i + 1) := fun i => Real.Gamma_pos_of_pos (by linarith [ha i])
  have hGp : 0 < Real.Gamma (∑ i, a i + m + 1) := Real.Gamma_pos_of_pos (by positivity)
  rw [hset, integral_eq_lintegral_of_nonneg_ae]
  · have e1 : ∫⁻ x in Z4 m t, ENNReal.ofReal (∏ i, x i ^ a i) = F4 a t := by
      refine setLIntegral_congr_fun (measurableSet_Z4 m t) fun x hx => ?_
      rw [g4, ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hx.1 i) _)]
    rw [e1, F4_scale a ha ht]
    have := congrArg ENNReal.toReal (key4 a ha)
    rw [ENNReal.toReal_mul, ENNReal.toReal_prod, ENNReal.toReal_ofReal hGp.le] at this
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), eq_div_iff hGp.ne']
    have h3 : ∏ i, (ENNReal.ofReal (Real.Gamma (a i + 1))).toReal = ∏ i, Real.Gamma (a i + 1) :=
      Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (hGpos i).le
    rw [h3] at this
    rw [← this]
    ring
  · exact (ae_restrict_iff' (measurableSet_Z4 m t)).2 (Filter.Eventually.of_forall fun x hx =>
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx.1 i) _)
  · exact (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _).aestronglyMeasurable

end NumberFieldKB.MilneANT.Dirichlet4
