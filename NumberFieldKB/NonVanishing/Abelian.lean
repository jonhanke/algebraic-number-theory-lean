import NumberFieldKB.NonVanishing.Summation

/-!
# The Abelian half of the natural-order Euler product

$F$ is a number field; $v$ runs over the nonzero primes of $\mathcal O_F$, $N(v)$ = `normP v`; $|a(v)|\le1$.

* **`tendsto_tsum_nps_one_add`** (Abel's theorem for the Laplace transform of a step function): if
  $B(X) = \sum_{\log N(v)<X}a(v)/N(v)\to\ell$, then $\sum_va(v)N(v)^{-1-\sigma}\to\ell$ as $\sigma\to0^+$. *Proof:*
  $\sum_va(v)N(v)^{-1-\sigma} = \sigma\int_0^\infty B(t)e^{-\sigma t}\,dt = \int_0^\infty B(u/\sigma)e^{-u}\,du$
  (`integral_stepSum_mul_cexp`), and dominated convergence ($B$ is bounded).
* `remLog a s v` $= -\log(1-a(v)N(v)^{-s})-a(v)N(v)^{-s}$, with $|r_v(s)|\le N(v)^{-2}$ on $\operatorname{Re}s\ge1$
  (`norm_remLog_le`), so $\sum_vr_v(1+\sigma)\to\sum_vr_v(1)$ (`tendsto_tsum_remLog`).
* `prod_eulerFactor_one_eq`: $\prod_{N(v)\le X}(1-a(v)/N(v))^{-1} = \exp\bigl(B(\log(X+1))+\sum_{N(v)\le X}r_v(1)\bigr)$.
-/

open Complex MeasureTheory Set Filter Topology IsDedekindDomain NumberField
open QuadFormsKB.NFEuler

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The Abelian step (step 4 of the proof in `NaturalOrder.lean`) -/

/-- A convergent step sum is bounded. -/
theorem exists_norm_stepSum_le (b : HeightOneSpectrum (𝓞 F) → ℂ) {ℓ : ℂ}
    (hB : Tendsto (stepSum b) atTop (𝓝 ℓ)) : ∃ C : ℝ, ∀ t, ‖stepSum b t‖ ≤ C := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hB.norm.eventually (eventually_le_nhds (lt_add_one ‖ℓ‖)))
  refine ⟨max (‖ℓ‖ + 1) (∑ v ∈ primesNormLe F ⌊Real.exp T⌋₊, ‖b v‖), fun t => ?_⟩
  rcases le_or_gt T t with h | h
  · exact (hT t h).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    rw [stepSum_eq_sum_of_subset b (S := primesNormLe F ⌊Real.exp T⌋₊) fun v hv =>
      mem_primesNormLe_of_log_lt (hv.trans h)]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    split_ifs <;> simp

/-- **Abel's theorem for the Laplace transform of the step function**: if $\sum_{\log N(v)<X}a(v)/N(v)\to\ell$, then
$\sum_va(v)N(v)^{-1-\sigma}\to\ell$ as $\sigma\to0^+$. -/
theorem tendsto_tsum_nps_one_add {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {ℓ : ℂ}
    (hB : Tendsto (stepSum fun v => a v / (normP v : ℂ)) atTop (𝓝 ℓ)) :
    Tendsto (fun σ : ℝ => ∑' v, a v * nps v (1 + σ)) (𝓝[>] 0) (𝓝 ℓ) := by
  obtain ⟨C, hC⟩ := exists_norm_stepSum_le (fun v => a v / (normP v : ℂ)) hB
  set B := stepSum fun v => a v / (normP v : ℂ) with hBdef
  have hBm : Measurable B := measurable_stepSum _
  have key : ∀ σ : ℝ, 0 < σ →
      ∑' v, a v * nps v (1 + σ) = ∫ u in Ioi (0 : ℝ), B (u / σ) * cexp (-(u : ℂ)) := by
    intro σ hσ
    have hsum : Summable fun v => ‖a v / (normP v : ℂ)‖ * (normP v : ℝ) ^ (-((σ : ℂ)).re) := by
      refine (summable_normP_rpow (σ := 1 + σ) (by linarith)).of_nonneg_of_le (fun v => ?_) (fun v => ?_)
      · exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (normP_pos' v).le _)
      · rw [ofReal_re, norm_div, Complex.norm_natCast, show -(1 + σ) = -1 + -σ by ring,
          Real.rpow_add (normP_pos' v), Real.rpow_neg_one]
        have h1 : ‖a v‖ ≤ 1 := ha v
        have h2 : 0 ≤ (normP v : ℝ) ^ (-σ) := Real.rpow_nonneg (normP_pos' v).le _
        have h3 : 0 < (normP v : ℝ) := normP_pos' v
        rw [div_eq_mul_inv]
        calc ‖a v‖ * (normP v : ℝ)⁻¹ * (normP v : ℝ) ^ (-σ)
            ≤ 1 * (normP v : ℝ)⁻¹ * (normP v : ℝ) ^ (-σ) := by gcongr
          _ = _ := by ring
    have h := integral_stepSum_mul_cexp (fun v => a v / (normP v : ℂ)) (w := (σ : ℂ))
      (by simpa using hσ) hsum
    have hterm : ∀ v, a v / (normP v : ℂ) * nps v (σ : ℂ) = a v * nps v (1 + σ) := by
      intro v
      have hne : (((normP v : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (normP_pos' v).ne'
      simp only [nps]
      rw [neg_add,cpow_add _ _ hne, cpow_neg_one, ofReal_natCast]
      ring
    simp only [hterm] at h
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ.ne'
    have h' := integral_comp_mul_left_Ioi' (fun u : ℝ => B (u / σ) * cexp (-(u : ℂ))) 0 hσ
    rw [mul_zero] at h'
    rw [← h']
    have e : (fun x : ℝ => B (σ * x / σ) * cexp (-((σ * x : ℝ) : ℂ))) =
        fun x => B x * cexp (-((σ : ℂ) * x)) := by
      funext x
      rw [mul_div_cancel_left₀ _ hσ.ne']
      push_cast; rfl
    simp only [e]
    rw [h, real_smul]
    field_simp
  have hmain : Tendsto (fun σ : ℝ => ∫ u in Ioi (0 : ℝ), B (u / σ) * cexp (-(u : ℂ))) (𝓝[>] 0)
      (𝓝 (∫ u in Ioi (0 : ℝ), ℓ * cexp (-(u : ℂ)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun u => C * Real.exp (-u)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun σ => ?_
      exact ((hBm.comp (measurable_id.div_const σ)).mul (by fun_prop)).aestronglyMeasurable
    · refine Eventually.of_forall fun σ => ae_restrict_of_forall_mem measurableSet_Ioi fun u _ => ?_
      rw [norm_mul, Complex.norm_exp]
      simp only [neg_re, ofReal_re]
      exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le
    · exact (integrableOn_exp_neg_Ioi 0).const_mul C
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have h1 : Tendsto (fun σ : ℝ => u / σ) (𝓝[>] 0) atTop := by
        simpa [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop (mem_Ioi.mp hu)
      exact (hB.comp h1).mul_const _
  have hval : ∫ u in Ioi (0 : ℝ), ℓ * cexp (-(u : ℂ)) = ℓ := by
    rw [MeasureTheory.integral_const_mul]
    have : ∀ u : ℝ, cexp (-(u : ℂ)) = ((Real.exp (-u) : ℝ) : ℂ) := fun u => by push_cast; rfl
    simp only [this]
    rw [show (∫ u in Ioi (0 : ℝ), ((Real.exp (-u) : ℝ) : ℂ)) =
      ((∫ u in Ioi (0 : ℝ), Real.exp (-u) : ℝ) : ℂ) from integral_ofReal, integral_exp_neg_Ioi_zero]
    simp
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (key σ hσ).symm

/-! ### The remainder of the logarithm -/

/-- The remainder $r_v(s) = -\log(1-a(v)N(v)^{-s})-a(v)N(v)^{-s}$. -/
def remLog (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  -log (1 - a v * nps v s) - a v * nps v s

theorem norm_remLog_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re)
    (v : HeightOneSpectrum (𝓞 F)) : ‖remLog a s v‖ ≤ (normP v : ℝ) ^ (-(2 : ℝ)) := by
  set w := a v * nps v s with hw
  have hN : (1 : ℝ) ≤ normP v := by have := two_le_normP v; exact_mod_cast (by omega : 1 ≤ normP v)
  have h1 : ‖w‖ ≤ (normP v : ℝ) ^ (-(1 : ℝ)) := by
    rw [hw, norm_mul, norm_nps]
    calc ‖a v‖ * (normP v : ℝ) ^ (-s.re) ≤ 1 * (normP v : ℝ) ^ (-(1 : ℝ)) := by
          exact mul_le_mul (ha v) (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
            (Real.rpow_nonneg (normP_pos' v).le _) zero_le_one
      _ = _ := one_mul _
  have h2 : ‖w‖ ≤ 1 / 2 := norm_mul_nps_le_half ha v hs
  have h3 := Complex.norm_log_one_add_sub_self_le (z := -w) (by rw [norm_neg]; linarith)
  rw [norm_neg] at h3
  have e : remLog a s v = -(log (1 + -w) - -w) := by simp only [remLog, ← hw]; ring_nf
  rw [e, norm_neg]
  refine h3.trans ?_
  have h4 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h5 : ‖w‖ ^ 2 ≤ (normP v : ℝ) ^ (-(2 : ℝ)) := by
    calc ‖w‖ ^ 2 ≤ ((normP v : ℝ) ^ (-(1 : ℝ))) ^ 2 := by gcongr
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul (normP_pos' v).le]; norm_num
  have h6 : 0 ≤ ‖w‖ ^ 2 := by positivity
  nlinarith

theorem summable_remLog {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    Summable (remLog a s) :=
  Summable.of_norm_bounded (summable_normP_rpow (σ := 2) (by norm_num)) (norm_remLog_le ha hs)

theorem tendsto_tsum_remLog {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) :
    Tendsto (fun σ : ℝ => ∑' v, remLog a (1 + σ) v) (𝓝[>] 0) (𝓝 (∑' v, remLog a 1 v)) := by
  have hb : ∀ᶠ σ : ℝ in 𝓝[>] 0, ∀ v, ‖remLog a (1 + σ) v‖ ≤ (normP v : ℝ) ^ (-(2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ v
    exact norm_remLog_le ha (by simpa using le_of_lt hσ) v
  have hs2 : Summable fun v : HeightOneSpectrum (𝓞 F) => (normP v : ℝ) ^ (-(2 : ℝ)) :=
    summable_normP_rpow (σ := 2) (by norm_num)
  refine tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ)) (f := fun σ v => remLog a (1 + σ) v)
    (g := fun v => remLog a 1 v) hs2 (fun v => ?_) hb
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  have hw : ‖a v * nps v 1‖ < 1 := lt_of_le_of_lt (norm_mul_nps_le_half ha v le_rfl) (by norm_num)
  have hslit : 1 - a v * nps v 1 ∈ slitPlane := by
    have : 0 < (1 - a v * nps v 1).re := by
      have := Complex.abs_re_le_norm (a v * nps v 1)
      have := neg_abs_le (a v * nps v 1).re
      have := le_abs_self (a v * nps v 1).re
      rw [sub_re, one_re]; linarith
    exact mem_slitPlane_iff.mpr (Or.inl this)
  have hcont : ContinuousAt (fun σ : ℝ => nps v (1 + (σ : ℂ))) 0 := by
    unfold nps
    refine ContinuousAt.cpow continuousAt_const (by fun_prop) (Or.inl ?_)
    simpa using normP_pos' v
  have hm : ContinuousAt (fun σ : ℝ => 1 - a v * nps v (1 + (σ : ℂ))) 0 := by fun_prop
  have hl : ContinuousAt (fun σ : ℝ => log (1 - a v * nps v (1 + (σ : ℂ)))) 0 := by
    refine ContinuousAt.comp (g := log) ?_ hm
    simpa using continuousAt_clog (by simpa using hslit)
  have hc : ContinuousAt (fun σ : ℝ => remLog a (1 + σ) v) 0 := by
    unfold remLog
    fun_prop
  simpa [remLog] using hc.tendsto

/-- The partial products at $s = 1$: $\prod_{N(v)\le X}(1-a(v)/N(v))^{-1} = \exp\bigl(B(\log(X+1))+\sum_{N(v)\le X}r_v(1)\bigr)$. -/
theorem prod_eulerFactor_one_eq (a : HeightOneSpectrum (𝓞 F) → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1) (X : ℕ) :
    ∏ v ∈ primesNormLe F X, eulerFactor a 1 v =
      cexp (stepSum (fun v => a v / (normP v : ℂ)) (Real.log (X + 1)) + ∑ v ∈ primesNormLe F X, remLog a 1 v) := by
  have hB : stepSum (fun v => a v / (normP v : ℂ)) (Real.log (X + 1)) =
      ∑ v ∈ primesNormLe F X, a v * nps v 1 := by
    have := stepSum_of_forall (fun v => a v / (normP v : ℂ)) (t := Real.log (X + 1))
      (S := primesNormLe F X) (fun v => ?_)
    · rw [this]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [nps]
      rw [cpow_neg_one,ofReal_natCast, div_eq_mul_inv]
    · rw [mem_primesNormLe, Real.log_lt_log_iff (normP_pos' v) (by positivity)]
      constructor
      · intro h
        have : (normP v : ℝ) ≤ X := by exact_mod_cast h
        linarith
      · intro h
        have h' : (normP v : ℝ) < (X : ℝ) + 1 := h
        have : normP v < X + 1 := by exact_mod_cast h'
        omega
  rw [hB, ← Finset.sum_add_distrib, Complex.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  have e : a v * nps v 1 + remLog a 1 v = -log (1 - a v * nps v 1) := by simp only [remLog]; ring
  rw [e, eulerFactor, Complex.exp_neg, Complex.exp_log (one_sub_mul_nps_ne_zero ha v (by simp))]

end

end NumberFieldKB.NonVanishing
