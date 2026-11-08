import NumberFieldKB.NonVanishing.Euler

/-!
# Sums over the primes of a number field: partial summation, Chebyshev's bound, Laplace transforms

$F$ is a number field; $v$ runs over the nonzero primes of $\mathcal O_F$, $\lambda_v = \log N(v)$.

* `sum_mul_eq_sub_integral`: **partial summation** with real thresholds: for a finite set $S$ with
  $\alpha\le\lambda_i\le X$ and $w$ differentiable,
  $\sum_{i\in S}b_iw(\lambda_i) = \bigl(\sum_{i\in S}b_i\bigr)w(X)-\int_\alpha^X\bigl(\sum_{\lambda_i<u}b_i\bigr)w'(u)\,du$.
* **`stepSum b t`** $=\sum_{\log N(v)<t}b(v)$, a measurable step function of $t$ (`measurable_stepSum`).
* **Chebyshev's bound over $F$** (`sum_log_normP_le`): $\sum_{N(v)\le n}\log N(v)\le d^2\log4\cdot n$, $d = [F:\mathbb Q]$
  (at most $d$ primes over each $p$, `QuadFormsKB.NFEuler.card_le_finrank`, each with $N(v)\le p^d$; Mathlib's
  `Chebyshev.theta_le_log4_mul_x`).
* **The Laplace transform of the step function** (`integral_stepSum_mul_cexp`): for $\operatorname{Re}w>0$ and
  $\sum_v|b(v)|N(v)^{-\operatorname{Re}w}<\infty$,
  $\int_0^\infty\mathrm{stepSum}\,b(t)\,e^{-wt}\,dt = w^{-1}\sum_vb(v)N(v)^{-w}$.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral IsDedekindDomain NumberField
open QuadFormsKB.NFEuler
open scoped Interval

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Partial summation with real thresholds -/

theorem integral_ite_lt_eq {g : ℝ → ℂ} {α X l : ℝ} (hl : α ≤ l ∧ l ≤ X) (hg : IntervalIntegrable g volume α X) :
    ∫ u in α..X, (if l < u then g u else 0) = ∫ u in l..X, g u := by
  have hfun : (fun u => if l < u then g u else 0) = (Ioi l).indicator g := by
    funext u; simp [Set.indicator_apply]
  have hind : IntervalIntegrable ((Ioi l).indicator g) volume α X := by
    rw [intervalIntegrable_iff] at hg ⊢
    exact hg.indicator measurableSet_Ioi
  have hlmem : l ∈ [[α, X]] := by rw [uIcc_of_le (hl.1.trans hl.2)]; exact hl
  rw [hfun, ← intervalIntegral.integral_add_adjacent_intervals (b := l)
    (hind.mono_set (uIcc_subset_uIcc left_mem_uIcc hlmem)) (hind.mono_set (uIcc_subset_uIcc hlmem right_mem_uIcc))]
  have h1 : ∫ u in α..l, (Ioi l).indicator g u = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℂ)) (Eventually.of_forall fun u hu => ?_)]
    · simp
    · rw [uIoc_of_le hl.1] at hu
      exact Set.indicator_of_notMem (fun h => (not_lt.mpr hu.2) h) _
  have h2 : ∫ u in l..X, (Ioi l).indicator g u = ∫ u in l..X, g u := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun u hu => ?_)
    rw [uIoc_of_le hl.2] at hu
    exact Set.indicator_of_mem hu.1 _
  rw [h1, h2, zero_add]

/-- **Partial summation** with real thresholds. -/
theorem sum_mul_eq_sub_integral {ι : Type*} (S : Finset ι) (b : ι → ℂ) (lam : ι → ℝ) {α X : ℝ}
    (hlam : ∀ i ∈ S, α ≤ lam i ∧ lam i ≤ X) {w w' : ℝ → ℂ}
    (hw : ∀ u ∈ [[α, X]], HasDerivAt w (w' u) u) (hw' : IntervalIntegrable w' volume α X) :
    ∑ i ∈ S, b i * w (lam i) =
      (∑ i ∈ S, b i) * w X - ∫ u in α..X, (∑ i ∈ S, if lam i < u then b i else 0) * w' u := by
  have hint : ∀ i ∈ S, ∫ u in α..X, (if lam i < u then b i * w' u else 0) = b i * (w X - w (lam i)) := by
    intro i hi
    have hlmem : lam i ∈ [[α, X]] := by rw [uIcc_of_le ((hlam i hi).1.trans (hlam i hi).2)]; exact hlam i hi
    rw [integral_ite_lt_eq (hlam i hi) (hw'.const_mul (b i)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hw u (uIcc_subset_uIcc hlmem right_mem_uIcc hu))
        (hw'.mono_set (uIcc_subset_uIcc hlmem right_mem_uIcc))]
  have hii : ∀ i ∈ S, IntervalIntegrable (fun u => if lam i < u then b i * w' u else 0) volume α X := by
    intro i _
    have hfun : (fun u => if lam i < u then b i * w' u else 0) = (Ioi (lam i)).indicator (fun u => b i * w' u) := by
      funext u; simp [Set.indicator_apply]
    rw [hfun]
    have h := hw'.const_mul (b i)
    rw [intervalIntegrable_iff] at h ⊢
    exact h.indicator measurableSet_Ioi
  have hfun : (fun u => (∑ i ∈ S, if lam i < u then b i else 0) * w' u) =
      fun u => ∑ i ∈ S, (if lam i < u then b i * w' u else 0) := by
    funext u; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => ?_; split_ifs <;> simp
  rw [hfun, intervalIntegral.integral_finsetSum hii, Finset.sum_congr rfl hint, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {F : Type} [Field F] [NumberField F]

/-! ### The step function $\sum_{\log N(v)<t}b(v)$ -/

/-- The nonzero primes of $\mathcal O_F$ form a countable set (finitely many of norm $\le n$ for each $n$). -/
instance : Countable (HeightOneSpectrum (𝓞 F)) := by
  have h : (Set.univ : Set (HeightOneSpectrum (𝓞 F))) = ⋃ n : ℕ, {v | normP v ≤ n} := by
    ext v; simp only [mem_univ, mem_iUnion, mem_ofPred_eq, true_iff]; exact ⟨normP v, le_rfl⟩
  exact Set.countable_univ_iff.mp (h ▸ Set.countable_iUnion fun n => (finite_normP_le n).countable)

theorem mem_primesNormLe_of_log_lt {v : HeightOneSpectrum (𝓞 F)} {t : ℝ} (h : Real.log (normP v) < t) :
    v ∈ primesNormLe F ⌊Real.exp t⌋₊ := by
  rw [mem_primesNormLe]
  refine Nat.le_floor ?_
  have := Real.exp_lt_exp.mpr h
  rw [Real.exp_log (normP_pos' v)] at this
  exact this.le

/-- **The step function** $t\mapsto\sum_{\log N(v)<t}b(v)$. -/
def stepSum (b : HeightOneSpectrum (𝓞 F) → ℂ) (t : ℝ) : ℂ :=
  ∑ v ∈ primesNormLe F ⌊Real.exp t⌋₊, if Real.log (normP v) < t then b v else 0

theorem stepSum_eq_sum_of_subset (b : HeightOneSpectrum (𝓞 F) → ℂ) {t : ℝ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v, Real.log (normP v) < t → v ∈ S) :
    stepSum b t = ∑ v ∈ S, if Real.log (normP v) < t then b v else 0 := by
  unfold stepSum
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext v
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨hS v h.2, h.2⟩, fun h => ⟨mem_primesNormLe_of_log_lt h.2, h.2⟩⟩

theorem stepSum_eq_tsum (b : HeightOneSpectrum (𝓞 F) → ℂ) (t : ℝ) :
    stepSum b t = ∑' v, if Real.log (normP v) < t then b v else 0 :=
  (tsum_eq_sum fun v hv => if_neg fun h => hv (mem_primesNormLe_of_log_lt h)).symm

/-- `stepSum b` is measurable (a pointwise limit of finite sums of indicator functions). -/
theorem measurable_stepSum (b : HeightOneSpectrum (𝓞 F) → ℂ) : Measurable (stepSum b) := by
  have hn : ∀ n : ℕ, Measurable fun t : ℝ => ∑ v ∈ primesNormLe F n,
      if Real.log (normP v) < t then b v else 0 := fun n =>
    Finset.measurable_sum _ fun v _ => Measurable.ite (measurableSet_Ioi (a := Real.log (normP v)))
      measurable_const measurable_const
  refine measurable_of_tendsto_metrizable hn (tendsto_pi_nhds.mpr fun t => ?_)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌊Real.exp t⌋₊] with n hn
  refine stepSum_eq_sum_of_subset b fun v hv => ?_
  have := mem_primesNormLe_of_log_lt hv
  rw [mem_primesNormLe] at this ⊢
  omega

theorem stepSum_of_forall (b : HeightOneSpectrum (𝓞 F) → ℂ) {t : ℝ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v, v ∈ S ↔ Real.log (normP v) < t) : stepSum b t = ∑ v ∈ S, b v := by
  rw [stepSum_eq_sum_of_subset b (S := S) fun v h => (hS v).mpr h]
  exact Finset.sum_congr rfl fun v hv => if_pos ((hS v).mp hv)

/-! ### Chebyshev's bound over $F$ -/

/-- **Chebyshev's bound over $F$**: $\sum_{N(v)\le n}\log N(v)\le d^2\log4\cdot n$, $d = [F:\mathbb Q]$. -/
@[kb "neukirch1999" "Ch. VII, §13 (Chebyshev-type bound for the primes of K) [unverified locator]"]
theorem sum_log_normP_le (n : ℕ) :
    ∑ v ∈ primesNormLe F n, Real.log (normP v) ≤ (Module.finrank ℚ F : ℝ) ^ 2 * Real.log 4 * n := by
  set d : ℕ := Module.finrank ℚ F
  set S := primesNormLe F n
  set T : Finset ℕ := (Finset.Ioc 0 n).filter Nat.Prime
  have hmaps : ∀ v ∈ S, (primeBelow v : ℕ) ∈ T := fun v hv => by
    rw [mem_primesNormLe] at hv
    simp only [T, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨(primeBelow v).2.pos, (primeBelow_le_normP v).trans hv⟩, (primeBelow v).2⟩
  have hlog : ∀ v : HeightOneSpectrum (𝓞 F), Real.log (normP v) ≤ d * Real.log (primeBelow v : ℕ) := by
    intro v
    have h := normP_le_pow_finrank v
    have hp : (0 : ℝ) < (primeBelow v : ℕ) := by exact_mod_cast (primeBelow v).2.pos
    calc Real.log (normP v) ≤ Real.log (((primeBelow v : ℕ) : ℝ) ^ d) :=
          Real.log_le_log (normP_pos' v) (by exact_mod_cast h)
      _ = d * Real.log (primeBelow v : ℕ) := by rw [Real.log_pow]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ p ∈ T, ∑ v ∈ S with (primeBelow v : ℕ) = p, Real.log (normP v) ≤
      (d : ℝ) ^ 2 * Real.log p := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hcard : (S.filter fun v => (primeBelow v : ℕ) = p).card ≤ d :=
      card_le_finrank ⟨p, hpp⟩ _ fun v hv => Subtype.ext (Finset.mem_filter.mp hv).2
    calc ∑ v ∈ S with (primeBelow v : ℕ) = p, Real.log (normP v)
        ≤ ∑ v ∈ S with (primeBelow v : ℕ) = p, (d : ℝ) * Real.log p :=
          Finset.sum_le_sum fun v hv => by rw [← (Finset.mem_filter.mp hv).2]; exact hlog v
      _ = (S.filter fun v => (primeBelow v : ℕ) = p).card * ((d : ℝ) * Real.log p) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ d * ((d : ℝ) * Real.log p) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
            (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
      _ = (d : ℝ) ^ 2 * Real.log p := by ring
  calc ∑ p ∈ T, ∑ v ∈ S with (primeBelow v : ℕ) = p, Real.log (normP v)
      ≤ ∑ p ∈ T, (d : ℝ) ^ 2 * Real.log p := Finset.sum_le_sum hfib
    _ = (d : ℝ) ^ 2 * Chebyshev.theta n := by
        rw [← Finset.mul_sum, Chebyshev.theta, Nat.floor_natCast]
    _ ≤ (d : ℝ) ^ 2 * (Real.log 4 * n) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) (by positivity)
    _ = _ := by ring

/-- The constant of Chebyshev's bound, $d^2\log 4$. -/
def chebConst (F : Type) [Field F] [NumberField F] : ℝ := (Module.finrank ℚ F : ℝ) ^ 2 * Real.log 4

theorem chebConst_nonneg : 0 ≤ chebConst F := by
  unfold chebConst; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity

/-- $\bigl|\sum_{\log N(v)<t}a(v)\log N(v)\bigr|\le d^2\log4\cdot e^t$ for $|a|\le1$. -/
theorem norm_stepSum_log_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) (t : ℝ) :
    ‖stepSum (fun v => a v * Real.log (normP v)) t‖ ≤ chebConst F * Real.exp t := by
  unfold stepSum
  refine (norm_sum_le _ _).trans ?_
  have hlog0 : ∀ v : HeightOneSpectrum (𝓞 F), 0 ≤ Real.log (normP v) := fun v =>
    Real.log_nonneg (by have := two_le_normP v; exact_mod_cast (by omega : 1 ≤ normP v))
  calc ∑ v ∈ primesNormLe F ⌊Real.exp t⌋₊,
        ‖if Real.log (normP v) < t then a v * Real.log (normP v) else 0‖
      ≤ ∑ v ∈ primesNormLe F ⌊Real.exp t⌋₊, Real.log (normP v) := by
        refine Finset.sum_le_sum fun v _ => ?_
        split_ifs
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlog0 v)]
          exact mul_le_of_le_one_left (hlog0 v) (ha v)
        · simpa using hlog0 v
    _ ≤ chebConst F * ⌊Real.exp t⌋₊ := sum_log_normP_le _
    _ ≤ chebConst F * Real.exp t :=
        mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos t).le) chebConst_nonneg

/-! ### The Laplace transform of the step function -/

theorem cexp_neg_mul_log (v : HeightOneSpectrum (𝓞 F)) (w : ℂ) :
    cexp (-(w * Real.log (normP v))) = nps v w := by
  rw [nps, cpow_def_of_ne_zero (by exact_mod_cast (normP_pos' v).ne'), ← ofReal_log (normP_pos' v).le]
  ring_nf

/-- **The Laplace transform of `stepSum b`**: $\int_0^\infty\mathrm{stepSum}\,b(t)e^{-wt}\,dt = w^{-1}\sum_vb(v)N(v)^{-w}$. -/
theorem integral_stepSum_mul_cexp (b : HeightOneSpectrum (𝓞 F) → ℂ) {w : ℂ} (hw : 0 < w.re)
    (hb : Summable fun v => ‖b v‖ * (normP v : ℝ) ^ (-w.re)) :
    ∫ t in Ioi (0 : ℝ), stepSum b t * cexp (-(w * t)) = (∑' v, b v * nps v w) / w := by
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; exact lt_irrefl 0 hw
  set G : HeightOneSpectrum (𝓞 F) → ℝ → ℂ := fun v =>
    (Ioi (Real.log (normP v))).indicator fun t => b v * cexp (-(w * t))
  have hlogpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Real.log (normP v) := fun v =>
    Real.log_pos (by have := two_le_normP v; exact_mod_cast (by omega : 1 < normP v))
  have h1 : ∀ t, stepSum b t * cexp (-(w * t)) = ∑' v, G v t := by
    intro t
    rw [stepSum_eq_tsum, ← tsum_mul_right]
    refine tsum_congr fun v => ?_
    simp only [G, Set.indicator_apply, mem_Ioi]
    split_ifs <;> simp
  have hon : ∀ v : HeightOneSpectrum (𝓞 F), IntegrableOn (fun t : ℝ => b v * cexp (-(w * t)))
      (Ioi (Real.log (normP v))) := fun v => by
    have := (integrableOn_exp_mul_complex_Ioi (a := -w) (by simpa using hw) (Real.log (normP v))).const_mul (b v)
    exact IntegrableOn.congr_fun this (fun t _ => by simp only [neg_mul]) measurableSet_Ioi
  have hInt : ∀ v, Integrable (G v) (volume.restrict (Ioi 0)) := fun v =>
    (integrable_indicator_iff measurableSet_Ioi).mpr ((hon v).mono_measure Measure.restrict_le_self)
  have hset : ∀ v : HeightOneSpectrum (𝓞 F), Ioi (0 : ℝ) ∩ Ioi (Real.log (normP v)) = Ioi (Real.log (normP v)) :=
    fun v => by rw [Ioi_inter_Ioi, max_eq_right (hlogpos v).le]
  have hint : ∀ v, ∫ t in Ioi (0 : ℝ), G v t = b v * nps v w / w := fun v => by
    simp only [G]
    rw [setIntegral_indicator measurableSet_Ioi, hset, MeasureTheory.integral_const_mul]
    have := integral_exp_mul_complex_Ioi (a := -w) (by simpa using hw) (Real.log (normP v))
    simp only [neg_mul] at this
    rw [this, neg_div_neg_eq, cexp_neg_mul_log]
    ring
  have hnorm : ∀ v, ∫ t in Ioi (0 : ℝ), ‖G v t‖ = ‖b v‖ * (normP v : ℝ) ^ (-w.re) / w.re := fun v => by
    simp only [G, norm_indicator_eq_indicator_norm]
    rw [setIntegral_indicator measurableSet_Ioi, hset]
    have hn : ∀ t : ℝ, ‖b v * cexp (-(w * t))‖ = ‖b v‖ * Real.exp (-w.re * t) := fun t => by
      rw [norm_mul, Complex.norm_exp]; simp
    simp only [hn]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi (by linarith), neg_div_neg_eq,
      Real.rpow_def_of_pos (normP_pos' v)]
    ring_nf
  have hsum : Summable fun v => ∫ t in Ioi (0 : ℝ), ‖G v t‖ := by
    simp only [hnorm]
    exact hb.div_const _
  rw [integral_congr_ae (Eventually.of_forall h1), ← integral_tsum_of_summable_integral_norm hInt hsum]
  simp only [hint]
  rw [tsum_div_const]

end

end NumberFieldKB.NonVanishing
