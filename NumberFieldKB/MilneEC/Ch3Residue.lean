import NumberFieldKB.MilneEC.Ch3Defs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Milne, Elliptic Curves, Chapter III: residues and the residue theorem for rectangles

Infrastructure for Proposition 2.1 of Chapter III of Milne, *Elliptic Curves* (`milne2006ec`):
Milne cites the residue theorem (Cartan 1963, III 5.2).  Mathlib has Cauchy's theorem for
rectangles (`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`) but no
residues; this file defines nothing new beyond `residue` (in `Ch3Defs.lean`) and proves:

* `residue_eq_circleIntegral`: for `f` meromorphic at `p`, the circle integral defining the
  residue is constant for small radii;
* `exists_principalPart`, `residue_eq_of_principalPart`: Laurent principal parts and the residue
  as the coefficient of `(z - p)⁻¹`;
* the residue of a logarithmic derivative is the order (`residue_logDeriv`);
* `rectIntegral_eq_two_pi_I_mul_sum_residue`: the residue theorem for a rectangle;
* `rectIntegral_eq_zero_of_periodic`: the integral round a period rectangle of a function
  with periods `1` and `τ` vanishes.
-/

open Complex Set Filter Topology MeasureTheory Real

namespace NumberFieldKB.MilneEC.III

variable {f g : ℂ → ℂ} {p : ℂ}

/-! ### Residues -/

/-! #### Helpers -/

lemma residue_eq_of_eventually {c : ℂ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), (2 * π * I)⁻¹ * ∮ z in C(p, r), f z = c) :
    residue f p = c := by
  unfold residue
  exact (tendsto_const_nhds.congr' (h.mono fun r hr => hr.symm)).limUnder_eq

lemma exists_ball_of_nhdsNE {P : ℂ → Prop} (h : ∀ᶠ z in 𝓝[≠] p, P z) :
    ∃ ε > 0, ∀ z, z ≠ p → dist z p < ε → P z := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨ε, hε, h⟩ := h
  exact ⟨ε, hε, fun z hz hd => h hd hz⟩

lemma dist_eq_of_mem_sphere {z : ℂ} {r : ℝ} (hz : z ∈ Metric.sphere p r) :
    dist z p = r := hz

lemma ne_of_mem_sphere {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ Metric.sphere p r) : z ≠ p := by
  intro h
  have := dist_eq_of_mem_sphere hz
  rw [h, dist_self] at this
  linarith

lemma continuousOn_term (c : ℂ) (m : ℤ) {r : ℝ} (hr : 0 < r) :
    ContinuousOn (fun z : ℂ => c * (z - p) ^ m) (Metric.sphere p r) := by
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const)
  intro z hz
  left
  exact sub_ne_zero.mpr (ne_of_mem_sphere hr hz)

lemma analyticAt_circleIntegral_zero {h : ℂ → ℂ} (hh : AnalyticAt ℂ h p) :
    ∃ ε > 0, ∀ r ∈ Ioo 0 ε, CircleIntegrable h p r ∧ ∮ z in C(p, r), h z = 0 := by
  obtain ⟨ε, hε, hd⟩ := Metric.eventually_nhds_iff.mp hh.eventually_analyticAt
  refine ⟨ε, hε, fun r hr => ?_⟩
  have hcb : Metric.closedBall p r ⊆ Metric.ball p ε := Metric.closedBall_subset_ball hr.2
  have hcont : ContinuousOn h (Metric.closedBall p r) := fun z hz =>
    (hd (Metric.mem_ball.mp (hcb hz))).continuousAt.continuousWithinAt
  refine ⟨ContinuousOn.circleIntegrable hr.1.le (hcont.mono ?_), ?_⟩
  · exact Metric.sphere_subset_closedBall
  · exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.1.le
      countable_empty hcont (fun z hz =>
        (hd (Metric.mem_ball.mp (hcb (Metric.ball_subset_closedBall hz.1)))).differentiableAt)

lemma circleIntegral_principalPart (n : ℕ) (c : ℕ → ℂ) {r : ℝ} (hr : 0 < r) :
    ∮ z in C(p, r), (∑ k ∈ Finset.range n, c k * (z - p) ^ (-((k : ℤ) + 1))) =
      2 * π * I * (if 0 < n then c 0 else 0) := by
  have hint : ∀ k ∈ Finset.range n,
      CircleIntegrable (fun z => c k * (z - p) ^ (-((k : ℤ) + 1))) p r := fun k _ =>
    ContinuousOn.circleIntegrable hr.le (continuousOn_term _ _ hr)
  rw [circleIntegral.integral_fun_sum hint]
  have hk : ∀ k ∈ Finset.range n, (∮ z in C(p, r), c k * (z - p) ^ (-((k : ℤ) + 1))) =
      if k = 0 then 2 * π * I * c 0 else 0 := by
    intro k _
    rw [circleIntegral.integral_const_mul]
    by_cases h0 : k = 0
    · subst h0
      simp only [Nat.cast_zero, zero_add, if_true, zpow_neg, zpow_one]
      rw [circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hr)]
      ring
    · rw [circleIntegral.integral_sub_zpow_of_ne, if_neg h0, mul_zero]
      omega
  rw [Finset.sum_congr rfl hk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_pos hn, Finset.sum_ite_eq' (Finset.range n) 0 (fun _ => 2 * π * I * c 0)]
    simp [hn]

lemma residue_eq_ite {n : ℕ} {c : ℕ → ℂ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h p)
    (hf : ∀ᶠ z in 𝓝[≠] p, f z = (∑ k ∈ Finset.range n, c k * (z - p) ^ (-((k : ℤ) + 1))) + h z) :
    ∃ ε > 0, ∀ r ∈ Ioo 0 ε, (2 * π * I)⁻¹ * ∮ z in C(p, r), f z = if 0 < n then c 0 else 0 := by
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_ball_of_nhdsNE hf
  obtain ⟨ε₂, hε₂, h₂⟩ := analyticAt_circleIntegral_zero hh
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r hr => ?_⟩
  have hr0 : 0 < r := hr.1
  have hsph : EqOn f (fun z => (∑ k ∈ Finset.range n, c k * (z - p) ^ (-((k : ℤ) + 1))) + h z)
      (Metric.sphere p r) := by
    intro z hz
    have hd : dist z p = r := hz
    apply h₁ z _ (hd ▸ lt_of_lt_of_le hr.2 (min_le_left _ _))
    intro hzp
    rw [hzp, dist_self] at hd
    linarith
  rw [circleIntegral.integral_congr hr0.le hsph]
  have hQ : CircleIntegrable (fun z => ∑ k ∈ Finset.range n, c k * (z - p) ^ (-((k : ℤ) + 1))) p r :=
    ContinuousOn.circleIntegrable hr0.le
      (continuousOn_finsetSum _ (fun k _ => continuousOn_term _ _ hr0))
  have h₂r := h₂ r ⟨hr0, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩
  rw [circleIntegral.integral_add hQ h₂r.1, h₂r.2, circleIntegral_principalPart n c hr0, add_zero]
  have : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [inv_mul_cancel_left₀ this]

/-- Taylor expansion with analytic remainder. -/
lemma exists_taylor {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p) (N : ℕ) :
    ∃ (a : ℕ → ℂ) (k : ℂ → ℂ), AnalyticAt ℂ k p ∧
      ∀ z, g z = (∑ j ∈ Finset.range N, a j * (z - p) ^ j) + (z - p) ^ N * k z := by
  induction N with
  | zero => exact ⟨fun _ => 0, g, hg, fun z => by simp⟩
  | succ N ih =>
    obtain ⟨a, k, hk, hz⟩ := ih
    obtain ⟨ps, hps⟩ := hk
    have hk' : AnalyticAt ℂ (dslope k p) p := (hps.has_fpower_series_dslope_fslope).analyticAt
    refine ⟨fun j => if j = N then k p else a j, dslope k p, hk', fun z => ?_⟩
    rw [Finset.sum_range_succ, hz z]
    have hs : ∑ j ∈ Finset.range N, (if j = N then k p else a j) * (z - p) ^ j =
        ∑ j ∈ Finset.range N, a j * (z - p) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_range.mp hj).ne]
    beta_reduce
    rw [hs, if_pos rfl]
    have := sub_smul_dslope k p z
    rw [smul_eq_mul] at this
    have h2 : k z = k p + (z - p) * dslope k p z := by rw [this]; ring
    rw [h2]
    ring

/-- Laurent principal part: a function meromorphic at `p` is, on a punctured neighbourhood of
`p`, a finite sum `∑_{k < n} c_k (z - p)^{-(k+1)}` plus a function analytic at `p`. -/
theorem exists_principalPart (hf : MeromorphicAt f p) :
    ∃ (n : ℕ) (c : ℕ → ℂ) (h : ℂ → ℂ), AnalyticAt ℂ h p ∧
      ∀ᶠ z in 𝓝[≠] p, f z = (∑ k ∈ Finset.range n, c k * (z - p) ^ (-((k : ℤ) + 1))) + h z := by
  cases ho : meromorphicOrderAt f p with
  | top =>
    refine ⟨0, fun _ => 0, fun _ => 0, analyticAt_const, ?_⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with z hz
    simp [hz]
  | coe m =>
    obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
    rcases le_or_gt 0 m with hm | hm
    · refine ⟨0, fun _ => 0, fun z => (z - p) ^ m * g z, ?_, ?_⟩
      · exact (AnalyticAt.zpow_nonneg (by fun_prop) hm).mul hg
      · filter_upwards [hfg] with z hz
        simp [hz]
    · obtain ⟨N, rfl⟩ : ∃ N : ℕ, m = -(N : ℤ) := ⟨m.natAbs, by omega⟩
      obtain ⟨a, k, hk, hz⟩ := exists_taylor hg N
      refine ⟨N, fun i => a (N - 1 - i), k, hk, ?_⟩
      filter_upwards [hfg, self_mem_nhdsWithin] with z hz1 hz2
      have hz0 : z - p ≠ 0 := sub_ne_zero.mpr hz2
      rw [hz1, smul_eq_mul, hz z, mul_add, ← mul_assoc, ← zpow_natCast, ← zpow_add₀ hz0]
      simp only [neg_add_cancel, zpow_zero, one_mul]
      congr 1
      rw [Finset.mul_sum]
      set F : ℕ → ℂ := fun j => a j * (z - p) ^ ((j : ℤ) - N) with hF
      calc ∑ i ∈ Finset.range N, (z - p) ^ (-(N : ℤ)) * (a i * (z - p) ^ i)
          = ∑ j ∈ Finset.range N, F j := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [hF]
            rw [mul_left_comm, ← zpow_natCast, ← zpow_add₀ hz0]
            congr 2
            ring
        _ = ∑ k ∈ Finset.range N, F (N - 1 - k) := (Finset.sum_range_reflect F N).symm
        _ = _ := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' := Finset.mem_range.mp hk
            have : ((N - 1 - k : ℕ) : ℤ) = N - 1 - k := by omega
            simp only [hF]
            rw [this]
            congr 2
            ring

/-- For `f` meromorphic at `p`, the integrals `∮_{|z-p|=r} f` are all equal for small `r > 0`,
and the residue is `(2πi)⁻¹` times this common value. -/
theorem residue_eq_circleIntegral (hf : MeromorphicAt f p) :
    ∃ ε > 0, ∀ r ∈ Ioo 0 ε, residue f p = (2 * π * I)⁻¹ * ∮ z in C(p, r), f z := by
  obtain ⟨n, c, h, hh, hfh⟩ := exists_principalPart hf
  obtain ⟨ε, hε, H⟩ := residue_eq_ite hh hfh
  have hres : residue f p = if 0 < n then c 0 else 0 :=
    residue_eq_of_eventually (Filter.eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr => H r hr)
  exact ⟨ε, hε, fun r hr => by rw [H r hr, hres]⟩

/-- The residue only depends on the germ of `f` on a punctured neighbourhood of `p`. -/
theorem residue_congr (h : f =ᶠ[𝓝[≠] p] g) : residue f p = residue g p := by
  obtain ⟨ε, hε, hε'⟩ := exists_ball_of_nhdsNE h
  have key : (fun r : ℝ => (2 * π * I)⁻¹ * ∮ z in C(p, r), f z) =ᶠ[𝓝[>] (0:ℝ)]
      (fun r => (2 * π * I)⁻¹ * ∮ z in C(p, r), g z) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    congr 1
    apply circleIntegral.integral_congr hr.1.le
    intro z hz
    exact hε' z (ne_of_mem_sphere hr.1 hz) (by rw [dist_eq_of_mem_sphere hz]; exact hr.2)
  unfold residue Filter.limUnder
  rw [Filter.map_congr key]

/-- The residue is the coefficient of `(z - p)⁻¹` in the principal part. -/
theorem residue_eq_of_principalPart {n : ℕ} (hn : 0 < n) {c : ℕ → ℂ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h p)
    (hf : ∀ᶠ z in 𝓝[≠] p, f z = (∑ k ∈ Finset.range n, c k * (z - p) ^ (-((k : ℤ) + 1))) + h z) :
    residue f p = c 0 := by
  obtain ⟨ε, hε, H⟩ := residue_eq_ite hh hf
  have := residue_eq_of_eventually
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr => H r hr)
  simpa [hn] using this

/-- A function with no pole at `p` (nonnegative order) has residue `0` there. -/
theorem residue_eq_zero_of_nonneg_order (hf : MeromorphicAt f p)
    (h0 : 0 ≤ meromorphicOrderAt f p) : residue f p = 0 := by
  obtain ⟨h, hh, hfh⟩ := (hf.meromorphicOrderAt_nonneg_iff).mp h0
  obtain ⟨ε, hε, H⟩ := residue_eq_ite (f := f) (n := 0) (c := fun _ => 0) hh
    (by filter_upwards [hfh] with z hz; simp [hz])
  simpa using residue_eq_of_eventually
    (Filter.eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr => H r hr)

lemma exists_circleIntegrable (hf : MeromorphicAt f p) :
    ∃ ε > 0, ∀ r ∈ Ioo 0 ε, CircleIntegrable f p r := by
  obtain ⟨ε, hε, h⟩ := exists_ball_of_nhdsNE hf.eventually_analyticAt
  refine ⟨ε, hε, fun r hr => ContinuousOn.circleIntegrable hr.1.le fun z hz => ?_⟩
  exact (h z (ne_of_mem_sphere hr.1 hz)
    (by rw [dist_eq_of_mem_sphere hz]; exact hr.2)).continuousAt.continuousWithinAt

lemma eventually_res (hf : MeromorphicAt f p) : ∀ᶠ r in 𝓝[>] (0 : ℝ),
    CircleIntegrable f p r ∧ residue f p = (2 * π * I)⁻¹ * ∮ z in C(p, r), f z := by
  obtain ⟨ε₁, hε₁, h₁⟩ := residue_eq_circleIntegral hf
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_circleIntegrable hf
  filter_upwards [Ioo_mem_nhdsGT (lt_min hε₁ hε₂)] with r hr
  exact ⟨h₂ r ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_right _ _)⟩,
    h₁ r ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩⟩

theorem residue_add (hf : MeromorphicAt f p) (hg : MeromorphicAt g p) :
    residue (f + g) p = residue f p + residue g p := by
  apply residue_eq_of_eventually
  filter_upwards [eventually_res hf, eventually_res hg] with r ⟨i1, r1⟩ ⟨i2, r2⟩
  show (2 * π * I)⁻¹ * ∮ z in C(p, r), (f z + g z) = _
  rw [circleIntegral.integral_add i1 i2, r1, r2, mul_add]

theorem residue_const_mul (hf : MeromorphicAt f p) (c : ℂ) :
    residue (fun z => c * f z) p = c * residue f p := by
  apply residue_eq_of_eventually
  filter_upwards [eventually_res hf] with r ⟨i1, r1⟩
  rw [circleIntegral.integral_const_mul, r1]
  ring

lemma circleIntegral_comp_add (f : ℂ → ℂ) (a p : ℂ) (r : ℝ) :
    ∮ z in C(p, r), f (z + a) = ∮ z in C(p + a, r), f z := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  have : circleMap p r θ + a = circleMap (p + a) r θ := by
    simp only [circleMap]; ring
  show deriv (circleMap p r) θ • f (circleMap p r θ + a) =
    deriv (circleMap (p + a) r) θ • f (circleMap (p + a) r θ)
  rw [this, deriv_circleMap, deriv_circleMap]

/-- Residue of a translate. -/
theorem residue_comp_add (a : ℂ) (hf : MeromorphicAt f (p + a)) :
    residue (fun z => f (z + a)) p = residue f (p + a) := by
  unfold residue
  simp only [circleIntegral_comp_add]

lemma circleIntegral_comp_mul {c : ℂ} (hc : c ≠ 0) (f : ℂ → ℂ) (p : ℂ) (r : ℝ) :
    ∮ z in C(p, r), f (c * z) = c⁻¹ * ∮ z in C(c * p, ‖c‖ * r), f z := by
  set G : ℝ → ℂ := fun φ =>
    deriv (circleMap (c * p) (‖c‖ * r)) φ • f (circleMap (c * p) (‖c‖ * r) φ) with hG
  have hper : Function.Periodic G (2 * π) := by
    intro φ
    simp only [hG, deriv_circleMap]
    rw [periodic_circleMap (c * p) _ φ, periodic_circleMap 0 _ φ]
  have key : ∀ θ : ℝ, (‖c‖ : ℂ) * exp (((θ : ℂ) + (arg c : ℂ)) * I) = c * exp (θ * I) := by
    intro θ
    rw [add_mul, Complex.exp_add]
    calc (‖c‖ : ℂ) * (exp (θ * I) * exp (arg c * I))
        = ((‖c‖ : ℂ) * exp (arg c * I)) * exp (θ * I) := by ring
      _ = _ := by rw [Complex.norm_mul_exp_arg_mul_I]
  have hshift : ∀ θ : ℝ, deriv (circleMap p r) θ • f (c * circleMap p r θ) =
      c⁻¹ • G (θ + arg c) := by
    intro θ
    have e1 : circleMap (c * p) (‖c‖ * r) (θ + arg c) = c * circleMap p r θ := by
      simp only [circleMap]
      push_cast
      linear_combination (r : ℂ) * key θ
    have e2 : circleMap 0 (‖c‖ * r) (θ + arg c) = c * circleMap 0 r θ := by
      simp only [circleMap]
      push_cast
      linear_combination (r : ℂ) * key θ
    simp only [hG, deriv_circleMap, e1, e2, smul_eq_mul]
    field_simp
  unfold circleIntegral
  simp_rw [hshift]
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_add_right G (arg c),
    zero_add, add_comm (2 * π) (arg c), hper.intervalIntegral_add_eq (arg c) 0, zero_add]
  rfl

/-- Residue after the complex-linear change of variables `z ↦ c z`. -/
theorem residue_comp_mul {c : ℂ} (hc : c ≠ 0) (hf : MeromorphicAt f (c * p)) :
    residue (fun z => f (c * z)) p = c⁻¹ * residue f (c * p) := by
  obtain ⟨ε, hε, h⟩ := residue_eq_circleIntegral hf
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  apply residue_eq_of_eventually
  filter_upwards [Ioo_mem_nhdsGT (div_pos hε hpos)] with r hr
  rw [circleIntegral_comp_mul hc, h (‖c‖ * r) ⟨mul_pos hpos hr.1, (lt_div_iff₀' hpos).mp hr.2⟩]
  ring

lemma logDeriv_principal (hf : MeromorphicAt f p) (htop : meromorphicOrderAt f p ≠ ⊤) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G p ∧
      ∀ᶠ z in 𝓝[≠] p, logDeriv f z = (ord f p : ℂ) * (z - p)⁻¹ + G z := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp htop
  have hord : ord f p = m := by unfold ord; rw [← hm]; simp
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hm.symm
  refine ⟨logDeriv g, ?_, ?_⟩
  · show AnalyticAt ℂ (fun x => deriv g x / g x) p
    exact hg.deriv.div hg hg0
  · have hF := logDeriv_congr_nhdsNE hfg
    have hgz : ∀ᶠ z in 𝓝[≠] p, g z ≠ 0 :=
      (hg.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hF, hgz, hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z h1 h2 h3 h4
    rw [h1, hord]
    have hz0 : z - p ≠ 0 := sub_ne_zero.mpr h4
    have hzp : DifferentiableAt ℂ (fun x : ℂ => x ^ m) (z - p) :=
      differentiableAt_zpow.mpr (Or.inl hz0)
    have h5 : logDeriv (fun w : ℂ => (w - p) ^ m) z = (m : ℂ) / (z - p) := by
      have := logDeriv_comp (f := fun x : ℂ => x ^ m) (g := fun w : ℂ => w - p) (x := z)
        hzp (differentiableAt_id.sub_const p)
      simp only [Function.comp_def] at this
      rw [this, logDeriv_zpow]
      simp
    have h6 := logDeriv_fun_mul (f := fun w : ℂ => (w - p) ^ m) (g := g) z
      (zpow_ne_zero m hz0) h2 (hzp.comp z (differentiableAt_id.sub_const p)) h3.differentiableAt
    simp only [smul_eq_mul]
    rw [h6, h5, div_eq_mul_inv]

/-- The residue of the logarithmic derivative `f'/f` at `p` is the order of `f` at `p`
(Milne, proof of Prop. 2.1 (b), pdf p. 91: `Res_P(f'/f) = ord_P(f)`). -/
theorem residue_logDeriv (hf : MeromorphicAt f p) (htop : meromorphicOrderAt f p ≠ ⊤) :
    residue (logDeriv f) p = ord f p := by
  obtain ⟨G, hG, hfG⟩ := logDeriv_principal hf htop
  exact residue_eq_of_principalPart (n := 1) (c := fun _ => (ord f p : ℂ)) one_pos hG
    (by filter_upwards [hfG] with z hz; simpa using hz)

/-- `Res_P(z f'/f) = P · ord_P(f)` (Milne, proof of Prop. 2.1 (c)). -/
theorem residue_id_mul_logDeriv (hf : MeromorphicAt f p) (htop : meromorphicOrderAt f p ≠ ⊤) :
    residue (fun z => z * logDeriv f z) p = p * ord f p := by
  obtain ⟨G, hG, hfG⟩ := logDeriv_principal hf htop
  refine residue_eq_of_principalPart (n := 1) (c := fun _ => p * (ord f p : ℂ))
    (h := fun z => (ord f p : ℂ) + z * G z) one_pos
    (by fun_prop) ?_
  filter_upwards [hfG, self_mem_nhdsWithin] with z hz hz2
  have hz0 : z - p ≠ 0 := sub_ne_zero.mpr hz2
  simp only [hz, Finset.sum_range_one, Nat.cast_zero, zero_add]
  field_simp
  ring

/-! ### The residue theorem for rectangles -/

/-! #### Rectangle helpers -/

/-- The boundary of the closed rectangle with corners `z`, `w`. -/
def rectBdry (z w : ℂ) : Set ℂ :=
  {x | x ∈ Icc z.re w.re ×ℂ Icc z.im w.im ∧
    (x.re = z.re ∨ x.re = w.re ∨ x.im = z.im ∨ x.im = w.im)}

lemma rectSides_integrable {h : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : ContinuousOn h (rectBdry z w)) :
    IntervalIntegrable (fun x : ℝ => h (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => h (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => h (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => h (z.re + y * I)) volume z.im w.im := by
  have hh : ∀ x ∈ Icc z.re w.re, ∀ y ∈ Icc z.im w.im, (x = z.re ∨ x = w.re ∨ y = z.im ∨ y = w.im) →
      ((x : ℂ) + y * I) ∈ rectBdry z w := by
    intro x hx y hy hxy
    refine ⟨mem_reProdIm.mpr ⟨by simpa using hx, by simpa using hy⟩, by simpa using hxy⟩
  have cx : ∀ y : ℝ, Continuous fun x : ℝ => (x : ℂ) + y * I := fun y => by fun_prop
  have cy : ∀ x : ℝ, Continuous fun y : ℝ => (x : ℂ) + y * I := fun x => by fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ContinuousOn.intervalIntegrable
  · refine hc.comp (cx _).continuousOn fun x hx => ?_
    rw [uIcc_of_le hre] at hx
    exact hh x hx _ ⟨le_rfl, him⟩ (Or.inr (Or.inr (Or.inl rfl)))
  · refine hc.comp (cx _).continuousOn fun x hx => ?_
    rw [uIcc_of_le hre] at hx
    exact hh x hx _ ⟨him, le_rfl⟩ (Or.inr (Or.inr (Or.inr rfl)))
  · refine hc.comp (cy _).continuousOn fun y hy => ?_
    rw [uIcc_of_le him] at hy
    exact hh _ ⟨hre, le_rfl⟩ y hy (Or.inr (Or.inl rfl))
  · refine hc.comp (cy _).continuousOn fun y hy => ?_
    rw [uIcc_of_le him] at hy
    exact hh _ ⟨le_rfl, hre⟩ y hy (Or.inl rfl)

lemma rectIntegral_add {h k : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hh : ContinuousOn h (rectBdry z w)) (hk : ContinuousOn k (rectBdry z w)) :
    rectIntegral (fun x => h x + k x) z w = rectIntegral h z w + rectIntegral k z w := by
  obtain ⟨h1, h2, h3, h4⟩ := rectSides_integrable hre him hh
  obtain ⟨k1, k2, k3, k4⟩ := rectSides_integrable hre him hk
  unfold rectIntegral
  simp only [intervalIntegral.integral_add h1 k1, intervalIntegral.integral_add h2 k2,
    intervalIntegral.integral_add h3 k3, intervalIntegral.integral_add h4 k4, smul_add]
  abel

lemma rectIntegral_const_mul (c : ℂ) (h : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun x => c * h x) z w = c * rectIntegral h z w := by
  unfold rectIntegral
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

lemma rectIntegral_sum {ι : Type*} (s : Finset ι) {φ : ι → ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hφ : ∀ i ∈ s, ContinuousOn (φ i) (rectBdry z w)) :
    rectIntegral (fun x => ∑ i ∈ s, φ i x) z w = ∑ i ∈ s, rectIntegral (φ i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectIntegral]
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [rectIntegral_add hre him (hφ i (Finset.mem_insert_self _ _))
      (continuousOn_finsetSum _ fun j hj => hφ j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hφ j (Finset.mem_insert_of_mem hj)]

lemma integral_congr_countable {a b : ℝ} {φ ψ : ℝ → ℂ} {T : Set ℝ} (hT : T.Countable)
    (h : ∀ x ∈ uIcc a b, x ∉ T → φ x = ψ x) : ∫ x in a..b, φ x = ∫ x in a..b, ψ x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hT.ae_notMem volume] with x hx hx'
  exact h x (uIoc_subset_uIcc hx') hx

lemma rectIntegral_congr_countable {z w : ℂ} {T : Set ℂ} (hT : T.Countable) {f k : ℂ → ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h : ∀ x ∈ Icc z.re w.re ×ℂ Icc z.im w.im, x ∉ T → f x = k x) :
    rectIntegral f z w = rectIntegral k z w := by
  have hb : ∀ y0 : ℝ, y0 ∈ Icc z.im w.im →
      ∫ x : ℝ in z.re..w.re, f (x + y0 * I) = ∫ x : ℝ in z.re..w.re, k (x + y0 * I) := by
    intro y0 hy0
    apply integral_congr_countable (T := (fun x : ℝ => (x : ℂ) + y0 * I) ⁻¹' T)
    · refine hT.preimage ?_
      intro a b hab
      simpa using hab
    · intro x hx hxT
      rw [uIcc_of_le hre] at hx
      exact h _ (mem_reProdIm.mpr ⟨by simpa using hx, by simpa using hy0⟩) hxT
  have hv : ∀ x0 : ℝ, x0 ∈ Icc z.re w.re →
      ∫ y : ℝ in z.im..w.im, f (x0 + y * I) = ∫ y : ℝ in z.im..w.im, k (x0 + y * I) := by
    intro x0 hx0
    apply integral_congr_countable (T := (fun y : ℝ => (x0 : ℂ) + y * I) ⁻¹' T)
    · refine hT.preimage ?_
      intro a b hab
      simpa using hab
    · intro y hy hyT
      rw [uIcc_of_le him] at hy
      exact h _ (mem_reProdIm.mpr ⟨by simpa using hx0, by simpa using hy⟩) hyT
  unfold rectIntegral
  rw [hb z.im ⟨le_rfl, him⟩, hb w.im ⟨him, le_rfl⟩, hv w.re ⟨hre, le_rfl⟩,
    hv z.re ⟨le_rfl, hre⟩]

lemma countable_of_isolated' {B : Set ℂ} (h : ∀ z ∈ B, ∃ U ∈ 𝓝 z, U ∩ B ⊆ {z}) :
    B.Countable := by
  have hd : DiscreteTopology B := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro ⟨z, hz⟩
    obtain ⟨U, hU, hUB⟩ := h z hz
    rw [isOpen_induced_iff]
    obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.mp hU
    refine ⟨V, hVo, ?_⟩
    ext ⟨w, hw⟩
    simp only [mem_preimage, mem_singleton_iff, Subtype.mk.injEq]
    constructor
    · intro hwV
      exact hUB ⟨hVU hwV, hw⟩
    · rintro rfl; exact hzV
  exact (HereditarilyLindelofSpace.isLindelof B).countable hd

lemma integral_horiz {F F' : ℂ → ℂ} {a b y : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (F' (x + y * I)) (x + y * I))
    (hc : IntervalIntegrable (fun x : ℝ => F' (x + y * I)) volume a b) :
    ∫ x : ℝ in a..b, F' (x + y * I) = F (b + y * I) - F (a + y * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + y * I)) ?_ hc
  intro x hx
  exact ((hF x hx).comp_add_const (x : ℂ) (y * I)).comp_ofReal

lemma integral_vert {F F' : ℂ → ℂ} {a b x : ℝ}
    (hF : ∀ y ∈ uIcc a b, HasDerivAt F (F' (x + y * I)) (x + y * I))
    (hc : IntervalIntegrable (fun y : ℝ => F' (x + y * I)) volume a b) :
    I • ∫ y : ℝ in a..b, F' (x + y * I) = F (x + b * I) - F (x + a * I) := by
  have : ∫ y : ℝ in a..b, I * F' (x + y * I) = F (x + b * I) - F (x + a * I) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => F (x + y * I)) ?_
      (hc.const_mul I)
    intro y hy
    have h1 : HasDerivAt (fun w : ℂ => (x : ℂ) + w * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)
    have h2 := (hF y hy).comp (y : ℂ) h1
    rw [mul_comm] at h2
    exact h2.comp_ofReal
  rw [← this, intervalIntegral.integral_const_mul, smul_eq_mul]

lemma rectIntegral_of_primitives {F' Fb Ft Fl Fr : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hcont : ContinuousOn F' (rectBdry z w))
    (hb : ∀ x ∈ uIcc z.re w.re, HasDerivAt Fb (F' (x + z.im * I)) (x + z.im * I))
    (ht : ∀ x ∈ uIcc z.re w.re, HasDerivAt Ft (F' (x + w.im * I)) (x + w.im * I))
    (hr : ∀ y ∈ uIcc z.im w.im, HasDerivAt Fr (F' (w.re + y * I)) (w.re + y * I))
    (hl : ∀ y ∈ uIcc z.im w.im, HasDerivAt Fl (F' (z.re + y * I)) (z.re + y * I)) :
    rectIntegral F' z w =
      (Fb (w.re + z.im * I) - Fb (z.re + z.im * I)) - (Ft (w.re + w.im * I) - Ft (z.re + w.im * I))
      + (Fr (w.re + w.im * I) - Fr (w.re + z.im * I))
      - (Fl (z.re + w.im * I) - Fl (z.re + z.im * I)) := by
  obtain ⟨h1, h2, h3, h4⟩ := rectSides_integrable hre him hcont
  unfold rectIntegral
  rw [integral_horiz hb h1, integral_horiz ht h2, integral_vert hr h3, integral_vert hl h4]

lemma side_ne {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) :
    (∀ t : ℝ, (t : ℂ) + z.im * I ≠ p) ∧ (∀ t : ℝ, (t : ℂ) + w.im * I ≠ p) ∧
    (∀ t : ℝ, (w.re : ℂ) + t * I ≠ p) ∧ (∀ t : ℝ, (z.re : ℂ) + t * I ≠ p) := by
  refine ⟨fun t h => ?_, fun t h => ?_, fun t h => ?_, fun t h => ?_⟩
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.im h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith
  · have := congrArg Complex.re h; simp at this; linarith

lemma rectBdry_ne {z w p x : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) (hx : x ∈ rectBdry z w) : x ≠ p := by
  rintro rfl
  rcases hx.2 with h | h | h | h <;> linarith

lemma continuousOn_term_bdry {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) (c : ℂ) (m : ℤ) :
    ContinuousOn (fun x : ℂ => c * (x - p) ^ m) (rectBdry z w) := by
  intro x hx
  have hne : x - p ≠ 0 := sub_ne_zero.mpr (rectBdry_ne h1 h2 h3 h4 hx)
  refine ContinuousAt.continuousWithinAt ?_
  exact continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).zpow₀ m (Or.inl hne))

lemma rectIntegral_zpow_lt {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) {m : ℤ} (hm : m < -1) :
    rectIntegral (fun x => (x - p) ^ m) z w = 0 := by
  have hm1 : ((m + 1 : ℤ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
  set F : ℂ → ℂ := fun x => (x - p) ^ (m + 1) / ((m + 1 : ℤ) : ℂ) with hF
  have hder : ∀ x, x ≠ p → HasDerivAt F ((x - p) ^ m) x := by
    intro x hx
    have := ((hasDerivAt_zpow (m + 1) (x - p) (Or.inl (sub_ne_zero.mpr hx))).comp_sub_const
      x p).div_const (((m + 1 : ℤ)) : ℂ)
    refine this.congr_deriv ?_
    field_simp
    simp
  obtain ⟨sb, st, sr, sl⟩ := side_ne h1 h2 h3 h4
  have hcont : ContinuousOn (fun x : ℂ => (x - p) ^ m) (rectBdry z w) := by
    have := continuousOn_term_bdry h1 h2 h3 h4 1 m
    simpa using this
  rw [rectIntegral_of_primitives (Fb := F) (Ft := F) (Fl := F) (Fr := F) (by linarith)
    (by linarith) hcont (fun x _ => hder _ (sb x)) (fun x _ => hder _ (st x))
    (fun x _ => hder _ (sr x)) (fun x _ => hder _ (sl x))]
  ring

lemma log_sub_log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) : log u - log (-u) = π * I := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos hu]

lemma log_sub_log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) : log u - log (-u) = -(π * I) := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg hu]

lemma rectIntegral_inv {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectIntegral (fun x => (x - p)⁻¹) z w = 2 * π * I := by
  have hd1 : ∀ x : ℂ, (0 < (x - p).re ∨ (x - p).im ≠ 0) →
      HasDerivAt (fun x => log (x - p)) (x - p)⁻¹ x := fun x hx =>
    (Complex.hasDerivAt_log (mem_slitPlane_iff.mpr hx)).comp_sub_const x p
  have hd2 : ∀ x : ℂ, (0 < (-(x - p)).re ∨ (-(x - p)).im ≠ 0) →
      HasDerivAt (fun x => log (-(x - p))) (x - p)⁻¹ x := by
    intro x hx
    have := (Complex.hasDerivAt_log (mem_slitPlane_iff.mpr hx)).comp x
      (((hasDerivAt_id x).sub_const p).neg)
    refine this.congr_deriv ?_
    rw [inv_neg]; ring
  have hcont : ContinuousOn (fun x : ℂ => (x - p)⁻¹) (rectBdry z w) := by
    have := continuousOn_term_bdry h1 h2 h3 h4 1 (-1)
    simpa [zpow_neg_one] using this
  rw [rectIntegral_of_primitives (Fb := fun x => log (x - p)) (Ft := fun x => log (x - p))
    (Fr := fun x => log (x - p)) (Fl := fun x => log (-(x - p))) (by linarith) (by linarith) hcont
    (fun x _ => hd1 _ (Or.inr (by simp; intro h; linarith)))
    (fun x _ => hd1 _ (Or.inr (by simp; intro h; linarith)))
    (fun y _ => hd1 _ (Or.inl (by simp; linarith)))
    (fun y _ => hd2 _ (Or.inl (by simp; linarith)))]
  have hu := log_sub_log_neg_of_im_pos (u := (z.re : ℂ) + w.im * I - p) (by simp; linarith)
  have hv := log_sub_log_neg_of_im_neg (u := (z.re : ℂ) + z.im * I - p) (by simp; linarith)
  linear_combination hu - hv

lemma rectIntegral_term {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) (c : ℂ) (k : ℕ) :
    rectIntegral (fun x => c * (x - p) ^ (-((k : ℤ) + 1))) z w =
      if k = 0 then 2 * π * I * c else 0 := by
  rw [rectIntegral_const_mul]
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.cast_zero, zero_add, ite_true, zpow_neg, zpow_one]
    rw [rectIntegral_inv h1 h2 h3 h4]
    ring
  · rw [rectIntegral_zpow_lt h1 h2 h3 h4, mul_zero, if_neg hk]
    omega

lemma rectIntegral_principalPart {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) (n : ℕ) (c : ℕ → ℂ) :
    rectIntegral (fun x => ∑ k ∈ Finset.range n, c k * (x - p) ^ (-((k : ℤ) + 1))) z w =
      2 * π * I * (if 0 < n then c 0 else 0) := by
  rw [rectIntegral_sum _ (by linarith) (by linarith)
    (fun k _ => continuousOn_term_bdry h1 h2 h3 h4 _ _)]
  rw [Finset.sum_congr rfl (fun k _ => rectIntegral_term h1 h2 h3 h4 (c k) k)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [if_pos hn, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn)]
    · simp
    · intro k _ hk
      simp [hk]

lemma limUnder_eq_of_analytic {g H : ℂ → ℂ} {x : ℂ} (hH : AnalyticAt ℂ H x)
    (hg : g =ᶠ[𝓝[≠] x] H) : limUnder (𝓝[≠] x) g = H x :=
  (Tendsto.congr' hg.symm (hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).limUnder_eq

lemma limUnder_eventuallyEq {g H : ℂ → ℂ} {x : ℂ} (hH : AnalyticAt ℂ H x)
    (hg : g =ᶠ[𝓝[≠] x] H) : (fun w => limUnder (𝓝[≠] w) g) =ᶠ[𝓝 x] H := by
  have hg' : ∀ᶠ w in 𝓝 x, w ≠ x → g w = H w := eventually_nhdsWithin_iff.mp hg
  filter_upwards [hg'.eventually_nhds, hH.eventually_analyticAt] with w hw hwa
  by_cases hwx : w = x
  · subst hwx; exact limUnder_eq_of_analytic hH hg
  · have h1 : ∀ᶠ w' in 𝓝 w, w' ≠ x := eventually_ne_nhds hwx
    have h2 := (hw.and h1).filter_mono (nhdsWithin_le_nhds (s := {w}ᶜ))
    have : g =ᶠ[𝓝[≠] w] H := by
      filter_upwards [h2] with w' h using h.1 h.2
    exact limUnder_eq_of_analytic hwa this

/-- The residue theorem for a rectangle (Cartan 1963, III 5.2, in the case of a rectangle):
let `f` be meromorphic at every point of the closed rectangle with corners `z`, `w`
(`z.re < w.re`, `z.im < w.im`), without poles (order `≥ 0`) except at the points of a finite
set `S` contained in the open rectangle.  Then the integral of `f` round the boundary is
`2πi ∑_{p ∈ S} Res_p f`.  Values of `f` at isolated points do not matter. -/
theorem rectIntegral_eq_two_pi_I_mul_sum_residue {z w : ℂ} (hre : z.re < w.re)
    (him : z.im < w.im) {S : Finset ℂ}
    (hS : ∀ p ∈ S, p ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im)
    (hmer : ∀ x ∈ Icc z.re w.re ×ℂ Icc z.im w.im, MeromorphicAt f x)
    (hpole : ∀ x ∈ Icc z.re w.re ×ℂ Icc z.im w.im, x ∉ S → 0 ≤ meromorphicOrderAt f x) :
    rectIntegral f z w = 2 * π * I * ∑ p ∈ S, residue f p := by
  classical
  have hSR : ∀ p ∈ S, p ∈ Icc z.re w.re ×ℂ Icc z.im w.im := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_reProdIm.mp (hS p hp)
    exact mem_reProdIm.mpr ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩
  have hSi : ∀ p ∈ S, z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im := fun p hp => by
    obtain ⟨h1, h2⟩ := mem_reProdIm.mp (hS p hp)
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩
  have hpp : ∀ p ∈ S, ∃ (n : ℕ) (c : ℕ → ℂ) (h : ℂ → ℂ), AnalyticAt ℂ h p ∧
      ∀ᶠ x in 𝓝[≠] p, f x = (∑ k ∈ Finset.range n, c k * (x - p) ^ (-((k : ℤ) + 1))) + h x :=
    fun p hp => exists_principalPart (hmer p (hSR p hp))
  choose! n c h hh hev using hpp
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ → ℂ → ℂ, ∀ q y,
      Q q y = ∑ k ∈ Finset.range (n q), c q k * (y - q) ^ (-((k : ℤ) + 1)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Qt, hQt⟩ : ∃ Qt : ℂ → ℂ, ∀ y, Qt y = ∑ q ∈ S, Q q y := ⟨_, fun _ => rfl⟩
  obtain ⟨gg, hgg⟩ : ∃ gg : ℂ → ℂ, ∀ y, gg y = f y - Qt y := ⟨_, fun _ => rfl⟩
  have hQan : ∀ q x, x ≠ q → AnalyticAt ℂ (Q q) x := by
    intro q x hxq
    have hne : (fun y : ℂ => y - q) x ≠ 0 := sub_ne_zero.mpr hxq
    have : Q q = fun y => ∑ k ∈ Finset.range (n q), c q k * (y - q) ^ (-((k : ℤ) + 1)) :=
      funext (hQ q)
    rw [this]
    exact Finset.analyticAt_fun_sum _ fun k _ =>
      analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).zpow hne)
  have hQtan : ∀ x, (∀ q ∈ S, x ≠ q) → AnalyticAt ℂ Qt x := by
    intro x hx
    have : Qt = fun y => ∑ q ∈ S, Q q y := funext hQt
    rw [this]
    exact Finset.analyticAt_fun_sum _ fun q hq => hQan q x (hx q hq)
  have hmodel : ∀ x ∈ Icc z.re w.re ×ℂ Icc z.im w.im,
      ∃ Hx : ℂ → ℂ, AnalyticAt ℂ Hx x ∧ gg =ᶠ[𝓝[≠] x] Hx := by
    intro x hx
    by_cases hxS : x ∈ S
    · refine ⟨fun y => h x y - ∑ q ∈ S.erase x, Q q y, (hh x hxS).sub
        (Finset.analyticAt_fun_sum _ fun q hq =>
          hQan q x (Finset.ne_of_mem_erase hq).symm), ?_⟩
      filter_upwards [hev x hxS] with y hy
      rw [← hQ] at hy
      rw [hgg, hQt, ← Finset.add_sum_erase S (fun q => Q q y) hxS, hy]
      ring
    · obtain ⟨h', hh', hfh'⟩ := ((hmer x hx).meromorphicOrderAt_nonneg_iff).mp (hpole x hx hxS)
      refine ⟨fun y => h' y - Qt y, hh'.sub (hQtan x fun q hq hxq => hxS (hxq ▸ hq)), ?_⟩
      filter_upwards [hfh'] with y hy
      rw [hgg, hy]
  choose! H hHan hgH using hmodel
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ x, G x = limUnder (𝓝[≠] x) gg := ⟨_, fun _ => rfl⟩
  have hGfun : G = fun x => limUnder (𝓝[≠] x) gg := funext hG
  have hGH : ∀ x ∈ Icc z.re w.re ×ℂ Icc z.im w.im, G =ᶠ[𝓝 x] H x := fun x hx => by
    rw [hGfun]; exact limUnder_eventuallyEq (hHan x hx) (hgH x hx)
  have hGan : ∀ x ∈ Icc z.re w.re ×ℂ Icc z.im w.im, AnalyticAt ℂ G x := fun x hx =>
    (hHan x hx).congr (hGH x hx).symm
  have hcauchy : rectIntegral G z w = 0 := by
    refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable G z w ∅
      countable_empty ?_ ?_
    · rw [uIcc_of_le hre.le, uIcc_of_le him.le]
      intro x hx
      exact (hGan x hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx1 := hx.1
      rw [min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
        max_eq_right him.le] at hx1
      obtain ⟨a1, a2⟩ := mem_reProdIm.mp hx1
      exact (hGan x (mem_reProdIm.mpr ⟨Ioo_subset_Icc_self a1, Ioo_subset_Icc_self a2⟩)).differentiableAt
  have hT : {x | x ∈ Icc z.re w.re ×ℂ Icc z.im w.im ∧ gg x ≠ G x}.Countable := by
    apply countable_of_isolated'
    rintro x ⟨hxR, -⟩
    have h1 : ∀ᶠ y in 𝓝[≠] x, gg y = G y := by
      have : G =ᶠ[𝓝[≠] x] H x := (hGH x hxR).filter_mono nhdsWithin_le_nhds
      filter_upwards [hgH x hxR, this] with y hy1 hy2 using hy1.trans hy2.symm
    refine ⟨{y | y ≠ x → gg y = G y}, eventually_nhdsWithin_iff.mp h1, ?_⟩
    rintro y ⟨hy1, -, hy2⟩
    by_contra hyx
    exact hy2 (hy1 hyx)
  have hcongr : rectIntegral f z w = rectIntegral (fun x => G x + Qt x) z w :=
    rectIntegral_congr_countable hT hre.le him.le (fun x hx hxT => by
      have h1 : gg x = G x := by
        by_contra hne
        exact hxT ⟨hx, hne⟩
      have e1 := hgg x
      linear_combination h1 - e1)
  have hcontG : ContinuousOn G (rectBdry z w) := fun x hx =>
    (hGan x hx.1).continuousAt.continuousWithinAt
  have hcontQ : ∀ q ∈ S, ContinuousOn (Q q) (rectBdry z w) := by
    intro q hq x hx
    obtain ⟨h1, h2, h3, h4⟩ := hSi q hq
    exact (hQan q x (rectBdry_ne h1 h2 h3 h4 hx)).continuousAt.continuousWithinAt
  have hQtfun : Qt = fun y => ∑ q ∈ S, Q q y := funext hQt
  have hcontQt : ContinuousOn Qt (rectBdry z w) := by
    rw [hQtfun]; exact continuousOn_finsetSum _ hcontQ
  have hres : ∀ q ∈ S, residue f q = if 0 < n q then c q 0 else 0 := by
    intro q hq
    obtain ⟨ε, hε, H'⟩ := residue_eq_ite (hh q hq) (hev q hq)
    exact residue_eq_of_eventually
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hε) fun r hr => H' r hr)
  rw [hcongr, rectIntegral_add hre.le him.le hcontG hcontQt, hcauchy, zero_add, hQtfun,
    rectIntegral_sum S hre.le him.le hcontQ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨h1, h2, h3, h4⟩ := hSi q hq
  rw [hres q hq, show Q q = fun y => ∑ k ∈ Finset.range (n q), c q k * (y - q) ^ (-((k : ℤ) + 1))
    from funext (hQ q)]
  exact rectIntegral_principalPart h1 h2 h3 h4 (n q) (c q)

/-- If `f` has periods `1` and `τ` (`Im τ > 0`), its integral round the boundary of the
rectangle `[a, a + 1] × [b, b + Im τ]` vanishes: the vertical sides cancel by the period `1`,
and the top side is the bottom side translated by `τ - Re τ`, which does not change the integral
of a function of period `1` over an interval of length `1`.  No integrability is needed. -/
theorem rectIntegral_eq_zero_of_periodic {τ : ℂ} (h1 : ∀ z, f (z + 1) = f z)
    (hτ : ∀ z, f (z + τ) = f z) (a b : ℝ) :
    rectIntegral f (a + b * I) (a + 1 + (b + τ.im) * I) = 0 := by
  have hper : Function.Periodic (fun x : ℝ => f (x + b * I)) 1 := by
    intro x
    have := h1 (x + b * I)
    simp only [ofReal_add, ofReal_one]
    rw [← this]; congr 1; ring
  have htop : ∀ x : ℝ, f (x + (b + τ.im : ℝ) * I) = (fun x : ℝ => f (x + b * I)) (x - τ.re) := by
    intro x
    have e : (x : ℂ) + ((b + τ.im : ℝ) : ℂ) * I = ((x - τ.re : ℝ) : ℂ) + b * I + τ := by
      apply Complex.ext <;> simp
    rw [e, hτ]
  have hint : ∫ x : ℝ in a..a + 1, f (x + (b + τ.im : ℝ) * I) = ∫ x : ℝ in a..a + 1, f (x + b * I) := by
    simp_rw [htop]
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => f (x + b * I)) τ.re]
    have := hper.intervalIntegral_add_eq (a - τ.re) a
    rw [show a + 1 - τ.re = a - τ.re + 1 by ring, this]
  have hv : ∀ y : ℝ, f ((a + 1 : ℝ) + y * I) = f (a + y * I) := by
    intro y
    have := h1 (a + y * I)
    rw [← this]; congr 1; push_cast; ring
  unfold rectIntegral
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
    add_im, mul_im, zero_add, one_re, one_im]
  simp_rw [hv]
  rw [hint]
  simp

end NumberFieldKB.MilneEC.III
