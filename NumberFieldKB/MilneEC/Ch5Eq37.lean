import NumberFieldKB.MilneEC.Ch5JFunction
import NumberFieldKB.MilneEC.Ch5LevelOne

/-!
# Milne, *Elliptic Curves*, Chapter V §2: the $q$-expansion (37) of $j$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter V, §2, equation (37), pdf p. 191:
$j = q^{-1} + 744 + 196884q + 21493760q^2 + \sum_{n\ge3}c(n)q^n$ with $c(n) \in \mathbb Z$. Proved here, so the
named statement `Eq37` holds.
-/

open UpperHalfPlane hiding I
open ModularForm Complex Filter Topology Matrix.SpecialLinearGroup
open scoped MatrixGroups Real Manifold

namespace NumberFieldKB.MilneEC.V

/-- The function `f` is given on the open unit disc by the power series with coefficients `A`. -/
def Rep (f : ℂ → ℂ) (A : PowerSeries ℂ) : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => A.coeff n * q ^ n) (f q)

/-- If $f$ is represented by $A$ on the unit disc, then $\sum_n |a_n| r^n$ converges for $0 \le r < 1$. -/
lemma Rep.summable_norm {f : ℂ → ℂ} {A : PowerSeries ℂ} (h : Rep f A) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) : Summable (fun n => ‖A.coeff n‖ * r ^ n) := by
  set r' : ℝ := (r + 1) / 2 with hr'
  have hr'0 : 0 < r' := by rw [hr']; linarith
  have hr'1 : r' < 1 := by rw [hr']; linarith
  have hrr' : r < r' := by rw [hr']; linarith
  have hs := (h (r' : ℂ) (by simpa [abs_of_pos hr'0] using hr'1)).summable
  have ht := hs.norm.tendsto_atTop_zero
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  have hC' : ∀ n, ‖A.coeff n‖ * r' ^ n ≤ C := by
    intro n
    have := hC ⟨n, rfl⟩
    simpa [norm_mul, norm_pow, abs_of_pos hr'0] using this
  have hgeo : Summable (fun n : ℕ => C * (r / r') ^ n) :=
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hr'0).mpr hrr')).mul_left C
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hgeo
  have h1 : ‖A.coeff n‖ * r ^ n = ‖A.coeff n‖ * r' ^ n * (r / r') ^ n := by
    rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hr'0.ne']
  rw [h1]
  exact mul_le_mul_of_nonneg_right (hC' n) (by positivity)

/-- If $f$ is represented by $A$, then $\sum_n |a_n q^n|$ converges for $|q| < 1$. -/
lemma Rep.summable_norm_mul {f : ℂ → ℂ} {A : PowerSeries ℂ} (h : Rep f A) {q : ℂ}
    (hq : ‖q‖ < 1) : Summable (fun n => ‖A.coeff n * q ^ n‖) := by
  simpa [norm_mul, norm_pow] using h.summable_norm (norm_nonneg q) hq

/-- The product of represented functions is represented by the product of the power series. -/
lemma Rep.mul {f g : ℂ → ℂ} {A B : PowerSeries ℂ} (hf : Rep f A) (hg : Rep g B) :
    Rep (fun q => f q * g q) (A * B) := by
  intro q hq
  have h1 := hf.summable_norm_mul hq
  have h2 := hg.summable_norm_mul hq
  have h3 := summable_norm_sum_mul_antidiagonal_of_summable_norm h1 h2
  have h4 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h1 h2
  rw [(hf q hq).tsum_eq, (hg q hq).tsum_eq] at h4
  have h5 : ∀ n, (A * B).coeff n * q ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (A.coeff kl.1 * q ^ kl.1) * (B.coeff kl.2 * q ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]; ring
  simp_rw [h5]
  rw [h4]
  exact h3.of_norm.hasSum

/-- A represented function has the given power series expansion on the open unit disc. -/
lemma Rep.hasFPowerSeriesOnBall {f : ℂ → ℂ} {A : PowerSeries ℂ} (h : Rep f A) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ (fun n => A.coeff n)) 0 1 where
  r_le := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    refine (FormalMultilinearSeries.ofScalars ℂ (fun n => A.coeff n)).le_radius_of_summable ?_
    have hr1 : (r : ℝ) < 1 := by exact_mod_cast hr
    simpa using h.summable_norm r.2 hr1
  r_pos := one_pos
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < 1 := by
      have : ‖y‖ₑ < 1 := by simpa [edist_zero_right] using hy
      rwa [← ofReal_norm, ENNReal.ofReal_lt_one] at this
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using h y hy'

/-- The power series representing a function on the unit disc is unique. -/
lemma Rep.unique {f : ℂ → ℂ} {A B : PowerSeries ℂ} (hA : Rep f A) (hB : Rep f B) : A = B := by
  have := hA.hasFPowerSeriesOnBall.hasFPowerSeriesAt.eq_formalMultilinearSeries
    hB.hasFPowerSeriesOnBall.hasFPowerSeriesAt
  ext n
  have h := FormalMultilinearSeries.ofScalars_series_eq_iff (E := ℂ) _ _ |>.mp this
  exact congrFun h n

/-- A function holomorphic on the unit disc is represented by its Taylor series at $0$. -/
lemma Rep.of_differentiableOn {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    Rep f (PowerSeries.mk fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n f 0) := by
  intro q hq
  have := (Complex.hasSum_taylorSeries_on_ball hf (c := 0) (z := q) (by simpa using hq))
  convert this using 2 with n
  simp only [PowerSeries.coeff_mk, smul_eq_mul, sub_zero]
  ring

/-- The $n$-th coefficient of a representing series is $f^{(n)}(0)/n!$. -/
lemma Rep.coeff_eq {f : ℂ → ℂ} {A : PowerSeries ℂ} (h : Rep f A)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) (n : ℕ) :
    A.coeff n = ((n.factorial : ℂ))⁻¹ * iteratedDeriv n f 0 := by
  rw [h.unique (Rep.of_differentiableOn hf)]
  simp

/-- Representability is preserved by changing the function on the open unit disc. -/
lemma Rep.congr {f g : ℂ → ℂ} {A : PowerSeries ℂ} (h : Rep f A)
    (hfg : ∀ q : ℂ, ‖q‖ < 1 → f q = g q) : Rep g A := fun q hq => (hfg q hq) ▸ h q hq

/-- The difference of represented functions is represented by the difference of the series. -/
lemma Rep.sub {f g : ℂ → ℂ} {A B : PowerSeries ℂ} (hf : Rep f A) (hg : Rep g B) :
    Rep (fun q => f q - g q) (A - B) := by
  intro q hq
  simpa [sub_mul] using (hf q hq).sub (hg q hq)

/-- The constant function $1$ is represented by the series $1$. -/
lemma Rep.one : Rep (fun _ => 1) 1 := by
  intro q hq
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  rw [PowerSeries.coeff_one]
  split_ifs with h <;> simp [h]

/-- The function $q \mapsto q^k$ is represented by the series $X^k$. -/
lemma Rep.X_pow (k : ℕ) : Rep (fun q => q ^ k) (PowerSeries.X ^ k) := by
  intro q hq
  convert hasSum_ite_eq k (q ^ k) using 1
  funext n
  rw [PowerSeries.coeff_X_pow]
  split_ifs with h <;> simp [h]

/-- If $f$ is represented by $A$, then $f^k$ is represented by $A^k$. -/
lemma Rep.pow {f : ℂ → ℂ} {A : PowerSeries ℂ} (h : Rep f A) (k : ℕ) :
    Rep (fun q => f q ^ k) (A ^ k) := by
  induction k with
  | zero => simpa using Rep.one
  | succ k ih => simpa [pow_succ] using ih.mul h

/-- A finite product of represented functions is represented by the product of the series. -/
lemma Rep.prod_range {f : ℕ → ℂ → ℂ} {A : ℕ → PowerSeries ℂ} (h : ∀ i, Rep (f i) (A i)) (N : ℕ) :
    Rep (fun q => ∏ i ∈ Finset.range N, f i q) (∏ i ∈ Finset.range N, A i) := by
  induction N with
  | zero => simpa using Rep.one
  | succ N ih => simpa [Finset.prod_range_succ] using ih.mul (h N)

/-- Partial products of `∏ (1 - X^(i+1))` over the integers. -/
noncomputable def pp (N : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ (i + 1))

/-- Partial products of `∏ (1 - q^(i+1))`. -/
noncomputable def PP (N : ℕ) (q : ℂ) : ℂ := ∏ i ∈ Finset.range N, (1 - q ^ (i + 1))

/-- The partial product $\prod_{i<N}(1-q^{i+1})$ is represented by the integer series $\prod_{i<N}(1-X^{i+1})$. -/
lemma rep_PP (N : ℕ) : Rep (PP N) (PowerSeries.map (Int.castRingHom ℂ) (pp N)) := by
  have h : ∀ i, Rep (fun q : ℂ => 1 - q ^ (i + 1)) (1 - PowerSeries.X ^ (i + 1)) :=
    fun i => Rep.one.sub (Rep.X_pow _)
  have := Rep.prod_range h N
  show Rep (fun q => ∏ i ∈ Finset.range N, (1 - q ^ (i + 1))) _
  simpa [pp, map_prod] using this

/-- Coefficients of index $n \le N$ do not change when passing from $N$ to $N+1$ factors. -/
lemma coeff_pp_succ (N n : ℕ) (hn : n ≤ N) : (pp (N + 1)).coeff n = (pp N).coeff n := by
  rw [pp, Finset.prod_range_succ, mul_sub, mul_one, map_sub, ← pp, mul_comm,
    PowerSeries.coeff_X_pow_mul', if_neg (by omega), sub_zero]

/-- The $n$-th coefficient of the partial product is stable for all $N \ge n$. -/
lemma coeff_pp_stable (n N : ℕ) (hN : n ≤ N) : (pp N).coeff n = (pp n).coeff n := by
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [coeff_pp_succ N n hN, ih]

/-- The partial product is infinitely differentiable (it is a polynomial). -/
lemma contDiff_PP (N : ℕ) : ContDiff ℂ ⊤ (PP N) := by
  unfold PP
  fun_prop

/-- The product `∏' (1 - q^(n+1))`. -/
noncomputable def P1 (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1))

/-- Every derivative of the partial products converges locally uniformly on the unit disc to that of the infinite product. -/
lemma tendsto_iteratedDeriv_PP (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N => iteratedDeriv k (PP N)) (iteratedDeriv k P1) atTop
      (Metric.ball (0 : ℂ) 1) := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact (multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn
        |>.tendstoLocallyUniformlyOn_finsetRange)
  | succ k ih =>
    have hd : ∀ᶠ N in atTop, DifferentiableOn ℂ (iteratedDeriv k (PP N)) (Metric.ball (0 : ℂ) 1) :=
      Filter.Eventually.of_forall fun N =>
        ((contDiff_PP N).differentiable_iteratedDeriv k (by simp)).differentiableOn
    have := ih.deriv hd Metric.isOpen_ball
    simp only [iteratedDeriv_succ]
    exact this

/-- The infinite product $\prod (1-q^{n+1})$ is holomorphic on the open unit disc. -/
lemma differentiableOn_P1 : DifferentiableOn ℂ P1 (Metric.ball (0 : ℂ) 1) :=
  differentiableOn_tprod_one_sub_pow

/-- The integer series of `∏ (1 - X^(i+1))`: coefficient `n` is that of the partial product `pp n`. -/
noncomputable def s1 : PowerSeries ℤ := PowerSeries.mk fun n => (pp n).coeff n

/-- The infinite product $\prod (1-q^{n+1})$ is represented by the integer series $s_1$. -/
lemma rep_P1 : Rep P1 (PowerSeries.map (Int.castRingHom ℂ) s1) := by
  have key : PowerSeries.map (Int.castRingHom ℂ) s1 = PowerSeries.mk fun n =>
      ((n.factorial : ℂ))⁻¹ * iteratedDeriv n P1 0 := by
    ext n
    simp only [s1, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
    have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
    have ht := (tendsto_iteratedDeriv_PP n).tendsto_at h0
    have hev : ∀ᶠ N in atTop, iteratedDeriv n (PP N) 0 = (n.factorial : ℂ) * ((pp n).coeff n : ℤ) := by
      filter_upwards [eventually_ge_atTop n] with N hN
      have := (rep_PP N).coeff_eq ((contDiff_PP N).differentiable (by simp)).differentiableOn n
      simp only [PowerSeries.coeff_map, eq_intCast] at this
      rw [coeff_pp_stable n N hN] at this
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      rw [this]
      field_simp
    have ht' : Tendsto (fun N => iteratedDeriv n (PP N) 0) atTop
        (nhds ((n.factorial : ℂ) * ((pp n).coeff n : ℤ))) :=
      tendsto_const_nhds.congr' (hev.mono fun N h => h.symm)
    have := tendsto_nhds_unique ht ht'
    rw [this]
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    field_simp
  rw [key]
  exact Rep.of_differentiableOn differentiableOn_P1

/-- The product $\prod (1-q^{n+1})$ is nonzero for $|q| < 1$. -/
lemma P1_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : P1 q ≠ 0 := by
  have hne : ∀ i : ℕ, 1 + (fun n : ℕ => -q ^ (n + 1)) i ≠ 0 := by
    intro i h0
    have h1 : q ^ (i + 1) = 1 := by simp only at h0; linear_combination -h0
    have h2 : ‖q ^ (i + 1)‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
    rw [h1] at h2; simp at h2
  have hsum : Summable (fun n : ℕ => ‖-q ^ (n + 1)‖) := by
    simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)
  have h := tprod_one_add_ne_zero_of_summable (ι := ℕ) (f := fun n => -q ^ (n + 1)) hne hsum
  simpa [P1, sub_eq_add_neg] using h

/-- The product `∏' (1 - q^(n+1))^24`. -/
noncomputable def P24 (q : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24

/-- For $|q| < 1$, $\prod (1-q^{n+1})^{24} = \left(\prod (1-q^{n+1})\right)^{24}$. -/
lemma P24_eq {q : ℂ} (hq : ‖q‖ < 1) : P24 q = P1 q ^ 24 :=
  (multipliable_one_sub_pow hq).tprod_pow 24

/-- The product $\prod (1-q^{n+1})^{24}$ is nonzero for $|q| < 1$. -/
lemma P24_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : P24 q ≠ 0 := by
  rw [P24_eq hq]; exact pow_ne_zero _ (P1_ne_zero hq)

/-- The product $\prod (1-q^{n+1})^{24}$ is represented by the integer series $s_1^{24}$. -/
lemma rep_P24 : Rep P24 (PowerSeries.map (Int.castRingHom ℂ) (s1 ^ 24)) := by
  have := rep_P1.pow 24
  rw [map_pow]
  exact this.congr fun q hq => (P24_eq hq).symm

/-- The product $\prod (1-q^{n+1})^{24}$ is holomorphic on the open unit disc. -/
lemma differentiableOn_P24 : DifferentiableOn ℂ P24 (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_P1.pow 24).congr fun q hq => P24_eq (by simpa using hq)

/-- The constant coefficient of $s_1$ is $1$. -/
lemma coeff_zero_s1 : s1.coeff 0 = 1 := by simp [s1, pp]

/-- The integer series inverse to `s1 ^ 24`. -/
noncomputable def uInv : PowerSeries ℤ := PowerSeries.invOfUnit (s1 ^ 24) 1

/-- The series $s_1^{24}$ times its inverse series is $1$. -/
lemma mul_uInv : s1 ^ 24 * uInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by
    rw [map_pow, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_s1]; simp)

/-- The reciprocal of `P24` is represented by the integer series `uInv`. -/
lemma rep_inv_P24 : Rep (fun q => (P24 q)⁻¹) (PowerSeries.map (Int.castRingHom ℂ) uInv) := by
  have hd : DifferentiableOn ℂ (fun q => (P24 q)⁻¹) (Metric.ball (0 : ℂ) 1) :=
    differentiableOn_P24.inv fun q hq => P24_ne_zero (by simpa using hq)
  set B := PowerSeries.mk fun n => ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun q => (P24 q)⁻¹) 0
  have hB : Rep (fun q => (P24 q)⁻¹) B := Rep.of_differentiableOn hd
  have h1 := rep_P24.mul hB
  have h2 : Rep (fun _ => (1 : ℂ)) (PowerSeries.map (Int.castRingHom ℂ) (s1 ^ 24) * B) :=
    h1.congr fun q hq => by simp [P24_ne_zero hq]
  have h3 := h2.unique Rep.one
  have h4 : PowerSeries.map (Int.castRingHom ℂ) (s1 ^ 24) * PowerSeries.map (Int.castRingHom ℂ) uInv
      = 1 := by rw [← map_mul, mul_uInv, map_one]
  have : B = PowerSeries.map (Int.castRingHom ℂ) uInv := by
    calc B = (PowerSeries.map (Int.castRingHom ℂ) uInv *
          PowerSeries.map (Int.castRingHom ℂ) (s1 ^ 24)) * B := by
            rw [mul_comm _ (PowerSeries.map _ (s1 ^ 24)), h4, one_mul]
      _ = _ := by rw [mul_assoc, h3, mul_one]
  rw [← this]; exact hB

open PowerSeries (X C) in
/-- The series $s_1$ equals $1 - X - X^2$ modulo $X^4$. -/
lemma s1_form : ∃ r : PowerSeries ℤ, s1 = (1 - X - X ^ 2) + X ^ 4 * r := by
  have p0 : pp 0 = 1 := by simp [pp]
  have p1 : pp 1 = 1 - X := by simp [pp]
  have p2 : pp 2 = 1 - X - X ^ 2 + X ^ 3 := by simp [pp, Finset.prod_range_succ]; ring
  have p3 : pp 3 = 1 - X - X ^ 2 + X ^ 4 + X ^ 5 - X ^ 6 := by
    simp [pp, Finset.prod_range_succ]; ring
  have hd : (X : PowerSeries ℤ) ^ 4 ∣ s1 - (1 - X - X ^ 2) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [s1, p0]
    · simp [s1, p1, PowerSeries.coeff_X]
    · simp [s1, p2, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · simp [s1, p3, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  obtain ⟨r, hr⟩ := hd
  exact ⟨r, by linear_combination hr⟩

open PowerSeries (X C) in
/-- Explicit expansion of $(1 - X - X^2)^{24}$ with the terms of degree at least $4$ collected. -/
lemma b24_form : (1 - X - X ^ 2 : PowerSeries ℤ) ^ 24 = 1 + C (-24) * X ^ 1 + C 252 * X ^ 2 +
    C (-1472) * X ^ 3 + X ^ 4 * (4830 * X^0 + (-6072) * X^1 + (-16192) * X^2 + 78936 * X^3 + (-82731) * X^4 + (-212520) * X^5 + 649704 * X^6 + (-73416) * X^7 + (-1977862) * X^8 + 2034672 * X^9 + 3487260 * X^10 + (-7072408) * X^11 + (-3432198) * X^12 + 15343944 * X^13 + 134596 * X^14 + (-25077360) * X^15 + 6067446 * X^16 + 33474936 * X^17 + (-12286968) * X^18 + (-38228232) * X^19 + 14903725 * X^20 + 38228232 * X^21 + (-12286968) * X^22 + (-33474936) * X^23 + 6067446 * X^24 + 25077360 * X^25 + 134596 * X^26 + (-15343944) * X^27 + (-3432198) * X^28 + 7072408 * X^29 + 3487260 * X^30 + (-2034672) * X^31 + (-1977862) * X^32 + 73416 * X^33 + 649704 * X^34 + 212520 * X^35 + (-82731) * X^36 + (-78936) * X^37 + (-16192) * X^38 + 6072 * X^39 + 4830 * X^40 + 1472 * X^41 + 252 * X^42 + 24 * X^43 + 1 * X^44) := by
  simp only [map_neg, map_ofNat]
  ring

open PowerSeries (X C) in
/-- The series $s_1^{24}$ equals $1 - 24X + 252X^2 - 1472X^3$ modulo $X^4$. -/
lemma a_form : ∃ K : PowerSeries ℤ, s1 ^ 24 = 1 + C (-24) * X ^ 1 + C 252 * X ^ 2 +
    C (-1472) * X ^ 3 + X ^ 4 * K := by
  obtain ⟨r, hr⟩ := s1_form
  obtain ⟨k, hk⟩ : X ^ 4 * r ∣ (1 - X - X ^ 2 + X ^ 4 * r) ^ 24 - (1 - X - X ^ 2 : PowerSeries ℤ) ^ 24 := by
    have := sub_dvd_pow_sub_pow (1 - X - X ^ 2 + X ^ 4 * r : PowerSeries ℤ) (1 - X - X ^ 2) 24
    rwa [add_sub_cancel_left] at this
  refine ⟨(4830 * X^0 + (-6072) * X^1 + (-16192) * X^2 + 78936 * X^3 + (-82731) * X^4 + (-212520) * X^5 + 649704 * X^6 + (-73416) * X^7 + (-1977862) * X^8 + 2034672 * X^9 + 3487260 * X^10 + (-7072408) * X^11 + (-3432198) * X^12 + 15343944 * X^13 + 134596 * X^14 + (-25077360) * X^15 + 6067446 * X^16 + 33474936 * X^17 + (-12286968) * X^18 + (-38228232) * X^19 + 14903725 * X^20 + 38228232 * X^21 + (-12286968) * X^22 + (-33474936) * X^23 + 6067446 * X^24 + 25077360 * X^25 + 134596 * X^26 + (-15343944) * X^27 + (-3432198) * X^28 + 7072408 * X^29 + 3487260 * X^30 + (-2034672) * X^31 + (-1977862) * X^32 + 73416 * X^33 + 649704 * X^34 + 212520 * X^35 + (-82731) * X^36 + (-78936) * X^37 + (-16192) * X^38 + 6072 * X^39 + 4830 * X^40 + 1472 * X^41 + 252 * X^42 + 24 * X^43 + 1 * X^44) + r * k, ?_⟩
  rw [hr, sub_eq_iff_eq_add.mp hk, b24_form]
  ring

/-- The integer series of the Eisenstein series `E₄`. -/
noncomputable def eS : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 n : ℤ)

open PowerSeries (X C) in
/-- The series of $E_4$ equals $1 + 240X + 2160X^2 + 6720X^3$ modulo $X^4$. -/
lemma e_form : ∃ L : PowerSeries ℤ, eS = 1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3 +
    X ^ 4 * L := by
  have hd : (X : PowerSeries ℤ) ^ 4 ∣ eS - (1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3) := by
    rw [PowerSeries.X_pow_dvd_iff]
    obtain ⟨h32, h33, -⟩ := sigma_values
    intro m hm
    interval_cases m
    · simp [eS]
    · simp [eS, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    · simp [eS, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, h32]
    · simp [eS, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, h33]
  obtain ⟨r, hr⟩ := hd
  exact ⟨r, by linear_combination hr⟩

open PowerSeries (X C) in
/-- The cube of the series of $E_4$ equals $1 + 720X + 179280X^2 + 16954560X^3$ modulo $X^4$. -/
lemma e3_form : ∃ M : PowerSeries ℤ, eS ^ 3 = 1 + C 720 * X ^ 1 + C 179280 * X ^ 2 +
    C 16954560 * X ^ 3 + X ^ 4 * M := by
  obtain ⟨L, hL⟩ := e_form
  obtain ⟨k, hk⟩ : X ^ 4 * L ∣ (1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3 + X ^ 4 * L) ^ 3 -
      (1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3 : PowerSeries ℤ) ^ 3 := by
    have := sub_dvd_pow_sub_pow (1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3 +
      X ^ 4 * L : PowerSeries ℤ) (1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3) 3
    rwa [add_sub_cancel_left] at this
  refine ⟨(396921600 * X^0 + 4607539200 * X^1 + 31115059200 * X^2 + 126572544000 * X^3 + 292626432000 * X^4 + 303464448000 * X^5) + L * k, ?_⟩
  rw [hL]
  have h2 : (1 + C 240 * X ^ 1 + C 2160 * X ^ 2 + C 6720 * X ^ 3 : PowerSeries ℤ) ^ 3 =
      1 + C 720 * X ^ 1 + C 179280 * X ^ 2 + C 16954560 * X ^ 3 + X ^ 4 * (396921600 * X^0 + 4607539200 * X^1 + 31115059200 * X^2 + 126572544000 * X^3 + 292626432000 * X^4 + 303464448000 * X^5) := by
    simp only [map_ofNat]
    ring
  linear_combination hk + h2

open PowerSeries (X C) in
/-- Coefficients of degree below $4$ of a product with a series of the form $1 + a_1X + a_2X^2 + a_3X^3 + X^4K$. -/
lemma coeff_mul_form (S K : PowerSeries ℤ) (a1 a2 a3 : ℤ) (n : ℕ) (hn : n < 4) :
    PowerSeries.coeff n (S * (1 + C a1 * X ^ 1 + C a2 * X ^ 2 + C a3 * X ^ 3 + X ^ 4 * K)) =
      PowerSeries.coeff n S + (if 1 ≤ n then a1 * PowerSeries.coeff (n - 1) S else 0) +
      (if 2 ≤ n then a2 * PowerSeries.coeff (n - 2) S else 0) +
      (if 3 ≤ n then a3 * PowerSeries.coeff (n - 3) S else 0) := by
  have key : ∀ (c : ℤ) (k : ℕ), PowerSeries.coeff n (S * (C c * X ^ k)) =
      if k ≤ n then c * PowerSeries.coeff (n - k) S else 0 := by
    intro c k
    rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    split_ifs <;> simp
  have hK : PowerSeries.coeff n (S * (X ^ 4 * K)) = 0 := by
    rw [mul_left_comm, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  simp only [mul_add, map_add, mul_one, key, hK, add_zero]

/-- The integer series of `E₄ ^ 3 / (q-expansion of Δ / q)`. -/
noncomputable def Sx : PowerSeries ℤ := eS ^ 3 * uInv

open PowerSeries (X C) in
/-- The first four coefficients of the series are $1$, $744$, $196884$, and $21493760$. -/
lemma Sx_coeffs : Sx.coeff 0 = 1 ∧ Sx.coeff 1 = 744 ∧ Sx.coeff 2 = 196884 ∧
    Sx.coeff 3 = 21493760 := by
  have h : Sx * s1 ^ 24 = eS ^ 3 := by
    rw [Sx, mul_assoc, mul_comm uInv, mul_uInv, mul_one]
  obtain ⟨K, hK⟩ := a_form
  obtain ⟨M, hM⟩ := e3_form
  have h' : Sx * (1 + C (-24) * X ^ 1 + C 252 * X ^ 2 + C (-1472) * X ^ 3 + X ^ 4 * K) =
      1 * (1 + C 720 * X ^ 1 + C 179280 * X ^ 2 + C 16954560 * X ^ 3 + X ^ 4 * M) := by
    rw [one_mul, ← hK, ← hM]; exact h
  have h1 : ∀ n, n < 4 → PowerSeries.coeff n Sx + (if 1 ≤ n then (-24) * PowerSeries.coeff (n - 1) Sx else 0) +
      (if 2 ≤ n then 252 * PowerSeries.coeff (n - 2) Sx else 0) +
      (if 3 ≤ n then (-1472) * PowerSeries.coeff (n - 3) Sx else 0) =
      PowerSeries.coeff n (1 : PowerSeries ℤ) + (if 1 ≤ n then 720 * PowerSeries.coeff (n - 1) (1 : PowerSeries ℤ) else 0) +
      (if 2 ≤ n then 179280 * PowerSeries.coeff (n - 2) (1 : PowerSeries ℤ) else 0) +
      (if 3 ≤ n then 16954560 * PowerSeries.coeff (n - 3) (1 : PowerSeries ℤ) else 0) := fun n hn => by
    have := congrArg (PowerSeries.coeff n) h'
    rwa [coeff_mul_form _ _ _ _ _ n hn, coeff_mul_form _ _ _ _ _ n hn] at this
  have e0 := h1 0 (by norm_num)
  have e1 := h1 1 (by norm_num)
  have e2 := h1 2 (by norm_num)
  have e3 := h1 3 (by norm_num)
  simp [PowerSeries.coeff_one] at e0 e1 e2 e3
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at e0 e1 e2 e3
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- The Eisenstein series $E_4$ is represented by its integer series in the variable $q$. -/
lemma rep_E4 : Rep (cuspFunction 1 (E₄ : ℍ → ℂ)) (PowerSeries.map (Int.castRingHom ℂ) eS) := by
  have hd : DifferentiableOn ℂ (cuspFunction 1 (E₄ : ℍ → ℂ)) (Metric.ball (0 : ℂ) 1) :=
    fun q hq => (ModularFormClass.differentiableAt_cuspFunction E₄ one_pos
      one_mem_strictPeriods_SL (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  have h := Rep.of_differentiableOn hd
  have : PowerSeries.map (Int.castRingHom ℂ) eS = qExpansion 1 (E₄ : ℍ → ℂ) := by
    ext n
    rw [E4_coeff]
    simp only [eS, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
    split_ifs <;> push_cast <;> rfl
  rw [this]
  exact h

/-- Equation (37) (pdf p. 191). -/
@[kb "milne2006ec" "Ch. V, §2, equation (37), pdf p. 191"]
theorem eq37 : Eq37 := by
  obtain ⟨h0, h1, h2, h3⟩ := Sx_coeffs
  refine ⟨⟨fun n => Sx.coeff (n + 1), h1, h2, h3, fun z => ?_⟩⟩
  set q : ℂ := cexp (2 * π * I * z) with hqdef
  have hqn : ‖q‖ < 1 := by
    have := Function.Periodic.norm_qParam_lt_one (h := 1) one_pos z.im_pos
    simpa [Function.Periodic.qParam, hqdef] using this
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hR : Rep (fun q => cuspFunction 1 (E₄ : ℍ → ℂ) q ^ 3 * (P24 q)⁻¹)
      (PowerSeries.map (Int.castRingHom ℂ) Sx) := by
    have := (rep_E4.pow 3).mul rep_inv_P24
    simpa [Sx, map_mul, map_pow] using this
  have hs := hR q hqn
  have hs1 := (hasSum_nat_add_iff' 1).mpr hs
  have hz := hs1.mul_left q⁻¹
  convert hz using 1
  · funext n
    simp only [PowerSeries.coeff_map, eq_intCast]
    field_simp
    ring
  · have hE : cuspFunction 1 (E₄ : ℍ → ℂ) q = E₄ z := by
      have := SlashInvariantFormClass.eq_cuspFunction E₄ z one_mem_strictPeriods_SL one_ne_zero
      rwa [qParam_one_eq] at this
    have hD : ModularForm.discriminant z = q * P24 q := by
      have := ModularForm.discriminant_eq_q_prod z
      rw [qParam_one_eq] at this
      simpa [P24, ModularForm.eta_q, Function.Periodic.qParam, hqdef] using this
    have hP := P24_ne_zero hqn
    simp only [Finset.range_one, Finset.sum_singleton, PowerSeries.coeff_map, eq_intCast,
      pow_zero, mul_one]
    rw [jFun_eq, hD, hE, h0]
    field_simp
    simp

end NumberFieldKB.MilneEC.V
