import NumberFieldKB.MilneCFT.Ch6.Basic

/-!
# Milne, *Class Field Theory*, Chapter VI §2: Dirichlet series and characters of finite abelian groups

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`. Locators give
Milne's printed page numbers (printed page = pdf page − 9).

* The complex power $n^z = e^{(\log n)z}$ (definition in prose, p. 183) is Mathlib's `Complex.cpow`
  (`cpow_eq_exp_log_mul`).
* **Proposition 2.1** (`prop_2_1`): a Dirichlet series whose coefficient sums satisfy $|S(x)|\le ax^b$ ($a,b>0$)
  converges uniformly on the regions $D(b,\delta,\varepsilon)$ (`sectorD`) and its sum is analytic on
  $\mathrm{Re}\,s > b$. Proved by summation by parts, as in Milne.
* **Lemma 2.10** (`lemma_2_10`) and **Lemma 4.7** (`lemma_4_7`): orthogonality of characters of a finite abelian group
  $A$ (characters $A\to\mathbb C^\times$), from Mathlib (`sum_hom_units_eq_zero`, and the additive characters'
  `AddChar.sum_apply_eq_zero_iff_ne_zero`).
-/

open Filter Topology

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6

/-- **The complex power** (Milne, *CFT*, Chapter VI, p. 183): for a real $n > 0$ and a complex $z$,
$n^z = e^{(\log n)z}$. Mathlib's `Complex.cpow`. -/
@[kb "milne2020cft" "Ch. VI, p. 183 (n^z = exp((log n) z))"]
theorem cpow_eq_exp_log_mul {n : ℝ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp (Real.log n * z) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), Complex.ofReal_log hn.le]

/-- Abel summation on a finite block `(m, n]`. -/
private lemma abel_Ioc (a f : ℕ → ℂ) (m n : ℕ) (h : m ≤ n) :
    ∑ k ∈ Finset.Ioc m n, a k * f k =
      (∑ k ∈ Finset.Icc 1 n, a k) * f (n + 1) - (∑ k ∈ Finset.Icc 1 m, a k) * f (m + 1)
        + ∑ k ∈ Finset.Ioc m n, (∑ j ∈ Finset.Icc 1 k, a j) * (f k - f (k + 1)) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn, Finset.sum_Ioc_succ_top hn, ih,
      Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    ring

/-- Real inequality used to telescope `∑ k^(-c-1)`. -/
private lemma step_ineq {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 1 < t) :
    c * t ^ (-c - 1) ≤ (t - 1) ^ (-c) - t ^ (-c) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have hlog : Real.log (t - 1) - Real.log t ≤ -(1 / t) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (t - 1) / t by positivity)
    rw [Real.log_div ht1.ne' ht0.ne'] at this
    have e : (t - 1) / t - 1 = -(1 / t) := by field_simp; ring
    linarith
  have h1 : (t - 1) ^ (-c) = t ^ (-c) * Real.exp (c * (Real.log t - Real.log (t - 1))) := by
    rw [Real.rpow_def_of_pos ht1, Real.rpow_def_of_pos ht0, ← Real.exp_add]; congr 1; ring
  have h2 : 1 + c * (1 / t) ≤ Real.exp (c * (Real.log t - Real.log (t - 1))) := by
    refine le_trans ?_ (Real.add_one_le_exp _)
    have : 1 / t ≤ Real.log t - Real.log (t - 1) := by linarith
    nlinarith
  have h3 : t ^ (-c - 1) = t ^ (-c) * (1 / t) := by
    rw [Real.rpow_sub ht0, Real.rpow_one]; field_simp
  have hp : 0 < t ^ (-c) := Real.rpow_pos_of_pos ht0 _
  rw [h1, h3]; nlinarith [mul_le_mul_of_nonneg_left h2 hp.le]

/-- Telescoped bound `∑_{k ∈ (m,n]} k^(-c-1) ≤ m^(-c)/c`. -/
private lemma sum_rpow_le {c : ℝ} (hc : 0 < c) (m n : ℕ) (hm : 1 ≤ m) (h : m ≤ n) :
    ∑ k ∈ Finset.Ioc m n, (k : ℝ) ^ (-c - 1) ≤ ((m : ℝ) ^ (-c) - (n : ℝ) ^ (-c)) / c := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ioc_succ_top hn]
    have hn1 : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      have : 1 ≤ n := le_trans hm hn
      push_cast; have : (1 : ℝ) ≤ n := by exact_mod_cast this
      linarith
    have := step_ineq hc hn1
    have e : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
    rw [e] at this
    rw [le_div_iff₀ hc] at ih ⊢
    nlinarith

/-- Step estimate `|k^(-s) - (k+1)^(-s)| ≤ |s| k^(-σ-1)`. -/
private lemma norm_step_le (s : ℂ) (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    ‖(k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  let g : ℝ → ℂ := fun y => (y : ℂ) ^ (-s)
  let g' : ℝ → ℂ := fun y => -s * (y : ℂ) ^ (-s - 1)
  have hd : ∀ y ∈ Set.Icc (k : ℝ) (k + 1), HasDerivWithinAt g (g' y) (Set.Icc (k : ℝ) (k + 1)) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hk0 hy.1
    have h1 := Complex.hasStrictDerivAt_cpow_const (c := -s)
      (Complex.ofReal_mem_slitPlane.2 hy0)
    exact (h1.hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hb : ∀ y ∈ Set.Icc (k : ℝ) (k + 1), ‖g' y‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hk0 hy.1
    have : ‖g' y‖ = ‖s‖ * y ^ (-s.re - 1) := by
      simp only [g', norm_mul, norm_neg]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hk0 hy.1 (by linarith))
      (norm_nonneg _)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc (k : ℝ) (k + 1))
    (Set.left_mem_Icc.2 (by linarith)) (Set.right_mem_Icc.2 (by linarith))
  simp only [g] at this
  rw [norm_sub_rev]
  have e : (((k : ℝ) + 1 : ℝ) : ℂ) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [e] at this
  simpa using this

/-- Tail estimate for a block of the Dirichlet series. -/
private lemma tail_bound (a : ℕ → ℂ) {A b : ℝ} (hA : 0 < A) (N0 : ℕ)
    (hN0 : ∀ n ≥ N0, ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ A * (n : ℝ) ^ b) {s : ℂ} (hb : 0 < b)
    (hs : b < s.re) {m n : ℕ} (hm1 : 1 ≤ m) (hmN : N0 ≤ m) (hmn : m ≤ n) :
    ‖∑ k ∈ Finset.Ioc m n, a k / (k : ℂ) ^ s‖ ≤
      A * (2 + ‖s‖ / (s.re - b)) * (m : ℝ) ^ (-(s.re - b)) := by
  set c := s.re - b with hc_def
  have hc : 0 < c := by linarith
  have hσ : 0 < s.re := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have e1 : ∀ k : ℕ, a k / (k : ℂ) ^ s = a k * (k : ℂ) ^ (-s) := by
    intro k; rw [Complex.cpow_neg, div_eq_mul_inv]
  simp_rw [e1]
  rw [abel_Ioc a (fun k : ℕ => (k : ℂ) ^ (-s)) m n hmn]
  have piece : ∀ j, m ≤ j →
      ‖(∑ k ∈ Finset.Icc 1 j, a k) * ((j + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ A * (m : ℝ) ^ (-c) := by
    intro j hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (lt_of_lt_of_le hm1 hj)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    have hjj : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc ‖∑ k ∈ Finset.Icc 1 j, a k‖ * ((j + 1 : ℕ) : ℝ) ^ (-s.re)
        ≤ (A * (j : ℝ) ^ b) * (j : ℝ) ^ (-s.re) :=
          mul_le_mul (hN0 j (le_trans hmN hj)) (Real.rpow_le_rpow_of_nonpos hj0 hjj (by linarith))
            (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ = A * (j : ℝ) ^ (-c) := by
          rw [mul_assoc, ← Real.rpow_add hj0]; congr 2; simp only [c]; ring
      _ ≤ A * (m : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hm0 (by exact_mod_cast hj) (by linarith)) hA.le
  have hsum : ‖∑ k ∈ Finset.Ioc m n, (∑ j ∈ Finset.Icc 1 k, a j) *
      ((k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))‖ ≤ A * ‖s‖ / c * (m : ℝ) ^ (-c) := by
    calc _ ≤ ∑ k ∈ Finset.Ioc m n, ‖(∑ j ∈ Finset.Icc 1 k, a j) *
            ((k : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ioc m n, A * ‖s‖ * (k : ℝ) ^ (-c - 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_Ioc.1 hk
          rw [norm_mul]
          have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          have h1 := norm_step_le s hσ k (by omega)
          have h2 := hN0 k (by omega)
          have h3 : (k : ℝ) ^ b * (k : ℝ) ^ (-s.re - 1) = (k : ℝ) ^ (-c - 1) := by
            rw [← Real.rpow_add hk0]; congr 1; simp only [c]; ring
          calc _ ≤ (A * (k : ℝ) ^ b) * (‖s‖ * (k : ℝ) ^ (-s.re - 1)) :=
                mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
            _ = A * ‖s‖ * ((k : ℝ) ^ b * (k : ℝ) ^ (-s.re - 1)) := by ring
            _ = _ := by rw [h3]
      _ = A * ‖s‖ * ∑ k ∈ Finset.Ioc m n, (k : ℝ) ^ (-c - 1) := by rw [Finset.mul_sum]
      _ ≤ A * ‖s‖ * (((m : ℝ) ^ (-c) - (n : ℝ) ^ (-c)) / c) :=
          mul_le_mul_of_nonneg_left (sum_rpow_le hc m n hm1 hmn) (by positivity)
      _ ≤ A * ‖s‖ * ((m : ℝ) ^ (-c) / c) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) hc.le)
            (by positivity)
      _ = A * ‖s‖ / c * (m : ℝ) ^ (-c) := by ring
  have p1 := piece n hmn
  have p2 := piece m le_rfl
  have hfin : A * (2 + ‖s‖ / c) * (m : ℝ) ^ (-c) =
      A * (m : ℝ) ^ (-c) + A * (m : ℝ) ^ (-c) + A * ‖s‖ / c * (m : ℝ) ^ (-c) := by ring
  rw [hfin]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add p1 p2)) hsum)

/-- Ratio bound on the region `D(b, δ, ε)`. -/
private lemma sector_ratio {b δ ε : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hε : 0 < ε) (hεpi : ε < Real.pi)
    {s : ℂ} (hs : s ∈ sectorD b δ ε) : ‖s‖ / (s.re - b) ≤ 1 / Real.sin ε + b / δ := by
  obtain ⟨h1, h2⟩ := hs
  have hsin : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε hεpi
  set z : ℂ := s - (b : ℂ) with hz
  have hzre : z.re = s.re - b := by simp [hz]
  have hc : 0 < s.re - b := by linarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hzre; simp at hzre; linarith
  have hznorm : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hcos := Complex.cos_arg hz0
  have hle : Real.sin ε ≤ Real.cos (Complex.arg z) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) h2
  rw [hcos, hzre, le_div_iff₀ hznorm] at hle
  have hzn : ‖z‖ / (s.re - b) ≤ 1 / Real.sin ε := by
    rw [div_le_div_iff₀ hc hsin]; nlinarith
  have hsn : ‖s‖ ≤ ‖z‖ + b := by
    have : s = z + (b : ℂ) := by simp [hz]
    calc ‖s‖ = ‖z + (b : ℂ)‖ := by rw [← this]
      _ ≤ ‖z‖ + ‖(b : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + b := by simp [abs_of_pos hb]
  have hbd : b / (s.re - b) ≤ b / δ := div_le_div_of_nonneg_left hb.le hδ (by linarith)
  calc ‖s‖ / (s.re - b) ≤ (‖z‖ + b) / (s.re - b) := by gcongr
    _ = ‖z‖ / (s.re - b) + b / (s.re - b) := add_div _ _ _
    _ ≤ _ := add_le_add hzn hbd

/-- Extract the bound on partial sums at natural numbers. -/
private lemma exists_N0 (a : ℕ → ℂ) {A b : ℝ}
    (hS : ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ A * x ^ b) :
    ∃ N0 : ℕ, ∀ n ≥ N0, ‖∑ k ∈ Finset.Icc 1 n, a k‖ ≤ A * (n : ℝ) ^ b := by
  obtain ⟨X, hX⟩ := eventually_atTop.1 hS
  refine ⟨⌈X⌉₊, fun n hn => ?_⟩
  have := hX n (le_trans (Nat.le_ceil X) (by exact_mod_cast hn))
  simpa using this

/-- Uniform Cauchy property on `D(b, δ, ε)`. -/
private lemma uniformCauchy_sector (a : ℕ → ℂ) {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hS : ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ A * x ^ b) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    UniformCauchySeqOn (fun (N : ℕ) (s : ℂ) => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) atTop
      (sectorD b δ ε) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro η hη
  by_cases hεpi : ε < Real.pi
  swap
  · refine ⟨0, fun m _ n _ s hs => ?_⟩
    exfalso
    have := hs.2
    have := abs_nonneg (Complex.arg (s - b))
    linarith [Real.pi_pos, not_lt.1 hεpi]
  obtain ⟨N0, hN0⟩ := exists_N0 a hS
  have hsin : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε hεpi
  set K := A * (2 + (1 / Real.sin ε + b / δ)) with hK
  have hlim : Tendsto (fun m : ℕ => K * (m : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop).const_mul K
    simpa using this
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hη))
  have key : ∀ m n : ℕ, max M (max N0 1) ≤ m → m ≤ n → ∀ s ∈ sectorD b δ ε,
      dist (∑ k ∈ Finset.Icc 1 m, a k / (k : ℂ) ^ s) (∑ k ∈ Finset.Icc 1 n, a k / (k : ℂ) ^ s)
        < η := by
    intro m n hm hmn s hs
    have hmM : M ≤ m := le_trans (le_max_left _ _) hm
    have hmN : N0 ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
    have hm1 : 1 ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
    have hsb : b + δ ≤ s.re := hs.1
    have hsb' : b < s.re := by linarith
    have e : ∀ N : ℕ, ∑ k ∈ Finset.Icc 1 N, a k / (k : ℂ) ^ s =
        ∑ k ∈ Finset.Ioc 0 N, a k / (k : ℂ) ^ s := by
      intro N; congr 1
    rw [e, e, dist_comm, dist_eq_norm, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le m) hmn]
    simp only [add_sub_cancel_left]
    have ht := tail_bound a hA N0 hN0 hb hsb' hm1 hmN hmn
    have hr := sector_ratio hb hδ hε hεpi hs
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hpow : (m : ℝ) ^ (-(s.re - b)) ≤ (m : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm1) (by linarith)
    calc _ ≤ A * (2 + ‖s‖ / (s.re - b)) * (m : ℝ) ^ (-(s.re - b)) := ht
      _ ≤ K * (m : ℝ) ^ (-δ) := by
          rw [hK]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA.le) hpow
            (Real.rpow_nonneg (by positivity) _) (by positivity)
      _ < η := hM m hmM
  refine ⟨max M (max N0 1), fun m hm n hn s hs => ?_⟩
  rcases le_total m n with h | h
  · exact key m n hm h s hs
  · rw [dist_comm]; exact key n m hn h s hs

/-- Every point of the half plane `Re s > b` has a neighbourhood of the form `D(b, δ, ε)`. -/
private lemma exists_sector_nhds {b : ℝ} {s0 : ℂ} (hs0 : b < s0.re) :
    ∃ δ ε : ℝ, 0 < δ ∧ 0 < ε ∧ sectorD b δ ε ∈ 𝓝 s0 := by
  set z0 : ℂ := s0 - (b : ℂ) with hz0
  have hre : 0 < z0.re := by simp [hz0]; linarith
  have hlt : |Complex.arg z0| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre)
  refine ⟨(s0.re - b) / 2, (Real.pi / 2 - |Complex.arg z0|) / 2, by linarith, by linarith, ?_⟩
  have h1 : ∀ᶠ s in 𝓝 s0, b + (s0.re - b) / 2 < s.re :=
    (Complex.continuous_re.tendsto s0).eventually (lt_mem_nhds (by linarith))
  have hslit : z0 ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hre)
  have hcont : ContinuousAt (fun s : ℂ => |Complex.arg (s - (b : ℂ))|) s0 :=
    by
      have hc1 : ContinuousAt Complex.arg (s0 - (b : ℂ)) := Complex.continuousAt_arg hslit
      have hc2 : ContinuousAt (fun s : ℂ => s - (b : ℂ)) s0 :=
        continuousAt_id.sub continuousAt_const
      exact (hc1.comp (f := fun s : ℂ => s - (b : ℂ)) hc2).abs
  have h2 : ∀ᶠ s in 𝓝 s0, |Complex.arg (s - (b : ℂ))| <
      Real.pi / 2 - (Real.pi / 2 - |Complex.arg z0|) / 2 :=
    hcont.tendsto.eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2] with s hs1 hs2
  exact ⟨hs1.le, hs2.le⟩

/-- The partial sums are differentiable in `s`. -/
private lemma differentiable_partial (a : ℕ → ℂ) (N : ℕ) :
    Differentiable ℂ (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) := by
  refine Differentiable.fun_sum fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.1 hn).1
    exact_mod_cast (by omega : n ≠ 0)
  have : (fun s : ℂ => a n / (n : ℂ) ^ s) = fun s => a n * (n : ℂ) ^ (-s) := by
    funext s; rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [this]
  exact (differentiable_const _).mul (Differentiable.const_cpow differentiable_id.neg (Or.inl hn0))

/-- **Proposition 2.1** (Milne, *CFT*, Chapter VI, p. 185): let $f(s) = \sum_{n\ge1}a(n)n^{-s}$, write
$S(x) = \sum_{n\le x}a(n)$, and suppose there are positive constants $a$, $b$ with $|S(x)|\le ax^b$ for all large $x$.
Then the series converges uniformly on $D(b,\delta,\varepsilon)$ for all $\delta,\varepsilon > 0$, and it converges to
an analytic function on the half plane $\mathrm{Re}\,s > b$. Here: the partial sums $\sum_{n=1}^N a(n)n^{-s}$ converge
uniformly on each $D(b,\delta,\varepsilon)$ to one function $f$, which is complex differentiable (equivalently
analytic) on $\mathrm{Re}\,s > b$. -/
@[kb "milne2020cft" "Ch. VI, Prop. 2.1"]
theorem prop_2_1 (a : ℕ → ℂ) {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hS : ∀ᶠ x : ℝ in atTop, ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖ ≤ A * x ^ b) :
    ∃ f : ℂ → ℂ,
      (∀ δ ε : ℝ, 0 < δ → 0 < ε →
        TendstoUniformlyOn (fun (N : ℕ) (s : ℂ) => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s) f atTop
          (sectorD b δ ε)) ∧
      DifferentiableOn ℂ f {s : ℂ | b < s.re} := by
  refine ⟨fun s => limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s), ?_, ?_⟩
  · intro δ ε hδ hε
    have hu := uniformCauchy_sector a hA hb hS hδ hε
    refine hu.tendstoUniformlyOn_of_tendsto fun s hs => ?_
    exact (hu.cauchySeq hs).tendsto_limUnder
  · have hu : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
        TendstoUniformlyOn (fun (N : ℕ) (s : ℂ) => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s)
          (fun s => limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s)) atTop
          (sectorD b δ ε) := by
      intro δ ε hδ hε
      have hu := uniformCauchy_sector a hA hb hS hδ hε
      refine hu.tendstoUniformlyOn_of_tendsto fun s hs => ?_
      exact (hu.cauchySeq hs).tendsto_limUnder
    have hloc : TendstoLocallyUniformlyOn
        (fun (N : ℕ) (s : ℂ) => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s)
        (fun s => limUnder atTop (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, a n / (n : ℂ) ^ s)) atTop
        {s : ℂ | b < s.re} := by
      intro u hu' s0 hs0
      obtain ⟨δ, ε, hδ, hε, hn⟩ := exists_sector_nhds (show b < s0.re from hs0)
      exact ⟨sectorD b δ ε, mem_nhdsWithin_of_mem_nhds hn, hu δ ε hδ hε u hu'⟩
    exact hloc.differentiableOn
      (Eventually.of_forall fun N => (differentiable_partial a N).differentiableOn)
      (isOpen_lt continuous_const Complex.continuous_re)

/-- **Lemma 2.10** (Milne, *CFT*, Chapter VI, p. 190): for a finite abelian group $A$ and a nontrivial character
$\chi : A\to\mathbb C^\times$, $\sum_{a\in A}\chi(a) = 0$. Mathlib's `sum_hom_units_eq_zero`. -/
@[kb "milne2020cft" "Ch. VI, Lemma 2.10"]
theorem lemma_2_10 {A : Type*} [CommGroup A] [Fintype A] (χ : A →* ℂˣ) (hχ : χ ≠ 1) :
    ∑ a : A, (χ a : ℂ) = 0 := by
  have h : (Units.coeHom ℂ).comp χ ≠ 1 := by
    intro h
    apply hχ
    ext a
    have := DFunLike.congr_fun h a
    simpa using this
  simpa using sum_hom_units_eq_zero _ h

/-- Characters `A →* ℂˣ` of a commutative group correspond to additive characters of `Additive A`. -/
def homUnitsEquivAddChar (A : Type*) [CommGroup A] : (A →* ℂˣ) ≃ AddChar (Additive A) ℂ where
  toFun χ :=
    { toFun := fun a => (χ a.toMul : ℂ)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by simp }
  invFun ψ := MonoidHom.toHomUnits (G := A) (M := ℂ) (ψ.toMonoidHom)
  left_inv χ := by ext a; exact rfl
  right_inv ψ := by ext a; exact rfl

/-- The characters $A\to\mathbb C^\times$ of a finite abelian group form a finite set (Milne, *CFT*, Chapter VI,
proof of Lemma 4.7: $A^\vee$ has as many elements as $A$). -/
instance finite_hom_units {A : Type*} [CommGroup A] [Finite A] : Finite (A →* ℂˣ) :=
  Finite.of_equiv _ (homUnitsEquivAddChar A).symm

/-- **Lemma 4.7** (Milne, *CFT*, Chapter VI, p. 197): for a finite abelian group $A$ and $a\in A$, $a \ne 1$,
$\sum_{\chi\in A^\vee}\chi(a) = 0$, where $A^\vee = \mathrm{Hom}(A,\mathbb C^\times)$ (a finite set,
`finite_hom_units`; the sum is `finsum`). From Mathlib's `AddChar.sum_apply_eq_zero_iff_ne_zero` for the additive
characters of `Additive A`. -/
@[kb "milne2020cft" "Ch. VI, Lemma 4.7"]
theorem lemma_4_7 {A : Type*} [CommGroup A] [Finite A] {a : A} (ha : a ≠ 1) :
    ∑ᶠ χ : A →* ℂˣ, (χ a : ℂ) = 0 := by
  classical
  have := Fintype.ofFinite A
  have : Fintype (A →* ℂˣ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have h0 := (AddChar.sum_apply_eq_zero_iff_ne_zero (α := Additive A) (a := Additive.ofMul a)).2
    (by simpa using ha)
  rw [← h0]
  exact Fintype.sum_equiv (homUnitsEquivAddChar A) _ _ (fun χ => by simp [homUnitsEquivAddChar])

/-- The case $a = 1$ in the proof of Lemma 4.7: $\sum_{\chi\in A^\vee}\chi(1) = |A^\vee| = |A|$. -/
theorem lemma_4_7_one {A : Type*} [CommGroup A] [Finite A] :
    ∑ᶠ χ : A →* ℂˣ, ((χ 1 : ℂˣ) : ℂ) = Nat.card A := by
  classical
  have := Fintype.ofFinite A
  have : Fintype (A →* ℂˣ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  simp only [map_one, Units.val_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have : Fintype.card (A →* ℂˣ) = Fintype.card (AddChar (Additive A) ℂ) :=
    Fintype.card_congr (homUnitsEquivAddChar A)
  rw [this, AddChar.card_eq, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_congr (Additive.ofMul : A ≃ Additive A).symm

end NumberFieldKB.MilneCFT.Ch6
