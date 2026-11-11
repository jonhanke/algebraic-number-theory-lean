import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Milne, *Class Field Theory*, VI, Remark 4.2 (a): real-variable lemmas for the Dirichlet-density half

Discrete Abel summation, the telescoping comparison with $\log\log$, the short-range Mertens estimate from an error
term in the prime number theorem, and summation by parts with bounded partial sums. Used in
`NumberFieldKB.MilneCFT.Ch6.Remark42aDirichlet`.
-/

open Filter Topology

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6.R42

/-! ## Part A: real-variable lemmas -/

/-- Discrete Abel summation against $1/n$: for $a<b$,
$\sum_{a<n\le b}\frac{P(n)-P(n-1)}{n} = \frac{P(b)}b - \frac{P(a)}{a+1} + \sum_{a<n<b}\frac{P(n)}{n(n+1)}$. -/
theorem abel_Ioc (P : ℕ → ℝ) {a b : ℕ} (hab : a < b) :
    ∑ n ∈ Finset.Ioc a b, (P n - P (n - 1)) / n =
      P b / b - P a / (a + 1) + ∑ n ∈ Finset.Ioo a b, P n / (n * (n + 1)) := by
  induction b, Nat.succ_le_of_lt hab using Nat.le_induction with
  | base =>
    have h1 : Finset.Ioc a (a + 1) = {a + 1} := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    have h2 : Finset.Ioo a (a + 1) = ∅ := by
      ext x; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    rw [h1, h2]
    simp only [Finset.sum_singleton, Finset.sum_empty, Nat.add_sub_cancel]
    push_cast
    ring
  | succ b hb ih =>
    have h3 : Finset.Ioo a (b + 1) = insert b (Finset.Ioo a b) := by
      ext x; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
    have h4 : b ∉ Finset.Ioo a b := by simp
    rw [Finset.sum_Ioc_succ_top (by omega), ih (by omega), h3, Finset.sum_insert h4]
    simp only [Nat.add_sub_cancel]
    have hb0 : (b : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
      linarith
    push_cast
    field_simp
    ring

/-- Telescoping comparison with $\log\log$: for $2\le a\le b$,
$\left|\sum_{a\le n<b}\frac1{(n+1)\log n} - (\log\log b-\log\log a)\right| \le \frac1{a\log a}$. -/
theorem loglog_telescope {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    |∑ n ∈ Finset.Ico a b, 1 / ((n + 1) * Real.log n) -
      (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 1 / (a * Real.log a) := by
  have key : ∀ n : ℕ, 2 ≤ n →
      |1 / (((n : ℝ) + 1) * Real.log n) - (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n))| ≤
        1 / ((n : ℝ) * Real.log n) - 1 / (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    intro n hn
    have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hL : 0 < Real.log n := Real.log_pos (by linarith)
    have hL' : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log hn0; push_cast; linarith
    have hL'pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hL hL'
    have hdiff : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n = Real.log (((n : ℝ) + 1) / n) := by
      rw [Real.log_div (by positivity) hn0.ne']; push_cast; ring
    have hup : Real.log (((n : ℝ) + 1) / n) ≤ 1 / n := by
      have := Real.log_le_sub_one_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
      have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
      linarith
    have hlo : 1 / ((n : ℝ) + 1) ≤ Real.log (((n : ℝ) + 1) / n) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < ((n : ℝ) + 1) / n by positivity)
      have e : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by field_simp; ring
      linarith
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    set L := Real.log n
    set L' := Real.log ((n + 1 : ℕ) : ℝ)
    rw [hcast]
    have ht : Real.log L' - Real.log L = Real.log (L' / L) := by rw [Real.log_div hL'pos.ne' hL.ne']
    have htup : Real.log (L' / L) ≤ 1 / ((n : ℝ) * L) := by
      have := Real.log_le_sub_one_of_pos (show 0 < L' / L by positivity)
      have e : L' / L - 1 = (L' - L) / L := by field_simp
      have e2 : (L' - L) / L ≤ (1 / n) / L := by
        apply div_le_div_of_nonneg_right _ hL.le; linarith
      have e3 : (1 / (n : ℝ)) / L = 1 / ((n : ℝ) * L) := by field_simp
      linarith
    have htlo : 1 / (((n : ℝ) + 1) * L') ≤ Real.log (L' / L) := by
      have := Real.one_sub_inv_le_log_of_pos (show 0 < L' / L by positivity)
      have e : 1 - (L' / L)⁻¹ = (L' - L) / L' := by field_simp
      have e2 : (1 / ((n : ℝ) + 1)) / L' ≤ (L' - L) / L' := by
        apply div_le_div_of_nonneg_right _ hL'pos.le; linarith
      have e3 : (1 / ((n : ℝ) + 1)) / L' = 1 / (((n : ℝ) + 1) * L') := by field_simp
      linarith
    have hcup : 1 / (((n : ℝ) + 1) * L) ≤ 1 / ((n : ℝ) * L) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    have hclo : 1 / (((n : ℝ) + 1) * L') ≤ 1 / (((n : ℝ) + 1) * L) := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    rw [abs_le]
    constructor <;> linarith
  have main : ∀ b : ℕ, a ≤ b →
      |∑ n ∈ Finset.Ico a b, 1 / (((n : ℝ) + 1) * Real.log n) -
        (Real.log (Real.log b) - Real.log (Real.log a))| ≤
        1 / ((a : ℝ) * Real.log a) - 1 / ((b : ℝ) * Real.log b) := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb]
      have := key b (by omega)
      have e : ∑ n ∈ Finset.Ico a b, 1 / (((n : ℝ) + 1) * Real.log n) +
            1 / (((b : ℝ) + 1) * Real.log b) - (Real.log (Real.log ((b + 1 : ℕ) : ℝ)) - Real.log (Real.log a)) =
          (∑ n ∈ Finset.Ico a b, 1 / (((n : ℝ) + 1) * Real.log n) -
            (Real.log (Real.log b) - Real.log (Real.log a))) +
          (1 / (((b : ℝ) + 1) * Real.log b) -
            (Real.log (Real.log ((b + 1 : ℕ) : ℝ)) - Real.log (Real.log b))) := by ring
      rw [e]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ _ := add_le_add ih this
        _ = _ := by ring
  have h := main b hab
  have hpos : 0 ≤ 1 / ((b : ℝ) * Real.log b) := by
    have : (0 : ℝ) ≤ Real.log b := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ b))
    positivity
  linarith

/-- **Short-range Mertens estimate** from an error term in the prime number theorem: if
$|P(n) - n/\log n|\le C n/\log^2 n$ for $n\ge2$, then for $2\le a<b\le 10a$,
$\left|\sum_{a<n\le b}\frac{P(n)-P(n-1)}n - (\log\log b - \log\log a)\right|\le\frac{11C+\log 10+1}{\log^2 a}$. -/
theorem block_mertens (P : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ n : ℕ, 2 ≤ n → |P n - n / Real.log n| ≤ C * n / Real.log n ^ 2)
    {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) (hb : b ≤ 10 * a) :
    |∑ n ∈ Finset.Ioc a b, (P n - P (n - 1)) / n - (Real.log (Real.log b) - Real.log (Real.log a))| ≤
      (11 * C + Real.log 10 + 1) / Real.log a ^ 2 := by
  have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hLa : 0 < Real.log a := Real.log_pos (by linarith)
  have hK : 0 < Real.log a ^ 2 := by positivity
  have hbR : (a : ℝ) < b := by exact_mod_cast hab
  have hb0 : (0 : ℝ) < b := by linarith
  have hbR10 : (b : ℝ) ≤ 10 * a := by exact_mod_cast hb
  have hLb : Real.log a ≤ Real.log b := Real.log_le_log ha0 hbR.le
  have hLbpos : 0 < Real.log b := lt_of_lt_of_le hLa hLb
  have hlogn : ∀ n : ℕ, a ≤ n → Real.log a ≤ Real.log n := fun n hn =>
    Real.log_le_log ha0 (by exact_mod_cast hn)
  set R : ℕ → ℝ := fun n => P n - n / Real.log n with hRdef
  have hR : ∀ n : ℕ, a ≤ n → |R n| ≤ C * n / Real.log a ^ 2 := by
    intro n hn
    have h1 := hP n (by omega)
    have hl := hlogn n hn
    have : C * n / Real.log n ^ 2 ≤ C * n / Real.log a ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) hK
      exact pow_le_pow_left₀ hLa.le hl 2
    exact le_trans h1 this
  have hS := abel_Ioc P hab
  have hsplit : ∑ n ∈ Finset.Ioo a b, P n / (n * (n + 1)) =
      ∑ n ∈ Finset.Ioo a b, 1 / (((n : ℝ) + 1) * Real.log n) +
        ∑ n ∈ Finset.Ioo a b, R n / (n * (n + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioo] at hn
    have hn2 : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
    have hl : 0 < Real.log n := Real.log_pos (by linarith)
    simp only [hRdef]
    field_simp
    ring
  have hIco : ∑ n ∈ Finset.Ico a b, 1 / (((n : ℝ) + 1) * Real.log n) =
      1 / (((a : ℝ) + 1) * Real.log a) +
        ∑ n ∈ Finset.Ioo a b, 1 / (((n : ℝ) + 1) * Real.log n) := by
    have : Finset.Ico a b = insert a (Finset.Ioo a b) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioo]; omega
    rw [this, Finset.sum_insert (by simp)]
  have hPb : P b / b = 1 / Real.log b + R b / b := by
    simp only [hRdef]; field_simp; ring
  have hPa : P a / (a + 1) = 1 / Real.log a - 1 / (((a : ℝ) + 1) * Real.log a) + R a / (a + 1) := by
    simp only [hRdef]; field_simp; ring
  have h1 : |1 / Real.log b - 1 / Real.log a| ≤ Real.log 10 / Real.log a ^ 2 := by
    have hl10 : Real.log b ≤ Real.log 10 + Real.log a := by
      rw [← Real.log_mul (by norm_num) ha0.ne']
      exact Real.log_le_log hb0 hbR10
    have e : 1 / Real.log b - 1 / Real.log a = -((Real.log b - Real.log a) / (Real.log a * Real.log b)) := by
      field_simp
      ring
    rw [e, abs_neg, abs_of_nonneg (by apply div_nonneg <;> nlinarith)]
    rw [div_le_div_iff₀ (by positivity) hK]
    have : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg hLa.le (sub_nonneg.2 hLb), mul_nonneg this (sub_nonneg.2 hLb)]
  have h2 : |∑ n ∈ Finset.Ico a b, 1 / (((n : ℝ) + 1) * Real.log n) -
      (Real.log (Real.log b) - Real.log (Real.log a))| ≤ 1 / Real.log a ^ 2 := by
    refine le_trans (loglog_telescope ha hab.le) ?_
    apply one_div_le_one_div_of_le hK
    have : Real.log a ≤ a := by
      have := Real.log_le_sub_one_of_pos ha0
      linarith
    nlinarith
  have hRb : |R b / b| ≤ C / Real.log a ^ 2 := by
    rw [abs_div, abs_of_pos hb0, div_le_iff₀ hb0]
    have := hR b hab.le
    calc _ ≤ _ := this
      _ = _ := by field_simp
  have hRa : |R a / (a + 1)| ≤ C / Real.log a ^ 2 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < a + 1), div_le_iff₀ (by linarith)]
    have := hR a le_rfl
    have e : C / Real.log a ^ 2 * (a + 1) = C * a / Real.log a ^ 2 + C / Real.log a ^ 2 := by ring
    have : 0 ≤ C / Real.log a ^ 2 := by positivity
    linarith
  have hRs : |∑ n ∈ Finset.Ioo a b, R n / (n * (n + 1))| ≤ 9 * C / Real.log a ^ 2 := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ n ∈ Finset.Ioo a b, |R n / (n * (n + 1))| ≤ C / Real.log a ^ 2 / (a + 1) := by
      intro n hn
      rw [Finset.mem_Ioo] at hn
      have hnR : (a : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
      have hn0 : (0 : ℝ) < n := by linarith
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n * (n + 1)), div_le_iff₀ (by positivity)]
      have := hR n hn.1.le
      have e : C / Real.log a ^ 2 / (a + 1) * (n * (n + 1)) =
          C * n / Real.log a ^ 2 * ((n + 1) / (a + 1)) := by field_simp
      have h3 : 1 ≤ ((n : ℝ) + 1) / (a + 1) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      have h4 : 0 ≤ C * n / Real.log a ^ 2 := by positivity
      rw [e]
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul]
    have hc : ((b - a - 1 : ℕ) : ℝ) ≤ 9 * a := by
      have : b - a - 1 ≤ 9 * a := by omega
      exact_mod_cast this
    have hCK : 0 ≤ C / Real.log a ^ 2 := by positivity
    have : ((b - a - 1 : ℕ) : ℝ) * (C / Real.log a ^ 2 / (a + 1)) =
        ((b - a - 1 : ℕ) : ℝ) / (a + 1) * (C / Real.log a ^ 2) := by ring
    rw [this]
    have h5 : ((b - a - 1 : ℕ) : ℝ) / (a + 1) ≤ 9 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have e : 9 * C / Real.log a ^ 2 = 9 * (C / Real.log a ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h5 hCK
  have hsum : (11 * C + Real.log 10 + 1) / Real.log a ^ 2 =
      Real.log 10 / Real.log a ^ 2 + 1 / Real.log a ^ 2 + 11 * (C / Real.log a ^ 2) := by ring
  have e9 : 9 * C / Real.log a ^ 2 = 9 * (C / Real.log a ^ 2) := by ring
  rw [hS, hsplit, hPb, hPa]
  rw [hIco] at h2
  rw [hsum]
  rw [abs_le] at h1 h2 hRb hRa hRs ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := hRb
  obtain ⟨h4a, h4b⟩ := hRa
  obtain ⟨h5a, h5b⟩ := hRs
  constructor <;> linarith

/-- Summation by parts with bounded partial sums: if $|\sum_{m\le n}u_m|\le M$ for all $n$ and $b$ is antitone and
nonnegative, then $|\sum_{m\le N}b_m u_m|\le M b_0$. -/
theorem abel_bound (u b : ℕ → ℝ) {M : ℝ} (hM : ∀ n, |∑ m ∈ Finset.range (n + 1), u m| ≤ M)
    (hb : Antitone b) (hb0 : ∀ n, 0 ≤ b n) (N : ℕ) :
    |∑ m ∈ Finset.range (N + 1), b m * u m| ≤ M * b 0 := by
  have hid : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1), b m * u m =
      b N * ∑ m ∈ Finset.range (N + 1), u m +
        ∑ m ∈ Finset.range N, (b m - b (m + 1)) * ∑ k ∈ Finset.range (m + 1), u k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hA : ∑ m ∈ Finset.range (N + 1 + 1), u m = ∑ m ∈ Finset.range (N + 1), u m + u (N + 1) :=
        Finset.sum_range_succ u (N + 1)
      rw [Finset.sum_range_succ (fun m => b m * u m) (N + 1), ih,
        Finset.sum_range_succ (fun m => (b m - b (m + 1)) * ∑ k ∈ Finset.range (m + 1), u k) N, hA]
      ring
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rw [hid N]
  have h1 : |b N * ∑ m ∈ Finset.range (N + 1), u m| ≤ b N * M := by
    rw [abs_mul, abs_of_nonneg (hb0 N)]
    exact mul_le_mul_of_nonneg_left (hM N) (hb0 N)
  have h2 : |∑ m ∈ Finset.range N, (b m - b (m + 1)) * ∑ k ∈ Finset.range (m + 1), u k| ≤
      ∑ m ∈ Finset.range N, (b m - b (m + 1)) * M := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro m _
    have : 0 ≤ b m - b (m + 1) := sub_nonneg.2 (hb (Nat.le_succ m))
    rw [abs_mul, abs_of_nonneg this]
    exact mul_le_mul_of_nonneg_left (hM m) this
  have h3 : ∑ m ∈ Finset.range N, (b m - b (m + 1)) * M = (b 0 - b N) * M := by
    rw [← Finset.sum_mul, Finset.sum_range_sub']
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ b N * M + (b 0 - b N) * M := add_le_add h1 (h2.trans h3.le)
    _ = M * b 0 := by ring

/-- $|\log(1+\delta/j) - \delta\log(1+1/j)|\le 1/j^2$ for $j\ge1$ and $0\le\delta\le1$. -/
theorem log_combo_bound {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    |Real.log (1 + δ / j) - δ * Real.log (1 + 1 / j)| ≤ 1 / (j : ℝ) ^ 2 := by
  have bnd : ∀ x : ℝ, 0 ≤ x → x - x ^ 2 ≤ Real.log (1 + x) ∧ Real.log (1 + x) ≤ x := by
    intro x hx
    constructor
    · have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
      have e : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
      have : x - x ^ 2 ≤ x / (1 + x) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith [pow_nonneg hx 3]
      linarith
    · have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
      linarith
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hs0 : 0 ≤ 1 / (j : ℝ) := by positivity
  have hs1 : 1 / (j : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hj1
  have e1 : δ / j = δ * (1 / j) := by ring
  have e2 : 1 / (j : ℝ) ^ 2 = (1 / (j : ℝ)) ^ 2 := by ring
  rw [e1, e2]
  set s : ℝ := 1 / j
  obtain ⟨a1, a2⟩ := bnd (δ * s) (by positivity)
  obtain ⟨b1, b2⟩ := bnd s hs0
  have hss : s ^ 2 ≥ 0 := by positivity
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg hδ0 (sub_nonneg.2 b2), mul_nonneg hs0 hs0, mul_nonneg (sub_nonneg.2 hδ1) (mul_nonneg hδ0 hss)]
  · nlinarith [mul_nonneg hδ0 (sub_nonneg.2 b1), mul_nonneg (sub_nonneg.2 hδ1) hss, mul_nonneg hδ0 hss]

/-- $\sum_{1\le j<K}1/j^2\le 2$. -/
theorem sum_inv_sq_le_two (K : ℕ) : ∑ j ∈ Finset.Ico 1 K, 1 / (j : ℝ) ^ 2 ≤ 2 := by
  have h : ∀ n : ℕ, 1 ≤ n → ∑ j ∈ Finset.Ico 1 (n + 1), 1 / (j : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : 1 / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases K with _ | n
  · simp
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := h n hn
      have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith

end NumberFieldKB.MilneCFT.Ch6.R42
