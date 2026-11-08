import NumberFieldKB.WeilBNT.FieldModule
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.FieldTheory.Finite.Basic

/-!
# Weil, *Basic Number Theory*, I.§3: classification of locally compact fields (arithmetic part)

$K$ is a nondiscrete locally compact division ring, `modK K` its module (`FieldModule`). Weil writes
$F(m)=\operatorname{mod}_K(m\cdot1_K)$ for $m\in\mathbb N$.

* `weil_I_3_lemma3`: Lemma 3. A multiplicative $F:\mathbb N\to\mathbb R_+$ with $F(m+n)\le A\sup(F(m),F(n))$ is
  either $\le1$ everywhere or $m\mapsto m^\lambda$ with $\lambda>0$.
* `modK_intCast_mul`: text p. 10, $\operatorname{mod}_K(mx)=F(\lvert m\rvert)\operatorname{mod}_K(x)$ for $m\in\mathbb Z$.
* `weil_I_3_lemma4`: Lemma 4. If $F$ is bounded then $F\le1$ and $K$ is ultrametric.
* `weil_I_3_thm5_charP`, `weil_I_3_thm5_charZero`: Thm. 5, the description of $F$: in
  characteristic $p>1$, $F(m)=0$ for $p\mid m$ and $1$ otherwise; in characteristic $0$, either
  $F(m)=\lvert m\rvert_p^{\delta}$ for a prime $p$ and some $\delta>0$, or $F(m)=m^{\delta}$ with $\delta>0$.

**Not formalized here** (recorded in the coverage table): the second half of Thm. 5(b), that in characteristic $0$
the closure of $\mathbb Q$ in $K$ is $\mathbb Q_v$ and $K$ is a division algebra of finite dimension $\delta$ over it
(Weil's proof uses I.§2 Thm. 3, Cor. 2: a locally compact topological vector space over $K$ is finite-dimensional),
the Corollary of Thm. 5 and the text p. 12 ($\mathbb R$-fields are $\mathbb R,\mathbb C,\mathbb H$).
-/

open Topology Filter
open scoped NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.WeilBNT.FieldModule

/-- A real inequality `k a ≤ c + k X` for all positive integers `k` forces `a ≤ X`. -/
theorem le_of_forall_nat_mul_le {a X c : ℝ} (h : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * a ≤ c + k * X) :
    a ≤ X := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := exists_nat_gt (c / (a - X))
  have h1 := h (k + 1) (by omega)
  have h2 : c / (a - X) < ((k + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  rw [div_lt_iff₀ (by linarith)] at h2
  nlinarith

/-- Digit bound for Lemma 3: expanding in base `n`. -/
theorem lemma3_digit_bound (g : ℕ → ℝ) {A : ℝ} (hA : 1 ≤ A) (hg1 : ∀ m, 1 ≤ g m)
    (hmul : ∀ m n, g (m * n) ≤ g m * g n) (hadd : ∀ m n, g (m + n) ≤ A * max (g m) (g n))
    {n : ℕ} (hn : 2 ≤ n) {B : ℝ} (hB : ∀ e < n, g e ≤ B) :
    ∀ m, g m ≤ B * (A * g n) ^ Nat.log n m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m < n
    · rw [Nat.log_of_lt hm]; simpa using hB m hm
    · push Not at hm
      have hq : m / n < m := Nat.div_lt_self (by omega) (by omega)
      have hB1 : 1 ≤ B := (hg1 0).trans (hB 0 (by omega))
      have hD : 1 ≤ A * g n := by nlinarith [hg1 n]
      have hlog : Nat.log n m = Nat.log n (m / n) + 1 := by
        have h1 := Nat.log_div_base n m
        have h2 : 0 < Nat.log n m := Nat.log_pos (by omega) hm
        omega
      have hm' : n * (m / n) + m % n = m := Nat.div_add_mod m n
      have h1 := ih (m / n) hq
      have h2 : g m ≤ A * max (g n * g (m / n)) (g (m % n)) := by
        calc g m = g (n * (m / n) + m % n) := by rw [hm']
          _ ≤ A * max (g (n * (m / n))) (g (m % n)) := hadd _ _
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            exact max_le_max (hmul _ _) le_rfl
      set P := (A * g n) ^ Nat.log n (m / n) with hP
      have hP1 : 1 ≤ P := one_le_pow₀ hD
      have h3 : g n * g (m / n) ≤ g n * (B * P) :=
        mul_le_mul_of_nonneg_left h1 (by linarith [hg1 n])
      have h4 : g (m % n) ≤ g n * (B * P) := by
        have := hB (m % n) (Nat.mod_lt _ (by omega))
        have h6 : B ≤ B * P := le_mul_of_one_le_right (by linarith) hP1
        have h7 : B * P ≤ g n * (B * P) := le_mul_of_one_le_left (by nlinarith) (hg1 n)
        linarith
      have h5 : max (g n * g (m / n)) (g (m % n)) ≤ g n * (B * P) := max_le h3 h4
      rw [hlog, pow_succ]
      calc g m ≤ A * (g n * (B * P)) := h2.trans (mul_le_mul_of_nonneg_left h5 (by linarith))
        _ = B * (P * (A * g n)) := by ring

/-- Key inequality of Lemma 3: `log g(m) · log n ≤ log m · (log A + log g(n))`. -/
theorem lemma3_key (g : ℕ → ℝ) {A : ℝ} (hA : 1 ≤ A) (hg1 : ∀ m, 1 ≤ g m)
    (hmul : ∀ m n, g (m * n) ≤ g m * g n) (hadd : ∀ m n, g (m + n) ≤ A * max (g m) (g n))
    (hpow : ∀ m k, g (m ^ k) = g m ^ k) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Real.log (g m) * Real.log n ≤ Real.log m * (Real.log A + Real.log (g n)) := by
  set B : ℝ := ∑ e ∈ Finset.range n, g e with hBdef
  have hB : ∀ e < n, g e ≤ B := fun e he =>
    Finset.single_le_sum (f := g) (fun i _ => by linarith [hg1 i]) (Finset.mem_range.2 he)
  have hB1 : 1 ≤ B := (hg1 0).trans (hB 0 (by omega))
  have hbound := lemma3_digit_bound g hA hg1 hmul hadd hn hB
  have hD : 1 ≤ A * g n := by nlinarith [hg1 n]
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  have hlogD : 0 ≤ Real.log (A * g n) := Real.log_nonneg hD
  have hlogD' : Real.log (A * g n) = Real.log A + Real.log (g n) :=
    Real.log_mul (by linarith) (by linarith [hg1 n])
  rw [← hlogD']
  refine le_of_forall_nat_mul_le (c := Real.log B * Real.log n) (fun k hk => ?_)
  have h1 := hbound (m ^ k)
  rw [hpow] at h1
  have hgm : 0 < g m := by linarith [hg1 m]
  have h2 := Real.log_le_log (pow_pos hgm k) h1
  rw [Real.log_pow, Real.log_mul (by linarith) (by positivity), Real.log_pow] at h2
  have h3 : (Nat.log n (m ^ k) : ℝ) ≤ k * Real.log m / Real.log n := by
    have := Real.natLog_le_logb (m ^ k) n
    rw [Real.logb] at this
    simpa [Nat.cast_pow, Real.log_pow] using this
  have h4 : (Nat.log n (m ^ k) : ℝ) * Real.log (A * g n) ≤ k * Real.log m / Real.log n * Real.log (A * g n) :=
    mul_le_mul_of_nonneg_right h3 hlogD
  have h5 : (k : ℝ) * Real.log (g m) ≤ Real.log B + k * Real.log m / Real.log n * Real.log (A * g n) := by
    linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hlogn.le
  have e : (Real.log B + k * Real.log m / Real.log n * Real.log (A * g n)) * Real.log n
      = Real.log B * Real.log n + k * (Real.log m * Real.log (A * g n)) := by
    field_simp
  rw [e] at h6
  linarith

/-- Symmetrised key inequality of Lemma 3 (replace `n` by `n ^ j`, let `j → ∞`). -/
theorem lemma3_key2 (g : ℕ → ℝ) {A : ℝ} (hA : 1 ≤ A) (hg1 : ∀ m, 1 ≤ g m)
    (hmul : ∀ m n, g (m * n) ≤ g m * g n) (hadd : ∀ m n, g (m + n) ≤ A * max (g m) (g n))
    (hpow : ∀ m k, g (m ^ k) = g m ^ k) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Real.log (g m) * Real.log n ≤ Real.log m * Real.log (g n) := by
  refine le_of_forall_nat_mul_le (c := Real.log m * Real.log A) (fun j hj => ?_)
  have hn' : 2 ≤ n ^ j := hn.trans (by simpa using Nat.pow_le_pow_right (by omega) hj)
  have h := lemma3_key g hA hg1 hmul hadd hpow hm hn'
  rw [hpow, Real.log_pow, Nat.cast_pow, Real.log_pow] at h
  nlinarith [h]

/-- `max 1 (x ^ k) = (max 1 x) ^ k` for nonnegative `x`. -/
theorem max_one_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : max 1 (x ^ k) = (max 1 x) ^ k := by
  rcases le_total x 1 with h | h
  · rw [max_eq_left h, one_pow, max_eq_left (pow_le_one₀ hx h)]
  · rw [max_eq_right h, max_eq_right (one_le_pow₀ h)]

/-- I.§3, Lemma 3. Weil assumes $F(mn)=F(m)F(n)$ and $F(m+n)\le A\sup(F(m),F(n))$ for all $m,n\in\mathbb N$. -/
@[kb "weil1973bnt" "Ch. I, §3, Lemma 3"]
theorem weil_I_3_lemma3 (F : ℕ → ℝ≥0) (hmul : ∀ m n, F (m * n) = F m * F n) {A : ℝ≥0}
    (hadd : ∀ m n, F (m + n) ≤ A * max (F m) (F n)) :
    (∀ m, F m ≤ 1) ∨ ∃ l : ℝ, 0 < l ∧ ∀ m, F m = (m : ℝ≥0) ^ l := by
  by_cases h1 : F 1 = 0
  · left
    intro m
    have := hmul m 1
    rw [mul_one, h1, mul_zero] at this
    simp [this]
  have hF1 : F 1 = 1 := by
    have : F 1 * F 1 = F 1 * 1 := by rw [mul_one, ← hmul, one_mul]
    exact mul_left_cancel₀ h1 this
  by_cases h0 : F 0 = 0
  swap
  · left
    intro m
    have := hmul 0 m
    rw [zero_mul] at this
    have h : F 0 * F m = F 0 * 1 := by rw [mul_one, ← this]
    exact (mul_left_cancel₀ h0 h).le
  have hFpow : ∀ m k, F (m ^ k) = F m ^ k := by
    intro m k
    induction k with
    | zero => simpa using hF1
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  set g : ℕ → ℝ := fun m => max 1 (F m : ℝ) with hg
  set A' : ℝ := max 1 (A : ℝ) with hA'
  have hA1 : 1 ≤ A' := le_max_left _ _
  have hg1 : ∀ m, 1 ≤ g m := fun m => le_max_left _ _
  have hFg : ∀ m, (F m : ℝ) ≤ g m := fun m => le_max_right _ _
  have hgmul : ∀ m n, g (m * n) ≤ g m * g n := by
    intro m n
    refine max_le (one_le_mul_of_one_le_of_one_le (hg1 m) (hg1 n)) ?_
    rw [hmul, NNReal.coe_mul]
    exact mul_le_mul (hFg m) (hFg n) (by positivity) (by linarith [hg1 m])
  have hgadd : ∀ m n, g (m + n) ≤ A' * max (g m) (g n) := by
    intro m n
    have hmax : 1 ≤ max (g m) (g n) := (hg1 m).trans (le_max_left _ _)
    refine max_le (by nlinarith) ?_
    have h := hadd m n
    have h' : (F (m + n) : ℝ) ≤ (A : ℝ) * max (F m : ℝ) (F n : ℝ) := by exact_mod_cast h
    refine h'.trans (mul_le_mul (le_max_right _ _) (max_le_max (hFg m) (hFg n)) (by positivity)
      (by linarith))
  have hgpow : ∀ m k, g (m ^ k) = g m ^ k := by
    intro m k
    simp only [hg, hFpow, NNReal.coe_pow]
    exact max_one_pow (by positivity) k
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log (g 2) / Real.log 2 with hc
  have hc0 : 0 ≤ c := div_nonneg (Real.log_nonneg (hg1 2)) hlog2.le
  have hgm : ∀ m : ℕ, 2 ≤ m → g m = (m : ℝ) ^ c := by
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have e1 := lemma3_key2 g hA1 hg1 hgmul hgadd hgpow hm (le_refl 2)
    have e2 := lemma3_key2 g hA1 hg1 hgmul hgadd hgpow (le_refl 2) hm
    have e : Real.log (g m) = c * Real.log m := by
      rw [hc]
      field_simp
      push_cast at e1 e2
      linarith
    rw [Real.rpow_def_of_pos hm0, mul_comm, ← e, Real.exp_log (by linarith [hg1 m])]
  by_cases hcz : c = 0
  · left
    intro m
    rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
      · simp [h0]
      · simp [hF1]
    · have := (hFg m).trans (hgm m hm).le
      rw [hcz, Real.rpow_zero] at this
      exact_mod_cast this
  · right
    have hcpos : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcz)
    refine ⟨c, hcpos, fun m => ?_⟩
    rcases Nat.lt_or_ge m 2 with hm | hm
    · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
      · simp [h0, NNReal.zero_rpow hcz]
      · simp [hF1]
    · apply NNReal.eq
      rw [NNReal.coe_rpow, NNReal.coe_natCast]
      have hgt : 1 < g m := by
        rw [hgm m hm]
        exact Real.one_lt_rpow (by exact_mod_cast hm) hcpos
      rw [← hgm m hm]
      by_contra hne
      have : g m = 1 := by
        have : (F m : ℝ) ≤ 1 := by
          by_contra hlt
          push Not at hlt
          exact hne (by simp only [hg]; rw [max_eq_right hlt.le])
        simp only [hg]; exact max_eq_left this
      linarith

variable {K : Type*} [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [T2Space K]

/-- The module is invariant under negation, since $(-1)^2=1$. -/
theorem modK_neg (y : K) : modK K (-y) = modK K y := by
  have hneg : modK K (-1) = 1 := by
    have h1 : modK K (-1) ^ 2 = 1 := by
      rw [sq, ← modK_mul]; simp
    exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).1 h1
  rw [← neg_one_mul, modK_mul, hneg, one_mul]

@[kb "weil1973bnt" "Ch. I, §3, text p. 10"]
theorem modK_intCast_mul (m : ℤ) (x : K) : modK K ((m : K) * x) = modK K (m.natAbs : K) * modK K x := by
  rw [modK_mul]
  congr 1
  rcases Int.natAbs_eq m with h | h
  · have : ((m : ℤ) : K) = ((m.natAbs : ℤ) : K) := congrArg _ h
    rw [this, Int.cast_natCast]
  · have : ((m : ℤ) : K) = -((m.natAbs : ℤ) : K) := by
      rw [← Int.cast_neg]; exact congrArg _ h
    rw [this, Int.cast_natCast, modK_neg]

variable [(𝓝[≠] (0 : K)).NeBot]

/-- The module of a sum of `2 ^ n` terms is at most `weilConst ^ n` times the largest module. -/
theorem modK_sum_range_two_pow (n : ℕ) : ∀ (x : ℕ → K) (M : ℝ≥0), (∀ i < 2 ^ n, modK K (x i) ≤ M) →
    modK K (∑ i ∈ Finset.range (2 ^ n), x i) ≤ weilConst K ^ n * M := by
  induction n with
  | zero => intro x M h; simpa using h 0 (by norm_num)
  | succ n ih =>
    intro x M h
    have e : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
    have h' : ∀ i < 2 ^ n + 2 ^ n, modK K (x i) ≤ M := by rw [← e]; exact h
    rw [e, Finset.sum_range_add]
    have h1 := ih x M (fun i hi => h' i (by omega))
    have h2 := ih (fun i => x (2 ^ n + i)) M (fun i hi => h' _ (by omega))
    calc _ ≤ weilConst K * max (modK K (∑ i ∈ Finset.range (2 ^ n), x i))
            (modK K (∑ i ∈ Finset.range (2 ^ n), x (2 ^ n + i))) := modK_add_le _ _
      _ ≤ weilConst K * (weilConst K ^ n * M) := by gcongr; exact max_le h1 h2
      _ = _ := by ring

/-- Core of Lemma 4: if the module is at most `1` on the natural numbers, then `modK z ≤ 1` implies
`modK (1 + z) ≤ 1`. -/
theorem modK_one_add_le_one (hF : ∀ m : ℕ, modK K (m : K) ≤ 1) {z : K} (hz : modK K z ≤ 1) :
    modK K (1 + z) ≤ 1 := by
  set A := weilConst K with hAdef
  have hA1 : 1 ≤ A := le_csSup bddAbove_weilConst ⟨0, by simp, by simp⟩
  have key : ∀ n : ℕ, modK K (1 + z) ^ (2 ^ n) ≤ A ^ (n + 1) := by
    intro n
    set N := 2 ^ n with hN
    have hN1 : 1 ≤ N := Nat.one_le_two_pow
    have hsum := modK_sum_range_two_pow (n + 1) (fun i => z ^ i * 1 ^ (N - i) * (N.choose i : K)) 1 (by
      intro i _
      rw [one_pow, mul_one, modK_mul, modK_pow]
      calc _ ≤ 1 * 1 := mul_le_mul' (pow_le_one₀ zero_le hz) (hF (N.choose i))
        _ = 1 := one_mul 1)
    have hbin : ∑ i ∈ Finset.range (2 ^ (n + 1)), z ^ i * 1 ^ (N - i) * (N.choose i : K)
        = (1 + z) ^ N := by
      rw [add_comm (1 : K) z, (Commute.one_right z).add_pow N]
      refine (Finset.sum_subset ?_ ?_).symm
      · intro i hi
        rw [Finset.mem_range] at hi ⊢
        have : 2 ^ (n + 1) = N + N := by rw [hN]; ring
        omega
      · intro i _ hi
        rw [Finset.mem_range, not_lt] at hi
        rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp
    rw [hbin, modK_pow, mul_one] at hsum
    exact hsum
  by_contra hlt
  push Not at hlt
  set t := modK K (1 + z) with ht
  have ht0 : (0 : ℝ) < t := by exact_mod_cast lt_trans zero_lt_one hlt
  have hlogt : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast hlt)
  have hk : ∀ n : ℕ, Real.log t ≤ ((n : ℝ) + 1) * Real.log A / 2 ^ n := by
    intro n
    have h1 : (t : ℝ) ^ (2 ^ n) ≤ (A : ℝ) ^ (n + 1) := by exact_mod_cast key n
    have h2 := Real.log_le_log (pow_pos ht0 _) h1
    rw [Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h3 := (h1.add h2).mul_const (Real.log A)
  rw [zero_add, zero_mul] at h3
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * Real.log A / 2 ^ n) atTop (𝓝 0) := by
    refine h3.congr (fun n => ?_)
    rw [one_div, inv_pow, pow_one]
    ring
  have := ge_of_tendsto' hlim hk
  linarith

@[kb "weil1973bnt" "Ch. I, §3, Lemma 4"]
theorem weil_I_3_lemma4 (h : BddAbove (Set.range fun m : ℕ => modK K (m : K))) :
    (∀ m : ℕ, modK K (m : K) ≤ 1) ∧ IsUltrametricMod K := by
  have hF : ∀ m : ℕ, modK K (m : K) ≤ 1 := by
    intro m
    obtain ⟨M, hM⟩ := h
    by_contra hgt
    push Not at hgt
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hgt
    have : modK K ((m ^ k : ℕ) : K) ≤ M := hM ⟨m ^ k, rfl⟩
    rw [Nat.cast_pow, modK_pow] at this
    exact absurd hk (not_lt.2 this)
  refine ⟨hF, fun x y => ?_⟩
  suffices H : ∀ x y : K, modK K y ≤ modK K x → modK K (x + y) ≤ modK K x by
    rcases le_total (modK K y) (modK K x) with hxy | hxy
    · rw [max_eq_left hxy]; exact H x y hxy
    · rw [max_eq_right hxy, add_comm]; exact H y x hxy
  intro x y hxy
  by_cases hx : x = 0
  · have : y = 0 := modK_eq_zero_iff.1 (le_antisymm (by simpa [hx] using hxy) zero_le)
    simp [hx, this]
  · have hz : modK K (y * x⁻¹) ≤ 1 := by
      rw [modK_mul, modK_inv hx]
      have hpos : 0 < modK K x := modK_pos_iff.2 hx
      rw [← div_eq_mul_inv]
      exact (div_le_one hpos).2 hxy
    have h1 := modK_one_add_le_one hF hz
    have e : x + y = (1 + y * x⁻¹) * x := by
      rw [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one, add_comm]
    rw [e, modK_mul]
    exact mul_le_of_le_one_left zero_le h1

@[kb "weil1973bnt" "Ch. I, §3, Thm. 5 (a)"]
theorem weil_I_3_thm5_charP (p : ℕ) [Fact p.Prime] [CharP K p] (m : ℕ) :
    modK K (m : K) = if (p ∣ m) then 0 else 1 := by
  split_ifs with hdvd
  · rw [(CharP.cast_eq_zero_iff K p m).2 hdvd]; exact modK_zero
  · have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hm : ((m : ZMod p)) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h1 := ZMod.pow_card_sub_one_eq_one hm
    have h2 : ((m ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact h1
    rw [ZMod.natCast_eq_natCast_iff] at h2
    have h3 : ((m ^ (p - 1) : ℕ) : K) = ((1 : ℕ) : K) := CharP.natCast_eq_natCast' K p h2
    have h4 : modK K (m : K) ^ (p - 1) = 1 := by
      rw [← modK_pow, ← Nat.cast_pow, h3]; simp
    exact (pow_eq_one_iff_of_nonneg zero_le (by omega)).1 h4

/-- Lemma 3 applied to $F(m)=\operatorname{mod}_K(m\cdot1_K)$, using Prop. 1 and Thm. 4 of I.§2. -/
theorem modK_nat_dichotomy :
    (∀ m : ℕ, modK K (m : K) ≤ 1) ∨ ∃ l : ℝ, 0 < l ∧ ∀ m : ℕ, modK K (m : K) = (m : ℝ≥0) ^ l :=
  weil_I_3_lemma3 (fun m : ℕ => modK K (m : K)) (fun m n => by simp [modK_mul])
    (A := weilConst K) (fun m n => by
      show modK K ((m + n : ℕ) : K) ≤ _
      rw [Nat.cast_add]
      exact modK_add_le _ _)

/-- Thm. 5 (b), description of $F$ in characteristic $0$: either $F(m)=\lvert m\rvert_p^\delta$ ($p$ a prime,
$\delta>0$: the case $v=p$) or $F(m)=m^\delta$ ($\delta>0$: the case $v=\infty$). -/
@[kb "weil1973bnt" "Ch. I, §3, Thm. 5 (b), the function F"]
theorem weil_I_3_thm5_charZero [CharZero K] :
    (∃ (p : ℕ) (_ : p.Prime) (l : ℝ), 0 < l ∧ ∀ m : ℕ, modK K (m : K) = ⟨(padicNorm p m : ℝ) ^ l,
      Real.rpow_nonneg (by exact_mod_cast padicNorm.nonneg _) _⟩)
    ∨ ∃ l : ℝ, 0 < l ∧ ∀ m : ℕ, modK K (m : K) = (m : ℝ≥0) ^ l := by
  rcases modK_nat_dichotomy (K := K) with hle | ⟨l, hl, h⟩
  swap
  · exact Or.inr ⟨l, hl, h⟩
  left
  obtain ⟨-, hU⟩ := weil_I_3_lemma4 (K := K) ⟨1, by rintro _ ⟨m, rfl⟩; exact hle m⟩
  -- some positive integer has module less than `1`
  have hex : ∃ n : ℕ, 0 < n ∧ modK K (n : K) < 1 := by
    obtain ⟨a, -, ha⟩ := (isCompact_modK_le (K := K) 1).exists_mapClusterPt (f := atTop)
      (u := fun n : ℕ => (n : K)) (Filter.tendsto_principal.2 (Eventually.of_forall fun n => hle n))
    have hS : {x : K | modK K (x - a) < 1 / 2} ∈ 𝓝 a := by
      refine (isOpen_lt (continuous_modK.comp (continuous_id.sub continuous_const))
        continuous_const).mem_nhds ?_
      show modK K (a - a) < 1 / 2
      rw [sub_self, modK_zero]; norm_num
    obtain ⟨m, -, hm⟩ := Filter.frequently_atTop.1 (ha.frequently hS) 0
    obtain ⟨m', hm', hm'S⟩ := Filter.frequently_atTop.1 (ha.frequently hS) (m + 1)
    refine ⟨m' - m, by omega, ?_⟩
    have e : ((m' - m : ℕ) : K) = ((m' : K) - a) + -((m : K) - a) := by
      rw [Nat.cast_sub (by omega)]; abel
    rw [e]
    refine lt_of_le_of_lt (hU _ _) ?_
    rw [modK_neg]
    have : max (modK K ((m' : K) - a)) (modK K ((m : K) - a)) < 1 / 2 := max_lt hm'S hm
    exact this.trans (by norm_num)
  classical
  set p := Nat.find hex with hpdef
  have hp0 : 0 < p := (Nat.find_spec hex).1
  have hp1 : modK K (p : K) < 1 := (Nat.find_spec hex).2
  have hFge : ∀ m : ℕ, 0 < m → m < p → 1 ≤ modK K (m : K) := by
    intro m hm0 hmp
    by_contra hlt
    exact Nat.find_min hex hmp ⟨hm0, not_le.1 hlt⟩
  have hp2 : 2 ≤ p := by
    by_contra hlt
    have : p = 1 := by omega
    rw [this] at hp1
    simp at hp1
  have hpp : p.Prime := by
    rw [Nat.prime_def]
    refine ⟨hp2, fun d hd => ?_⟩
    obtain ⟨k, hk⟩ := hd
    by_contra hne
    push Not at hne
    obtain ⟨hd1, hdp⟩ := hne
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hdlt : d < p := lt_of_le_of_ne (Nat.le_of_dvd hp0 ⟨k, hk⟩) hdp
    have hk1 : k ≠ 1 := by rintro rfl; apply hdp; omega
    have hklt : k < p := by
      have : 2 ≤ d := by omega
      have : 2 ≤ k := by omega
      nlinarith
    have h3 : modK K (p : K) = modK K (d : K) * modK K (k : K) := by
      rw [← modK_mul, ← Nat.cast_mul, ← hk]
    have h4 := mul_le_mul' (hFge d hd0 hdlt) (hFge k hk0 hklt)
    rw [one_mul, ← h3] at h4
    exact absurd hp1 (not_lt.2 h4)
  have hcong : ∀ x : ℕ, modK K ((1 + p * x : ℕ) : K) = 1 := by
    intro x
    have hlt : modK K ((p * x : ℕ) : K) < modK K (1 : K) := by
      rw [Nat.cast_mul, modK_mul, modK_one]
      calc _ ≤ modK K (p : K) * 1 := mul_le_mul' le_rfl (hle x)
        _ < 1 := by rw [mul_one]; exact hp1
    have := modK_add_eq_of_lt hU hlt
    rw [Nat.cast_add, Nat.cast_one, this, modK_one]
  have : Fact p.Prime := ⟨hpp⟩
  have hunit : ∀ m : ℕ, ¬ p ∣ m → modK K (m : K) = 1 := by
    intro m hm
    have hm' : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
    have h1 := ZMod.pow_card_sub_one_eq_one hm'
    have h2 : ((m ^ (p - 1) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by push_cast; exact h1
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    have h3 : m ^ (p - 1) = 1 + p * (m ^ (p - 1) / p) := by
      have := Nat.div_add_mod (m ^ (p - 1)) p
      rw [h2, Nat.mod_eq_of_lt hpp.one_lt] at this
      rw [add_comm]; exact this.symm
    have h4 : modK K (m : K) ^ (p - 1) = 1 := by
      rw [← modK_pow, ← Nat.cast_pow, h3]; exact hcong _
    exact (pow_eq_one_iff_of_nonneg zero_le (by omega)).1 h4
  -- the exponent
  have hFp0 : 0 < modK K (p : K) := modK_pos_iff.2 (Nat.cast_ne_zero.2 hp0.ne')
  have hf0 : (0 : ℝ) < (modK K (p : K) : ℝ) := by exact_mod_cast hFp0
  have hf1 : (modK K (p : K) : ℝ) < 1 := by exact_mod_cast hp1
  have hpR : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hpR
  have hlogf : Real.log (modK K (p : K) : ℝ) < 0 := Real.log_neg hf0 hf1
  set l : ℝ := -Real.log (modK K (p : K) : ℝ) / Real.log p with hldef
  have hl : 0 < l := div_pos (by linarith) hlogp
  have hfp : (modK K (p : K) : ℝ) = (p : ℝ) ^ (-l) := by
    rw [Real.rpow_def_of_pos (by linarith), hldef]
    have : Real.log p * -(-Real.log (modK K (p : K) : ℝ) / Real.log p)
        = Real.log (modK K (p : K) : ℝ) := by
      field_simp
    rw [this, Real.exp_log hf0]
  refine ⟨p, hpp, l, hl, fun m => ?_⟩
  apply NNReal.eq
  show (modK K (m : K) : ℝ) = (padicNorm p m : ℝ) ^ l
  by_cases hm0 : m = 0
  · subst hm0
    simp [Real.zero_rpow hl.ne']
  · obtain ⟨k, hk⟩ : ∃ k, k = padicValNat p m := ⟨_, rfl⟩
    obtain ⟨m', hm'⟩ := pow_padicValNat_dvd (p := p) (n := m)
    rw [← hk] at hm'
    have hnd : ¬ p ∣ m' := by
      rintro ⟨c, hc⟩
      apply pow_succ_padicValNat_not_dvd (p := p) hm0
      exact ⟨c, by rw [← hk, hm', hc, pow_succ]; ring⟩
    have hFm : modK K (m : K) = modK K (p : K) ^ k := by
      conv_lhs => rw [hm']
      rw [Nat.cast_mul, modK_mul, Nat.cast_pow, modK_pow, hunit m' hnd, mul_one]
    have hnorm : (padicNorm p m : ℝ) = (((p : ℝ) ^ k)⁻¹) := by
      rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm0), padicValRat.of_nat, ← hk]
      push_cast
      rw [zpow_neg, zpow_natCast]
    rw [hFm, hnorm]
    have hp0R : (0 : ℝ) ≤ p := by linarith
    push_cast
    rw [hfp, Real.inv_rpow (pow_nonneg hp0R _), ← Real.rpow_natCast, ← Real.rpow_mul hp0R,
      ← Real.rpow_natCast, ← Real.rpow_mul hp0R, ← Real.rpow_neg (by positivity)]
    congr 1
    ring

/-- Def. 2: $K$ is a $p$-field if $p$ is a prime and $\operatorname{mod}_K(p\cdot1_K)<1$. -/
def IsPField (K : Type*) [DivisionRing K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [LocallyCompactSpace K] [T2Space K] (p : ℕ) : Prop :=
  p.Prime ∧ modK K (p : K) < 1

/-- Text after Def. 2: in a $p$-field the module is bounded on the prime ring, so $K$ is ultrametric. -/
@[kb "weil1973bnt" "Ch. I, §3, text p. 12 (a p-field is ultrametric)"]
theorem isUltrametricMod_of_isPField {p : ℕ} (hK : IsPField K p) : IsUltrametricMod K := by
  rcases modK_nat_dichotomy (K := K) with h | ⟨l, hl, h⟩
  · exact (weil_I_3_lemma4 ⟨1, by rintro _ ⟨m, rfl⟩; exact h m⟩).2
  · exfalso
    have h1 : modK K (p : K) = (p : ℝ≥0) ^ l := h p
    have h2 : (1 : ℝ≥0) < (p : ℝ≥0) ^ l :=
      NNReal.one_lt_rpow (by exact_mod_cast hK.1.one_lt) hl
    have h3 := hK.2
    rw [h1] at h3
    exact absurd h3 (not_lt.2 h2.le)

end NumberFieldKB.WeilBNT.FieldModule
