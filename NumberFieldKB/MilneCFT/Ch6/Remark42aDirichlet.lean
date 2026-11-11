import NumberFieldKB.MilneCFT.Ch6.Remark42aTauCeti
import NumberFieldKB.MilneCFT.Ch6.Remark42aAnalysis
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real

/-!
# Milne, *Class Field Theory*, VI, Remark 4.2 (a): the Dirichlet-density half, from the error-term prime number theorem

Milne's Dirichlet density (`MilneHasDirichletDensity`) is the *bounded-difference* form:
$\sum_{p\in T}p^{-s} - \delta\log\frac1{s-1}$ is bounded as $s\downarrow1$. For the primes $T$ with leading decimal
digit $1$ and $\delta = \log_{10}2$ this is proved here from the named input **`R42.PNTError`**, the prime number
theorem with the classical error term
$$\pi(x) = \frac{x}{\log x} + O\!\left(\frac{x}{\log^2 x}\right)$$
(de la Vallée Poussin 1899; any error term $O(x/\log^{2}x)$ suffices). Plain $\pi(x)\sim x/\log x$ does not suffice
for the bounded-difference form: the argument needs each decade $(10^j, 10^{j+1}]$ to contribute $O(1/j^2)$.

Route (`remark_4_2a_of_pntError`):
1. **Short-range Mertens estimate** (`block_mertens`): for $2\le a<b\le 10a$,
   $\sum_{a<p\le b}1/p = \log\log b - \log\log a + O(1/\log^2 a)$, by discrete Abel summation
   (`abel_Ioc`) against $\pi(n) = n/\log n + R(n)$ and the telescoping bounds
   $\frac1{(n+1)\log(n+1)} \le \log\log(n+1)-\log\log n \le \frac1{n\log n}$ (`loglog_telescope`).
2. **Bounded partial sums** (`partialSum_bounded`): $A(N) = \sum_{p\le N}(\mathbf 1_T(p)-\delta)/p$ is bounded: over a
   decade the main terms give $\log(1+\delta/j) - \delta\log(1+1/j) = O(1/j^2)$ (`log_combo_bound`, `decade_bound`).
3. **Abel summation in $s$** (`abel_bound`): $\left|\sum_p(\mathbf 1_T(p)-\delta)p^{-s}\right|$ is bounded uniformly
   in $s>1$ by $\sup_N|A(N)|$ plus a boundary term; then `isBigO_primeIdealZetaSum_sub_log` over $\mathbb Q$.
-/

open Filter Topology IsDedekindDomain NumberField Asymptotics

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6.R42

/-! ## The named input -/

/-- **The prime number theorem with the classical error term** (named input; de la Vallée Poussin 1899; e.g.
Montgomery–Vaughan, *Multiplicative Number Theory I*, Theorem 6.9, gives $\pi(x) = \mathrm{li}(x) +
O(x e^{-c\sqrt{\log x}})$, and $\mathrm{li}(x) = x/\log x + O(x/\log^2 x)$): $|\pi(x) - x/\log x| \le C x/\log^2 x$
for $x\ge 2$. Here $\pi(x)$ is the number of primes of $\mathbb Q$ of norm at most $x$
(`NumberFieldKB.MilneANT.primeCount`). Not in Mathlib, Tau Ceti or the other ports, which have only
$\pi(x)\sim x/\log x$ (`R42.pnt`). -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a) (input: prime number theorem with error term)"]
structure PNTError : Prop where
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |(NumberFieldKB.MilneANT.primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x : ℝ) - x / Real.log x| ≤
      C * x / Real.log x ^ 2

/-! ## Part B: prime counts at integers -/

/-- $\pi_S(n)$ at a natural number, as a real number. -/
def pc (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) : ℝ := TauCeti.primeCount ℚ S (n : ℝ)

/-- The increment $\pi_S(n) - \pi_S(n-1)$ (the number of primes of $S$ of norm $n$). -/
def dpc (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) : ℝ := pc S n - pc S (n - 1)

theorem pc_eq (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) :
    pc S n = (NumberFieldKB.MilneANT.primeCount S n : ℝ) := tauCeti_primeCount_eq S n

theorem pc_zero (S : Set (HeightOneSpectrum (𝓞 ℚ))) : pc S 0 = 0 :=
  TauCeti.primeCount_eq_zero_of_lt_two S (by norm_num)

theorem dpc_nonneg (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) : 0 ≤ dpc S n := by
  unfold dpc pc
  have := TauCeti.primeCount_mono (K := ℚ) S (show ((n - 1 : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.sub_le n 1)
  linarith

theorem dpc_univ (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) :
    dpc Set.univ n = dpc S n + dpc Sᶜ n := by
  have h : ∀ x, TauCeti.primeCount ℚ Set.univ x = TauCeti.primeCount ℚ S x + TauCeti.primeCount ℚ Sᶜ x := by
    intro x
    rw [← TauCeti.primeCount_union disjoint_compl_right, Set.union_compl_self]
  unfold dpc pc
  rw [h, h]
  ring

theorem dpc_le (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) : dpc S n ≤ dpc Set.univ n := by
  rw [dpc_univ S n]
  linarith [dpc_nonneg Sᶜ n]

/-- The increment is the number of primes of $S$ in $(n-1, n]$. -/
theorem dpc_eq_ncard (S : Set (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) :
    dpc S n = ({𝔭 ∈ S | (((n - 1 : ℕ) : ℝ)) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ (n : ℝ)}.ncard : ℝ) := by
  unfold dpc
  rw [pc_eq, pc_eq, primeCount_split S (show ((n - 1 : ℕ) : ℝ) ≤ n by exact_mod_cast Nat.sub_le n 1)]
  push_cast
  ring

/-- In $(10^j, 2\cdot10^j]$ every prime has leading digit $1$. -/
theorem dpc_block_one {j n : ℕ} (hj : 1 ≤ j) (h1 : 10 ^ j < n) (h2 : n ≤ 2 * 10 ^ j) :
    dpc leadingDigitOnePrimes n = dpc Set.univ n := by
  rw [dpc_univ leadingDigitOnePrimes n]
  suffices h : dpc leadingDigitOnePrimesᶜ n = 0 by rw [h, add_zero]
  rw [dpc_eq_ncard]
  have hempty : {𝔭 ∈ leadingDigitOnePrimesᶜ | (((n - 1 : ℕ) : ℝ)) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ (n : ℝ)} = ∅ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hv hlo hhi
    have hlo' : n - 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast hlo
    have hhi' : Ideal.absNorm v.asIdeal ≤ n := by exact_mod_cast hhi
    have hmem : v ∈ {𝔭 ∈ (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) | ((10 : ℝ) ^ j) <
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ 2 * 10 ^ j} := by
      refine ⟨trivial, ?_, ?_⟩
      · have : 10 ^ j < Ideal.absNorm v.asIdeal := by omega
        exact_mod_cast this
      · have : Ideal.absNorm v.asIdeal ≤ 2 * 10 ^ j := by omega
        exact_mod_cast this
    rw [← block_one j hj] at hmem
    exact hv hmem.1
  rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-- In $(2\cdot10^j, 10^{j+1}]$ no prime has leading digit $1$. -/
theorem dpc_block_other {j n : ℕ} (h1 : 2 * 10 ^ j < n) (h2 : n ≤ 10 ^ (j + 1)) :
    dpc leadingDigitOnePrimes n = 0 := by
  rw [dpc_eq_ncard]
  have hempty : {𝔭 ∈ leadingDigitOnePrimes | (((n - 1 : ℕ) : ℝ)) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ (n : ℝ)} = ∅ := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hv hlo hhi
    have hlo' : n - 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast hlo
    have hhi' : Ideal.absNorm v.asIdeal ≤ n := by exact_mod_cast hhi
    have hmem : v ∈ {𝔭 ∈ leadingDigitOnePrimes | (2 * 10 ^ j : ℝ) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ 10 ^ (j + 1)} := by
      refine ⟨hv, ?_, ?_⟩
      · have : 2 * 10 ^ j < Ideal.absNorm v.asIdeal := by omega
        exact_mod_cast this
      · have : Ideal.absNorm v.asIdeal ≤ 10 ^ (j + 1) := by omega
        exact_mod_cast this
    rw [block_other j] at hmem
    exact hmem
  rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-! ## Part C: bounded partial sums -/

/-- $\delta = \log_{10}2$. -/
abbrev δ₀ : ℝ := Real.log 2 / Real.log 10

theorem log_ten_pos : 0 < Real.log 10 := Real.log_pos (by norm_num)

theorem one_le_log_ten : 1 ≤ Real.log 10 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  norm_num at this ⊢
  linarith

theorem δ₀_nonneg : 0 ≤ δ₀ := div_nonneg (Real.log_nonneg (by norm_num)) log_ten_pos.le

theorem δ₀_le_one : δ₀ ≤ 1 := by
  rw [div_le_one log_ten_pos]
  exact Real.log_le_log (by norm_num) (by norm_num)

/-- The summand $u_n = (\mathbf 1_T - \delta)(n)/n$ (zero unless $n$ is prime). -/
def uT (n : ℕ) : ℝ := (dpc leadingDigitOnePrimes n - δ₀ * dpc Set.univ n) / n

/-- $S(a,b) = \sum_{a<p\le b}1/p$. -/
def sumInv (a b : ℕ) : ℝ := ∑ n ∈ Finset.Ioc a b, dpc Set.univ n / n

theorem abs_uT_le (n : ℕ) : |uT n| ≤ dpc Set.univ n / n := by
  unfold uT
  rw [abs_div, Nat.abs_cast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have h0 := dpc_nonneg leadingDigitOnePrimes n
  have h1 := dpc_le leadingDigitOnePrimes n
  have h2 := δ₀_nonneg
  have h3 := δ₀_le_one
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_sum_uT_le (a b : ℕ) : |∑ n ∈ Finset.Ioc a b, uT n| ≤ sumInv a b :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => abs_uT_le n)

theorem sumInv_mono {a b b' : ℕ} (h : b ≤ b') : sumInv a b ≤ sumInv a b' := by
  unfold sumInv
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_right h)
  intro n _ _
  exact div_nonneg (dpc_nonneg _ n) (Nat.cast_nonneg n)

theorem sumInv_nonneg (a b : ℕ) : 0 ≤ sumInv a b :=
  Finset.sum_nonneg fun n _ => div_nonneg (dpc_nonneg _ n) (Nat.cast_nonneg n)

/-- $\log\log(c\cdot10^j) - \log\log 10^j = \log(1 + \log c/(j\log 10))$. -/
theorem loglog_ratio (c : ℝ) (hc : 1 ≤ c) {j : ℕ} (hj : 1 ≤ j) :
    Real.log (Real.log (c * 10 ^ j)) - Real.log (Real.log (10 ^ j)) =
      Real.log (1 + Real.log c / Real.log 10 / j) := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hl : Real.log ((10 : ℝ) ^ j) = j * Real.log 10 := by rw [Real.log_pow]
  have hl2 : Real.log (c * 10 ^ j) = Real.log c + j * Real.log 10 := by
    rw [Real.log_mul (by linarith) (by positivity), hl]
  have hpos : 0 < (j : ℝ) * Real.log 10 := mul_pos hj' log_ten_pos
  have hc0 : 0 ≤ Real.log c := Real.log_nonneg hc
  rw [hl, hl2, ← Real.log_div (by positivity) hpos.ne']
  congr 1
  field_simp
  ring

section PNT

variable {C : ℝ} (hC : 0 ≤ C)
  (hP : ∀ x : ℝ, 2 ≤ x →
    |(NumberFieldKB.MilneANT.primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x : ℝ) - x / Real.log x| ≤
      C * x / Real.log x ^ 2)
include hC hP

omit hC in
theorem hP_nat : ∀ n : ℕ, 2 ≤ n → |pc Set.univ n - n / Real.log n| ≤ C * n / Real.log n ^ 2 := by
  intro n hn
  rw [pc_eq]
  exact hP n (by exact_mod_cast hn)

/-- The short-range Mertens estimate for the actual primes. -/
theorem sumInv_mertens {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) (hb : b ≤ 10 * a) :
    |sumInv a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤
      (11 * C + Real.log 10 + 1) / Real.log a ^ 2 :=
  block_mertens (pc Set.univ) hC (hP_nat hP) ha hab hb

/-- One decade contributes $O(1/j^2)$. -/
theorem decade_bound {j : ℕ} (hj : 1 ≤ j) :
    |∑ n ∈ Finset.Ioc (10 ^ j) (10 ^ (j + 1)), uT n| ≤ (1 + (11 * C + Real.log 10 + 1)) / (j : ℝ) ^ 2 := by
  set E := 11 * C + Real.log 10 + 1 with hE
  set a := 10 ^ j with ha
  have ha2 : 2 ≤ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj : 10 ^ 1 ≤ 10 ^ j)
  have hsplit := Finset.sum_Ioc_consecutive uT (show a ≤ 2 * a by omega)
    (show 2 * a ≤ 10 ^ (j + 1) by rw [pow_succ]; omega)
  have h1 : ∑ n ∈ Finset.Ioc a (2 * a), uT n = (1 - δ₀) * sumInv a (2 * a) := by
    unfold sumInv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    unfold uT
    rw [dpc_block_one hj hn.1 hn.2]
    ring
  have h2 : ∑ n ∈ Finset.Ioc (2 * a) (10 ^ (j + 1)), uT n = -δ₀ * sumInv (2 * a) (10 ^ (j + 1)) := by
    unfold sumInv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    unfold uT
    rw [dpc_block_other hn.1 hn.2]
    ring
  rw [← hsplit, h1, h2]
  have e1 := sumInv_mertens hC hP ha2 (show a < 2 * a by omega) (show 2 * a ≤ 10 * a by omega)
  have e2 := sumInv_mertens hC hP (show 2 ≤ 2 * a by omega)
    (show 2 * a < 10 ^ (j + 1) by rw [pow_succ]; omega)
    (show 10 ^ (j + 1) ≤ 10 * (2 * a) by rw [pow_succ]; omega)
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hla : Real.log (a : ℝ) = j * Real.log 10 := by rw [ha]; push_cast; rw [Real.log_pow]
  have hla2 : (j : ℝ) ≤ Real.log (a : ℝ) := by
    rw [hla]; nlinarith [one_le_log_ten]
  have hapos : (0 : ℝ) < a := by positivity
  have hlog2a : Real.log (a : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
    Real.log_le_log hapos (by push_cast; linarith)
  have hE0 : 0 ≤ E := by have := log_ten_pos; rw [hE]; positivity
  have hjpos : (0 : ℝ) < j := by linarith
  have hb1 : E / Real.log (a : ℝ) ^ 2 ≤ E / (j : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hE0 (by positivity) (pow_le_pow_left₀ hjpos.le hla2 2)
  have hb2 : E / Real.log ((2 * a : ℕ) : ℝ) ^ 2 ≤ E / (j : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left hE0 (by positivity) (pow_le_pow_left₀ hjpos.le (hla2.trans hlog2a) 2)
  have m1 : Real.log (Real.log ((2 * a : ℕ) : ℝ)) - Real.log (Real.log (a : ℝ)) =
      Real.log (1 + δ₀ / j) := by
    have := loglog_ratio 2 (by norm_num) hj
    rw [ha]; push_cast; rw [this]
  have m2 : Real.log (Real.log ((10 ^ (j + 1) : ℕ) : ℝ)) - Real.log (Real.log (a : ℝ)) =
      Real.log (1 + 1 / j) := by
    have := loglog_ratio 10 (by norm_num) hj
    rw [div_self log_ten_pos.ne'] at this
    rw [ha]; push_cast; rw [pow_succ, mul_comm, this]
  have hc := log_combo_bound δ₀_nonneg δ₀_le_one hj
  have hd0 := δ₀_nonneg
  have hd1 := δ₀_le_one
  set L1 := Real.log (Real.log ((2 * a : ℕ) : ℝ))
  set L0 := Real.log (Real.log (a : ℝ))
  set L2 := Real.log (Real.log ((10 ^ (j + 1) : ℕ) : ℝ))
  have key : (1 - δ₀) * sumInv a (2 * a) + -δ₀ * sumInv (2 * a) (10 ^ (j + 1)) =
      (Real.log (1 + δ₀ / j) - δ₀ * Real.log (1 + 1 / j)) +
        ((1 - δ₀) * (sumInv a (2 * a) - (L1 - L0)) -
          δ₀ * (sumInv (2 * a) (10 ^ (j + 1)) - (L2 - L1))) := by
    rw [← m1, ← m2]; ring
  rw [key]
  rw [abs_le] at e1 e2 hc ⊢
  have hjj : 1 / (j : ℝ) ^ 2 + E / (j : ℝ) ^ 2 = (1 + E) / (j : ℝ) ^ 2 := by ring
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, hc.1, hc.2, hb1, hb2]

end PNT

/-- The partial sums $A(N) = \sum_{0<n\le N}u_n = \sum_{p\le N}(\mathbf 1_T(p) - \delta)/p$. -/
def AT (N : ℕ) : ℝ := ∑ n ∈ Finset.Ioc 0 N, uT n

theorem AT_pow_ten (K : ℕ) (hK : 1 ≤ K) :
    AT (10 ^ K) = AT 10 + ∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc (10 ^ j) (10 ^ (j + 1)), uT n := by
  induction K, hK using Nat.le_induction with
  | base => simp [AT]
  | succ K hK ih =>
    rw [Finset.sum_Ico_succ_top hK, ← add_assoc, ← ih, AT, AT,
      Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ K))]

theorem sum_range_eq_AT (n : ℕ) : ∑ m ∈ Finset.range (n + 1), uT m = AT n := by
  induction n with
  | zero => simp [AT, uT]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, AT, AT, Finset.sum_Ioc_succ_top (Nat.zero_le n)]

theorem log_three_ge_one : 1 ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  norm_num at this ⊢
  linarith

section PNT2

variable {C : ℝ} (hC : 0 ≤ C)
  (hP : ∀ x : ℝ, 2 ≤ x →
    |(NumberFieldKB.MilneANT.primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x : ℝ) - x / Real.log x| ≤
      C * x / Real.log x ^ 2)
include hC hP

/-- **The partial sums $A(N)$ are bounded.** -/
theorem AT_bounded : ∃ M : ℝ, ∀ N : ℕ, |AT N| ≤ M := by
  set E := 11 * C + Real.log 10 + 1 with hE
  have hE0 : 0 ≤ E := by have := log_ten_pos; rw [hE]; positivity
  refine ⟨sumInv 0 10 + 2 * (1 + E) + (1 + E), fun N => ?_⟩
  have h0 := sumInv_nonneg 0 10
  rcases le_or_gt N 10 with hN | hN
  · have := (abs_sum_uT_le 0 N).trans (sumInv_mono hN)
    unfold AT; nlinarith
  set K := Nat.log 10 N with hKdef
  have hK1 : 1 ≤ K := Nat.log_pos (by norm_num) hN.le
  have hlo : 10 ^ K ≤ N := Nat.pow_log_le_self 10 (by omega)
  have hhi : N < 10 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hsplit : AT N = AT (10 ^ K) + ∑ n ∈ Finset.Ioc (10 ^ K) N, uT n := by
    unfold AT; rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hlo]
  -- the last, incomplete decade
  have hlast : |∑ n ∈ Finset.Ioc (10 ^ K) N, uT n| ≤ 1 + E := by
    refine (abs_sum_uT_le _ _).trans ((sumInv_mono hhi.le).trans ?_)
    have ha2 : 2 ≤ 10 ^ K := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hK1 : 10 ^ 1 ≤ 10 ^ K)
    have e := sumInv_mertens hC hP ha2 (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self K))
      (by rw [pow_succ]; omega)
    have m2 : Real.log (Real.log ((10 ^ (K + 1) : ℕ) : ℝ)) - Real.log (Real.log ((10 ^ K : ℕ) : ℝ)) =
        Real.log (1 + 1 / K) := by
      have := loglog_ratio 10 (by norm_num) hK1
      rw [div_self log_ten_pos.ne'] at this
      push_cast; rw [pow_succ, mul_comm, this]
    rw [m2] at e
    have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have hl1 : Real.log (1 + 1 / K) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / K by positivity)
      have : (1 : ℝ) / K ≤ 1 := by rw [div_le_one (by linarith)]; exact hK'
      linarith
    have hla : (1 : ℝ) ≤ Real.log ((10 ^ K : ℕ) : ℝ) := by
      push_cast; rw [Real.log_pow]; nlinarith [one_le_log_ten]
    have hEl : E / Real.log ((10 ^ K : ℕ) : ℝ) ^ 2 ≤ E :=
      div_le_self hE0 (one_le_pow₀ hla)
    rw [abs_le] at e
    linarith [e.2]
  have hdec : |∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc (10 ^ j) (10 ^ (j + 1)), uT n| ≤ 2 * (1 + E) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.Ico 1 K, |∑ n ∈ Finset.Ioc (10 ^ j) (10 ^ (j + 1)), uT n|
        ≤ ∑ j ∈ Finset.Ico 1 K, (1 + E) * (1 / (j : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have := decade_bound hC hP (Finset.mem_Ico.1 hj).1
          rw [mul_one_div]; exact this
      _ = (1 + E) * ∑ j ∈ Finset.Ico 1 K, 1 / (j : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (1 + E) * 2 := mul_le_mul_of_nonneg_left (sum_inv_sq_le_two K) (by linarith)
      _ = 2 * (1 + E) := by ring
  have h10 : |AT 10| ≤ sumInv 0 10 := abs_sum_uT_le 0 10
  rw [hsplit, AT_pow_ten K hK1]
  calc |AT 10 + ∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc (10 ^ j) (10 ^ (j + 1)), uT n +
        ∑ n ∈ Finset.Ioc (10 ^ K) N, uT n|
      ≤ |AT 10| + |∑ j ∈ Finset.Ico 1 K, ∑ n ∈ Finset.Ioc (10 ^ j) (10 ^ (j + 1)), uT n| +
        |∑ n ∈ Finset.Ioc (10 ^ K) N, uT n| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- A crude bound $\pi(n)\le 3(1+C)(n+1)$. -/
theorem pc_univ_le (n : ℕ) : pc Set.univ n ≤ 3 * (1 + C) * (n + 1) := by
  have key : ∀ m : ℕ, 3 ≤ m → pc Set.univ m ≤ (1 + C) * m := by
    intro m hm
    have h := hP_nat hP m (by omega)
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hl : 1 ≤ Real.log m := log_three_ge_one.trans (Real.log_le_log (by norm_num) hm')
    have h1 : (m : ℝ) / Real.log m ≤ m := div_le_self (by linarith) hl
    have h2 : C * m / Real.log m ^ 2 ≤ C * m := div_le_self (by positivity) (one_le_pow₀ hl)
    rw [abs_le] at h
    nlinarith [h.2]
  rcases le_or_gt 3 n with hn | hn
  · have := key n hn
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  · have h3 := key 3 le_rfl
    have hmono : pc Set.univ n ≤ pc Set.univ 3 :=
      TauCeti.primeCount_mono (K := ℚ) _ (by exact_mod_cast hn.le)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at h3
    nlinarith

end PNT2

/-- $W(k) = \pi_T(k) - \delta\,\pi(k)$. -/
def WT (k : ℕ) : ℝ := pc leadingDigitOnePrimes k - δ₀ * pc Set.univ k

/-- The Abel weights $b_n = \max(n,1)^{1-s}$. -/
def bS (s : ℝ) (n : ℕ) : ℝ := ((max n 1 : ℕ) : ℝ) ^ (1 - s)

theorem abel_s_identity (s : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, NumberFieldKB.MilneANT.abelD s k * WT (k + 1) =
      ∑ n ∈ Finset.range (N + 1), bS s n * uT n - NumberFieldKB.MilneANT.abelU s N * WT N := by
  induction N with
  | zero => simp [uT, WT, pc_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ _ (N + 1)]
    have hx : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hb : bS s (N + 1) * uT (N + 1) =
        NumberFieldKB.MilneANT.abelU s N * (WT (N + 1) - WT N) := by
      simp only [bS, uT, WT, dpc, NumberFieldKB.MilneANT.abelU, Nat.add_sub_cancel]
      rw [max_eq_left (by omega)]
      push_cast
      rw [Real.rpow_sub hx, Real.rpow_one, Real.rpow_neg hx.le]
      field_simp
      ring
    rw [hb]
    simp only [NumberFieldKB.MilneANT.abelD]
    ring

section PNT3

variable {C : ℝ} (hC : 0 ≤ C)
  (hP : ∀ x : ℝ, 2 ≤ x →
    |(NumberFieldKB.MilneANT.primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x : ℝ) - x / Real.log x| ≤
      C * x / Real.log x ^ 2)
include hC hP

/-- **Uniform bound in $s$**: $\left|\sum_{p\in T}p^{-s} - \delta\sum_p p^{-s}\right|\le B$ for all $s>1$. -/
theorem zeta_diff_bounded : ∃ B : ℝ, ∀ s : ℝ, 1 < s →
    |leadingDigitOnePrimes.primeIdealZetaSum s - δ₀ * (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))).primeIdealZetaSum s|
      ≤ B := by
  obtain ⟨M, hM⟩ := AT_bounded hC hP
  refine ⟨M + 6 * (1 + C), fun s hs => ?_⟩
  obtain ⟨hsT, eT⟩ := NumberFieldKB.MilneANT.primeIdealZetaSum_eq_tsum leadingDigitOnePrimes hs
  obtain ⟨hsU, eU⟩ := NumberFieldKB.MilneANT.primeIdealZetaSum_eq_tsum
    (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) hs
  have hsum : HasSum (fun k => NumberFieldKB.MilneANT.abelD s k * WT (k + 1))
      (leadingDigitOnePrimes.primeIdealZetaSum s -
        δ₀ * (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))).primeIdealZetaSum s) := by
    rw [eT, eU]
    convert hsT.hasSum.sub (hsU.hasSum.mul_left δ₀) using 1
    funext k
    simp only [WT, pc_eq]
    push_cast
    ring
  have hbound : ∀ N : ℕ, |∑ k ∈ Finset.range N, NumberFieldKB.MilneANT.abelD s k * WT (k + 1)| ≤
      M + 6 * (1 + C) := by
    intro N
    rw [abel_s_identity]
    have hab : |∑ n ∈ Finset.range (N + 1), bS s n * uT n| ≤ M * bS s 0 := by
      refine abel_bound uT (bS s) (fun n => (sum_range_eq_AT n).symm ▸ hM n) ?_ ?_ N
      · intro m n hmn
        unfold bS
        exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < max m 1 by omega))
          (by exact_mod_cast max_le_max hmn le_rfl) (by linarith)
      · intro n; unfold bS; positivity
    have hb0 : bS s 0 = 1 := by simp [bS]
    rw [hb0, mul_one] at hab
    have hx : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hU : NumberFieldKB.MilneANT.abelU s N * ((N : ℝ) + 1) ≤ 1 := by
      unfold NumberFieldKB.MilneANT.abelU
      rw [Real.rpow_neg hx.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hx s), mul_one]
      calc (N : ℝ) + 1 = ((N : ℝ) + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((N : ℝ) + 1) ^ s := Real.rpow_le_rpow_of_exponent_le (by linarith) hs.le
    have hU0 : 0 ≤ NumberFieldKB.MilneANT.abelU s N := by
      unfold NumberFieldKB.MilneANT.abelU; positivity
    have hW : |WT N| ≤ 6 * (1 + C) * ((N : ℝ) + 1) := by
      have h1 := pc_univ_le hC hP N
      have h2 : pc leadingDigitOnePrimes N ≤ pc Set.univ N :=
        TauCeti.primeCount_mono_set (Set.subset_univ _) _
      have h3 : 0 ≤ pc leadingDigitOnePrimes N := TauCeti.primeCount_nonneg _ _
      have := δ₀_nonneg
      have := δ₀_le_one
      unfold WT
      rw [abs_le]
      constructor <;> nlinarith
    have hbd : |NumberFieldKB.MilneANT.abelU s N * WT N| ≤ 6 * (1 + C) := by
      rw [abs_mul, abs_of_nonneg hU0]
      calc NumberFieldKB.MilneANT.abelU s N * |WT N|
          ≤ NumberFieldKB.MilneANT.abelU s N * (6 * (1 + C) * ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hW hU0
        _ = 6 * (1 + C) * (NumberFieldKB.MilneANT.abelU s N * ((N : ℝ) + 1)) := by ring
        _ ≤ 6 * (1 + C) * 1 := mul_le_mul_of_nonneg_left hU (by linarith)
        _ = 6 * (1 + C) := mul_one _
    calc _ ≤ |∑ n ∈ Finset.range (N + 1), bS s n * uT n| + |NumberFieldKB.MilneANT.abelU s N * WT N| :=
          abs_sub _ _
      _ ≤ M + 6 * (1 + C) := add_le_add hab hbd
  exact le_of_tendsto' hsum.tendsto_sum_nat.abs hbound

end PNT3

/-- **Remark 4.2 (a), Dirichlet half, from the error-term prime number theorem** (Milne, *CFT*, VI, p. 194): given
`PNTError`, the primes with leading decimal digit $1$ have Dirichlet density $\log_{10}2$ in Milne's
bounded-difference sense. -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a) (Dirichlet density, from the prime number theorem with error term)"]
theorem dirichlet_of_pntError (h : PNTError) :
    MilneHasDirichletDensity leadingDigitOnePrimes (Real.log 2 / Real.log 10) := by
  obtain ⟨C, hC, hP⟩ := h.bound
  obtain ⟨B, hB⟩ := zeta_diff_bounded hC hP
  have h1 : (fun s : ℝ => leadingDigitOnePrimes.primeIdealZetaSum s -
      δ₀ * (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))).primeIdealZetaSum s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    refine IsBigO.of_bound B ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa using hB s hs
  have h2 := (NumberFieldKB.Chebotarev.isBigO_primeIdealZetaSum_sub_log (F := ℚ)).const_mul_left δ₀
  unfold MilneHasDirichletDensity
  refine (h1.add h2).congr_left fun s => ?_
  ring

end NumberFieldKB.MilneCFT.Ch6.R42

namespace NumberFieldKB.MilneCFT.Ch6

/-- **Remark 4.2 (a)** (Milne, *CFT*, VI, p. 194), from the prime number theorem with error term (`R42.PNTError`):
both halves of the named statement. The no-natural-density half is unconditional (`remark_4_2a_not_natural`). -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a)"]
theorem remark_4_2a_of_pntError (h : R42.PNTError) : Remark4_2a :=
  ⟨R42.dirichlet_of_pntError h, remark_4_2a_not_natural⟩

end NumberFieldKB.MilneCFT.Ch6
