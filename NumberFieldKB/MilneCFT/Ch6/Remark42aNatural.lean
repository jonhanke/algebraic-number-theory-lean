import NumberFieldKB.MilneCFT.Ch6.Density

/-!
# Milne, *Class Field Theory*, VI, Remark 4.2 (a): no natural density, from the prime number theorem

The primes with leading decimal digit $1$ have no natural density, given the prime number theorem
$\pi(x) \sim x/\log x$ (`not_natural_of_pnt`). Writing $r(x) = \pi_T(x)/\pi(x)$: every prime in $(10^k, 2\cdot10^k]$
has leading digit $1$ and none in $(2\cdot10^k, 10^{k+1}]$ does, so
$r(2\cdot10^k) = r(10^k)\rho_k + 1 - \rho_k$ and $r(10^{k+1}) = r(2\cdot10^k)\sigma_k$ with
$\rho_k = \pi(10^k)/\pi(2\cdot10^k)\to\frac12$ and $\sigma_k = \pi(2\cdot10^k)/\pi(10^{k+1})\to\frac15$. A limit
$\delta$ of $r$ would satisfy $\delta = \frac{\delta+1}2$ and $\delta = \frac\delta5$.
-/

open Filter Topology IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6.R42

/-! ## Leading digits -/

theorem getLast?_digits_div_ten (n : ℕ) (h : 10 ≤ n) :
    (Nat.digits 10 n).getLast? = (Nat.digits 10 (n / 10)).getLast? := by
  have hn : n ≠ 0 := by omega
  have hq : n / 10 ≠ 0 := by omega
  rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn)]
  obtain ⟨a, l, hl⟩ : ∃ a l, Nat.digits 10 (n / 10) = a :: l := by
    cases h' : Nat.digits 10 (n / 10) with
    | nil => exact absurd h' (Nat.digits_ne_nil_iff_ne_zero.mpr hq)
    | cons a l => exact ⟨a, l, rfl⟩
  rw [hl, List.getLast?_cons_cons]

theorem getLast?_digits_div_pow (k n : ℕ) (h : 10 ^ k ≤ n) :
    (Nat.digits 10 n).getLast? = (Nat.digits 10 (n / 10 ^ k)).getLast? := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have h10 : 10 ≤ n := le_trans (by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) h
    rw [getLast?_digits_div_ten n h10, ih (n / 10)]
    · rw [Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    · rw [Nat.le_div_iff_mul_le (by norm_num), ← pow_succ]
      exact h

theorem leadingDigit_eq (k n d : ℕ) (hd1 : 1 ≤ d) (hd : d < 10) (hlo : d * 10 ^ k ≤ n)
    (hhi : n < (d + 1) * 10 ^ k) : (Nat.digits 10 n).getLast? = some d := by
  have hpos : 0 < 10 ^ k := by positivity
  have h1 : 10 ^ k ≤ n := le_trans (by nlinarith) hlo
  rw [getLast?_digits_div_pow k n h1]
  have hq : n / 10 ^ k = d := by
    apply le_antisymm
    · have : n / 10 ^ k < d + 1 := (Nat.div_lt_iff_lt_mul hpos).mpr hhi
      omega
    · exact (Nat.le_div_iff_mul_le hpos).mpr hlo
  rw [hq, Nat.digits_of_lt 10 d (by omega) hd]
  simp

/-! ## Counting -/

open NumberFieldKB.MilneANT

/-- The norm of a prime of $\mathbb Q$ is a prime power. -/
theorem isPrimePow_absNorm (v : HeightOneSpectrum (𝓞 ℚ)) : IsPrimePow (Ideal.absNorm v.asIdeal) := by
  classical
  have : v.asIdeal.IsMaximal := v.isMaximal
  let : Field (𝓞 ℚ ⧸ v.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  let := Fintype.ofFinite (𝓞 ℚ ⧸ v.asIdeal)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact Fintype.isPrimePow_card_of_field

theorem not_isPrimePow_of_two_five {n : ℕ} (h2 : 2 ∣ n) (h5 : 5 ∣ n) : ¬ IsPrimePow n := by
  rintro ⟨p, k, hp, hk, rfl⟩
  have hp' := hp.nat_prime
  have e2 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp').mp
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
  have e5 : 5 = p := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp').mp
    (Nat.Prime.dvd_of_dvd_pow (by norm_num) h5)
  omega

/-- Splitting a prime count at $a \le b$. -/
theorem primeCount_split (S : Set (HeightOneSpectrum (𝓞 ℚ))) {a b : ℝ} (hab : a ≤ b) :
    primeCount S b = primeCount S a +
      {𝔭 ∈ S | a < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ b}.ncard := by
  have hfa : {𝔭 ∈ S | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ a}.Finite :=
    (finite_setOf_absNorm_le a).subset fun 𝔭 h => h.2
  have hfb : {𝔭 ∈ S | a < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ b}.Finite :=
    (finite_setOf_absNorm_le b).subset fun 𝔭 h => h.2.2
  have hdisj : Disjoint {𝔭 ∈ S | (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ a}
      {𝔭 ∈ S | a < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧ (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ b} := by
    rw [Set.disjoint_left]
    rintro 𝔭 ⟨-, h1⟩ ⟨-, h2, -⟩
    linarith
  rw [primeCount, primeCount, ← Set.ncard_union_eq hdisj hfa hfb]
  congr 1
  ext 𝔭
  simp only [Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hS, hb⟩
    rcases le_or_gt (Ideal.absNorm 𝔭.asIdeal : ℝ) a with h | h
    · exact Or.inl ⟨hS, h⟩
    · exact Or.inr ⟨hS, h, hb⟩
  · rintro (⟨hS, h⟩ | ⟨hS, -, h⟩)
    · exact ⟨hS, h.trans hab⟩
    · exact ⟨hS, h⟩

theorem norm_ne_of_two_five (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (h2 : 2 ∣ n) (h5 : 5 ∣ n) :
    Ideal.absNorm v.asIdeal ≠ n := by
  intro h
  exact not_isPrimePow_of_two_five h2 h5 (h ▸ isPrimePow_absNorm v)

/-- Every prime in $(10^k, 2\cdot 10^k]$ has leading digit $1$ ($k \ge 1$). -/
theorem block_one (k : ℕ) (hk : 1 ≤ k) :
    {𝔭 ∈ leadingDigitOnePrimes | ((10 : ℝ) ^ k) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ 2 * 10 ^ k} =
    {𝔭 ∈ (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) | ((10 : ℝ) ^ k) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ 2 * 10 ^ k} := by
  ext 𝔭
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and]
  refine ⟨fun h => h.2, fun ⟨h1, h2⟩ => ⟨?_, h1, h2⟩⟩
  set n := Ideal.absNorm 𝔭.asIdeal
  have h1' : 10 ^ k < n := by exact_mod_cast h1
  have h2' : n ≤ 2 * 10 ^ k := by exact_mod_cast h2
  have hne : n ≠ 2 * 10 ^ k := by
    apply norm_ne_of_two_five
    · exact dvd_mul_right 2 _
    · exact Dvd.dvd.mul_left (dvd_pow (by norm_num : (5 : ℕ) ∣ 10) (by omega)) 2
  show (Nat.digits 10 n).getLast? = some 1
  exact leadingDigit_eq k n 1 le_rfl (by norm_num) (by omega) (by omega)

/-- No prime in $(2\cdot10^k, 10^{k+1}]$ has leading digit $1$. -/
theorem block_other (k : ℕ) :
    {𝔭 ∈ leadingDigitOnePrimes | (2 * 10 ^ k : ℝ) < (Ideal.absNorm 𝔭.asIdeal : ℝ) ∧
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ 10 ^ (k + 1)} = ∅ := by
  ext 𝔭
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hT h1 h2
  set n := Ideal.absNorm 𝔭.asIdeal
  have h1' : 2 * 10 ^ k < n := by exact_mod_cast h1
  have h2' : n ≤ 10 ^ (k + 1) := by exact_mod_cast h2
  have hne : n ≠ 10 ^ (k + 1) := by
    apply norm_ne_of_two_five
    · exact dvd_pow (by norm_num) (by omega)
    · exact dvd_pow (by norm_num) (by omega)
  have hpos : 0 < 10 ^ k := by positivity
  set d := n / 10 ^ k
  have hd1 : d * 10 ^ k ≤ n := Nat.div_mul_le_self n _
  have hd2 : n < (d + 1) * 10 ^ k := by
    have := Nat.lt_div_mul_add (a := n) hpos
    simpa [add_mul, d] using this
  have hd2' : 2 ≤ d := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  have hd9 : d < 10 := (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [pow_succ] at h2'; omega)
  have := leadingDigit_eq k n d (by omega) hd9 hd1 hd2
  change (Nat.digits 10 n).getLast? = some 1 at hT
  rw [this] at hT
  simp at hT
  omega

theorem count_double (k : ℕ) (hk : 1 ≤ k) :
    (primeCount leadingDigitOnePrimes (2 * 10 ^ k) : ℝ) + primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) ((10 : ℝ) ^ k) =
      primeCount leadingDigitOnePrimes ((10 : ℝ) ^ k) + primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) (2 * 10 ^ k) := by
  have hle : (10 : ℝ) ^ k ≤ 2 * 10 ^ k := by
    have : (0 : ℝ) ≤ 10 ^ k := by positivity
    linarith
  rw [primeCount_split leadingDigitOnePrimes hle, primeCount_split Set.univ hle, block_one k hk]
  push_cast
  ring

theorem count_ten (k : ℕ) :
    primeCount leadingDigitOnePrimes ((10 : ℝ) ^ (k + 1)) =
      primeCount leadingDigitOnePrimes (2 * 10 ^ k) := by
  have hle : (2 * 10 ^ k : ℝ) ≤ 10 ^ (k + 1) := by
    have : (0 : ℝ) ≤ 10 ^ k := by positivity
    rw [pow_succ]; linarith
  rw [primeCount_split leadingDigitOnePrimes hle, block_other k, Set.ncard_empty, add_zero]

/-! ## The limit argument -/

/-- The prime number theorem over $\mathbb Q$, in the form used here: $\pi(x)/(x/\log x) \to 1$. -/
def PNT : Prop :=
  Tendsto (fun x : ℝ => (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x : ℝ) / (x / Real.log x))
    atTop (𝓝 1)

local notation "π" => fun x : ℝ => (primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 ℚ))) x : ℝ)

theorem eventually_pos (hP : PNT) : ∀ᶠ x in atTop, 0 < π x := by
  have h1 := hP.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num))
  filter_upwards [h1, eventually_gt_atTop 1] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hxl : 0 < x / Real.log x := div_pos (by linarith) hlog
  by_contra hneg
  push Not at hneg
  have : (π x) / (x / Real.log x) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hxl.le
  linarith

/-- $\pi(cx)/\pi(x) \to c$ for $c \ge 1$. -/
theorem ratio_tendsto (hP : PNT) {c : ℝ} (hc : 1 ≤ c) :
    Tendsto (fun x => π (c * x) / π x) atTop (𝓝 c) := by
  have hc0 : 0 < c := by linarith
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop := tendsto_id.const_mul_atTop hc0
  have h1 : Tendsto (fun x : ℝ => π (c * x) / ((c * x) / Real.log (c * x))) atTop (𝓝 1) := hP.comp hcx
  have h2 : Tendsto (fun x : ℝ => (x / Real.log x) / π x) atTop (𝓝 1) := by
    have := hP.inv₀ one_ne_zero
    simpa [inv_div] using this
  have h3 : Tendsto (fun x : ℝ => Real.log x / Real.log (c * x)) atTop (𝓝 1) := by
    have hl : Tendsto (fun x : ℝ => Real.log c / Real.log x + 1) atTop (𝓝 1) := by
      have : Tendsto (fun x : ℝ => Real.log c / Real.log x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
      simpa using this.add_const 1
    have := hl.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    rw [Real.log_mul hc0.ne' (by linarith)]
    field_simp
  have h := (h1.mul h2).mul (h3.const_mul c)
  rw [one_mul, one_mul, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1, eventually_pos hP] with x hx hpx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hcx1 : 1 < c * x := by nlinarith
  have hlogc : Real.log (c * x) ≠ 0 := (Real.log_pos hcx1).ne'
  have hx0 : x ≠ 0 := by linarith
  field_simp

theorem alg_double (A B C D : ℝ) (hB : 0 < B) (hD : 0 < D) (h : C + B = A + D) :
    C / D = A / B * (B / D) + 1 - B / D := by
  field_simp
  linear_combination h

theorem alg_ratio (A B C : ℝ) (hB : 0 < B) : A / B / (C / B) = A / C := by
  rcases eq_or_ne C 0 with h | h
  · simp [h]
  · field_simp

theorem alg_ten (C D E : ℝ) (hD : 0 < D) (hE : 0 < E) : C / E = C / D * (D / E) := by
  field_simp

/-- **Remark 4.2 (a), second half, from the prime number theorem**: the primes with leading digit $1$ have no natural
density. -/
theorem not_natural_of_pnt (hP : PNT) (δ : ℝ) :
    ¬ NumberFieldKB.MilneANT.HasNaturalDensity leadingDigitOnePrimes δ := by
  intro h
  have hx : Tendsto (fun k : ℕ => (10 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hx2 : Tendsto (fun k : ℕ => 2 * (10 : ℝ) ^ k) atTop atTop :=
    hx.const_mul_atTop (by norm_num)
  have hx10 : Tendsto (fun k : ℕ => (10 : ℝ) ^ (k + 1)) atTop atTop :=
    hx.comp (tendsto_add_atTop_nat 1)
  have ha := h.comp hx
  have hb := h.comp hx2
  have hc := h.comp hx10
  have hρ : Tendsto (fun k : ℕ => π ((10 : ℝ) ^ k) / π (2 * 10 ^ k)) atTop (𝓝 (2⁻¹)) := by
    have := ((ratio_tendsto hP (c := 2) (by norm_num)).comp hx).inv₀ (by norm_num)
    refine this.congr fun k => ?_
    dsimp only [Function.comp_apply]
    exact inv_div _ _
  have hσ : Tendsto (fun k : ℕ => π (2 * 10 ^ k) / π ((10 : ℝ) ^ (k + 1))) atTop (𝓝 (2 / 10)) := by
    have h2 := (ratio_tendsto hP (c := 2) (by norm_num)).comp hx
    have h10 := (ratio_tendsto hP (c := 10) (by norm_num)).comp hx
    have := h2.div h10 (by norm_num)
    refine this.congr' ?_
    filter_upwards [hx.eventually (eventually_pos hP)] with k hk
    rw [pow_succ, mul_comm ((10 : ℝ) ^ k) 10]
    exact alg_ratio _ _ _ hk
  have hpos := hx.eventually (eventually_pos hP)
  have hpos2 := hx2.eventually (eventually_pos hP)
  have hpos10 := hx10.eventually (eventually_pos hP)
  -- `b = a ρ + 1 - ρ`
  have hb' : Tendsto (fun k : ℕ => (primeCount leadingDigitOnePrimes (2 * 10 ^ k) : ℝ) / π (2 * 10 ^ k))
      atTop (𝓝 (δ * 2⁻¹ + 1 - 2⁻¹)) := by
    have := ((ha.mul hρ).add_const 1).sub hρ
    refine this.congr' ?_
    filter_upwards [hpos, hpos2, eventually_ge_atTop 1] with k h1 h2 hk
    exact (alg_double _ _ _ _ h1 h2 (count_double k hk)).symm
  have hc' : Tendsto (fun k : ℕ => (primeCount leadingDigitOnePrimes ((10 : ℝ) ^ (k + 1)) : ℝ) /
      π ((10 : ℝ) ^ (k + 1))) atTop (𝓝 (δ * (2 / 10))) := by
    have := hb.mul hσ
    refine this.congr' ?_
    filter_upwards [hpos2, hpos10] with k h2 h10
    dsimp only [Function.comp_apply]
    rw [count_ten k]
    exact (alg_ten _ _ _ h2 h10).symm
  have e1 := tendsto_nhds_unique hb hb'
  have e2 := tendsto_nhds_unique hc hc'
  linarith

end NumberFieldKB.MilneCFT.Ch6.R42
