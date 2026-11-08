import NumberFieldKB.NonVanishing.LogDeriv
import NumberFieldKB.NonVanishing.Dedekind

/-!
# Landau's positivity argument: real Euler products do not vanish at $s = 1$

$F$ is a number field; $v$ runs over the nonzero primes of $\mathcal O_F$, $N(v)$ = `normP v`. Let $a(v)\in\{0,1,-1\}$
and let $L$ be an entire function with $L(s) = \prod_v(1-a(v)N(v)^{-s})^{-1}$ for $\operatorname{Re}s>1$. Then
**$L(1)\ne0$** (`landau_ne_zero`). This is the case of quadratic characters, where the 3-4-1 argument gives nothing.

*Proof* (Mathlib's proof for quadratic Dirichlet characters, `DirichletCharacter.LFunction_apply_one_ne_zero`, with
Euler products in place of Dirichlet series over $\mathbb N$). If $L(1) = 0$, then $Z(s) = \zeta_F(s)L(s)$
$= (s-1)\zeta_F(s)\cdot L(s)/(s-1)$ (`zetaRes`, `dslope`) is entire. On $\operatorname{Re}s>1$, $Z = e^G$ with
$-G'(s) = \sum_v\sum_{m\ge1}(1+a(v)^m)\log N(v)\,N(v)^{-ms}$, the $L$-series of the nonnegative arithmetic function
`lamCoeff a` (`LSeries_lamCoeff`); so the derivatives of $-G'$ at $2$ alternate in sign (Mathlib's
`LSeries.iteratedDeriv_alternating`), hence so do those of $Z = e^G$ (`iteratedDeriv_alternating_of_deriv_eq`, Leibniz),
and $Z(-2)\ge Z(2)>0$ (Mathlib's `Differentiable.apply_le_of_iteratedDeriv_alternating`). But $\zeta_F(-2) = 0$
(`dedekindZetaCont_neg_two`, the trivial zero: $1/\Gamma_{\mathbb R}$ and $1/\Gamma_{\mathbb C}$ vanish at $-2$), so
$Z(-2) = 0$.
-/

open Complex Filter Topology IsDedekindDomain NumberField
open QuadFormsKB.NFEuler NumberFieldKB.HeckeL
open scoped ComplexOrder

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The trivial zero $\zeta_F(-2) = 0$ -/

/-- **$\zeta_F(-2) = 0$** (the factor $1/(\Gamma_{\mathbb R}(s)^{r_1}\Gamma_{\mathbb C}(s)^{r_2})$ vanishes at $s = -2$). -/
theorem dedekindZetaCont_neg_two : dedekindZetaCont F (-2) = 0 := by
  have h1 : Complex.Gammaℝ (-2) = 0 := by
    rw [Complex.Gammaℝ_def, show (-2 : ℂ) / 2 = -((1 : ℕ) : ℂ) by push_cast; norm_num,
      Complex.Gamma_neg_nat_eq_zero, mul_zero]
  have h2 : Complex.Gammaℂ (-2) = 0 := by
    rw [Complex.Gammaℂ, show (-2 : ℂ) = -((2 : ℕ) : ℂ) by push_cast; rfl, Complex.Gamma_neg_nat_eq_zero, mul_zero]
  have hn := one_le_nrPlaces (F := F)
  have hg : gammaFactor F (-2) = 0 := by
    rw [gammaFactor]
    by_cases h : InfinitePlace.nrRealPlaces F = 0
    · have : InfinitePlace.nrComplexPlaces F ≠ 0 := by omega
      rw [h2, zero_pow this, mul_zero]
    · rw [h1, zero_pow h, zero_mul]
  rw [dedekindZetaCont_of_ne (by norm_num), hg, div_zero]

/-! ### Alternating derivatives of $e^G$ -/

/-- **Leibniz induction.** If $Z' = -fZ$ near $c$, all derivatives of $f$ at $c$ alternate in sign
($0\le(-1)^nf^{(n)}(c)$) and $0\le Z(c)$, then so do those of $Z$. -/
theorem iteratedDeriv_alternating_of_deriv_eq {Z f : ℂ → ℂ} {c : ℂ} (hZ : AnalyticAt ℂ Z c) (hf : AnalyticAt ℂ f c)
    (hder : deriv Z =ᶠ[𝓝 c] fun s => -(f s * Z s)) (hfalt : ∀ n, 0 ≤ (-1) ^ n * iteratedDeriv n f c)
    (hZc : 0 ≤ Z c) (n : ℕ) : 0 ≤ (-1) ^ n * iteratedDeriv n Z c := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simpa using hZc
    rw [iteratedDeriv_succ', hder.iteratedDeriv_eq n]
    have hmul : iteratedDeriv n (fun s => -(f s * Z s)) c =
        -∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv i f c * iteratedDeriv (n - i) Z c := by
      rw [iteratedDeriv_fun_neg, iteratedDeriv_fun_mul hf.contDiffAt hZ.contDiffAt]
    rw [hmul, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_nonneg fun i hi => ?_
    have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    have h := pow_add (-1 : ℂ) i (n - i)
    rw [Nat.add_sub_cancel' hi'] at h
    have e : (-1 : ℂ) ^ (n + 1) * -((n.choose i : ℂ) * iteratedDeriv i f c * iteratedDeriv (n - i) Z c) =
        (n.choose i : ℂ) * ((-1) ^ i * iteratedDeriv i f c) * ((-1) ^ (n - i) * iteratedDeriv (n - i) Z c) := by
      linear_combination (n.choose i * iteratedDeriv i f c * iteratedDeriv (n - i) Z c) * h
    rw [e]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hfalt i)) (ih (n - i) (by omega))

/-! ### The coefficients of $-G'$ -/

/-- The coefficient of $n^{-s}$ in $\sum_v\sum_{m\ge1}(1+a(v)^m)\log N(v)\,N(v)^{-ms}$. -/
def lamCoeff (a : HeightOneSpectrum (𝓞 F) → ℂ) (n : ℕ) : ℂ :=
  ∑ v ∈ primesNormLe F n, ∑ m ∈ Finset.range n,
    if normP v ^ (m + 1) = n then (1 + a v ^ (m + 1)) * Real.log (normP v) else 0

theorem lamCoeff_nonneg {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, a v = 0 ∨ a v = 1 ∨ a v = -1) :
    0 ≤ lamCoeff a := by
  intro n
  refine Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun m _ => ?_
  split_ifs
  · refine mul_nonneg ?_ (Complex.zero_le_real.mpr (log_normP_pos v).le)
    rcases ha v with h | h | h
    · rw [h, zero_pow (by omega)]; norm_num
    · rw [h, one_pow]; norm_num
    · rcases neg_one_pow_eq_or ℂ (m + 1) with h' | h' <;> rw [h, h'] <;> norm_num
  · exact le_rfl

theorem lamCoeff_zero (a : HeightOneSpectrum (𝓞 F) → ℂ) : lamCoeff a 0 = 0 := by
  have : primesNormLe F 0 = ∅ := by
    ext v
    simp only [mem_primesNormLe, Finset.notMem_empty, iff_false, not_le]
    exact lt_of_lt_of_le (by norm_num) (two_le_normP v)
  simp [lamCoeff, this]

/-- $(N(v)^{-s})^k = (N(v)^k)^{-s}$. -/
theorem nps_pow (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) (k : ℕ) :
    nps v s ^ k = ((normP v ^ k : ℕ) : ℂ) ^ (-s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    simp [nps]

/-- The summand $(1+a(v)^{m+1})\log N(v)\,N(v)^{-(m+1)s}$ indexed by $(v,m)$. -/
def lamTerm (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) (i : HeightOneSpectrum (𝓞 F) × ℕ) : ℂ :=
  (1 + a i.1 ^ (i.2 + 1)) * (Real.log (normP i.1) : ℂ) * nps i.1 s ^ (i.2 + 1)

theorem norm_lamTerm_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) (v : HeightOneSpectrum (𝓞 F))
    (m : ℕ) (s : ℂ) :
    ‖lamTerm a s (v, m)‖ ≤ 2 * Real.log (normP v) * ((normP v : ℝ) ^ (-s.re)) ^ (m + 1) := by
  rw [lamTerm, norm_mul, norm_mul, norm_pow, norm_nps, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (log_normP_pos v)]
  have h1 : ‖1 + a v ^ (m + 1)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    have := pow_le_one₀ (norm_nonneg (a v)) (ha v) (n := m + 1)
    rw [norm_one, norm_pow]
    linarith
  have hl := (log_normP_pos v).le
  have hr : 0 ≤ ((normP v : ℝ) ^ (-s.re)) ^ (m + 1) :=
    pow_nonneg (Real.rpow_nonneg (normP_pos' v).le _) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hl) hr

theorem summable_norm_lamTerm {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun i : HeightOneSpectrum (𝓞 F) × ℕ => ‖lamTerm a s i‖ := by
  set r : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (normP v : ℝ) ^ (-s.re) with hr
  have hr0 : ∀ v, 0 ≤ r v := fun v => Real.rpow_nonneg (normP_pos' v).le _
  have hr1 : ∀ v, r v ≤ 1 / 2 := fun v => rpow_neg_normP_le_half v hs.le
  have hB0 : 0 ≤ fun i : HeightOneSpectrum (𝓞 F) × ℕ => 2 * Real.log (normP i.1) * r i.1 ^ (i.2 + 1) :=
    fun i => by
      have := log_normP_pos i.1
      have := hr0 i.1
      positivity
  have hB : Summable fun i : HeightOneSpectrum (𝓞 F) × ℕ => 2 * Real.log (normP i.1) * r i.1 ^ (i.2 + 1) := by
    refine (summable_prod_of_nonneg hB0).mpr ⟨fun v => ?_, ?_⟩
    · exact ((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one (hr0 v) (by linarith [hr1 v]))).mul_left (2 * Real.log (normP v))
    · refine ((summable_log_mul_rpow (F := F) hs).mul_left 4).of_nonneg_of_le
        (fun v => tsum_nonneg fun m => hB0 (v, m)) fun v => ?_
      have e : ∑' m : ℕ, r v ^ (m + 1) = r v * (1 - r v)⁻¹ := by
        simp_rw [pow_succ']
        rw [tsum_mul_left, tsum_geometric_of_lt_one (hr0 v) (by linarith [hr1 v])]
      have hI : (1 - r v)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith [hr1 v]) (by norm_num)]
        linarith [hr1 v]
      have hlr : 0 ≤ Real.log (normP v) * r v := mul_nonneg (log_normP_pos v).le (hr0 v)
      simp only [tsum_mul_left, e]
      calc 2 * Real.log (normP v) * (r v * (1 - r v)⁻¹) = 2 * (Real.log (normP v) * r v) * (1 - r v)⁻¹ := by ring
        _ ≤ 2 * (Real.log (normP v) * r v) * 2 := by gcongr
        _ = 4 * (Real.log (normP v) * (normP v : ℝ) ^ (-s.re)) := by simp only [hr]; ring
  exact hB.of_nonneg_of_le (fun _ => norm_nonneg _) fun ⟨v, m⟩ => norm_lamTerm_le ha v m s

theorem hasSum_pow_succ {b : ℂ} (hb : ‖b‖ < 1) : HasSum (fun m : ℕ => b ^ (m + 1)) (b / (1 - b)) := by
  have := (hasSum_geometric_of_norm_lt_one hb).mul_left b
  convert this using 1
  · funext m; ring
  · rw [div_eq_mul_inv]

theorem hasSum_lamTerm_fiber {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => lamTerm a s (v, m))
      (((fun _ => (1 : ℂ)) v * Real.log (normP v) * nps v s / (1 - (fun _ => (1 : ℂ)) v * nps v s)) +
        a v * Real.log (normP v) * nps v s / (1 - a v * nps v s)) := by
  have h1 : ‖nps v s‖ < 1 := (norm_nps_le_half v hs.le).trans_lt (by norm_num)
  have h2 : ‖a v * nps v s‖ < 1 := (norm_mul_nps_le_half ha v hs.le).trans_lt (by norm_num)
  have h := ((hasSum_pow_succ h1).mul_left (Real.log (normP v) : ℂ)).add
    ((hasSum_pow_succ h2).mul_left (Real.log (normP v) : ℂ))
  convert h using 1
  · funext m
    simp only [lamTerm, mul_pow]
    ring
  · simp only [one_mul]
    ring

theorem summable_logDeriv_term {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => a v * Real.log (normP v) * nps v s / (1 - a v * nps v s) := by
  refine ((summable_log_mul_rpow (F := F) hs).mul_left 2).of_norm_bounded fun v => ?_
  have hd : 1 / 2 ≤ ‖1 - a v * nps v s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a v * nps v s)
    have := norm_mul_nps_le_half ha v hs.le
    rw [norm_one] at *
    linarith
  have hn : ‖a v * (Real.log (normP v) : ℂ) * nps v s‖ ≤ Real.log (normP v) * (normP v : ℝ) ^ (-s.re) := by
    rw [norm_mul, norm_mul, norm_nps, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (log_normP_pos v)]
    have h0 : 0 ≤ Real.log (normP v) * (normP v : ℝ) ^ (-s.re) :=
      mul_nonneg (log_normP_pos v).le (Real.rpow_nonneg (normP_pos' v).le _)
    calc ‖a v‖ * Real.log (normP v) * (normP v : ℝ) ^ (-s.re)
        = ‖a v‖ * (Real.log (normP v) * (normP v : ℝ) ^ (-s.re)) := by ring
      _ ≤ 1 * (Real.log (normP v) * (normP v : ℝ) ^ (-s.re)) := mul_le_mul_of_nonneg_right (ha v) h0
      _ = _ := one_mul _
  rw [norm_div, div_le_iff₀ (by linarith)]
  have h0 : 0 ≤ Real.log (normP v) * (normP v : ℝ) ^ (-s.re) :=
    mul_nonneg (log_normP_pos v).le (Real.rpow_nonneg (normP_pos' v).le _)
  nlinarith

theorem hasSum_term_lamCoeff {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (LSeries.term (lamCoeff a) s) (∑' i, lamTerm a s i) := by
  have hS := (summable_norm_lamTerm ha hs).of_norm.hasSum
  convert hS.tsum_fiberwise (fun i : HeightOneSpectrum (𝓞 F) × ℕ => normP i.1 ^ (i.2 + 1)) using 1
  funext n
  rw [tsum_subtype ((fun i : HeightOneSpectrum (𝓞 F) × ℕ => normP i.1 ^ (i.2 + 1)) ⁻¹' {n}) (lamTerm a s),
    tsum_eq_sum (s := primesNormLe F n ×ˢ Finset.range n), Finset.sum_product]
  · rw [LSeries.term_def]
    split_ifs with hn
    · subst hn
      simp
    · rw [lamCoeff, Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : normP v ^ (m + 1) = n
      · rw [Set.indicator_of_mem (show (v, m) ∈ _ from h), lamTerm, nps_pow]
        simp only [h, ↓reduceIte, Complex.cpow_neg, div_eq_mul_inv]
      · rw [Set.indicator_of_notMem (show (v, m) ∉ _ from h)]
        simp [h]
  · rintro ⟨v, m⟩ hvm
    by_cases h : normP v ^ (m + 1) = n
    swap
    · exact Set.indicator_of_notMem (show (v, m) ∉ _ from h) _
    exfalso
    apply hvm
    have h2 := two_le_normP v
    simp only [Finset.mem_product, mem_primesNormLe, Finset.mem_range]
    constructor
    · rw [← h]
      exact Nat.le_self_pow (by omega) _
    · have := Nat.lt_pow_self (show 1 < normP v by omega) (n := m + 1)
      omega

theorem abscissaOfAbsConv_lamCoeff_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (lamCoeff a) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  exact (hasSum_term_lamCoeff ha (s := (y : ℂ)) (by simpa using hy)).summable

/-- **$-G'$ as an $L$-series**: $\sum_n\mathrm{lamCoeff}(n)n^{-s} = \sum_v\lambda_v\frac{w_v}{1-w_v}+\sum_v\lambda_v\frac{a(v)w_v}{1-a(v)w_v}$,
$w_v = N(v)^{-s}$, for $\operatorname{Re}s>1$. -/
theorem LSeries_lamCoeff {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (lamCoeff a) s =
      (∑' v : HeightOneSpectrum (𝓞 F), (fun _ => (1 : ℂ)) v *Real.log (normP v) * nps v s / (1 - (fun _ => (1 : ℂ)) v * nps v s)) +
        ∑' v, a v * Real.log (normP v) * nps v s / (1 - a v * nps v s) := by
  have h1 := summable_logDeriv_term (F := F) (a := fun _ => 1) (fun _ => by simp) hs
  have h2 := summable_logDeriv_term ha hs
  have hS := (summable_norm_lamTerm ha hs).of_norm.hasSum
  have hv := hS.prod_fiberwise fun v => hasSum_lamTerm_fiber ha v hs
  rw [LSeries, (hasSum_term_lamCoeff ha hs).tsum_eq, ← hv.tsum_eq, h1.tsum_add h2]

/-! ### Landau's theorem -/

/-- `logEuler b` is real on real arguments $x>1$ when the $b(v)$ are real of absolute value $\le1$. -/
theorem logEuler_im_eq_zero {b : HeightOneSpectrum (𝓞 F) → ℂ} (hb : ∀ v, ‖b v‖ ≤ 1) (hreal : ∀ v, (b v).im = 0)
    {x : ℝ} (hx : 1 < x) : (logEuler b (x : ℂ)).im = 0 := by
  rw [logEuler, Complex.im_tsum (summable_neg_log hb (by simpa using hx))]
  refine (tsum_congr fun v => ?_).trans tsum_zero
  have hbv : b v = ((b v).re : ℂ) := Complex.ext (by simp) (by simp [hreal v])
  have hre : |(b v).re| ≤ 1 := by
    have := hb v
    rwa [hbv, Complex.norm_real, Real.norm_eq_abs] at this
  have hr0 := Real.rpow_nonneg (normP_pos' v).le (-x)
  have hr1 : (normP v : ℝ) ^ (-x) ≤ 1 / 2 := rpow_neg_normP_le_half v hx.le
  have hnps : nps v (x : ℂ) = (((normP v : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [nps, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (normP_pos' v).le]
  have hz : 1 - b v * nps v (x : ℂ) = ((1 - (b v).re * (normP v : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [hnps]
    conv_lhs => rw [hbv]
    push_cast
    ring
  have hpos : 0 ≤ 1 - (b v).re * (normP v : ℝ) ^ (-x) := by
    have := abs_le.mp hre
    nlinarith
  rw [hz, Complex.neg_im, Complex.log_im, Complex.arg_ofReal_of_nonneg hpos, neg_zero]
/-- **Landau's positivity argument.** If $a(v)\in\{0,1,-1\}$ and the Euler product
$\prod_v(1-a(v)N(v)^{-s})^{-1}$ ($\operatorname{Re}s>1$) is the restriction of an entire function $L$, then $L(1)\ne0$. -/
@[kb "neukirch1999" "Ch. VII, §13 (L(1, χ) ≠ 0 for real χ, Landau's theorem on Dirichlet series with nonnegative coefficients) [unverified locator]"]
theorem landau_ne_zero {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, a v = 0 ∨ a v = 1 ∨ a v = -1) {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) (hLe : ∀ s : ℂ, 1 < s.re → L s = cexp (logEuler a s)) : L 1 ≠ 0 := by
  intro hL1
  have ha1 : ∀ v, ‖a v‖ ≤ 1 := fun v => by rcases ha v with h | h | h <;> simp [h]
  have haim : ∀ v, (a v).im = 0 := fun v => by rcases ha v with h | h | h <;> simp [h]
  have hdsl : Differentiable ℂ (dslope L 1) :=
    differentiableOn_univ.mp ((differentiableOn_dslope Filter.univ_mem).mpr hL.differentiableOn)
  set Z : ℂ → ℂ := fun s => zetaRes F s * dslope L 1 s with hZ
  have hZd : Differentiable ℂ Z := differentiable_zetaRes.mul hdsl
  have hZeq : ∀ s : ℂ, 1 < s.re →
      Z s = cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) s + logEuler a s) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by simp [h] at hs
    have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    rw [Complex.exp_add, ← dedekindZetaCont_eq_exp hs, ← hLe s hs, hZ]
    simp only [zetaRes_of_ne hs1, dslope_of_ne _ hs1, slope_def_module, hL1, sub_zero, smul_eq_mul]
    field_simp
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderiv : ∀ s : ℂ, 1 < s.re → deriv Z s = -(LSeries (lamCoeff a) s * Z s) := by
    intro s hs
    have hG : HasDerivAt (fun w => logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) w + logEuler a w) _ s :=
      (hasDerivAt_logEuler (F := F) (a := fun _ => 1) (fun _ => by simp) hs).add
        (hasDerivAt_logEuler ha1 hs)
    have heq : Z =ᶠ[𝓝 s] fun w => cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) w + logEuler a w) :=
      Filter.eventually_of_mem (hU.mem_nhds hs) fun w hw => hZeq w hw
    rw [heq.deriv_eq, hG.cexp.deriv, LSeries_lamCoeff ha1 hs, hZeq s hs]
    ring
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have hder : deriv Z =ᶠ[𝓝 (2 : ℂ)] fun s => -(LSeries (lamCoeff a) s * Z s) :=
    Filter.eventually_of_mem (hU.mem_nhds h2) fun w hw => hderiv w hw
  have habs : LSeries.abscissaOfAbsConv (lamCoeff a) < ((2 : ℝ) : EReal) :=
    lt_of_le_of_lt (abscissaOfAbsConv_lamCoeff_le ha1) (by norm_cast)
  have hfa : AnalyticAt ℂ (LSeries (lamCoeff a)) 2 :=
    LSeries_analyticOnNhd (lamCoeff a) 2 (by simpa using habs)
  have hfalt : ∀ n, 0 ≤ (-1 : ℂ) ^ n * iteratedDeriv n (LSeries (lamCoeff a)) 2 := fun n => by
    simpa using LSeries.iteratedDeriv_alternating (lamCoeff_nonneg ha) habs n
  have hZ2 : 0 < Z 2 := by
    have him : (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) (2 : ℂ) + logEuler a (2 : ℂ)).im = 0 := by
      have e : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
      rw [Complex.add_im, e, logEuler_im_eq_zero (fun _ => by simp) (fun _ => by simp) (by norm_num),
        logEuler_im_eq_zero ha1 haim (by norm_num), add_zero]
    rw [hZeq 2 h2]
    have : logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) (2 : ℂ) + logEuler a (2 : ℂ) =
        ((logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) (2 : ℂ) + logEuler a (2 : ℂ)).re : ℂ) :=
      Complex.ext (by simp) (by simpa using him)
    rw [this, ← Complex.ofReal_exp]
    exact Complex.zero_lt_real.mpr (Real.exp_pos _)
  have hle : Z 2 ≤ Z (-2) :=
    hZd.apply_le_of_iteratedDeriv_alternating
      (fun n _ => iteratedDeriv_alternating_of_deriv_eq (hZd.analyticAt 2) hfa hder hfalt hZ2.le n)
      (by rw [Complex.le_def]; norm_num)
  have hZm : Z (-2) = 0 := by
    rw [hZ]
    simp only [zetaRes_of_ne (show (-2 : ℂ) ≠ 1 by norm_num), dedekindZetaCont_neg_two, mul_zero, zero_mul]
  rw [hZm] at hle
  exact absurd (lt_of_lt_of_le hZ2 hle) (lt_irrefl _)

end

end NumberFieldKB.NonVanishing
