import QuadFormsKB.Analysis.NFEulerProduct
import QuadFormsKB.Citation

/-!
# Euler products over the primes of a number field, and the 3-4-1 inequality

$F$ is a number field; $v$ runs over the nonzero primes of $\mathcal O_F$, $N(v)$ = `normP v`. For coefficients
$a(v)\in\mathbb C$ with $|a(v)|\le1$ and $\operatorname{Re}s>1$:

* **`eulerFactor a s v`** $= (1-a(v)N(v)^{-s})^{-1}$ and **`logEuler a s`** $=\sum_v-\log(1-a(v)N(v)^{-s})$
  (principal logarithm, absolutely convergent); **`hasProd_eulerFactor`**: $\prod_v(1-a(v)N(v)^{-s})^{-1}$ converges
  unconditionally to $\exp(\texttt{logEuler}\ a\ s)$. Hecke $L$-functions ($a(v) = \chi_v(\varpi_v)$ or $0$), Dedekind
  zeta functions ($a = 1$) and $L(s,\chi_{E/F})$ ($a = \chi_{E/F}\in\{0,\pm1\}$) are all of this form.
* **The 3-4-1 inequality** (`one_le_norm_prod_three_four_one`): if every $a(v)$ is $0$ or of absolute value $1$, then
  for real $x>1$ and $y$,
  $$\bigl|P_1(x)^3\,P_a(x+iy)^4\,P_{a^2}(x+2iy)\bigr|\ge1,$$
  with $P_b(s) = \exp(\texttt{logEuler}\ b\ s)$ (Mertens' argument; Mathlib's `DirichletCharacter.norm_LSeries_product_ge_one`
  is the case of Dirichlet characters). The pointwise inequality is Mathlib's private `re_log_comb_nonneg'`, reproved.
* **`ne_zero_of_three_four_one`**: the analytic conclusion. If $Z(1+x) = O(1/x)$ as $x\to0^+$, $L$ is differentiable at
  $1+it$, $L_2$ continuous at $1+2it$ and the product of the three is $\ge1$ in absolute value for $x>0$, then
  $L(1+it)\ne0$.
-/

open Complex Filter Topology Asymptotics IsDedekindDomain NumberField
open QuadFormsKB.NFEuler

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### The Euler factors -/

/-- $N(v)^{-s}$. -/
abbrev nps (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ := ((normP v : ℝ) : ℂ) ^ (-s)

theorem normP_pos' (v : HeightOneSpectrum (𝓞 F)) : (0 : ℝ) < normP v := by
  have := two_le_normP v; positivity

theorem norm_nps (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ‖nps v s‖ = (normP v : ℝ) ^ (-s.re) := by
  rw [nps, Complex.norm_cpow_eq_rpow_re_of_pos (normP_pos' v), neg_re]

theorem norm_nps_le_half (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 ≤ s.re) : ‖nps v s‖ ≤ 1 / 2 := by
  rw [norm_nps]; exact rpow_neg_normP_le_half v hs

theorem norm_mul_nps_le_half {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 ≤ s.re) : ‖a v * nps v s‖ ≤ 1 / 2 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (ha v)).trans (norm_nps_le_half v hs)

theorem one_sub_mul_nps_ne_zero {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 ≤ s.re) : 1 - a v * nps v s ≠ 0 := by
  intro h
  have h1 : a v * nps v s = 1 := (sub_eq_zero.mp h).symm
  have := norm_mul_nps_le_half ha v hs
  rw [h1, norm_one] at this
  norm_num at this

/-- **The Euler factor** $(1-a(v)N(v)^{-s})^{-1}$. -/
def eulerFactor (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  (1 - a v * nps v s)⁻¹

/-- **The logarithm of the Euler product** $\sum_v-\log(1-a(v)N(v)^{-s})$. -/
def logEuler (a : HeightOneSpectrum (𝓞 F) → ℂ) (s : ℂ) : ℂ :=
  ∑' v, -log (1 - a v * nps v s)

theorem summable_norm_mul_nps {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable fun v => ‖a v * nps v s‖ := by
  refine (summable_normP_rpow hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun v => ?_
  rw [norm_mul, ← norm_nps]
  exact mul_le_of_le_one_left (norm_nonneg _) (ha v)

theorem summable_neg_log {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable fun v => -log (1 - a v * nps v s) :=
  (summable_norm_mul_nps ha hs).of_norm.clog_one_sub.neg

/-- **The Euler product converges** to $\exp(\texttt{logEuler}\ a\ s)$ for $\operatorname{Re}s>1$. -/
theorem hasProd_eulerFactor {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (eulerFactor a s) (cexp (logEuler a s)) := by
  unfold logEuler
  have h := (summable_neg_log ha hs).hasSum.cexp
  convert h using 1
  funext v
  simp only [Function.comp_apply, eulerFactor, Complex.exp_neg,
    Complex.exp_log (one_sub_mul_nps_ne_zero ha v hs.le)]

theorem eulerFactor_ne_zero {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 1 ≤ s.re) : eulerFactor a s v ≠ 0 :=
  inv_ne_zero (one_sub_mul_nps_ne_zero ha v hs)

/-! ### The 3-4-1 inequality -/

/-- The pointwise positivity (Mathlib's private `re_log_comb_nonneg'`): for $0\le a<1$ and $|z| = 1$,
$3\operatorname{Re}(-\log(1-a))+4\operatorname{Re}(-\log(1-az))+\operatorname{Re}(-\log(1-az^2))\ge0$. -/
theorem re_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

theorem re_neg_log_one_sub_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) : 0 ≤ (-log (1 - (a : ℂ))).re := by
  rw [neg_re, ← ofReal_one, ← ofReal_sub, ← ofReal_log (by linarith), ofReal_re, neg_nonneg]
  exact Real.log_nonpos (by linarith) (by linarith)

/-- $N(v)^{-(x+iy)} = N(v)^{-x}\cdot N(v)^{-iy}$ with $N(v)^{-x}$ real. -/
theorem nps_add (v : HeightOneSpectrum (𝓞 F)) (x y : ℝ) :
    nps v (x + y * I) = (((normP v : ℝ) ^ (-x) : ℝ) : ℂ) * ((normP v : ℝ) : ℂ) ^ (-(y * I)) := by
  rw [nps, neg_add, cpow_add _ _ (by exact_mod_cast (normP_pos' v).ne'), ← ofReal_neg,
    ← ofReal_cpow (normP_pos' v).le]

theorem norm_cpow_neg_I_mul (v : HeightOneSpectrum (𝓞 F)) (y : ℝ) :
    ‖((normP v : ℝ) : ℂ) ^ (-(y * I))‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (normP_pos' v)]
  simp

/-- The positivity for one Euler factor: $a(v)\in\{0\}\cup S^1$. -/
theorem re_log_comb_nonneg_prime {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, a v = 0 ∨ ‖a v‖ = 1)
    (v : HeightOneSpectrum (𝓞 F)) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    0 ≤ 3 * (-log (1 - 1 * nps v x)).re + 4 * (-log (1 - a v * nps v (x + y * I))).re +
      (-log (1 - a v ^ 2 * nps v (x + 2 * y * I))).re := by
  set r : ℝ := (normP v : ℝ) ^ (-x)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (normP_pos' v).le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by have := two_le_normP v; exact_mod_cast
    (by omega : 1 < normP v)) (by linarith)
  have h0 : 1 * nps v x = (r : ℂ) := by
    rw [one_mul, show (x : ℂ) = (x : ℂ) + (0 : ℝ) * I by simp, nps_add]; simp [r]
  rw [h0]
  rcases ha v with h | h
  · rw [h]
    simp only [zero_mul, sub_zero, log_one, neg_zero, zero_re, mul_zero, add_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have := re_neg_log_one_sub_nonneg hr0 hr1
    linarith
  · set u : ℂ := ((normP v : ℝ) : ℂ) ^ (-(y * I))
    have hz : ‖a v * u‖ = 1 := by rw [norm_mul, h, norm_cpow_neg_I_mul, one_mul]
    have h1 : a v * nps v (x + y * I) = r * (a v * u) := by rw [nps_add]; ring
    have h2 : a v ^ 2 * nps v (x + 2 * y * I) = r * (a v * u) ^ 2 := by
      have : ((x : ℂ) + 2 * y * I) = (x : ℂ) + ((2 * y : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, nps_add]
      have hu : ((normP v : ℝ) : ℂ) ^ (-(((2 * y : ℝ) : ℂ) * I)) = u ^ 2 := by
        rw [← cpow_nat_mul]
        congr 1
        push_cast
        ring
      rw [hu]
      ring
    rw [h1, h2]
    exact re_log_comb_nonneg hr0 hr1 hz

/-- **The 3-4-1 inequality.** If each $a(v)$ is $0$ or has absolute value $1$, then for $x>1$,
$|P_1(x)^3P_a(x+iy)^4P_{a^2}(x+2iy)|\ge1$. -/
@[kb "neukirch1999" "Ch. VII, §13 (non-vanishing of L(s, χ) on Re s = 1, Mertens' 3-4-1 argument) [unverified locator]"]
theorem one_le_norm_prod_three_four_one {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, a v = 0 ∨ ‖a v‖ = 1)
    {x : ℝ} (hx : 1 < x) (y : ℝ) :
    1 ≤ ‖cexp (logEuler (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℂ)) x) ^ 3 * cexp (logEuler a (x + y * I)) ^ 4 *
      cexp (logEuler (fun v => a v ^ 2) (x + 2 * y * I))‖ := by
  have ha1 : ∀ v, ‖a v‖ ≤ 1 := fun v => by rcases ha v with h | h <;> simp [h]
  have ha2 : ∀ v, ‖a v ^ 2‖ ≤ 1 := fun v => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (ha1 v)
  have h0 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(fun _ => (1 : ℂ)) v‖ ≤ 1 := fun v => by simp
  have hx0 : 1 < (x : ℂ).re := by simpa using hx
  have hx1 : 1 < ((x : ℂ) + y * I).re := by simpa using hx
  have hx2 : 1 < ((x : ℂ) + 2 * y * I).re := by simpa using hx
  have H₀ := summable_neg_log h0 hx0
  have H₁ := summable_neg_log ha1 hx1
  have H₂ := summable_neg_log ha2 hx2
  have hsum₀ := (hasSum_re H₀.hasSum).summable.mul_left 3
  have hsum₁ := (hasSum_re H₁.hasSum).summable.mul_left 4
  have hsum₂ := (hasSum_re H₂.hasSum).summable
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, Complex.norm_exp,
    Real.one_le_exp_iff]
  simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, Nat.cast_ofNat]
  rw [logEuler, logEuler, logEuler, re_tsum H₀, re_tsum H₁, re_tsum H₂, ← tsum_mul_left, ← tsum_mul_left,
    ← hsum₀.tsum_add hsum₁, ← (hsum₀.add hsum₁).tsum_add hsum₂]
  refine tsum_nonneg fun v => ?_
  have := re_log_comb_nonneg_prime ha v hx y
  norm_num at this ⊢
  linarith

/-! ### The analytic conclusion -/

/-- If $L(1+it) = 0$ then $L(1+x+it) = O(x)$ as $x\to0^+$. -/
theorem isBigO_horizontal_of_eq_zero {L : ℂ → ℂ} {t : ℝ} (hL : DifferentiableAt ℂ L (1 + t * I))
    (h : L (1 + t * I) = 0) :
    (fun x : ℝ ↦ L (1 + x + t * I)) =O[𝓝[>] 0] fun x : ℝ ↦ (x : ℂ) := by
  have e : (fun x : ℝ => L (1 + x + t * I)) = fun x : ℝ => L (x + (1 + t * I)) := by
    funext x; congr 1; ring
  rw [e]
  have := hL.hasDerivAt
  rw [← zero_add (1 + (t : ℂ) * I)] at this
  simpa only [zero_add, h, sub_zero] using (Complex.isBigO_comp_ofReal_nhds
    (this.comp_add_const 0 _).differentiableAt.isBigO_sub).mono nhdsWithin_le_nhds

/-- **The analytic 3-4-1 argument.** -/
theorem ne_zero_of_three_four_one {Z L L₂ : ℂ → ℂ} {t : ℝ}
    (hprod : ∀ x : ℝ, 0 < x → 1 ≤ ‖Z (1 + x) ^ 3 * L (1 + x + t * I) ^ 4 * L₂ (1 + x + 2 * t * I)‖)
    (hZ : (fun x : ℝ => Z (1 + x)) =O[𝓝[>] 0] fun x : ℝ => (1 : ℂ) / x)
    (hL : DifferentiableAt ℂ L (1 + t * I)) (hL₂ : ContinuousAt L₂ (1 + 2 * t * I)) :
    L (1 + t * I) ≠ 0 := by
  intro Hz
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | h
    · rw [ofReal_zero, zero_pow (by norm_num), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr h), one_mul, mul_one]
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ Z (1 + x) ^ 3 * L (1 + x + t * I) ^ 4 * L₂ (1 + x + 2 * t * I) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall
      fun x hx ↦ (norm_one (α := ℝ)).symm ▸ hprod x hx
  have hL₂' : (fun x : ℝ ↦ L₂ (1 + x + 2 * t * I)) =O[𝓝[>] 0] fun _ ↦ (1 : ℂ) := by
    refine IsBigO.mono ?_ nhdsWithin_le_nhds
    have hc : ContinuousAt (fun x : ℝ => L₂ (1 + x + 2 * t * I)) 0 := by
      have : ContinuousAt (fun x : ℝ => (1 : ℂ) + x + 2 * t * I) 0 := by fun_prop
      refine ContinuousAt.comp (g := L₂) ?_ this
      simpa using hL₂
    exact hc.tendsto.isBigO_one ℂ
  have H := (hZ.pow 3).mul ((isBigO_horizontal_of_eq_zero hL Hz).pow 4) |>.mul hL₂'
  simp only [help] at H
  replace H := (H₀.trans H).norm_right
  simp only [norm_real] at H
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

end

end NumberFieldKB.NonVanishing
