import NumberFieldKB.LocalZeta.Basic
import NumberFieldKB.Ideles.Norm
import NumberFieldKB.HeckeCharacter.Local
import QuadFormsKB.Tamagawa.Measure.Weil.IdeleMeasures

/-!
# Local zeta integrals at a finite place

$F$ is a number field, $v$ a finite place, $F_v$ = `v.adicCompletion F`, $q = N(v)$, $\varpi$ a uniformizer
(QuadFormsKB's `ϖU v`), $dx$ the self-dual measure `selfDualV v` (for QuadFormsKB's standard character `psiV v`, so
$\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$), and $|x|_v = \Delta_v(x)$ the modulus
($= \|x\|$, `distribHaarChar_adicCompletion`; $|\varpi|_v = q^{-1}$, `modV_eq`).

* **`tateHaarV v`**: Tate's multiplicative Haar measure $d^\times x = \frac{q}{q-1}\frac{dx}{|x|_v}$ on $F_v^\times$
  (Cassels–Fröhlich Ch. XV, §2.3), i.e. $\lambda_v^{-1}\omega_v$ with QuadFormsKB's $\omega_v$ = `omegaV v` and
  $\lambda_v = 1 - q^{-1}$; **`tateHaarV_unitsVSub`**: $\operatorname{vol}^\times(\mathcal O_v^\times) =
  \operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$ (`volO_toReal`).
* **The shells** $\varpi^n\mathcal O_v^\times = \{|x|_v = q^{-n}\}$ (`shell v n`): every multiplicative Haar measure gives
  them the mass of $\mathcal O_v^\times$ (`measure_shell`), and $|x|_v = q^{-n}$ on them (`distribHaarChar_of_mem_shell`).
* **Convergence** (`integrable_zetaIntegrand`): if $f$ is measurable, bounded and supported in $\mathfrak p_v^{-N}$, and
  $|\chi| = |\cdot|_v^a$, the zeta integrand is integrable for $\operatorname{Re}s > -a$ (for unitary $\chi$:
  $\operatorname{Re}s > 0$).
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set WithZero
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil

namespace NumberFieldKB.LocalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-! ### Tate's multiplicative measure -/

/-- **Tate's multiplicative Haar measure** on $F_v^\times$: $d^\times x = \frac{N(v)}{N(v)-1}\frac{dx}{|x|_v}$ with $dx$ the
self-dual measure; QuadFormsKB's $\lambda_v^{-1}\omega_v$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3 [unverified locator] (d^×α = (N𝔭/(N𝔭 − 1)) dα/|α|)"]
def tateHaarV : Measure Fvˣ := (lamV v)⁻¹.toNNReal • omegaV v

instance : (tateHaarV v).IsMulLeftInvariant := by
  unfold tateHaarV; infer_instance

/-- **$\operatorname{vol}^\times(\mathcal O_v^\times) = \operatorname{vol}(\mathcal O_v)$** for Tate's measure. -/
theorem tateHaarV_unitsVSub : tateHaarV v (unitsVSub v) = volO v := by
  rw [tateHaarV, Measure.smul_apply, ← lamV_inv_mul_omegaV_unitsVSub, ENNReal.smul_def, smul_eq_mul]
  rfl

/-- $\operatorname{vol}(\mathcal O_v) = N(\mathfrak d_v)^{-1/2}$ for the self-dual measure, $N(\mathfrak d_v) = N(v)^{d_v}$. -/
theorem volO_toReal :
    (volO v).toReal = ((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) := by
  rw [volO, coe_adicCompletionIntegers_eq, ← selfDualV_real_Ov]
  rfl

theorem volO_lt_top : volO v < ⊤ := (volO_ne_top v).lt_top

theorem continuous_distribHaarChar_v : Continuous (distribHaarChar Fv : Fvˣ → ℝ≥0) :=
  continuous_distribHaarChar_adic v

/-! ### Shells -/

/-- **The shell** $\varpi^n\mathcal O_v^\times = \{u\in F_v^\times : v(u) = \exp(-n)\}$. -/
def shell (n : ℤ) : Set Fvˣ := {u | Valued.v (u : Fv) = exp (-n)}

theorem valued_ϖU_zpow (n : ℤ) : Valued.v (((ϖU v) ^ n : Fvˣ) : Fv) = exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, ϖU, Units.val_mk0, valued_ϖ_zpow]

theorem shell_eq_preimage (n : ℤ) : shell v n = (fun u => (ϖU v) ^ (-n) * u) ⁻¹' unitsVSub v := by
  ext u
  simp only [shell, unitsVSub, mem_preimage, mem_ofPred_eq, Units.val_mul, map_mul, valued_ϖU_zpow, neg_neg]
  constructor
  · intro h; rw [h, ← exp_add, add_neg_cancel, exp_zero]
  · intro h
    have := congrArg (fun x => exp (-n) * x) h
    simp only [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul, mul_one] at this
    exact this

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell v n) := by
  rw [shell_eq_preimage]
  exact (measurableSet_unitsVSub v).preimage (measurable_const_mul _)

/-- Every left-invariant measure gives each shell the mass of $\mathcal O_v^\times$. -/
theorem measure_shell (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (n : ℤ) : μ (shell v n) = μ (unitsVSub v) := by
  rw [shell_eq_preimage, measure_preimage_mul]

/-- $|u|_v = \Delta_v(\varpi)^n = N(v)^{-n}$ on the shell $\varpi^n\mathcal O_v^\times$. -/
theorem distribHaarChar_of_mem_shell {n : ℤ} {u : Fvˣ} (hu : u ∈ shell v n) :
    (distribHaarChar Fv u : ℝ) = (modV v : ℝ) ^ n := by
  rw [shell_eq_preimage, mem_preimage] at hu
  have h1 := distribHaarChar_eq_one_of_mem_unitsVSub hu
  have hu' : u = (ϖU v) ^ n * ((ϖU v) ^ (-n) * u) := by group
  rw [hu', map_mul, h1, mul_one, map_zpow, NNReal.coe_zpow]
  rfl

theorem pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell v)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro u hm hn
  simp only [shell, mem_ofPred_eq] at hm hn
  rw [hm, exp_inj, neg_inj] at hn
  exact hmn hn

/-- The valuation of a unit is $\exp(-n)$ for some $n\in\mathbb Z$: the units are the union of the shells. -/
theorem mem_shell_log (u : Fvˣ) : u ∈ shell v (-log (Valued.v (u : Fv))) := by
  have h0 : Valued.v (u : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  simp only [shell, mem_ofPred_eq, neg_neg, exp_log h0]

/-- $\{u : v(u)\le\exp(N)\} = \bigcup_{k\in\mathbb N}\varpi^{k-N}\mathcal O_v^\times$. -/
theorem setOf_valued_le_eq_iUnion (N : ℤ) :
    {u : Fvˣ | Valued.v (u : Fv) ≤ exp N} = ⋃ k : ℕ, shell v (k - N) := by
  ext u
  simp only [mem_ofPred_eq, mem_iUnion, shell]
  constructor
  · intro h
    have h0 : Valued.v (u : Fv) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    rw [← exp_log h0, exp_le_exp] at h
    refine ⟨(N - log (Valued.v (u : Fv))).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), show -(N - log (Valued.v (u : Fv)) - N) = log (Valued.v (u : Fv)) by ring,
      exp_log h0]
  · rintro ⟨k, hk⟩
    rw [hk, exp_le_exp]
    omega

theorem measurableSet_setOf_valued_le (N : ℤ) : MeasurableSet {u : Fvˣ | Valued.v (u : Fv) ≤ exp N} := by
  rw [setOf_valued_le_eq_iUnion]
  exact MeasurableSet.iUnion fun k => measurableSet_shell v _

/-! ### Convergence -/

theorem modV_lt_one : (modV v : ℝ) < 1 := by
  rw [modV_eq]
  exact inv_lt_one_of_one_lt₀ (one_lt_absNorm v)

theorem modV_pos' : (0 : ℝ) < modV v := by exact_mod_cast modV_pos v

/-- $\int_{\{v(u)\le\exp N\}}|u|_v^b\,d\mu(u) < \infty$ for $b > 0$ and a left-invariant $\mu$ with
$\mu(\mathcal O_v^\times) < \infty$ (a geometric series over the shells). -/
theorem lintegral_valued_le_rpow_lt_top (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (hU : μ (unitsVSub v) ≠ ⊤)
    (N : ℤ) {b : ℝ} (hb : 0 < b) (C : ℝ) :
    ∫⁻ u in {u : Fvˣ | Valued.v (u : Fv) ≤ exp N}, ENNReal.ofReal (C * (distribHaarChar Fv u : ℝ) ^ b) ∂μ < ⊤ := by
  set m : ℝ := (modV v : ℝ)
  have hm0 : 0 < m := modV_pos' v
  have hm1 : m < 1 := modV_lt_one v
  rw [setOf_valued_le_eq_iUnion, lintegral_iUnion (fun k => measurableSet_shell v _) (pairwise_disjoint_shell v |>.comp_of_injective
    (fun a b h => by simpa using h))]
  have hk : ∀ k : ℕ, ∫⁻ u in shell v (k - N), ENNReal.ofReal (C * (distribHaarChar Fv u : ℝ) ^ b) ∂μ =
      ENNReal.ofReal (C * (m ^ (-N : ℤ)) ^ b * (m ^ b) ^ k) * μ (unitsVSub v) := by
    intro k
    rw [setLIntegral_congr_fun (measurableSet_shell v _) (g := fun _ => ENNReal.ofReal (C * (m ^ (-N : ℤ)) ^ b * (m ^ b) ^ k))
      (fun u hu => ?_), setLIntegral_const, measure_shell]
    rw [distribHaarChar_of_mem_shell v hu, zpow_sub₀ hm0.ne', zpow_natCast, div_eq_mul_inv, ← zpow_neg,
      Real.mul_rpow (pow_nonneg hm0.le _) (zpow_nonneg hm0.le _), ← Real.rpow_natCast, ← Real.rpow_mul hm0.le,
      ← Real.rpow_natCast (m ^ b), ← Real.rpow_mul hm0.le, mul_comm (k : ℝ) b]
    ring_nf
  simp_rw [hk]
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ hU.lt_top
  have hr : m ^ b < 1 := Real.rpow_lt_one hm0.le hm1 hb
  by_cases hC : 0 ≤ C
  · have hc0 : 0 ≤ C * (m ^ (-N : ℤ)) ^ b := mul_nonneg hC (Real.rpow_nonneg (zpow_nonneg hm0.le _) _)
    have hsum : Summable fun k : ℕ => C * (m ^ (-N : ℤ)) ^ b * (m ^ b) ^ k :=
      (summable_geometric_of_lt_one (Real.rpow_nonneg hm0.le _) hr).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hc0 (pow_nonneg (Real.rpow_nonneg hm0.le _) _)) hsum]
    exact ENNReal.ofReal_lt_top
  · have : ∀ k : ℕ, ENNReal.ofReal (C * (m ^ (-N : ℤ)) ^ b * (m ^ b) ^ k) = 0 := fun k =>
      ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC)
        (Real.rpow_nonneg (zpow_nonneg hm0.le _) _)) (pow_nonneg (Real.rpow_nonneg hm0.le _) _))
    simp_rw [this, tsum_zero]
    exact ENNReal.zero_lt_top

/-- **Absolute convergence of the local zeta integral at a finite place**: if $f$ is measurable, bounded by $C$ and
vanishes outside $\{v(x)\le\exp N\} = \mathfrak p_v^{-N}$, $\chi$ is continuous with $|\chi| = |\cdot|_v^a$ (for unitary
$\chi$, $a = 0$), and $\operatorname{Re}s > -a$, then $f(u)\chi(u)|u|_v^s$ is integrable for every left-invariant measure
with $\mu(\mathcal O_v^\times) < \infty$ (e.g. `tateHaarV v`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.3, Lemma 2.3.1 / §2.4 [unverified locator] (ζ(f, c) converges for σ > 0)"]
theorem integrable_zetaIntegrand {f : Fv → ℂ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {N : ℤ}
    (hsupp : ∀ x, f x ≠ 0 → Valued.v x ≤ exp N) {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re)
    (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (hU : μ (unitsVSub v) ≠ ⊤) :
    Integrable (zetaIntegrand f χ s) μ := by
  have hΔ := continuous_distribHaarChar_v v
  refine ⟨?_, ?_⟩
  · refine (((hf.comp Units.continuous_val.measurable).mul
      (Units.continuous_val.comp hχc).measurable).mul ?_).aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hΔ)).measurable.pow_const _
  · set S := {u : Fvˣ | Valued.v (u : Fv) ≤ exp N}
    have hbound : ∀ u, ‖zetaIntegrand f χ s u‖ₑ ≤
        S.indicator (fun u => ENNReal.ofReal (C * (distribHaarChar Fv u : ℝ) ^ (a + s.re))) u := by
      intro u
      have hpos := distribHaarChar_pos' u
      have hnorm : ‖zetaIntegrand f χ s u‖ = ‖f u‖ * (distribHaarChar Fv u : ℝ) ^ (a + s.re) := by
        rw [zetaIntegrand, norm_mul, norm_mul, hχ, Complex.norm_cpow_eq_rpow_re_of_pos hpos, mul_assoc,
          ← Real.rpow_add hpos]
      by_cases hu : u ∈ S
      · rw [indicator_of_mem hu, ← ofReal_norm, hnorm]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg hpos.le _))
      · rw [indicator_of_notMem hu]
        have : f u = 0 := by
          by_contra h
          exact hu (hsupp _ h)
        simp [zetaIntegrand, this]
    calc ∫⁻ u, ‖zetaIntegrand f χ s u‖ₑ ∂μ
        ≤ ∫⁻ u, S.indicator (fun u => ENNReal.ofReal (C * (distribHaarChar Fv u : ℝ) ^ (a + s.re))) u ∂μ :=
          lintegral_mono hbound
      _ = ∫⁻ u in S, ENNReal.ofReal (C * (distribHaarChar Fv u : ℝ) ^ (a + s.re)) ∂μ :=
          lintegral_indicator (measurableSet_setOf_valued_le v N) _
      _ < ⊤ := lintegral_valued_le_rpow_lt_top v μ hU N hs C

theorem tateHaarV_unitsVSub_ne_top : tateHaarV v (unitsVSub v) ≠ ⊤ := by
  rw [tateHaarV_unitsVSub]; exact volO_ne_top v

/-! ### The unramified computation -/

/-- The characteristic function $\mathbf 1_{\mathcal O_v}$ of the valuation ring. -/
def charO : Fv → ℂ := (v.adicCompletionIntegers F : Set Fv).indicator 1

theorem charO_apply (x : Fv) : charO v x = if Valued.v x ≤ 1 then 1 else 0 := by
  classical
  rw [charO, Set.indicator_apply]
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Pi.one_apply]

theorem measurable_charO : Measurable (charO v) :=
  (measurable_const.indicator (measureSet_O' v))
where measureSet_O' (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := measurableSet_O v

/-- A character trivial on $\mathcal O_v^\times$ takes the value $\chi(\varpi)^n$ on the shell $\varpi^n\mathcal O_v^\times$. -/
theorem apply_of_mem_shell {χ : Fvˣ →* ℂˣ} (hur : ∀ u ∈ unitsVSub v, χ u = 1) {n : ℤ} {u : Fvˣ}
    (hu : u ∈ shell v n) : χ u = χ (ϖU v) ^ n := by
  rw [shell_eq_preimage, mem_preimage] at hu
  have hu' : u = (ϖU v) ^ n * ((ϖU v) ^ (-n) * u) := by group
  rw [hu', map_mul, hur _ hu, mul_one, map_zpow]

theorem ofReal_pow_cpow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (s : ℂ) :
    (((x ^ k : ℝ)) : ℂ) ^ s = ((x : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx _) hx, ih, pow_succ]

/-- $|\varpi|_v^s = N(v)^{-s}$. -/
theorem modV_cpow (s : ℂ) : ((modV v : ℝ) : ℂ) ^ s = ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s) := by
  rw [modV_eq, Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg _)]
  exact Real.pi_ne_zero.symm

/-- **The unramified local zeta integral** for any left-invariant measure $\mu$ on $F_v^\times$ with
$\mu(\mathcal O_v^\times) < \infty$: if $\chi$ is trivial on $\mathcal O_v^\times$ and $|\chi| = |\cdot|_v^a$ with
$\operatorname{Re}s > -a$, then
$$Z(\mathbf 1_{\mathcal O_v},\chi,s) = \frac{\mu(\mathcal O_v^\times)}{1 - \chi(\varpi)N(v)^{-s}}.$$ -/
theorem zetaIntegral_charO_of_measure {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) (hur : ∀ u ∈ unitsVSub v, χ u = 1)
    {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re)
    (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (hU : μ (unitsVSub v) ≠ ⊤) :
    zetaIntegral μ (charO v) χ s =
      (μ (unitsVSub v)).toReal / (1 - (χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s)) := by
  have hint := integrable_zetaIntegrand v (measurable_charO v) (C := 1)
    (fun x => by rw [charO_apply]; split_ifs <;> simp) (N := 0)
    (fun x hx => by
      by_cases h : Valued.v x ≤ 1
      · simpa using h
      · simp [charO_apply, h] at hx)
    hχc hχ hs μ hU
  set r : ℂ := (χ (ϖU v) : ℂ) * ((modV v : ℝ) : ℂ) ^ s
  have hr : ‖r‖ < 1 := by
    have h1 : ‖(χ (ϖU v) : ℂ)‖ = (modV v : ℝ) ^ a := hχ _
    rw [norm_mul, h1, Complex.norm_cpow_eq_rpow_re_of_pos (modV_pos' v), ← Real.rpow_add (modV_pos' v)]
    exact Real.rpow_lt_one (modV_pos' v).le (modV_lt_one v) hs
  have hzero : ∀ u, u ∉ ⋃ k : ℕ, shell v (k - 0) → zetaIntegrand (charO v) χ s u = 0 := by
    intro u hu
    rw [← setOf_valued_le_eq_iUnion, mem_ofPred_eq, exp_zero] at hu
    simp [zetaIntegrand, charO_apply, hu]
  rw [zetaIntegral, ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_iUnion (fun k => measurableSet_shell v _)
      ((pairwise_disjoint_shell v).comp_of_injective (fun a b h => by simpa using h)) hint.integrableOn]
  have hk : ∀ k : ℕ, ∫ u in shell v (k - 0), zetaIntegrand (charO v) χ s u ∂μ = (μ (unitsVSub v)).toReal * r ^ k := by
    intro k
    rw [setIntegral_congr_fun (measurableSet_shell v _) (g := fun _ => r ^ k) (fun u hu => ?_), setIntegral_const,
      Measure.real, measure_shell, Complex.real_smul]
    have hv : Valued.v (u : Fv) ≤ 1 := by
      have : Valued.v (u : Fv) = exp (-((k : ℤ) - 0)) := hu
      rw [this, ← exp_zero, exp_le_exp]; omega
    simp only [zetaIntegrand, charO_apply, hv, ite_true, one_mul, apply_of_mem_shell v hur hu,
      distribHaarChar_of_mem_shell v hu, sub_zero, zpow_natCast, Units.val_pow_eq_pow_val, r, mul_pow]
    rw [Complex.ofReal_pow, ← ofReal_pow_cpow (modV_pos' v).le, Complex.ofReal_pow]
  simp_rw [hk]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr, div_eq_mul_inv]
  simp only [r, modV_cpow]

/-- **The unramified local zeta integral with Tate's measure** (Cassels–Fröhlich Ch. XV, §2.5 [unverified locator]):
for $\chi$ trivial on $\mathcal O_v^\times$ with $|\chi| = |\cdot|_v^a$ and $\operatorname{Re}s > -a$,
$$Z(\mathbf 1_{\mathcal O_v},\chi,s) = \frac{\operatorname{vol}^\times(\mathcal O_v^\times)}{1 - \chi(\varpi)N(v)^{-s}},
\qquad \operatorname{vol}^\times(\mathcal O_v^\times) = N(\mathfrak d_v)^{-1/2}.$$ -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.5 [unverified locator] (ζ(f, c) = (N𝔡)^{−1/2}(1 − c(π))^{−1} for unramified c)"]
theorem zetaIntegral_tateHaarV_charO {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) (hur : ∀ u ∈ unitsVSub v, χ u = 1)
    {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re) :
    zetaIntegral (tateHaarV v) (charO v) χ s =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ diffExp v) ^ (-(1 : ℝ) / 2) : ℝ) /
        (1 - (χ (ϖU v) : ℂ) * ((Ideal.absNorm v.asIdeal : ℝ) : ℂ) ^ (-s)) := by
  rw [zetaIntegral_charO_of_measure v hχc hur hχ hs _ (tateHaarV_unitsVSub_ne_top v), tateHaarV_unitsVSub,
    volO_toReal]

/-! ### Schwartz–Bruhat functions -/

/-- **Schwartz–Bruhat functions on $F_v$** (Tate's class at a finite place): locally constant with compact support.
QuadFormsKB's `IsSchwartzBruhatV` (finite combinations of coset indicators) is contained in it
(`IsSchwartzBruhatLC.of_isSchwartzBruhatV`). -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified locator] (the class 𝔅 at a 𝔭-adic place: locally constant, compact support)"]
def IsSchwartzBruhatLC (f : Fv → ℂ) : Prop := IsLocallyConstant f ∧ HasCompactSupport f

theorem one_lt_norm_ϖ_inv : 1 < ‖HN.ϖ v‖⁻¹ :=
  (one_lt_inv₀ (norm_pos_iff.mpr (HN.ϖ_ne_zero v))).mpr (norm_ϖ_lt_one v)

theorem norm_ϖ_zpow_neg (n : ℕ) : ‖HN.ϖ v ^ (-(n : ℤ))‖ = ‖HN.ϖ v‖⁻¹ ^ n := by
  rw [norm_zpow, zpow_neg, zpow_natCast, inv_pow]

namespace IsSchwartzBruhatLC

variable {v} {f : v.adicCompletion F → ℂ}

theorem continuous (hf : IsSchwartzBruhatLC v f) : Continuous f := hf.1.continuous

theorem measurable (hf : IsSchwartzBruhatLC v f) : Measurable f := hf.continuous.measurable

theorem integrable (hf : IsSchwartzBruhatLC v f) (μ : Measure Fv) [IsFiniteMeasureOnCompacts μ] :
    Integrable f μ := hf.continuous.integrable_of_hasCompactSupport hf.2

theorem exists_bound (hf : IsSchwartzBruhatLC v f) : ∃ C, ∀ x, ‖f x‖ ≤ C :=
  hf.continuous.bounded_above_of_compact_support hf.2

/-- A Schwartz–Bruhat function vanishes outside some $\mathfrak p_v^{-N}$. -/
theorem exists_support (hf : IsSchwartzBruhatLC v f) : ∃ N : ℤ, ∀ x, f x ≠ 0 → Valued.v x ≤ exp N := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fv)).mp hf.2.isCompact.isBounded
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (one_lt_norm_ϖ_inv v)
  refine ⟨n, fun x hx => ?_⟩
  have hx' := hR (subset_tsupport f hx)
  have : x ∈ (latticeV v (-(n : ℤ)) : Set Fv) := by
    rw [coe_latticeV, Metric.mem_closedBall, dist_zero_right, norm_ϖ_zpow_neg]
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    exact hx'.trans hn.le
  rw [SetLike.mem_coe, mem_latticeV, neg_neg] at this
  exact this

/-- **Uniform local constancy**: a Schwartz–Bruhat function is invariant under translation by some $\mathfrak p_v^M$. -/
theorem exists_uniform (hf : IsSchwartzBruhatLC v f) : ∃ M : ℤ, ∀ x h : Fv, Valued.v h ≤ exp (-M) → f (x + h) = f x := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (c := fun i : Fv => f ⁻¹' {f i}) hf.2.isCompact
    (fun i => hf.1.isOpen_fiber _) (fun x _ => mem_iUnion.mpr ⟨x, rfl⟩)
  have key : ∀ x ∈ tsupport f, ∀ h : Fv, ‖h‖ < δ → f (x + h) = f x := by
    intro x hx h hh
    obtain ⟨i, hi⟩ := hball x hx
    have h1 : x + h ∈ Metric.ball x δ := by rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hh
    have h2 : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
    rw [show f (x + h) = f i from hi h1, show f x = f i from hi h2]
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (norm_ϖ_lt_one v)
  refine ⟨n, fun x h hh => ?_⟩
  have hnorm : ‖h‖ < δ := by
    have : h ∈ (latticeV v (n : ℤ) : Set Fv) := (mem_latticeV v).mpr hh
    rw [coe_latticeV, Metric.mem_closedBall, dist_zero_right, norm_zpow, zpow_natCast] at this
    exact this.trans_lt hn
  by_cases hx : x ∈ tsupport f
  · exact key x hx h hnorm
  · by_cases hxh : x + h ∈ tsupport f
    · have := key (x + h) hxh (-h) (by rwa [norm_neg])
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxh]

/-- QuadFormsKB's Schwartz–Bruhat functions (finite combinations of coset indicators $\mathbf 1_{c+\mathfrak p_v^k}$) are
locally constant with compact support. -/
theorem of_isSchwartzBruhatV (hf : IsSchwartzBruhatV v f) : IsSchwartzBruhatLC v f := by
  obtain ⟨n, a, c, k, rfl⟩ := hf
  have hball : ∀ (c : Fv) (k : ℤ), IsSchwartzBruhatLC v (ballIndV v c k) := by
    intro c k
    have hr : ‖HN.ϖ v ^ k‖ ≠ 0 := (norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v))).ne'
    have hU : IsClopen {x : Fv | Valued.v (x - c) ≤ exp (-k)} := by
      rw [ballIndV_eq]; exact IsUltrametricDist.isClopen_closedBall c hr
    refine ⟨?_, ?_⟩
    · have h : (⇑(LocallyConstant.charFn ℂ hU) : v.adicCompletion F → ℂ) = ballIndV v c k := by
        rw [LocallyConstant.coe_charFn]; rfl
      exact h ▸ (LocallyConstant.charFn ℂ hU).isLocallyConstant
    · refine HasCompactSupport.intro (isCompact_closedBall c ‖HN.ϖ v ^ k‖) fun x hx => ?_
      rw [← ballIndV_eq] at hx
      exact indicator_of_notMem hx _
  have hsum : (fun x => ∑ i, a i * ballIndV v (c i) (k i) x) = ∑ i, fun x => a i * ballIndV v (c i) (k i) x := by
    funext x; rw [Finset.sum_apply]
  rw [hsum]
  refine Finset.sum_induction _ (IsSchwartzBruhatLC v) (fun g h hg hh => ⟨hg.1.add hh.1, hg.2.add hh.2⟩)
    ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩ fun i _ => ?_
  exact ⟨(IsLocallyConstant.const (a i)).mul (hball (c i) (k i)).1, (hball (c i) (k i)).2.mul_left⟩

/-- **The Fourier transform preserves Schwartz–Bruhat functions** at a finite place: if $f$ is invariant under
$\mathfrak p_v^M$ and supported in $\mathfrak p_v^{-N}$, then $\hat f$ is supported in $\mathfrak p_v^{-M-d_v}$ (the
annihilator of $\mathfrak p_v^M$) and invariant under $\mathfrak p_v^N$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.2 [unverified locator] (f ∈ 𝔅 ⇒ f̂ ∈ 𝔅 at a 𝔭-adic place)"]
theorem fourierV (hf : IsSchwartzBruhatLC v f) : IsSchwartzBruhatLC v (fourierV v f) := by
  obtain ⟨M, hM⟩ := hf.exists_uniform
  obtain ⟨N, hN⟩ := hf.exists_support
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hr : 0 < ‖HN.ϖ v ^ N‖ := norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v))
    filter_upwards [Metric.closedBall_mem_nhds y hr] with y' hy'
    rw [← ballIndV_eq, mem_ofPred_eq] at hy'
    unfold QuadFormsKB.Analysis.fourierV
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : f x = 0
    · simp [hx]
    · have hxv := hN x hx
      have h1 : psiV v (x * (y' - y)) = 1 := by
        refine psiV_eq_one_of_le_one v ?_
        rw [map_mul]
        calc Valued.v x * Valued.v (y' - y) ≤ exp N * exp (-N) := mul_le_mul' hxv hy'
          _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
      have : x * y' = x * y + x * (y' - y) := by ring
      simp only
      rw [this, AddChar.map_add_eq_mul, h1, mul_one]
  · refine HasCompactSupport.intro (isCompact_latticeV v (-M - diffExp v)) fun y hy => ?_
    by_contra hne
    apply hy
    rw [← annihV_latticeV]
    intro h hh
    rw [SetLike.mem_coe, mem_latticeV] at hh
    have heq : QuadFormsKB.Analysis.fourierV v f y = (psiV v (h * y) : ℂ) * QuadFormsKB.Analysis.fourierV v f y := by
      unfold QuadFormsKB.Analysis.fourierV
      rw [← integral_const_mul, ← integral_add_right_eq_self _ h]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hM x h hh, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have h1 : ((psiV v (h * y) : Circle) : ℂ) = 1 := by
      have := mul_right_cancel₀ hne (heq.symm.trans (one_mul _).symm)
      exact this
    exact Circle.coe_eq_one.mp h1 |> fun h => by exact_mod_cast h

end IsSchwartzBruhatLC

/-! ### The local functional equation at a finite place -/

theorem omegaV_unitsVSub_ne_top : omegaV v (unitsVSub v) ≠ ⊤ := by
  rw [omegaV_unitsVSub]
  refine ne_top_of_le_ne_top (volO_ne_top v) (measure_mono fun x hx => ?_)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (le_of_eq hx)

/-- The inverse of a character with $|\chi| = |\cdot|_v^a$ has $|\chi^{-1}| = |\cdot|_v^{-a}$. -/
theorem norm_inv_apply {χ : Fvˣ →* ℂˣ} {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a)
    (u : Fvˣ) : ‖((χ⁻¹ u : ℂˣ) : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ (-a) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hχ, Real.rpow_neg (NNReal.coe_nonneg _)]

theorem continuous_inv_char {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) : Continuous (χ⁻¹ : Fvˣ →* ℂˣ) := by
  have : (χ⁻¹ : Fvˣ →* ℂˣ) = fun u => (χ u)⁻¹ := by funext u; rfl
  rw [this]; exact hχc.inv

namespace IsSchwartzBruhatLC

variable {v} {f : v.adicCompletion F → ℂ}

/-- **Convergence for Schwartz–Bruhat functions**: $Z(f,\chi,s)$ converges absolutely for $\operatorname{Re}s > -a$
when $|\chi| = |\cdot|_v^a$ (for unitary $\chi$: $\operatorname{Re}s > 0$). -/
theorem integrable_zetaIntegrand (hf : IsSchwartzBruhatLC v f) {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχc : Continuous χ) {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar (v.adicCompletion F) u : ℝ) ^ a) {s : ℂ} (hs : 0 < a + s.re)
    (μ : Measure (v.adicCompletion F)ˣ) [μ.IsMulLeftInvariant] (hU : μ (unitsVSub v) ≠ ⊤) :
    Integrable (zetaIntegrand f χ s) μ := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨N, hN⟩ := hf.exists_support
  exact LocalZeta.integrable_zetaIntegrand v hf.measurable hC hN hχc hχ hs μ hU

end IsSchwartzBruhatLC

/-- **Tate's local functional equation at a finite place** (Cassels–Fröhlich Ch. XV, Thm. 2.4.1): for Schwartz–Bruhat
functions $f, g$ on $F_v$, a continuous quasi-character $\chi$ with $|\chi| = |\cdot|_v^a$, and
$0 < a + \operatorname{Re}s < 1$ (for unitary $\chi$: $0 < \operatorname{Re}s < 1$),
$$Z(f,\chi,s)\,Z(\hat g,\chi^{-1},1-s) = Z(g,\chi,s)\,Z(\hat f,\chi^{-1},1-s),$$
with Tate's measure `tateHaarV v` and QuadFormsKB's self-dual Fourier transform `fourierV v`. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 [unverified locator] (the local functional equation)"]
theorem zetaIntegral_fourierV_comm {f g : Fv → ℂ} (hf : IsSchwartzBruhatLC v f) (hg : IsSchwartzBruhatLC v g)
    {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a)
    {s : ℂ} (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    zetaIntegral (tateHaarV v) f χ s * zetaIntegral (tateHaarV v) (fourierV v g) χ⁻¹ (1 - s) =
      zetaIntegral (tateHaarV v) g χ s * zetaIntegral (tateHaarV v) (fourierV v f) χ⁻¹ (1 - s) := by
  have hs' : 0 < -a + (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hU := omegaV_unitsVSub_ne_top v
  have key := zetaIntegral_mul_fourier_comm (continuous_distribHaarChar_v v) (selfDualV v) (psiV v)
    (continuous_psiV v) χ s (hf.integrable _) (hg.integrable _)
    (hf.integrable_zetaIntegrand hχc hχ hs0 (omegaV v) hU)
    (hg.integrable_zetaIntegrand hχc hχ hs0 (omegaV v) hU)
    (hf.fourierV.integrable_zetaIntegrand (continuous_inv_char v hχc) (norm_inv_apply v hχ) hs' (omegaV v) hU)
    (hg.fourierV.integrable_zetaIntegrand (continuous_inv_char v hχc) (norm_inv_apply v hχ) hs' (omegaV v) hU)
  simp only [tateHaarV, zetaIntegral_smul_measure]
  rw [mul_mul_mul_comm, mul_mul_mul_comm _ (zetaIntegral _ g χ s)]
  exact congrArg (fun z => _ * z) key

/-! ### The local gamma factor -/

/-- A continuous character of $F_v^\times$ is trivial on some higher unit group $U_v^{(n)}$, $n\ge1$
($\mathbb C^\times$ has no small subgroups). -/
theorem exists_unitFiltration_eq_one {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) :
    ∃ n, 1 ≤ n ∧ ∀ u ∈ unitFiltration v n, χ u = 1 := by
  set U : Set ℂˣ := {z | ‖(z : ℂ) - 1‖ < 1 / 2}
  have hU : IsOpen U :=
    isOpen_lt (continuous_norm.comp (Units.continuous_val.sub continuous_const)) continuous_const
  have h1 : χ ⁻¹' U ∈ 𝓝 1 := hχc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [U]))
  obtain ⟨n, hn⟩ := exists_unitFiltration_subset h1
  refine ⟨n + 1, by omega, fun u hu => ?_⟩
  have hu' : u ∈ unitFiltration v n := unitFiltration_antitone (by omega) hu
  have h := MonoidHom.eq_one_of_norm_sub_one_lt (χ.comp (unitFiltration v n).subtype) fun x => hn x.2
  exact DFunLike.congr_fun h ⟨u, hu'⟩

/-- On the units, $\mathbf 1_{1+\mathfrak p_v^m}$ is the indicator of $U_v^{(m)}$ for $m\ge1$. -/
theorem ballIndV_one_units {m : ℕ} (hm : 1 ≤ m) (u : Fvˣ) :
    ballIndV v 1 m u = (unitFiltration v m : Set Fvˣ).indicator 1 u := by
  classical
  rw [ballIndV, Set.indicator_apply, Set.indicator_apply]
  simp only [mem_ofPred_eq, SetLike.mem_coe, mem_unitFiltration, Pi.one_apply]
  congr 1
  apply propext
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  have h' : Valued.v ((u : Fv) - 1) < 1 :=
    h.trans_lt (by rw [← exp_zero, exp_lt_exp]; omega)
  have : (u : Fv) = ((u : Fv) - 1) + 1 := by ring
  rw [this, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one]), map_one]

theorem isOpen_unitFiltration {m : ℕ} (hm : 1 ≤ m) : IsOpen (unitFiltration v m : Set Fvˣ) := by
  have hr : ‖HN.ϖ v ^ (m : ℤ)‖ ≠ 0 := (norm_pos_iff.mpr (zpow_ne_zero _ (HN.ϖ_ne_zero v))).ne'
  have hU : IsOpen {x : Fv | Valued.v (x - 1) ≤ exp (-(m : ℤ))} := by
    rw [ballIndV_eq]; exact (IsUltrametricDist.isClopen_closedBall (1 : Fv) hr).isOpen
  have : (unitFiltration v m : Set Fvˣ) = Units.val ⁻¹' {x : Fv | Valued.v (x - 1) ≤ exp (-(m : ℤ))} := by
    ext u
    have := ballIndV_one_units v hm u
    simp only [ballIndV, Set.indicator_apply] at this
    simp only [mem_preimage, mem_ofPred_eq]
    by_cases h1 : u ∈ (unitFiltration v m : Set Fvˣ) <;>
      by_cases h2 : Valued.v ((u : Fv) - 1) ≤ exp (-(m : ℤ)) <;> simp_all
  rw [this]
  exact hU.preimage Units.continuous_val

/-- **The test function $\mathbf 1_{1+\mathfrak p_v^m}$**: if $\chi$ is trivial on $U_v^{(m)}$ ($m\ge1$), then
$Z(\mathbf 1_{1+\mathfrak p_v^m},\chi,s) = \operatorname{vol}^\times(U_v^{(m)})$ for every $s$. -/
theorem zetaIntegral_ballIndV_one {χ : Fvˣ →* ℂˣ} {m : ℕ} (hm : 1 ≤ m) (hχm : ∀ u ∈ unitFiltration v m, χ u = 1)
    (μ : Measure Fvˣ) (s : ℂ) :
    zetaIntegral μ (ballIndV v 1 m) χ s = (μ (unitFiltration v m)).toReal := by
  have hmeas : MeasurableSet (unitFiltration v m : Set Fvˣ) := (isOpen_unitFiltration v hm).measurableSet
  have hpt : zetaIntegrand (ballIndV v 1 m) χ s = (unitFiltration v m : Set Fvˣ).indicator 1 := by
    funext u
    rw [zetaIntegrand, ballIndV_one_units v hm]
    by_cases hu : u ∈ (unitFiltration v m : Set Fvˣ)
    · have h1 : distribHaarChar Fv u = 1 := distribHaarChar_eq_one_of_mem_unitsVSub (mem_unitFiltration.mp hu).1
      rw [indicator_of_mem hu, hχm u hu, h1]
      simp
    · rw [indicator_of_notMem hu]
      simp
  rw [zetaIntegral, hpt, show ((unitFiltration v m : Set Fvˣ).indicator 1 : Fvˣ → ℂ) =
    (unitFiltration v m : Set Fvˣ).indicator (fun _ => (1 : ℂ)) from rfl, integral_indicator hmeas, setIntegral_const,
    Complex.real_smul, mul_one, Measure.real]

theorem tateHaarV_unitFiltration_pos {m : ℕ} (hm : 1 ≤ m) : 0 < tateHaarV v (unitFiltration v m) := by
  have : (tateHaarV v).IsHaarMeasure := by
    unfold tateHaarV
    have hc : (lamV v)⁻¹.toNNReal ≠ 0 := by
      simpa using inv_pos.mpr (lamV_pos v)
    exact Measure.IsHaarMeasure.nnreal_smul _ hc
  exact (isOpen_unitFiltration v hm).measure_pos _ ⟨1, (unitFiltration v m).one_mem⟩

theorem tateHaarV_unitFiltration_lt_top (m : ℕ) : tateHaarV v (unitFiltration v m) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono fun u hu => (mem_unitFiltration.mp hu).1) ?_
  exact (tateHaarV_unitsVSub_ne_top v).lt_top

/-- The level $m\ge1$ of the test function $\mathbf 1_{1+\mathfrak p_v^m}$ in the gamma factor: some $m$ with $\chi$
trivial on $U_v^{(m)}$. -/
def gammaLevel {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) : ℕ := (exists_unitFiltration_eq_one v hχc).choose

/-- **The local gamma factor** $\gamma_v(\chi,s) = Z(\hat f_0,\chi^{-1},1-s)/Z(f_0,\chi,s)$ for the test function
$f_0 = \mathbf 1_{1+\mathfrak p_v^m}$, $m$ = `gammaLevel`. By `zetaIntegral_fourierV_eq_gammaFactorV` it does not
depend on the test function. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 [unverified locator] (the factor ρ(c))"]
def gammaFactorV {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) (s : ℂ) : ℂ :=
  zetaIntegral (tateHaarV v) (fourierV v (ballIndV v 1 (gammaLevel v hχc))) χ⁻¹ (1 - s) /
    zetaIntegral (tateHaarV v) (ballIndV v 1 (gammaLevel v hχc)) χ s

/-- **The local functional equation, gamma-factor form** (Tate's Thm. 2.4.1): for every Schwartz–Bruhat $f$ on $F_v$
and $0 < a + \operatorname{Re}s < 1$ ($|\chi| = |\cdot|_v^a$),
$$Z(\hat f,\chi^{-1},1-s) = \gamma_v(\chi,s)\,Z(f,\chi,s),$$
so $Z(\hat f,\chi^{-1},1-s)/Z(f,\chi,s)$ is independent of $f$. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 [unverified locator] (ζ(f̂, ĉ) = ρ(c) ζ(f, c))"]
theorem zetaIntegral_fourierV_eq_gammaFactorV {f : Fv → ℂ} (hf : IsSchwartzBruhatLC v f)
    {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ) {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a)
    {s : ℂ} (hs0 : 0 < a + s.re) (hs1 : a + s.re < 1) :
    zetaIntegral (tateHaarV v) (fourierV v f) χ⁻¹ (1 - s) =
      gammaFactorV v hχc s * zetaIntegral (tateHaarV v) f χ s := by
  have hm : 1 ≤ gammaLevel v hχc := (exists_unitFiltration_eq_one v hχc).choose_spec.1
  have hχm : ∀ u ∈ unitFiltration v (gammaLevel v hχc), χ u = 1 :=
    (exists_unitFiltration_eq_one v hχc).choose_spec.2
  set m := gammaLevel v hχc
  have hf0 : IsSchwartzBruhatLC v (ballIndV v 1 m) :=
    IsSchwartzBruhatLC.of_isSchwartzBruhatV ⟨1, fun _ => 1, fun _ => 1, fun _ => m, by funext x; simp⟩
  have hZ0 : zetaIntegral (tateHaarV v) (ballIndV v 1 m) χ s ≠ 0 := by
    rw [zetaIntegral_ballIndV_one v hm hχm]
    exact_mod_cast (ENNReal.toReal_pos (tateHaarV_unitFiltration_pos v hm).ne'
      (tateHaarV_unitFiltration_lt_top v m).ne).ne'
  have hfe := zetaIntegral_fourierV_comm v hf hf0 hχc hχ hs0 hs1
  rw [gammaFactorV, div_mul_eq_mul_div, eq_div_iff hZ0, mul_comm, ← hfe, mul_comm]

end

end NumberFieldKB.LocalZeta
