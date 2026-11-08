import NumberFieldKB.LocalZeta.NonArchimedean
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Holomorphy of the local zeta integral at a finite place

Let $F_v$ be the completion of a number field at a finite place $v$, $f$ a locally constant function with compact
support on $F_v$, and $\chi$ a continuous quasi-character of $F_v^\times$ whose absolute value is $|\cdot|_v^a$.
Tate's shell expansion cuts $F_v^\times$ into the shells $\varpi^k\mathcal O_v^\times$ (`shell v k`). On the shell of
index $k$ the modulus $|u|_v$ is constant, equal to $q^{-k}$, so
$$Z(f,\chi,s) = \sum_{k\in\mathbb Z} c_k\,e^{-s k\log q},\qquad c_k = \int_{\varpi^k\mathcal O_v^\times} f\chi\,d\mu,$$
(`zetaIntegral_eq_tsum`), a power series in $q^{-s}$ whose coefficients do not depend on $s$ and vanish for $k$ below
a bound (`zetaCoeff_eq_zero`). The coefficients decay like $q^{-ka}$ (`norm_zetaCoeff_le`), so on every vertical strip
inside the half plane $0 < a + \operatorname{Re}s$ the series converges uniformly and its sum is holomorphic
(`differentiableOn_zetaIntegral_strip`).

* **`differentiableOn_zetaIntegral`**: the local zeta integral is holomorphic on the half plane $0 < a + \operatorname{Re}s$
  of absolute convergence, for every left invariant measure on $F_v^\times$ giving finite mass to the units.
* **`differentiableOn_zetaIntegral_tateHaarV`**: the same for Tate's measure `tateHaarV v`.
-/

open IsDedekindDomain NumberField MeasureTheory Filter Topology Set WithZero
open scoped ENNReal NNReal
open QuadFormsKB QuadFormsKB.Analysis QuadFormsKB.Tamagawa.Measure.Weil

namespace NumberFieldKB.LocalZeta

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Fv" => v.adicCompletion F

/-- $\log|\varpi|_v = -\log N(v)$, a negative real number. -/
def logModV : ℝ := Real.log (modV v : ℝ)

theorem logModV_neg : logModV v < 0 := Real.log_neg (modV_pos' v) (modV_lt_one v)

/-- **The shell coefficient** $c_k = \int_{\varpi^k\mathcal O_v^\times} f(u)\chi(u)\,d\mu(u)$ (independent of $s$). -/
def zetaCoeff (μ : Measure Fvˣ) (f : Fv → ℂ) (χ : Fvˣ →* ℂˣ) (k : ℤ) : ℂ :=
  ∫ u in shell v k, f u * (χ u : ℂ) ∂μ

/-- On the shell of index $k$, $|u|_v^s = e^{s\,k\log|\varpi|_v}$. -/
theorem cpow_modulus_of_mem_shell {k : ℤ} {u : Fvˣ} (hu : u ∈ shell v k) (s : ℂ) :
    ((distribHaarChar Fv u : ℝ) : ℂ) ^ s = Complex.exp (s * (((k : ℝ) * logModV v : ℝ) : ℂ)) := by
  have hm := modV_pos' v
  have hpos : (0 : ℝ) < (modV v : ℝ) ^ k := zpow_pos hm k
  rw [distribHaarChar_of_mem_shell v hu, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    ← Complex.ofReal_log hpos.le, Real.log_zpow]
  congr 1
  rw [logModV]
  ring

/-- **The shell expansion** of the local zeta integral: for $0 < a + \operatorname{Re}s$,
$Z(f,\chi,s) = \sum_{k\in\mathbb Z} c_k\,e^{s\,k\log|\varpi|_v}$. -/
theorem zetaIntegral_eq_tsum {f : Fv → ℂ} (hf : IsSchwartzBruhatLC v f) {χ : Fvˣ →* ℂˣ} (hχc : Continuous χ)
    {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) (μ : Measure Fvˣ) [μ.IsMulLeftInvariant]
    (hU : μ (unitsVSub v) ≠ ⊤) {s : ℂ} (hs : 0 < a + s.re) :
    zetaIntegral μ f χ s =
      ∑' k : ℤ, zetaCoeff v μ f χ k * Complex.exp (s * (((k : ℝ) * logModV v : ℝ) : ℂ)) := by
  have hint := hf.integrable_zetaIntegrand hχc hχ hs μ hU
  have hunion : (⋃ k : ℤ, shell v k) = univ :=
    eq_univ_of_forall fun u => mem_iUnion.mpr ⟨_, mem_shell_log v u⟩
  have hsum : zetaIntegral μ f χ s = ∑' k : ℤ, ∫ u in shell v k, zetaIntegrand f χ s u ∂μ := by
    rw [zetaIntegral, ← integral_iUnion (fun k => measurableSet_shell v k) (pairwise_disjoint_shell v)
      hint.integrableOn, hunion, Measure.restrict_univ]
  rw [hsum]
  refine tsum_congr fun k => ?_
  rw [zetaCoeff, ← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_shell v k) fun u hu => ?_
  simp only [zetaIntegrand]
  rw [cpow_modulus_of_mem_shell v hu]

/-- The coefficient $c_k$ vanishes on the shells below the support of $f$. -/
theorem zetaCoeff_eq_zero {f : Fv → ℂ} {N : ℤ} (hN : ∀ x, f x ≠ 0 → Valued.v x ≤ exp N) {k : ℤ} (hk : k < -N)
    (μ : Measure Fvˣ) (χ : Fvˣ →* ℂˣ) : zetaCoeff v μ f χ k = 0 := by
  rw [zetaCoeff]
  refine (setIntegral_congr_fun (measurableSet_shell v k) (g := fun _ => (0 : ℂ)) fun u hu => ?_).trans
    (by simp)
  have hv : Valued.v (u : Fv) = exp (-k) := hu
  by_cases h : f u = 0
  · simp [h]
  · exfalso
    have h2 := hN _ h
    rw [hv, exp_le_exp] at h2
    omega

/-- **Size of the shell coefficients**: $|c_k| \le C\,|\varpi|_v^{ka}\,\mu(\mathcal O_v^\times)$. -/
theorem norm_zetaCoeff_le {f : Fv → ℂ} {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) {χ : Fvˣ →* ℂˣ} {a : ℝ}
    (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) (μ : Measure Fvˣ) [μ.IsMulLeftInvariant]
    (hU : μ (unitsVSub v) ≠ ⊤) (k : ℤ) :
    ‖zetaCoeff v μ f χ k‖ ≤ C * Real.exp (a * ((k : ℝ) * logModV v)) * (μ (unitsVSub v)).toReal := by
  have hm := modV_pos' v
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hfin : μ (shell v k) < ⊤ := by rw [measure_shell]; exact hU.lt_top
  have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (s := shell v k)
    (f := fun u : Fvˣ => f u * (χ u : ℂ)) (C := C * Real.exp (a * ((k : ℝ) * logModV v))) hfin ?_
  · rw [measureReal_def, measure_shell] at h1
    exact h1
  · intro u hu
    rw [norm_mul, hχ, distribHaarChar_of_mem_shell v hu]
    have h2 : ((modV v : ℝ) ^ k) ^ a = Real.exp (a * ((k : ℝ) * logModV v)) := by
      rw [Real.rpow_def_of_pos (zpow_pos hm k), Real.log_zpow, logModV]
      congr 1
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.exp_pos _).le

theorem isOpen_strip (a σ τ : ℝ) : IsOpen {s : ℂ | σ < a + s.re ∧ a + s.re < τ} :=
  (isOpen_lt (continuous_const : Continuous fun _ : ℂ => σ) (by fun_prop : Continuous fun s : ℂ => a + s.re)).inter
    (isOpen_lt (by fun_prop : Continuous fun s : ℂ => a + s.re) (continuous_const : Continuous fun _ : ℂ => τ))

/-- On each bounded vertical strip $\sigma < a + \operatorname{Re}s < \tau$ with $\sigma > 0$, the local zeta integral is
holomorphic (uniform convergence of the shell expansion). -/
theorem differentiableOn_zetaIntegral_strip {f : Fv → ℂ} (hf : IsSchwartzBruhatLC v f) {χ : Fvˣ →* ℂˣ}
    (hχc : Continuous χ) {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a)
    (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (hU : μ (unitsVSub v) ≠ ⊤) {σ τ : ℝ} (hσ : 0 < σ) :
    DifferentiableOn ℂ (fun s => zetaIntegral μ f χ s) {s : ℂ | σ < a + s.re ∧ a + s.re < τ} := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨N₀, hN₀⟩ := hf.exists_support
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = max N₀ 0 := ⟨(max N₀ 0).toNat, Int.toNat_of_nonneg (le_max_right _ _)⟩
  have hN : ∀ x, f x ≠ 0 → Valued.v x ≤ exp (n : ℤ) := fun x hx =>
    (hN₀ x hx).trans (exp_le_exp.mpr (hn ▸ le_max_left _ _))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hL := logModV_neg v
  have hM0 : 0 ≤ (μ (unitsVSub v)).toReal := ENNReal.toReal_nonneg
  set G : ℕ → ℂ → ℂ := fun j s => zetaCoeff v μ f χ ((j : ℤ) - n) *
    Complex.exp (s * (((((j : ℤ) - n : ℤ) : ℝ) * logModV v : ℝ) : ℂ)) with hG
  have heq : ∀ s ∈ {s : ℂ | σ < a + s.re ∧ a + s.re < τ},
      zetaIntegral μ f χ s = ∑' j : ℕ, G j s := by
    intro s hs
    have hs0 : 0 < a + s.re := hσ.trans hs.1
    rw [zetaIntegral_eq_tsum v hf hχc hχ μ hU hs0]
    have hinj : Function.Injective (fun j : ℕ => (j : ℤ) - n) := fun x y h => by simpa using h
    refine (hinj.tsum_eq (f := fun k : ℤ => zetaCoeff v μ f χ k *
      Complex.exp (s * (((k : ℝ) * logModV v : ℝ) : ℂ))) ?_).symm
    intro k hk
    rw [Function.mem_support] at hk
    by_contra hr
    apply hk
    have hk2 : k < -(n : ℤ) := by
      by_contra hge
      exact hr ⟨(k + n).toNat, by show (((k + n).toNat : ℕ) : ℤ) - n = k; omega⟩
    simp [zetaCoeff_eq_zero v hN hk2 μ χ]
  have hU' : IsOpen {s : ℂ | σ < a + s.re ∧ a + s.re < τ} := isOpen_strip a σ τ
  have hdiff : DifferentiableOn ℂ (fun s => ∑' j : ℕ, G j s) {s : ℂ | σ < a + s.re ∧ a + s.re < τ} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun j : ℕ => (C * (μ (unitsVSub v)).toReal * Real.exp (τ * (-logModV v) * n)) *
        (Real.exp (σ * logModV v)) ^ j) ?_ ?_ hU' ?_
    · refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
      rw [Real.exp_lt_one_iff]
      exact mul_neg_of_pos_of_neg hσ hL
    · intro j
      exact Differentiable.differentiableOn (by simp only [hG]; fun_prop)
    · intro j s hs
      have hk' : (((j : ℤ) - n : ℤ) : ℝ) = (j : ℝ) - n := by push_cast; rfl
      have h1 := norm_zetaCoeff_le v hC hχ μ hU ((j : ℤ) - n)
      have hre : (s * (((((j : ℤ) - n : ℤ) : ℝ) * logModV v : ℝ) : ℂ)).re =
          s.re * ((((j : ℤ) - n : ℤ) : ℝ) * logModV v) := by
        simp [Complex.mul_re]
      simp only [hG]
      rw [norm_mul, Complex.norm_exp, hre]
      have he1 : σ ≤ a + s.re := hs.1.le
      have he2 : a + s.re ≤ τ := hs.2.le
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      calc ‖zetaCoeff v μ f χ ((j : ℤ) - n)‖ * Real.exp (s.re * ((((j : ℤ) - n : ℤ) : ℝ) * logModV v))
          ≤ (C * Real.exp (a * ((((j : ℤ) - n : ℤ) : ℝ) * logModV v)) * (μ (unitsVSub v)).toReal) *
              Real.exp (s.re * ((((j : ℤ) - n : ℤ) : ℝ) * logModV v)) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = C * (μ (unitsVSub v)).toReal * Real.exp ((a + s.re) * ((((j : ℤ) - n : ℤ) : ℝ) * logModV v)) := by
            rw [add_mul, Real.exp_add]; ring
        _ ≤ C * (μ (unitsVSub v)).toReal * (Real.exp (σ * logModV v * j) * Real.exp (τ * (-logModV v) * n)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC0 hM0)
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            rw [hk']
            nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr he1) (neg_nonneg.mpr hL.le)) hj0,
              mul_nonneg (mul_nonneg (sub_nonneg.mpr he2) (neg_nonneg.mpr hL.le)) hn0]
        _ = (C * (μ (unitsVSub v)).toReal * Real.exp (τ * (-logModV v) * n)) * (Real.exp (σ * logModV v)) ^ j := by
            rw [← Real.exp_nat_mul, show (j : ℝ) * (σ * logModV v) = σ * logModV v * j by ring]
            ring
  exact hdiff.congr heq

/-- **Holomorphy of the local zeta integral at a finite place** (Tate): if $f$ is locally constant with compact
support, $\chi$ is continuous with $|\chi| = |\cdot|_v^a$, and $\mu$ is a left invariant measure on $F_v^\times$ with
$\mu(\mathcal O_v^\times) < \infty$, then $s\mapsto Z(f,\chi,s)$ is holomorphic on the half plane
$0 < a + \operatorname{Re}s$ of absolute convergence. -/
@[kb "casselsfrohlich1967" "Ch. XV (Tate), §2.4, Thm. 2.4.1 [unverified locator] (ζ(f, c) is holomorphic where it converges)"]
theorem differentiableOn_zetaIntegral {f : Fv → ℂ} (hf : IsSchwartzBruhatLC v f) {χ : Fvˣ →* ℂˣ}
    (hχc : Continuous χ) {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a)
    (μ : Measure Fvˣ) [μ.IsMulLeftInvariant] (hU : μ (unitsVSub v) ≠ ⊤) :
    DifferentiableOn ℂ (fun s => zetaIntegral μ f χ s) {s : ℂ | 0 < a + s.re} := by
  intro s hs
  have hs' : 0 < a + s.re := hs
  have hmem : s ∈ {w : ℂ | (a + s.re) / 2 < a + w.re ∧ a + w.re < a + s.re + 1} :=
    ⟨by linarith, by linarith⟩
  exact ((differentiableOn_zetaIntegral_strip v hf hχc hχ μ hU (by linarith : 0 < (a + s.re) / 2)).differentiableAt
    ((isOpen_strip a _ _).mem_nhds hmem)).differentiableWithinAt

/-- **Holomorphy of the local zeta integral for Tate's measure** `tateHaarV v`. -/
theorem differentiableOn_zetaIntegral_tateHaarV {f : Fv → ℂ} (hf : IsSchwartzBruhatLC v f) {χ : Fvˣ →* ℂˣ}
    (hχc : Continuous χ) {a : ℝ} (hχ : ∀ u, ‖(χ u : ℂ)‖ = (distribHaarChar Fv u : ℝ) ^ a) :
    DifferentiableOn ℂ (fun s => zetaIntegral (tateHaarV v) f χ s) {s : ℂ | 0 < a + s.re} :=
  differentiableOn_zetaIntegral v hf hχc hχ (tateHaarV v) (tateHaarV_unitsVSub_ne_top v)

end

end NumberFieldKB.LocalZeta
