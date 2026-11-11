import NumberFieldKB.NonVanishing.LogDeriv
import NumberFieldKB.NonVanishing.Abelian
import NumberFieldKB.NonVanishing.Newman
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# The Euler product at $s = 1$ in the natural order

$F$ is a number field; $v$ runs over the nonzero primes of $\mathcal O_F$, $N(v)$ = `normP v`, $\lambda_v = \log N(v)$.
Let $a(v)\in\mathbb C$ with $|a(v)|\le1$, and let $L$ be holomorphic and without zeros on an open set $U$ containing the
closed half-plane $\operatorname{Re}s\ge1$, with $L(s) = \prod_v(1-a(v)N(v)^{-s})^{-1}$ for $\operatorname{Re}s>1$
(`L s = exp (logEuler a s)`). Then (**`tendsto_prod_eulerFactor_one`**)
$$\prod_{N(v)\le X}\bigl(1-a(v)N(v)^{-1}\bigr)^{-1}\longrightarrow L(1)\qquad(X\to\infty).$$

*Proof.*
1. $f(t) = \vartheta_a(e^t)e^{-t}$, $\vartheta_a(x) = \sum_{N(v)<x}a(v)\lambda_v$ (`thetaNorm`), is bounded by Chebyshev's
   bound (`norm_thetaNorm_le`); its Laplace transform is $(1+z)^{-1}\sum_va(v)\lambda_vN(v)^{-1-z} =
   (1+z)^{-1}\bigl(-L'/L(1+z)-H(1+z)\bigr)$ (`LogDeriv.lean`), holomorphic on a neighbourhood of
   $\operatorname{Re}z\ge0$. Newman's theorem: $\int_0^Tf$ converges, so it is bounded (`exists_bound_integral_thetaNorm`).
2. Partial summation with $e^{-u}$: $A(X) = \sum_{\lambda_v<X}a(v)\lambda_v/N(v) = \vartheta_a(e^X)e^{-X}+\int_0^Xf$ is
   bounded (`exists_bound_stepSum_logDiv`).
3. Partial summation with $1/u$: $B(X) = \sum_{\lambda_v<X}a(v)/N(v) = A(X)/X+\int_{\log2}^XA(u)u^{-2}\,du$ converges
   to some $\ell$ (`exists_tendsto_stepSum_div`).
4. Abel's theorem for the Laplace transform: $\sum_va(v)N(v)^{-1-\sigma} = \sigma\int_0^\infty B(t)e^{-\sigma t}\,dt\to\ell$
   as $\sigma\to0^+$ (`tendsto_tsum_nps_one_add`).
5. $-\log(1-w) = w+r(w)$ with $\sum_v|r(w_v)|<\infty$ uniformly on $\operatorname{Re}s\ge1$: both the partial products at
   $s = 1$ and $L(1+\sigma)$ tend to $\exp(\ell+R)$, and $L(1+\sigma)\to L(1)$ by continuity.

Only boundedness comes out of Newman's theorem; the value is identified by the Abelian step 4 (no prime ideal theorem
with an error term is needed).
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral IsDedekindDomain NumberField
open QuadFormsKB.NFEuler
open scoped Interval

namespace NumberFieldKB.NonVanishing

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

/-! ### Step 1: Newman's theorem for $\vartheta_a(e^t)e^{-t}$ -/

/-- $f_a(t) = \vartheta_a(e^t)e^{-t}$ with $\vartheta_a(x) = \sum_{N(v)<x}a(v)\log N(v)$. -/
def thetaNorm (a : HeightOneSpectrum (𝓞 F) → ℂ) (t : ℝ) : ℂ :=
  stepSum (fun v => a v * Real.log (normP v)) t * cexp (-(t : ℂ))

theorem norm_thetaNorm_le {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) (t : ℝ) :
    ‖thetaNorm a t‖ ≤ chebConst F := by
  unfold thetaNorm
  rw [norm_mul, Complex.norm_exp]
  simp only [neg_re, ofReal_re]
  calc _ ≤ chebConst F * Real.exp t * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (norm_stepSum_log_le ha t) (Real.exp_pos _).le
    _ = chebConst F := by rw [mul_assoc, ← Real.exp_add]; simp

theorem measurable_thetaNorm (a : HeightOneSpectrum (𝓞 F) → ℂ) : Measurable (thetaNorm a) := by
  unfold thetaNorm
  exact (measurable_stepSum _).mul (by fun_prop)

/-- The Laplace transform of `thetaNorm a`. -/
theorem integral_thetaNorm_mul_cexp {a : HeightOneSpectrum (𝓞 F) → ℂ} (ha : ∀ v, ‖a v‖ ≤ 1) {z : ℂ}
    (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), thetaNorm a t * cexp (-(z * t)) =
      (∑' v, a v * Real.log (normP v) * nps v (1 + z)) / (1 + z) := by
  have hre : 0 < (1 + z).re := by rw [add_re, one_re]; linarith
  have h1 : ∀ t : ℝ, thetaNorm a t * cexp (-(z * t)) =
      stepSum (fun v => a v * Real.log (normP v)) t * cexp (-((1 + z) * t)) := by
    intro t
    unfold thetaNorm
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp only [h1]
  refine integral_stepSum_mul_cexp _ hre ?_
  have hσ : 1 < 1 + z.re := by linarith
  refine (summable_log_mul_rpow (F := F) hσ).of_nonneg_of_le (fun v => by positivity) fun v => ?_
  rw [add_re, one_re, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (log_normP_pos v)]
  exact mul_le_mul_of_nonneg_right (by simpa [mul_comm] using mul_le_of_le_one_left (log_normP_pos v).le (ha v))
    (Real.rpow_nonneg (normP_pos' v).le _)

/-- The hypotheses on $L$: holomorphic and without zeros on an open $U\supseteq\{\operatorname{Re}s\ge1\}$, and the Euler
product $\exp(\texttt{logEuler}\ a)$ on $\operatorname{Re}s>1$. -/
structure EulerData (a : HeightOneSpectrum (𝓞 F) → ℂ) (L : ℂ → ℂ) : Prop where
  norm_le : ∀ v, ‖a v‖ ≤ 1
  exists_open : ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 1 ≤ s.re} ⊆ U ∧ DifferentiableOn ℂ L U ∧ ∀ s ∈ U, L s ≠ 0
  eq_exp : ∀ s : ℂ, 1 < s.re → L s = cexp (logEuler a s)

/-- **Newman's theorem applied to $\vartheta_a(e^t)e^{-t}$**: $\int_0^T\vartheta_a(e^t)e^{-t}\,dt$ converges. -/
theorem exists_tendsto_integral_thetaNorm {a : HeightOneSpectrum (𝓞 F) → ℂ} {L : ℂ → ℂ} (hL : EulerData a L) :
    ∃ c : ℂ, Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, thetaNorm a t) atTop (𝓝 c) := by
  have ha := hL.norm_le
  obtain ⟨U, hU, hsub, hdL, hne⟩ := hL.exists_open
  set V : Set ℂ := U ∩ {s | 3 / 4 < s.re} with hV
  have hVo : IsOpen V := hU.inter (isOpen_lt continuous_const Complex.continuous_re)
  set U' : Set ℂ := (fun z : ℂ => 1 + z) ⁻¹' V with hU'
  have hU'o : IsOpen U' := hVo.preimage (by fun_prop)
  have hmap : MapsTo (fun z : ℂ => 1 + z) U' V := fun z hz => hz
  have hre : ∀ z ∈ U', 3 / 4 < (1 + z).re := fun z hz => hz.2
  set g : ℂ → ℂ := fun z => (-deriv L (1 + z) / L (1 + z) - hFun a (1 + z)) / (1 + z) with hg
  have hd1 : DifferentiableOn ℂ (fun z => deriv L (1 + z)) U' :=
    ((hdL.deriv hU).mono inter_subset_left).comp (by fun_prop) hmap
  have hd2 : DifferentiableOn ℂ (fun z => L (1 + z)) U' := (hdL.mono inter_subset_left).comp (by fun_prop) hmap
  have hd3 : DifferentiableOn ℂ (fun z => hFun a (1 + z)) U' :=
    (differentiableOn_hFun ha).comp (by fun_prop) (fun z hz => hre z hz)
  have hgd : DifferentiableOn ℂ g U' := by
    refine ((hd1.neg.div hd2 fun z hz => hne _ hz.1).sub hd3).div (by fun_prop) fun z hz => ?_
    intro h
    have := hre z hz
    rw [h] at this
    norm_num at this
  refine ⟨g 0, newman (f := thetaNorm a) (g := g) (B := chebConst F) (measurable_thetaNorm a).aestronglyMeasurable
    (fun t _ => norm_thetaNorm_le ha t) hU'o (fun z hz => ?_) hgd (fun z hz => ?_)⟩
  · have hz' : 0 ≤ z.re := hz
    have h1 : 1 ≤ (1 + z).re := by rw [add_re, one_re]; linarith
    exact ⟨hsub h1, show 3 / 4 < (1 + z).re by linarith⟩
  · have h1 : 1 < (1 + z).re := by rw [add_re, one_re]; linarith
    rw [integral_thetaNorm_mul_cexp ha hz, hg]
    simp only
    rw [neg_logDeriv_eq ha hL.eq_exp h1, tsum_logDeriv_eq ha h1, add_sub_cancel_right]

theorem exists_bound_integral_thetaNorm {a : HeightOneSpectrum (𝓞 F) → ℂ} {L : ℂ → ℂ} (hL : EulerData a L) :
    ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T → ‖∫ t in (0 : ℝ)..T, thetaNorm a t‖ ≤ C := by
  obtain ⟨c, hc⟩ := exists_tendsto_integral_thetaNorm hL
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp (hc.norm.eventually (eventually_lt_nhds (lt_add_one ‖c‖)))
  refine ⟨max (‖c‖ + 1) (chebConst F * T0), fun T hT => ?_⟩
  rcases le_total T0 T with h | h
  · exact (hT0 T h).le.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := chebConst F) fun t _ =>
      norm_thetaNorm_le hL.norm_le t).trans ?_
    rw [sub_zero, abs_of_nonneg hT]
    exact mul_le_mul_of_nonneg_left h chebConst_nonneg

/-! ### Step 2: $\sum_{\log N(v)<X}a(v)\log N(v)/N(v)$ is bounded -/

/-- Partial summation for step functions: if `b v * w (log N v) = c v` then
`stepSum c X = stepSum b X * w X - ∫_α^X stepSum b u * w' u`. -/
theorem stepSum_mul_eq (b c : HeightOneSpectrum (𝓞 F) → ℂ) {α X : ℝ} (hαX : α ≤ X)
    (hα : ∀ v : HeightOneSpectrum (𝓞 F), Real.log (normP v) < X → α ≤ Real.log (normP v)) {w w' : ℝ → ℂ}
    (hw : ∀ u ∈ [[α, X]], HasDerivAt w (w' u) u) (hw' : IntervalIntegrable w' volume α X)
    (hc : ∀ v, b v * w (Real.log (normP v)) = c v) :
    stepSum c X = stepSum b X * w X - ∫ u in α..X, stepSum b u * w' u := by
  set S := (primesNormLe F ⌊Real.exp X⌋₊).filter (fun v => Real.log (normP v) < X) with hSdef
  have hmem : ∀ v, v ∈ S ↔ Real.log (normP v) < X := fun v =>
    ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨mem_primesNormLe_of_log_lt h, h⟩⟩
  have hS : ∀ {t : ℝ}, t ≤ X → ∀ v : HeightOneSpectrum (𝓞 F), Real.log (normP v) < t → v ∈ S :=
    fun ht v h => (hmem v).mpr (h.trans_le ht)
  have hlam : ∀ i ∈ S, α ≤ Real.log (normP i) ∧ Real.log (normP i) ≤ X := fun i hi =>
    ⟨hα i ((hmem i).mp hi), ((hmem i).mp hi).le⟩
  have h := sum_mul_eq_sub_integral S b (fun v => Real.log (normP v)) hlam hw hw'
  rw [stepSum_of_forall c hmem, stepSum_of_forall b hmem]
  rw [Finset.sum_congr rfl (fun i _ => hc i)] at h
  rw [h]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hαX] at hu
  rw [← stepSum_eq_sum_of_subset b (hS hu.2)]

/-- $A(X) = \vartheta_a(e^X)e^{-X}+\int_0^X\vartheta_a(e^u)e^{-u}\,du$ (partial summation with $e^{-u}$). -/
theorem stepSum_logDiv_eq (a : HeightOneSpectrum (𝓞 F) → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    stepSum (fun v => a v * Real.log (normP v) / (normP v : ℂ)) X =
      thetaNorm a X + ∫ u in (0 : ℝ)..X, thetaNorm a u := by
  have hw : ∀ u ∈ [[(0 : ℝ), X]], HasDerivAt (fun u : ℝ => cexp (-(u : ℂ))) (-cexp (-(u : ℂ))) u := fun u _ => by
    simpa using (hasDerivAt_id u).ofReal_comp.neg.cexp
  have h := stepSum_mul_eq (fun v => a v * Real.log (normP v))
    (fun v => a v * Real.log (normP v) / (normP v : ℂ)) hX (fun v _ => (log_normP_pos v).le) hw
    (Continuous.intervalIntegrable (by fun_prop) _ _) (fun v => by
      rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (normP_pos' v)]
      simp [div_eq_mul_inv])
  rw [h]
  have h2 : ∫ u in (0 : ℝ)..X, stepSum (fun v => a v * Real.log (normP v)) u * -cexp (-(u : ℂ)) =
      -∫ u in (0 : ℝ)..X, thetaNorm a u := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp [thetaNorm]
  rw [h2, sub_neg_eq_add]
  rfl

theorem exists_bound_stepSum_logDiv {a : HeightOneSpectrum (𝓞 F) → ℂ} {L : ℂ → ℂ} (hL : EulerData a L) :
    ∃ C : ℝ, ∀ X : ℝ, ‖stepSum (fun v => a v * Real.log (normP v) / (normP v : ℂ)) X‖ ≤ C := by
  obtain ⟨C1, hC1⟩ := exists_bound_integral_thetaNorm hL
  refine ⟨chebConst F + |C1|, fun X => ?_⟩
  have hc0 := chebConst_nonneg (F := F)
  rcases le_or_gt 0 X with hX | hX
  · rw [stepSum_logDiv_eq a hX]
    refine (norm_add_le _ _).trans (add_le_add (norm_thetaNorm_le hL.norm_le X) ((hC1 X hX).trans (le_abs_self _)))
  · have hS : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F))) ↔
        Real.log (normP v) < X := fun v => by
      have := log_normP_pos v
      exact ⟨fun h => absurd h (Finset.notMem_empty _), fun h => by linarith⟩
    rw [stepSum_of_forall _ hS]
    simpa using add_nonneg hc0 (abs_nonneg C1)

/-! ### Step 3: $\sum_{\log N(v)<X}a(v)/N(v)$ converges -/

/-- $B(X) = A(X)/X+\int_{\log2}^XA(u)u^{-2}\,du$ (partial summation with $1/u$). -/
theorem stepSum_div_eq (a : HeightOneSpectrum (𝓞 F) → ℂ) {X : ℝ} (hX : Real.log 2 ≤ X) :
    stepSum (fun v => a v / (normP v : ℂ)) X =
      stepSum (fun v => a v * Real.log (normP v) / (normP v : ℂ)) X / X +
        ∫ u in (Real.log 2)..X, stepSum (fun v => a v * Real.log (normP v) / (normP v : ℂ)) u / (u : ℂ) ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : ∀ u ∈ [[Real.log 2, X]], 0 < u := fun u hu => by
    rw [uIcc_of_le hX] at hu; exact hl2.trans_le hu.1
  have hw : ∀ u ∈ [[Real.log 2, X]], HasDerivAt (fun u : ℝ => ((u⁻¹ : ℝ) : ℂ)) (((-(u ^ 2)⁻¹ : ℝ)) : ℂ) u :=
    fun u hu => (hasDerivAt_inv (hpos u hu).ne').ofReal_comp
  have hint : IntervalIntegrable (fun u : ℝ => (((-(u ^ 2)⁻¹ : ℝ)) : ℂ)) volume (Real.log 2) X :=
    ContinuousOn.intervalIntegrable (Complex.continuous_ofReal.comp_continuousOn
      (ContinuousOn.neg (ContinuousOn.inv₀ (continuousOn_pow 2) fun u hu => (pow_pos (hpos u hu) 2).ne')))
  have h := stepSum_mul_eq (fun v => a v * Real.log (normP v) / (normP v : ℂ))
    (fun v => a v / (normP v : ℂ)) hX
    (fun v _ => Real.log_le_log (by norm_num) (by exact_mod_cast two_le_normP v)) hw hint (fun v => by
      have : (Real.log (normP v) : ℂ) ≠ 0 := by exact_mod_cast (log_normP_pos v).ne'
      have h2 : (normP v : ℂ) ≠ 0 := by exact_mod_cast (normP_pos' v).ne'
      rw [Complex.ofReal_inv]
      field_simp)
  rw [h]
  have h2 : ∫ u in (Real.log 2)..X, stepSum (fun v => a v * Real.log (normP v) / (normP v : ℂ)) u *
      (((-(u ^ 2)⁻¹ : ℝ)) : ℂ) =
      -∫ u in (Real.log 2)..X, stepSum (fun v => a v * Real.log (normP v) / (normP v : ℂ)) u / (u : ℂ) ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    push_cast
    ring
  rw [h2, sub_neg_eq_add]
  push_cast
  ring

theorem exists_tendsto_stepSum_div {a : HeightOneSpectrum (𝓞 F) → ℂ} {L : ℂ → ℂ} (hL : EulerData a L) :
    ∃ ℓ : ℂ, Tendsto (stepSum fun v => a v / (normP v : ℂ)) atTop (𝓝 ℓ) := by
  obtain ⟨C, hC⟩ := exists_bound_stepSum_logDiv hL
  set A : ℝ → ℂ := stepSum fun v => a v * Real.log (normP v) / (normP v : ℂ) with hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfi : IntegrableOn (fun u : ℝ => A u / (u : ℂ) ^ 2) (Ioi (Real.log 2)) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hl2).const_mul C)
      ((measurable_stepSum _).div (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hl2.trans hu
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0, Real.rpow_neg hu0.le,
      Real.rpow_two, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hC u) (by positivity)
  refine ⟨∫ u in Ioi (Real.log 2), A u / (u : ℂ) ^ 2, ?_⟩
  have h1 : Tendsto (fun X : ℝ => A X / (X : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := C)).div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with X hX
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
    exact div_le_div_of_nonneg_right (hC X) hX.le
  have h2 := intervalIntegral_tendsto_integral_Ioi (Real.log 2) hfi tendsto_id
  refine (by simpa using h1.add h2 : Tendsto _ atTop _).congr' ?_
  filter_upwards [eventually_ge_atTop (Real.log 2)] with X hX
  exact (stepSum_div_eq a hX).symm

/-! ### Step 5: the Euler product -/

/-- **The Euler product at $s = 1$ in the natural order.** If $|a|\le1$ and $L = \prod_v(1-a(v)N(v)^{-s})^{-1}$ on
$\operatorname{Re}s>1$ continues holomorphically and without zeros to an open set containing
$\operatorname{Re}s\ge1$, then $\prod_{N(v)\le X}(1-a(v)N(v)^{-1})^{-1}\to L(1)$. -/
@[kb "zagier1997" "Newman's analytic theorem, applied as in the proof of the prime number theorem [unverified locator]"]
theorem tendsto_prod_eulerFactor_one {a : HeightOneSpectrum (𝓞 F) → ℂ} {L : ℂ → ℂ} (hL : EulerData a L) :
    Tendsto (fun X : ℕ => ∏ v ∈ primesNormLe F X, eulerFactor a 1 v) atTop (𝓝 (L 1)) := by
  have ha := hL.norm_le
  obtain ⟨U, hU, hsub, hdL, -⟩ := hL.exists_open
  obtain ⟨ℓ, hℓ⟩ := exists_tendsto_stepSum_div hL
  set R : ℂ := ∑' v, remLog a 1 v with hR
  have hs1 : 1 ≤ (1 : ℂ).re := le_rfl
  have hlog : Tendsto (fun X : ℕ => Real.log ((X : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hP : Tendsto (fun X : ℕ => ∏ v ∈ primesNormLe F X, eulerFactor a 1 v) atTop (𝓝 (cexp (ℓ + R))) := by
    simp only [prod_eulerFactor_one_eq a ha]
    exact (Complex.continuous_exp.tendsto _).comp
      ((hℓ.comp hlog).add ((summable_remLog ha hs1).hasSum.comp tendsto_primesNormLe))
  have hσ1 : Tendsto (fun σ : ℝ => L (1 + (σ : ℂ))) (𝓝[>] 0) (𝓝 (cexp (ℓ + R))) := by
    have h := ((tendsto_tsum_nps_one_add ha hℓ).add (tendsto_tsum_remLog ha))
    refine ((Complex.continuous_exp.tendsto _).comp h).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (0 : ℝ) < σ := hσ
    have h1 : 1 < (1 + (σ : ℂ)).re := by simp; linarith
    simp only [Function.comp]
    rw [hL.eq_exp _ h1, logEuler, ← (summable_norm_mul_nps ha h1).of_norm.tsum_add
      (summable_remLog ha h1.le)]
    congr 1
    refine tsum_congr fun v => ?_
    simp [remLog]
  have hσ2 : Tendsto (fun σ : ℝ => L (1 + (σ : ℂ))) (𝓝[>] 0) (𝓝 (L 1)) := by
    have hc : ContinuousAt L 1 := hdL.continuousOn.continuousAt (hU.mem_nhds (hsub (by simp)))
    have hlin : Tendsto (fun σ : ℝ => 1 + (σ : ℂ)) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun σ : ℝ => 1 + (σ : ℂ)) (𝓝 0) (𝓝 (1 + ((0 : ℝ) : ℂ))) :=
        (Continuous.tendsto (by fun_prop) 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    exact hc.tendsto.comp hlin
  rw [tendsto_nhds_unique hσ2 hσ1]
  exact hP

end

end NumberFieldKB.NonVanishing
