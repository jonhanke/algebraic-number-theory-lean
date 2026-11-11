import NumberFieldKB.Chebotarev.PrimeDensity
import NumberFieldKB.Chebotarev.DensityTools
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import QuadFormsKB.Citation
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star

/-!
# Weil, *Basic Number Theory*, VII.§1 Cor. 2–3 and VII.§5 Cor. 3–4: places of modular degree one

$k_0\subseteq k$ are number fields (`K₀`, `K`, with `[Algebra K₀ K]`); $v$ runs over the finite places of $k$
(the nonzero primes of $\mathcal O_k$, `HeightOneSpectrum (𝓞 K)`), $q_v=N\mathfrak p_v$ (`normP v`). Weil's
*modular degree* $f(v)$ of $k_v$ over the closure $(k_0)_u$ of $k_0$ in $k_v$ ($u$ the place of $k_0$ below $v$)
is the residue degree of $\mathfrak p_v$ over $\mathfrak p_u$ (`modDeg K₀ v`, Mathlib's `Ideal.inertiaDeg`);
indeed $q_v=q_u^{f(v)}$.

* **`weil_VII_1_cor2`** (VII.§1 Cor. 2): if $f(v)>1$ for almost all $v\in M$, then $\sum_{v\in M}q_v^{-\sigma}$
  converges for $\sigma>1/2$, hence (**`weil_VII_1_cor2_multipliable`**) so does
  $p(M,\sigma)=\prod_{v\in M}(1-q_v^{-\sigma})^{-1}$.
* **`weil_VII_1_cor3`** (VII.§1 Cor. 3): for such $M$ and $\lvert\theta_v\rvert\le1$, the product
  $\prod_{v\in M}(1-\theta_vq_v^{-s})^{-1}$ converges absolutely and is $\ne0$ for $\operatorname{Re}s>1/2$;
  **`weil_VII_1_cor3_differentiableOn`**: it is holomorphic there.
* **`weil_VII_5_cor3`** (VII.§5 Cor. 3): if $f(v)>1$ for almost all finite $v\notin V$, then
  $q(k,V,s)=\prod_{v\in V}(1-q_v^{-s})^{-1}$ converges for real $s>1$ and $(s-1)q(k,V,s)$ tends to a finite limit
  $>0$ as $s\to1^+$. (Weil lets $s$ be complex with $\operatorname{Re}s>1$; the limit is taken here along real
  $s\to1^+$, which is what Cor. 4 and the text p. 126 use.)
* **`weil_VII_5_text126`** (text p. 126): such a $V$ is infinite: there are infinitely many places of $k$ of
  modular degree $1$ over $k_0$.
* **`weil_VII_5_cor4`** (VII.§5 Cor. 4): if moreover $k'/k$ has degree $n$ and every $v\in V$ has $n$ distinct
  places of $k'$ above it, then $k'=k$ (`Module.finrank K K' = 1`).

Proofs follow Weil: Cor. 2 by grouping the places over each rational prime $p$ (at most $[k:\mathbb Q]$ of them, each
with $q_v\ge p^2$ when $f(v)\ge2$); Cor. 3 of §5 by $\zeta_k(s)=q(k,V,s)\,p(M,s)$ with $M$ the complement of $V$ and the
simple pole of $\zeta_k$; Cor. 4 by $q(k',V',s)=q(k,V,s)^n$.
-/

open IsDedekindDomain NumberField Filter Topology Set
open QuadFormsKB.NFEuler

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {K₀ K : Type} [Field K₀] [NumberField K₀] [Field K] [NumberField K] [Algebra K₀ K]

variable (K₀) in
/-- **Weil's modular degree $f(v)$** of $k_v$ over the closure of $k_0$ in $k_v$ (VII.§1 Cor. 2): the residue degree
of $\mathfrak p_v$ over the prime of $\mathcal O_{k_0}$ below it, so that $q_v=q_u^{f(v)}$. -/
abbrev modDeg (v : HeightOneSpectrum (𝓞 K)) : ℕ := v.asIdeal.inertiaDeg (𝓞 K₀)


/-! ### Auxiliary estimates -/

/-- The constant $a_0=2^{-1/2}<1$ bounding $n^{-\sigma}$ for $n\ge2$, $\sigma\ge1/2$. -/
def a0 : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))

lemma a0_lt_one : a0 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma rpow_neg_le_a0 {n σ : ℝ} (hn : 2 ≤ n) (hσ : 1 / 2 ≤ σ) : n ^ (-σ) ≤ a0 :=
  (Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)).trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))

lemma norm_inv_one_sub_sub_one_le {𝕜 : Type*} [NormedField 𝕜] {z : 𝕜} {a : ℝ} (ha : a < 1)
    (hz : ‖z‖ ≤ a) : ‖(1 - z)⁻¹ - 1‖ ≤ ‖z‖ / (1 - a) := by
  have h1 : 1 - a ≤ ‖(1 : 𝕜) - z‖ := by
    have := norm_sub_norm_le (1 : 𝕜) z
    rw [norm_one] at this
    linarith
  have h2 : (1 : 𝕜) - z ≠ 0 := by
    intro h
    rw [h, norm_zero] at h1
    linarith
  have : (1 - z)⁻¹ - 1 = z / (1 - z) := by field_simp; ring
  rw [this, norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) h1

lemma log_inv_one_sub_bounds {x a : ℝ} (hx0 : 0 ≤ x) (hxa : x ≤ a) (ha : a < 1) :
    0 ≤ Real.log ((1 - x)⁻¹) ∧ Real.log ((1 - x)⁻¹) ≤ x / (1 - a) := by
  have hx1 : x < 1 := by linarith
  have hpos : 0 < (1 - x)⁻¹ := inv_pos.2 (by linarith)
  refine ⟨Real.log_nonneg (one_le_inv₀ (by linarith) |>.2 (by linarith)), ?_⟩
  have h := Real.log_le_sub_one_of_pos hpos
  have h2 := norm_inv_one_sub_sub_one_le (z := x) ha (by rwa [Real.norm_of_nonneg hx0])
  rw [Real.norm_of_nonneg hx0] at h2
  exact h.trans ((le_abs_self _).trans (by rwa [← Real.norm_eq_abs]))

lemma summable_log_term {ι : Type*} (n : ι → ℝ) (hn : ∀ i, 2 ≤ n i) {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (h : Summable fun i => n i ^ (-σ)) : Summable fun i => Real.log ((1 - n i ^ (-σ))⁻¹) := by
  refine Summable.of_nonneg_of_le (fun i => (log_inv_one_sub_bounds (Real.rpow_nonneg (by linarith [hn i]) _)
    (rpow_neg_le_a0 (hn i) hσ) a0_lt_one).1) (fun i => (log_inv_one_sub_bounds
    (Real.rpow_nonneg (by linarith [hn i]) _) (rpow_neg_le_a0 (hn i) hσ) a0_lt_one).2) (h.div_const _)

lemma multipliable_pos_of_summable {ι : Type*} (n : ι → ℝ) (hn : ∀ i, 2 ≤ n i) {σ : ℝ} (hσ : 1 / 2 ≤ σ)
    (h : Summable fun i => n i ^ (-σ)) :
    Multipliable (fun i => (1 - n i ^ (-σ))⁻¹) ∧ 0 < ∏' i, (1 - n i ^ (-σ))⁻¹ := by
  have hpos : ∀ i, 0 < (1 - n i ^ (-σ))⁻¹ := fun i =>
    inv_pos.2 (by linarith [rpow_neg_le_a0 (hn i) hσ, a0_lt_one])
  have hl := summable_log_term n hn hσ h
  refine ⟨Real.multipliable_of_summable_log hpos hl, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hpos hl]
  exact Real.exp_pos _

/-- For $f(v)\ge2$: $q_v\ge p^2$. -/
lemma sq_le_normP {v : HeightOneSpectrum (𝓞 K)} (hv : 2 ≤ modDeg K₀ v) :
    ((primeBelow v : ℕ) : ℝ) ^ 2 ≤ (normP v : ℝ) := by
  set u := v.under (𝓞 K₀)
  haveI := NumberFieldKB.Chebotarev.liesOver_under (F := K₀) K v
  have h := NumberFieldKB.Chebotarev.absNorm_pow_inertiaDeg_eq (F := K₀) K v u
  have hp : primeBelow v = primeBelow u := by
    apply Subtype.ext
    show Ideal.absNorm (Ideal.under ℤ v.asIdeal) = Ideal.absNorm (Ideal.under ℤ u.asIdeal)
    congr 1
    exact (Ideal.under_under (A := ℤ) (B := 𝓞 K₀) v.asIdeal).symm
  have h1 : primeBelow v ≤ normP u := hp ▸ primeBelow_le_normP u
  have h2 : (primeBelow v : ℕ) ^ 2 ≤ normP v := by
    rw [← h]
    exact (Nat.pow_le_pow_left h1 2).trans (Nat.pow_le_pow_right (by have := two_le_normP u; omega) hv)
  exact_mod_cast h2

lemma summable_ge2 {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun v : HeightOneSpectrum (𝓞 K) =>
      if 2 ≤ modDeg K₀ v then (normP v : ℝ) ^ (-σ) else 0) := by
  set n := Module.finrank ℚ K
  have hP : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(2 * σ)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hle : ∀ v : HeightOneSpectrum (𝓞 K), (if 2 ≤ modDeg K₀ v then (normP v : ℝ) ^ (-σ) else 0) ≤
      ((primeBelow v : ℕ) : ℝ) ^ (-(2 * σ)) := by
    intro v
    split_ifs with h
    · have h1 := sq_le_normP (K₀ := K₀) h
      have hp : (0 : ℝ) < ((primeBelow v : ℕ) : ℝ) := by exact_mod_cast (primeBelow v).2.pos
      calc (normP v : ℝ) ^ (-σ) ≤ (((primeBelow v : ℕ) : ℝ) ^ 2) ^ (-σ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
        _ = _ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; congr 1; push_cast; ring
    · positivity
  have hnn : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ (if 2 ≤ modDeg K₀ v then (normP v : ℝ) ^ (-σ) else 0) :=
    fun v => by split_ifs <;> positivity
  refine summable_of_sum_le (c := n * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(2 * σ))) hnn fun u => ?_
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := primeBelow) (t := u.image primeBelow)
    (fun v hv => Finset.mem_image_of_mem _ hv)]
  have hfib : ∀ p ∈ u.image primeBelow,
      ∑ v ∈ u with primeBelow v = p, (if 2 ≤ modDeg K₀ v then (normP v : ℝ) ^ (-σ) else 0) ≤
        n * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    intro p _
    calc _ ≤ ∑ v ∈ u with primeBelow v = p, ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
          refine Finset.sum_le_sum fun v hv => ?_
          have := hle v
          rwa [(Finset.mem_filter.mp hv).2] at this
      _ = (u.filter (primeBelow · = p)).card * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast card_le_finrank p _ fun v hv => (Finset.mem_filter.mp hv).2
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact hP.sum_le_tsum _ fun p _ => by positivity

lemma norm_term_le {v : HeightOneSpectrum (𝓞 K)} (θ s : ℂ) (hθ : ‖θ‖ ≤ 1) :
    ‖θ * (normP v : ℂ) ^ (-s)‖ ≤ (normP v : ℝ) ^ (-s.re) := by
  have hpos : 0 < normP v := lt_of_lt_of_le (by norm_num) (two_le_normP v)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  calc ‖θ‖ * (normP v : ℝ) ^ (-s.re) ≤ 1 * (normP v : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hθ (by positivity)
    _ = _ := one_mul _

/-- **Weil VII.§1 Cor. 2 (series form).** If $M$ is a set of finite places of $k$ such that $f(v)>1$ for almost all
$v\in M$, then $\sum_{v\in M}q_v^{-\sigma}$ converges for $\sigma>1/2$. -/
@[kb "weil1973bnt" "Ch. VII, §1, Cor. 2 of Prop. 1 (p. 104)"]
theorem weil_VII_1_cor2 (M : Set (HeightOneSpectrum (𝓞 K)))
    (hM : {v ∈ M | modDeg K₀ v ≤ 1}.Finite) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable fun v : M => (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-σ) := by
  have hg := summable_ge2 (K₀ := K₀) (K := K) hσ
  set F0 : Set (HeightOneSpectrum (𝓞 K)) := {v ∈ M | modDeg K₀ v ≤ 1}
  have h0 : Summable (F0.indicator fun v : HeightOneSpectrum (𝓞 K) => (normP v : ℝ) ^ (-σ)) :=
    summable_of_ne_finset_zero (s := hM.toFinset) (fun v hv => indicator_of_notMem (fun h => hv (hM.mem_toFinset.2 h)) _)
  have hind : Summable (M.indicator fun v : HeightOneSpectrum (𝓞 K) => (normP v : ℝ) ^ (-σ)) := by
    refine Summable.of_nonneg_of_le (fun v => indicator_nonneg (fun _ _ => by positivity) v)
      (fun v => ?_) (hg.add h0)
    have hn0 : 0 ≤ F0.indicator (fun v : HeightOneSpectrum (𝓞 K) => (normP v : ℝ) ^ (-σ)) v :=
      indicator_nonneg (fun _ _ => by positivity) v
    have hn1 : 0 ≤ (if 2 ≤ modDeg K₀ v then (normP v : ℝ) ^ (-σ) else 0) := by
      split_ifs <;> positivity
    by_cases hvM : v ∈ M
    · rw [indicator_of_mem hvM]
      by_cases h2 : 2 ≤ modDeg K₀ v
      · simp only [h2, if_true, Pi.add_apply]; linarith
      · have hv1 : v ∈ F0 := ⟨hvM, by omega⟩
        simp only [h2, if_false, Pi.add_apply, indicator_of_mem hv1]; linarith
    · rw [indicator_of_notMem hvM]; simpa using add_nonneg hn1 hn0
  exact (summable_subtype_iff_indicator (s := M)).2 hind

/-- **Weil VII.§1 Cor. 2.** For $M$ as in `weil_VII_1_cor2`, the product
$p(M,\sigma)=\prod_{v\in M}(1-q_v^{-\sigma})^{-1}$ converges (unconditionally, to a positive limit) for
$\sigma>1/2$. -/
@[kb "weil1973bnt" "Ch. VII, §1, Cor. 2 of Prop. 1 (p. 104)"]
theorem weil_VII_1_cor2_multipliable (M : Set (HeightOneSpectrum (𝓞 K)))
    (hM : {v ∈ M | modDeg K₀ v ≤ 1}.Finite) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Multipliable (fun v : M => (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-σ))⁻¹) ∧
      0 < ∏' v : M, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-σ))⁻¹ := by
  exact multipliable_pos_of_summable (fun v : M => (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ))
    (fun v => by exact_mod_cast two_le_normP _) hσ.le (weil_VII_1_cor2 M hM hσ)

/-- **Weil VII.§1 Cor. 3.** For $M$ as in Cor. 2 and complex $\theta_v$ with $\lvert\theta_v\rvert\le1$, the product
$\prod_{v\in M}(1-\theta_vq_v^{-s})^{-1}$ converges absolutely and is nonzero for $\operatorname{Re}s>1/2$. -/
@[kb "weil1973bnt" "Ch. VII, §1, Cor. 3 of Prop. 1 (p. 104)"]
theorem weil_VII_1_cor3 (M : Set (HeightOneSpectrum (𝓞 K)))
    (hM : {v ∈ M | modDeg K₀ v ≤ 1}.Finite) (θ : M → ℂ) (hθ : ∀ v, ‖θ v‖ ≤ 1)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun v : M => ‖θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s)‖) ∧
    Multipliable (fun v : M => (1 - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s))⁻¹) ∧
      ∏' v : M, (1 - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  have hσ := weil_VII_1_cor2 M hM hs
  have hb : ∀ v : M, ‖θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s)‖ ≤
      (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s.re) := fun v => norm_term_le _ _ (hθ v)
  have hsum : Summable (fun v : M => ‖θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s)‖) :=
    Summable.of_nonneg_of_le (fun v => norm_nonneg _) hb (by simpa using hσ)
  have hlt : ∀ v : M, ‖θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s)‖ ≤ a0 := fun v =>
    (hb v).trans (rpow_neg_le_a0 (by exact_mod_cast two_le_normP _) hs.le)
  have hf : Summable (fun v : M => ‖(1 - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s))⁻¹ - 1‖) :=
    Summable.of_nonneg_of_le (fun v => norm_nonneg _)
      (fun v => norm_inv_one_sub_sub_one_le a0_lt_one (hlt v)) (hsum.div_const _)
  have heq : (fun v : M => (1 - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s))⁻¹) =
      fun v => 1 + ((1 - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s))⁻¹ - 1) := by
    funext v; ring
  refine ⟨hsum, ?_, ?_⟩
  · rw [heq]; exact multipliable_one_add_of_summable hf
  · rw [heq]
    refine tprod_one_add_ne_zero_of_summable (fun v => ?_) hf
    have : (1 : ℂ) - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s) ≠ 0 := by
      intro h
      have := hlt v
      have h1 : θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s) = 1 := by linear_combination -h
      rw [h1, norm_one] at this
      linarith [a0_lt_one]
    simpa using this

/-- **Weil VII.§1 Cor. 3 (holomorphy).** The product of Cor. 3 is holomorphic in $\operatorname{Re}s>1/2$. -/
@[kb "weil1973bnt" "Ch. VII, §1, Cor. 3 of Prop. 1 (p. 104)"]
theorem weil_VII_1_cor3_differentiableOn (M : Set (HeightOneSpectrum (𝓞 K)))
    (hM : {v ∈ M | modDeg K₀ v ≤ 1}.Finite) (θ : M → ℂ) (hθ : ∀ v, ‖θ v‖ ≤ 1) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∏' v : M, (1 - θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s))⁻¹)
      {s : ℂ | 1 / 2 < s.re} := by
  set U : Set ℂ := {s | 1 / 2 < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let z : M → ℂ → ℂ := fun v s => θ v * (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ^ (-s)
  let f : M → ℂ → ℂ := fun v s => (1 - z v s)⁻¹ - 1
  have hn0 : ∀ v : M, (normP (v : HeightOneSpectrum (𝓞 K)) : ℂ) ≠ 0 := fun v => by
    have := two_le_normP (v : HeightOneSpectrum (𝓞 K)); exact_mod_cast (by omega : normP (v : HeightOneSpectrum (𝓞 K)) ≠ 0)
  have hz : ∀ v, Differentiable ℂ (z v) := fun v =>
    (differentiable_const _).mul (differentiable_neg.const_cpow (Or.inl (hn0 v)))
  have hzle : ∀ v : M, ∀ s ∈ U, ‖z v s‖ ≤ a0 := fun v s hs =>
    (norm_term_le (v := (v : HeightOneSpectrum (𝓞 K))) (θ v) s (hθ v)).trans
      (rpow_neg_le_a0 (by exact_mod_cast two_le_normP _) hs.le)
  have hne : ∀ v : M, ∀ s ∈ U, 1 - z v s ≠ 0 := by
    intro v s hs h
    have := hzle v s hs
    have h1 : z v s = 1 := by linear_combination -h
    rw [h1, norm_one] at this
    linarith [a0_lt_one]
  have hfd : ∀ v : M, DifferentiableOn ℂ (fun s => 1 + f v s) U := fun v =>
    ((differentiable_const _).sub (hz v)).differentiableOn.inv (hne v) |>.sub_const 1 |>.const_add 1
  have hlim : HasProdLocallyUniformlyOn (fun (v : M) s => 1 + f v s) (fun s => ∏' v : M, (1 + f v s)) U := by
    refine hasProdLocallyUniformlyOn_of_forall_compact hU fun S hS hC => ?_
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using tendstoUniformlyOn_empty
    obtain ⟨s0, hs0, hmin⟩ := hC.exists_isMinOn hSne Complex.continuous_re.continuousOn
    have hσ : 1 / 2 < s0.re := hS hs0
    have hsum := (weil_VII_1_cor2 (K₀ := K₀) M hM hσ).div_const (1 - a0)
    refine Summable.hasProdUniformlyOn_one_add (f := f) hC hsum (Filter.Eventually.of_forall fun v s hs => ?_)
      (fun v => ?_)
    · have hsU := hS hs
      have h1 := norm_inv_one_sub_sub_one_le a0_lt_one (hzle v s hsU)
      have h2 : ‖z v s‖ ≤ (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s0.re) :=
        (norm_term_le (v := (v : HeightOneSpectrum (𝓞 K))) (θ v) s (hθ v)).trans
          (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by have := two_le_normP (v : HeightOneSpectrum (𝓞 K)); omega))
            (by have := hmin hs; simp only [Set.mem_setOf_eq] at this; linarith))
      exact h1.trans (div_le_div_of_nonneg_right h2 (by linarith [a0_lt_one]))
    · exact ((hfd v).sub_const 1 |>.congr (fun s _ => by simp)).continuousOn.mono hS
  have hd := hlim.differentiableOn
    (Filter.Eventually.of_forall fun t => DifferentiableOn.fun_finsetProd (fun v _ => hfd v)) hU
  refine hd.congr fun s _ => ?_
  simp only [f]
  congr 1
  funext v
  ring

/-! ### Auxiliary results for §5 -/

lemma modDeg_pos (v : HeightOneSpectrum (𝓞 K)) : 1 ≤ modDeg K₀ v := by
  haveI := v.isPrime
  exact Ideal.inertiaDeg_pos v.asIdeal (𝓞 K₀)

lemma multipliable_pos_subtype (W : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Multipliable (fun v : W => (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹) ∧
      0 < ∏' v : W, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹ :=
  multipliable_pos_of_summable (fun v : W => (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ))
    (fun v => by exact_mod_cast two_le_normP _) (by linarith) ((summable_normP_rpow hs).subtype W)

lemma zetaR_eq_split (V : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    dedekindZetaR K s = (∏' v : V, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹) *
      ∏' v : (Vᶜ : Set (HeightOneSpectrum (𝓞 K))),
        (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹ := by
  have h1 := (multipliable_pos_subtype V hs).1.hasProd
  have h2 := (multipliable_pos_subtype Vᶜ hs).1.hasProd
  exact (hasProd_dedekindZeta hs).unique
    (HasProd.mul_compl (f := fun v : HeightOneSpectrum (𝓞 K) => (1 - (normP v : ℝ) ^ (-s))⁻¹) h1 h2)

lemma tendsto_sub_one_mul_zetaR :
    Tendsto (fun s : ℝ => (s - 1) * dedekindZetaR K s) (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  refine h.congr fun s => ?_
  simp [dedekindZetaR, Complex.mul_re]

lemma continuous_rpow_neg (n : ℝ) (hn : 0 < n) : Continuous fun s : ℝ => n ^ (-s) :=
  Continuous.rpow continuous_const continuous_neg (fun _ => Or.inl hn.ne')

lemma tendsto_tprod_of_finite (W : Set (HeightOneSpectrum (𝓞 K)))
    (hW : {v | v ∈ W ∧ modDeg K₀ v ≤ 1}.Finite) :
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun s : ℝ => ∏' v : W, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹)
      (𝓝[>] 1) (𝓝 c) := by
  have hq2 : ∀ v : W, (2 : ℝ) ≤ (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) := fun v => by
    exact_mod_cast two_le_normP _
  let ℓ : ℝ → W → ℝ := fun s v => Real.log ((1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹)
  have hcont : ∀ v : W, ContinuousOn (fun s => ℓ s v) (Set.Ici (3 / 4)) := by
    intro v
    have hc := continuous_rpow_neg (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) (by linarith [hq2 v])
    refine ContinuousOn.log (ContinuousOn.inv₀ (continuousOn_const.sub hc.continuousOn) fun s hs => ?_) ?_
    · have := rpow_neg_le_a0 (hq2 v) (show (1 / 2 : ℝ) ≤ s by have := hs.out; linarith)
      linarith [a0_lt_one]
    · intro s hs
      have := rpow_neg_le_a0 (hq2 v) (show (1 / 2 : ℝ) ≤ s by have := hs.out; linarith)
      have : 0 < 1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s) := by linarith [a0_lt_one]
      exact (inv_pos.2 this).ne'
  have hsum34 : Summable fun v : W => (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-(3 / 4 : ℝ)) :=
    weil_VII_1_cor2 (K₀ := K₀) W hW (by norm_num)
  have hL : ContinuousOn (fun s => ∑' v : W, ℓ s v) (Set.Ici (3 / 4)) := by
    refine continuousOn_tsum hcont (hsum34.div_const (1 - a0)) fun v s hs => ?_
    have hs' : (3 / 4 : ℝ) ≤ s := hs.out
    have hx0 : 0 ≤ (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s) := by positivity
    have hb := log_inv_one_sub_bounds hx0 (rpow_neg_le_a0 (hq2 v) (by linarith)) a0_lt_one
    rw [Real.norm_of_nonneg hb.1]
    refine hb.2.trans (div_le_div_of_nonneg_right ?_ (by linarith [a0_lt_one]))
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hq2 v]) (by linarith)
  have hpos : ∀ s : ℝ, 3 / 4 ≤ s → ∀ v : W,
      0 < (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹ := fun s hs v =>
    inv_pos.2 (by linarith [rpow_neg_le_a0 (hq2 v) (show (1 / 2 : ℝ) ≤ s by linarith), a0_lt_one])
  have hQ : ∀ s : ℝ, 3 / 4 ≤ s →
      ∏' v : W, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹ =
        Real.exp (∑' v : W, ℓ s v) := fun s hs =>
    (Real.rexp_tsum_eq_tprod (hpos s hs) (summable_log_term _ hq2 (by linarith)
      (weil_VII_1_cor2 (K₀ := K₀) W hW (by linarith)))).symm
  refine ⟨Real.exp (∑' v : W, ℓ 1 v), Real.exp_pos _, ?_⟩
  have h1 : Tendsto (fun s : ℝ => ∑' v : W, ℓ s v) (𝓝[>] 1) (𝓝 (∑' v : W, ℓ 1 v)) :=
    ((hL 1 (by norm_num)).mono (fun s (hs : 1 < s) => (show (3 / 4 : ℝ) ≤ s by linarith)))
  have h2 := (Real.continuous_exp.tendsto _).comp h1
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  exact (hQ s (by linarith)).symm

/-- **Weil VII.§5 Cor. 3.** Let $V$ be a set of finite places of $k$ such that $f(v)>1$ for almost all finite places
$v\notin V$. Then $q(k,V,s)=\prod_{v\in V}(1-q_v^{-s})^{-1}$ converges for real $s>1$, and $(s-1)q(k,V,s)$ tends to a
finite limit $c>0$ as $s\to1^+$. -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 3 of Thm. 2 (p. 126)"]
theorem weil_VII_5_cor3 (V : Set (HeightOneSpectrum (𝓞 K)))
    (hV : {v | v ∉ V ∧ modDeg K₀ v ≤ 1}.Finite) :
    (∀ s : ℝ, 1 < s →
      Multipliable (fun v : V => (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹)) ∧
    ∃ c : ℝ, 0 < c ∧ Tendsto
      (fun s : ℝ => (s - 1) * ∏' v : V, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹)
      (𝓝[>] 1) (𝓝 c) := by
  refine ⟨fun s hs => (multipliable_pos_subtype V hs).1, ?_⟩
  obtain ⟨c0, hc0, hQ⟩ := tendsto_tprod_of_finite (K₀ := K₀) Vᶜ hV
  refine ⟨dedekindZeta_residue K / c0, div_pos (dedekindZeta_residue_pos K) hc0, ?_⟩
  refine ((tendsto_sub_one_mul_zetaR (K := K)).div hQ hc0.ne').congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : (1 : ℝ) < s := hs
  have hQpos := (multipliable_pos_subtype Vᶜ hs').2
  simp only [Pi.div_apply]
  rw [zetaR_eq_split V hs', mul_div_assoc, mul_div_cancel_right₀ _ hQpos.ne']

/-- **Weil VII.§5, text p. 126.** A set $V$ as in Cor. 3 is infinite; in particular ($V$ the places of modular
degree $1$) there are infinitely many places of $k$ of modular degree $1$ over $k_0$. -/
@[kb "weil1973bnt" "Ch. VII, §5, text p. 126"]
theorem weil_VII_5_text126 (V : Set (HeightOneSpectrum (𝓞 K)))
    (hV : {v | v ∉ V ∧ modDeg K₀ v ≤ 1}.Finite) : V.Infinite := by
  intro hfin
  obtain ⟨-, c, hc, hlim⟩ := weil_VII_5_cor3 (K₀ := K₀) V hV
  haveI := hfin.fintype
  have hq2 : ∀ v : V, (2 : ℝ) ≤ (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) := fun v => by
    exact_mod_cast two_le_normP _
  have hP : Tendsto (fun s : ℝ => ∏ v : V, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹)
      (𝓝[>] 1) (𝓝 (∏ v : V, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-(1 : ℝ)))⁻¹)) := by
    refine tendsto_finset_prod _ fun v _ => ?_
    have hc := continuous_rpow_neg (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) (by linarith [hq2 v])
    have hne : 1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-(1 : ℝ)) ≠ 0 := by
      have := rpow_neg_le_a0 (hq2 v) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      linarith [a0_lt_one]
    exact ((continuous_const.sub hc).continuousAt.inv₀ hne).tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (by
        have h : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub tendsto_const_nhds
        simpa using h)
  have h0 := hs.mul hP
  simp only [zero_mul] at h0
  refine hc.ne' (tendsto_nhds_unique hlim (h0.congr fun s => ?_))
  rw [tprod_fintype]

variable (K₀ K) in
/-- **Weil VII.§5, text p. 126 (degree-one places).** There are infinitely many finite places of $k$ of modular
degree $1$ over $k_0$. -/
@[kb "weil1973bnt" "Ch. VII, §5, text p. 126"]
theorem infinite_modDeg_eq_one : {v : HeightOneSpectrum (𝓞 K) | modDeg K₀ v = 1}.Infinite := by
  refine weil_VII_5_text126 (K₀ := K₀) {v : HeightOneSpectrum (𝓞 K) | modDeg K₀ v = 1} ?_
  refine Set.finite_empty.subset fun v hv => ?_
  have := modDeg_pos (K₀ := K₀) v
  have h2 := hv.2
  exact hv.1 (by simp only [Set.mem_ofPred_eq]; omega)

/-! ### Auxiliary results for Cor. 4 -/

lemma tprod_eq_exp_tsum_log {E : Type} [Field E] [NumberField E] (W : Set (HeightOneSpectrum (𝓞 E)))
    {s : ℝ} (hs : 1 < s) :
    ∏' v : W, (1 - (normP (v : HeightOneSpectrum (𝓞 E)) : ℝ) ^ (-s))⁻¹ =
      Real.exp (∑' v : W, Real.log ((1 - (normP (v : HeightOneSpectrum (𝓞 E)) : ℝ) ^ (-s))⁻¹)) := by
  have hq2 : ∀ v : W, (2 : ℝ) ≤ (normP (v : HeightOneSpectrum (𝓞 E)) : ℝ) := fun v => by
    exact_mod_cast two_le_normP _
  have hpos : ∀ v : W, 0 < (1 - (normP (v : HeightOneSpectrum (𝓞 E)) : ℝ) ^ (-s))⁻¹ := fun v =>
    inv_pos.2 (by linarith [rpow_neg_le_a0 (hq2 v) (show (1 / 2 : ℝ) ≤ s by linarith), a0_lt_one])
  exact (Real.rexp_tsum_eq_tprod hpos (summable_log_term _ hq2 (by linarith)
    ((summable_normP_rpow hs).subtype W))).symm

section Cor4

variable {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K₀ K'] [IsScalarTower K₀ K K']

lemma inertiaDeg_eq_one_of_split (v : HeightOneSpectrum (𝓞 K))
    (hsplit : (v.asIdeal.primesOver (𝓞 K')).ncard = Module.finrank K K')
    (w : HeightOneSpectrum (𝓞 K')) (hw : w.under (𝓞 K) = v) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  haveI := v.isPrime
  haveI : Fintype (v.asIdeal.primesOver (𝓞 K')) :=
    (Algebra.QuasiFinite.finite_primesOver (R := 𝓞 K) (S := 𝓞 K') v.asIdeal).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 K')
  rw [← IsFractionRing.finrank_eq (𝓞 K) K (𝓞 K') K'] at hsum
  have hcard : Fintype.card (v.asIdeal.primesOver (𝓞 K')) = Module.finrank K K' := by
    rw [← hsplit, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  have hge : ∀ q ∈ (Finset.univ : Finset (v.asIdeal.primesOver (𝓞 K'))),
      1 ≤ q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) := by
    intro q _
    haveI := q.2.1
    have h1 : 0 < q.1.ramificationIdx (𝓞 K) := Ideal.ramificationIdx_pos (q := q.1) (R := 𝓞 K)
    have h2 : 0 < q.1.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos q.1 (𝓞 K)
    exact Nat.mul_pos h1 h2
  have heq : ∑ q : v.asIdeal.primesOver (𝓞 K'), 1 =
      ∑ q : v.asIdeal.primesOver (𝓞 K'), q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K) := by
    rw [hsum, ← hcard]; simp
  have hall := (Finset.sum_eq_sum_iff_of_le hge).1 heq
  have hmem : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 K') :=
    ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩
  have := hall ⟨w.asIdeal, hmem⟩ (Finset.mem_univ _)
  exact (mul_eq_one.1 this.symm).2

lemma normP_eq_of_split (V : Set (HeightOneSpectrum (𝓞 K)))
    (hsplit : ∀ v ∈ V, (v.asIdeal.primesOver (𝓞 K')).ncard = Module.finrank K K')
    (w : HeightOneSpectrum (𝓞 K')) (hw : w.under (𝓞 K) ∈ V) :
    normP w = normP (w.under (𝓞 K)) := by
  haveI := NumberFieldKB.Chebotarev.liesOver_under (F := K) K' w
  have h := NumberFieldKB.Chebotarev.absNorm_pow_inertiaDeg_eq (F := K) K' w (w.under (𝓞 K))
  rw [inertiaDeg_eq_one_of_split _ (hsplit _ hw) w rfl, pow_one] at h
  exact h.symm

lemma tprod_fibre (V : Set (HeightOneSpectrum (𝓞 K)))
    (hsplit : ∀ v ∈ V, (v.asIdeal.primesOver (𝓞 K')).ncard = Module.finrank K K') {s : ℝ} (hs : 1 < s) :
    ∏' w : {w : HeightOneSpectrum (𝓞 K') | w.under (𝓞 K) ∈ V},
        (1 - (normP (w : HeightOneSpectrum (𝓞 K')) : ℝ) ^ (-s))⁻¹ =
      (∏' v : V, (1 - (normP (v : HeightOneSpectrum (𝓞 K)) : ℝ) ^ (-s))⁻¹) ^ Module.finrank K K' := by
  set V' : Set (HeightOneSpectrum (𝓞 K')) := {w | w.under (𝓞 K) ∈ V} with hV'
  set n := Module.finrank K K'
  rw [tprod_eq_exp_tsum_log V' hs, tprod_eq_exp_tsum_log V hs, ← Real.exp_nat_mul]
  congr 1
  let ℓK : HeightOneSpectrum (𝓞 K) → ℝ := fun v => Real.log ((1 - (normP v : ℝ) ^ (-s))⁻¹)
  let ℓK' : HeightOneSpectrum (𝓞 K') → ℝ := fun v => Real.log ((1 - (normP v : ℝ) ^ (-s))⁻¹)
  have hq2 : ∀ v : V', (2 : ℝ) ≤ (normP (v : HeightOneSpectrum (𝓞 K')) : ℝ) := fun v => by
    exact_mod_cast two_le_normP _
  have hsumV' : Summable (V'.indicator ℓK') :=
    (summable_subtype_iff_indicator (s := V')).1
      (summable_log_term _ hq2 (by linarith) ((summable_normP_rpow hs).subtype V'))
  show ∑' w : V', ℓK' w = n * ∑' v : V, ℓK v
  rw [tsum_subtype V' ℓK', tsum_subtype V ℓK, ← tsum_mul_left,
    NumberFieldKB.Chebotarev.tsum_eq_tsum_fibre (F := K) K' _ hsumV']
  refine tsum_congr fun 𝔭 => ?_
  rw [NumberFieldKB.Chebotarev.tsum_fibre_eq_card_mul K' 𝔭 V' ℓK' (ℓK 𝔭)]
  · by_cases h𝔭 : 𝔭 ∈ V
    · have hset : {P ∈ V' | P.asIdeal.LiesOver 𝔭.asIdeal} =
          {P : HeightOneSpectrum (𝓞 K') | P.asIdeal.LiesOver 𝔭.asIdeal} := by
        ext P
        simp only [Set.mem_ofPred_eq]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        have : P.under (𝓞 K) = 𝔭 :=
          HeightOneSpectrum.ext (by simpa using ((Ideal.liesOver_iff _ _).1 h).symm)
        show P.under (𝓞 K) ∈ V
        rw [this]; exact h𝔭
      rw [hset, NumberFieldKB.Chebotarev.ncard_fibre_eq, hsplit 𝔭 h𝔭, indicator_of_mem h𝔭]
    · have hset : {P ∈ V' | P.asIdeal.LiesOver 𝔭.asIdeal} = ∅ := by
        ext P
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        have : P.under (𝓞 K) = 𝔭 :=
          HeightOneSpectrum.ext (by simpa using ((Ideal.liesOver_iff _ _).1 h2).symm)
        exact h𝔭 (this ▸ h1)
      rw [hset, indicator_of_notMem h𝔭]; simp
  · intro P hP hPp
    show Real.log _ = Real.log _
    rw [normP_eq_of_split V hsplit P hP, hPp]

end Cor4

/-- **Weil VII.§5 Cor. 4.** Let $V$ be as in Cor. 3 and $k'/k$ an extension of degree $n$ such that every $v\in V$
has $n$ distinct places of $k'$ above it. Then $k'=k$, i.e. $n=1$. ($k'/k$ is separable since the characteristic
is $0$.) -/
@[kb "weil1973bnt" "Ch. VII, §5, Cor. 4 of Thm. 2 (p. 126)"]
theorem weil_VII_5_cor4 {K' : Type} [Field K'] [NumberField K'] [Algebra K K'] [Algebra K₀ K']
    [IsScalarTower K₀ K K'] (V : Set (HeightOneSpectrum (𝓞 K)))
    (hV : {v | v ∉ V ∧ modDeg K₀ v ≤ 1}.Finite)
    (hsplit : ∀ v ∈ V, (v.asIdeal.primesOver (𝓞 K')).ncard = Module.finrank K K') :
    Module.finrank K K' = 1 := by
  set n := Module.finrank K K' with hn
  have hn0 : 0 < n := Module.finrank_pos
  by_contra hne
  have hn2 : 2 ≤ n := by omega
  set V' : Set (HeightOneSpectrum (𝓞 K')) := {w | w.under (𝓞 K) ∈ V} with hV'def
  have hfib : ∀ v : HeightOneSpectrum (𝓞 K),
      {w : HeightOneSpectrum (𝓞 K') | w.under (𝓞 K) = v}.Finite := by
    intro v
    haveI := v.isPrime
    have hf : (v.asIdeal.primesOver (𝓞 K')).Finite :=
      Algebra.QuasiFinite.finite_primesOver (R := 𝓞 K) (S := 𝓞 K') v.asIdeal
    refine Set.Finite.of_injOn (f := HeightOneSpectrum.asIdeal) (fun w hw => ?_)
      (fun _ _ _ _ h => HeightOneSpectrum.ext h) hf
    exact ⟨w.isPrime, ⟨by rw [← (show w.under (𝓞 K) = v from hw)]; rfl⟩⟩
  have hV' : {w : HeightOneSpectrum (𝓞 K') | w ∉ V' ∧ modDeg K₀ w ≤ 1}.Finite := by
    refine (hV.biUnion fun v _ => hfib v).subset fun w hw => ?_
    simp only [Set.mem_iUnion]
    refine ⟨w.under (𝓞 K), ⟨hw.1, ?_⟩, rfl⟩
    haveI := NumberFieldKB.Chebotarev.liesOver_under (F := K) K' w
    have h1 := Ideal.inertiaDeg_tower (R := 𝓞 K₀) (S := 𝓞 K) (T := 𝓞 K')
      (w.under (𝓞 K)).asIdeal w.asIdeal
    have h2 : 0 < w.asIdeal.inertiaDeg (𝓞 K) := by
      haveI := w.isPrime
      exact Ideal.inertiaDeg_pos w.asIdeal (𝓞 K)
    have h3 : modDeg K₀ (w.under (𝓞 K)) ≤ modDeg K₀ w := by
      show (w.under (𝓞 K)).asIdeal.inertiaDeg (𝓞 K₀) ≤ w.asIdeal.inertiaDeg (𝓞 K₀)
      rw [h1]; exact Nat.le_mul_of_pos_right _ h2
    exact h3.trans hw.2
  obtain ⟨-, c, hc, hlim⟩ := weil_VII_5_cor3 (K₀ := K₀) V hV
  obtain ⟨-, c', hc', hlim'⟩ := weil_VII_5_cor3 (K₀ := K₀) V' hV'
  have hs0 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (by
      have h : Tendsto (fun s : ℝ => s - 1) (𝓝 1) (𝓝 (1 - 1)) := tendsto_id.sub tendsto_const_nhds
      simpa using h)
  have h1 := ((hs0.pow (n - 1)).mul hlim')
  rw [zero_pow (by omega), zero_mul] at h1
  have h2 := hlim.pow n
  have h3 : c ^ n = 0 := by
    refine tendsto_nhds_unique h2 (h1.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (1 : ℝ) < s := hs
    have := tprod_fibre (K' := K') V hsplit hs'
    simp only [V', hV'def] at *
    rw [this, mul_pow, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
  exact (pow_pos hc n).ne' h3

end NumberFieldKB.WeilBNT
