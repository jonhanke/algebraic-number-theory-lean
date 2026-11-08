import NumberFieldKB.MilneCFT.Ch5RayClassOrder
import NumberFieldKB.MilneANT.Ch8
import NumberFieldKB.HeckeL.DedekindCont

/-!
# $L$-series and the density of primes in arithmetic progressions (Milne, *Class Field Theory*, Chapter V, §2)

* **Theorem 2.1** (`theorem_2_1a`, `theorem_2_1b_ne_zero`, and the convergence statement `Theorem2_1b`): the Riemann
  zeta function and Dirichlet $L$-series (Mathlib);
* Dirichlet density (p. 155): `NumberField`-wide notion `Set.HasDirichletDensity` of this library;
* **Theorem 2.2** (`theorem_2_2`) and **Corollary 2.3** (`cor_2_3`, with the splitting criterion
  `mem_splitPrimes_cyclotomic_iff`), proved from the Chebotarev density theorem;
* Weber characters and their $L$-series (p. 155): the Introduction's `weberLSeries`; **Theorem 2.4** (a)
  (`theorem_2_4a`, the library's continuation of $\zeta_K$ with Mathlib's residue) and (b) (named, `Theorem2_4b`);
* **Theorem 2.5** (`theorem_2_5`, in `Ch5Density.lean`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev Filter Topology
open NumberField.InfinitePlace NumberField.Units
open scoped nonZeroDivisors

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT

/-! ## Theorem 2.1 -/

/-- **Theorem 2.1(a)** (Milne, *CFT*, V, p. 154): the Riemann zeta function extends to a meromorphic function on
$\mathrm{Re}(s) > 0$ with $\zeta(s) = \frac1{s-1} + \varphi(s)$, $\varphi$ holomorphic on $\mathrm{Re}(s) > 0$ (Mathlib's
`riemannZeta`, entire away from $1$, with `tendsto_riemannZeta_sub_one_div`). -/
@[kb "milne2020cft" "Ch. V, Theorem 2.1(a)"]
theorem theorem_2_1a : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ {s | 0 < s.re} ∧
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → riemannZeta s = 1 / (s - 1) + φ s := by
  set f : ℂ → ℂ := fun s => riemannZeta s - 1 / (s - 1) with hf
  refine ⟨Function.update f 1 (Real.eulerMascheroniConstant : ℂ), ?_, ?_⟩
  · have h : DifferentiableOn ℂ (Function.update f 1 (Real.eulerMascheroniConstant : ℂ)) Set.univ := by
      refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem).mp
        ⟨?_, ?_⟩
      · intro s hs
        have hs1 : s ≠ 1 := hs.2
        have : DifferentiableAt ℂ f s :=
          (differentiableAt_riemannZeta hs1).sub
            ((differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
              (sub_ne_zero.mpr hs1))
        refine DifferentiableAt.differentiableWithinAt ?_
        refine this.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with t ht
        exact Function.update_of_ne ht _ _
      · exact continuousAt_update_same.mpr tendsto_riemannZeta_sub_one_div
    exact h.mono (Set.subset_univ _)
  · intro s _ hs
    simp [hf, Function.update_of_ne hs]

/-- **Theorem 2.1(b), nonvanishing** (Milne, *CFT*, V, p. 154; Mathlib's
`DirichletCharacter.LFunction_apply_one_ne_zero`): for a nontrivial Dirichlet character $\chi$, $L(1,\chi) \ne 0$. -/
@[kb "milne2020cft" "Ch. V, Theorem 2.1(b) (L(1, χ) ≠ 0)"]
theorem theorem_2_1b_ne_zero {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) :
    χ.LFunction 1 ≠ 0 :=
  DirichletCharacter.LFunction_apply_one_ne_zero hχ

/-- Helper: consecutive terms of $n^{-s}$ differ by at most $|s|\,n^{-\mathrm{Re}(s)-1}$ for $\mathrm{Re}(s) > 0$. -/
theorem norm_natCast_cpow_neg_sub_le (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun y : ℝ => (y : ℂ) ^ (-s)) (f' := fun y : ℝ => (-s) * (y : ℂ) ^ (-s - 1))
    (s := Set.Icc (n : ℝ) (n + 1)) (C := ‖s‖ * (n : ℝ) ^ (-s.re - 1))
    (fun y hy => by
      have hy0 : y ≠ 0 := (lt_of_lt_of_le hn' hy.1).ne'
      exact (hasDerivAt_ofReal_cpow_const hy0 (neg_ne_zero.mpr hs0)).hasDerivWithinAt)
    (fun y hy => by
      have hy0 : 0 < y := lt_of_lt_of_le hn' hy.1
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      exact Real.rpow_le_rpow_of_nonpos hn' hy.1 (by linarith))
    (convex_Icc _ _) (x := (n : ℝ)) (y := (n : ℝ) + 1)
    (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  simp only [add_sub_cancel_left, norm_one, mul_one] at key
  rw [norm_sub_rev]
  simpa using key

/-- Helper: the sum of a nontrivial Dirichlet character over any `m` consecutive integers vanishes. -/
theorem sum_range_add_dirichletCharacter {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) (N : ℕ) :
    ∑ x ∈ Finset.range m, χ ((N + x : ℕ) : ZMod m) = 0 := by
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  refine Finset.sum_bij (fun x _ => ((N + x : ℕ) : ZMod m)) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro x hx y hy hxy
    have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
    have h2 : x ≡ y [MOD m] := Nat.ModEq.add_left_cancel' N h1
    rw [Finset.mem_range] at hx hy
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  · intro a _
    refine ⟨(a - (N : ZMod m)).val, Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring

/-- Helper: the partial sums of a nontrivial Dirichlet character are bounded by the modulus. -/
theorem norm_sum_range_dirichletCharacter_le {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (N : ℕ) : ‖∑ k ∈ Finset.range N, χ (k : ZMod m)‖ ≤ m := by
  have hper : ∀ q r : ℕ, ∑ k ∈ Finset.range (r + q * m), χ (k : ZMod m) = ∑ k ∈ Finset.range r, χ (k : ZMod m) := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show r + (q + 1) * m = (r + q * m) + m by ring, Finset.sum_range_add,
        sum_range_add_dirichletCharacter χ hχ, add_zero, ih]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have := hper (N / m) (N % m)
  rw [show N % m + N / m * m = N by rw [mul_comm]; exact Nat.mod_add_div N m] at this
  rw [this]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.range (N % m), ‖χ (k : ZMod m)‖ ≤ ∑ k ∈ Finset.range (N % m), (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
    _ = (N % m : ℕ) := by simp
    _ ≤ m := by exact_mod_cast (Nat.mod_lt N hm).le

/-- Helper: the summand of the series obtained from $\sum_n\chi(n)n^{-s}$ by Abel summation. -/
def abelTerm {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ) (i : ℕ) : ℂ :=
  ((i : ℂ) ^ (-s) - ((i + 1 : ℕ) : ℂ) ^ (-s)) * ∑ k ∈ Finset.range (i + 1), χ (k : ZMod m)

/-- Helper: a bound for `abelTerm` which is uniform for $\delta \le \mathrm{Re}(s)$ and $|s| \le R$, and summable. -/
theorem norm_abelTerm_le {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) {δ R : ℝ} (hδ : 0 < δ)
    {s : ℂ} (hs : δ ≤ s.re) (hR : ‖s‖ ≤ R) (i : ℕ) :
    ‖abelTerm χ s i‖ ≤ m * ((if i = 0 then 1 else 0) + R * (i : ℝ) ^ (-δ - 1)) := by
  have hsre : 0 < s.re := lt_of_lt_of_le hδ hs
  have hs0 : s ≠ 0 := fun h => by simp [h] at hsre
  unfold abelTerm
  rw [norm_mul, mul_comm]
  have hS := norm_sum_range_dirichletCharacter_le χ hχ (i + 1)
  refine mul_le_mul hS ?_ (norm_nonneg _) (Nat.cast_nonneg _)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0), Real.zero_rpow (show -δ - 1 ≠ 0 by linarith)]
  · simp only [hi.ne', ite_false, zero_add]
    refine (norm_natCast_cpow_neg_sub_le s hsre i hi).trans ?_
    have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
    exact mul_le_mul hR (Real.rpow_le_rpow_of_exponent_le hi1 (by linarith))
      (Real.rpow_nonneg (by linarith) _) ((norm_nonneg _).trans hR)

/-- Helper: `abelTerm` is summable for $\mathrm{Re}(s) > 0$. -/
theorem summable_abelTerm {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Summable (abelTerm χ s) := by
  refine Summable.of_norm_bounded (g := fun i : ℕ => (m : ℝ) * ((if i = 0 then 1 else 0) + ‖s‖ * (i : ℝ) ^ (-s.re - 1))) ?_
    (fun i => norm_abelTerm_le χ hχ hs le_rfl le_rfl i)
  refine Summable.mul_left _ (Summable.add ?_ (Summable.mul_left _ ?_))
  · exact summable_of_ne_finset_zero (s := {0}) fun i hi => by simp at hi; simp [hi]
  · exact Real.summable_nat_rpow.mpr (by linarith)

/-- Helper: the Abel-summed series is holomorphic on $\mathrm{Re}(s) > 0$. -/
theorem differentiableOn_tsum_abelTerm {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (fun s => ∑' i, abelTerm χ s i) {s : ℂ | 0 < s.re} := by
  intro s0 hs0
  have hs0' : 0 < s0.re := hs0
  set δ := s0.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set U : Set ℂ := {s | δ < s.re ∧ ‖s‖ < ‖s0‖ + 1} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hs0U : s0 ∈ U := ⟨by simp only [hδ]; linarith, by linarith⟩
  have hsum : Summable (fun i : ℕ => (m : ℝ) * ((if i = 0 then 1 else 0) + (‖s0‖ + 1) * (i : ℝ) ^ (-δ - 1))) := by
    refine Summable.mul_left _ (Summable.add ?_ (Summable.mul_left _ ?_))
    · exact summable_of_ne_finset_zero (s := {0}) fun i hi => by simp at hi; simp [hi]
    · exact Real.summable_nat_rpow.mpr (by linarith)
  have hd := Complex.differentiableOn_tsum_of_summable_norm hsum (U := U) (F := fun i s => abelTerm χ s i)
    (fun i s hs => by
      have hsre : 0 < s.re := lt_trans hδ0 hs.1
      have hneg : -s ≠ 0 := neg_ne_zero.mpr (fun h => by simp [h] at hsre)
      refine DifferentiableAt.differentiableWithinAt ?_
      unfold abelTerm
      refine DifferentiableAt.mul (DifferentiableAt.sub ?_ ?_) (differentiableAt_const _)
      · exact DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inr hneg)
      · exact DifferentiableAt.const_cpow differentiableAt_id.neg (Or.inr hneg))
    hUo (fun i s hs => norm_abelTerm_le χ hχ hδ0 hs.1.le hs.2.le i)
  exact (hd.differentiableAt (hUo.mem_nhds hs0U)).differentiableWithinAt

/-- Helper: the partial sums of $\sum_n\chi(n)n^{-s}$ converge, for $\mathrm{Re}(s) > 0$, to the Abel-summed series. -/
theorem tendsto_sum_range_abelTerm {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, χ n * (n : ℂ) ^ (-s)) atTop (𝓝 (∑' i, abelTerm χ s i)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have hid : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), χ (n : ZMod m) * (n : ℂ) ^ (-s) =
      (N : ℂ) ^ (-s) * ∑ k ∈ Finset.range (N + 1), χ (k : ZMod m) + ∑ i ∈ Finset.range N, abelTerm χ s i := by
    intro N
    have := Finset.sum_range_by_parts (fun i : ℕ => (i : ℂ) ^ (-s)) (fun i : ℕ => χ (i : ZMod m)) (N + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at this
    calc _ = ∑ n ∈ Finset.range (N + 1), (n : ℂ) ^ (-s) * χ (n : ZMod m) :=
          Finset.sum_congr rfl fun n _ => mul_comm _ _
      _ = _ := this
      _ = _ := by
        rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold abelTerm
        ring
  refine Tendsto.congr (fun N => (hid N).symm) ?_
  have h1 : Tendsto (fun N : ℕ => (N : ℂ) ^ (-s) * ∑ k ∈ Finset.range (N + 1), χ (k : ZMod m)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun N : ℕ => (m : ℝ) * (N : ℝ) ^ (-s.re)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN, mul_comm]
      simpa using mul_le_mul_of_nonneg_right (norm_sum_range_dirichletCharacter_le χ hχ (N + 1))
        (Real.rpow_nonneg (Nat.cast_nonneg N) (-s).re)
    · simpa using ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop).const_mul (m : ℝ)
  have h2 := (summable_abelTerm χ hχ hs).hasSum.tendsto_sum_nat
  simpa using h1.add h2

/-- Helper: for $\mathrm{Re}(s) > 1$ the Abel-summed series is the Dirichlet $L$-function. -/
theorem tsum_abelTerm_eq_lFunction {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) : ∑' i, abelTerm χ s i = χ.LFunction s := by
  have h1 := tendsto_sum_range_abelTerm χ hχ (lt_trans zero_lt_one hs)
  have h2 : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, χ n * (n : ℂ) ^ (-s)) atTop (𝓝 (χ.LFunction s)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    have hsum := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs)
    have := hsum.hasSum.tendsto_sum_nat
    refine this.congr fun N => Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
      simp [LSeries.term, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_neg, div_eq_mul_inv]
  exact tendsto_nhds_unique h1 h2

/-- **Theorem 2.1(b), convergence** (Milne, *CFT*, V, p. 154; Serre 1970, VI, Prop. 12): for a nontrivial Dirichlet
character $\chi$ the series $\sum_{n>0}\chi(n)n^{-s}$ converges for $\mathrm{Re}(s) > 0$, to Mathlib's
`DirichletCharacter.LFunction`. -/
@[kb "milne2020cft" "Ch. V, Theorem 2.1(b) (convergence for Re(s) > 0)"]
theorem theorem_2_1b_tendsto {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1) (s : ℂ)
    (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, χ n * (n : ℂ) ^ (-s)) atTop (𝓝 (χ.LFunction s)) := by
  have hF := differentiableOn_tsum_abelTerm χ hχ
  have hG : DifferentiableOn ℂ χ.LFunction {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hpre : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hF.analyticOnNhd hU) (hG.analyticOnNhd hU)
    hpre h2 (by
      have : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      exact tsum_abelTerm_eq_lFunction χ hχ hz)
  rw [← heq hs]
  exact tendsto_sum_range_abelTerm χ hχ hs

/-! ## Theorem 2.2 and Corollary 2.3 -/

/-- **Theorem 2.2** (Milne, *CFT*, V, p. 155; proved from Chebotarev, `MilneANT.example_8_34_dirichlet`): for $a$ prime to
$m$, the primes $p \equiv a \bmod m$ have Dirichlet density $1/\varphi(m)$. -/
@[kb "milne2020cft" "Ch. V, Theorem 2.2"]
theorem theorem_2_2 (m : ℕ) [NeZero m] (a : ℕ) (ha : a.Coprime m) :
    {v : HeightOneSpectrum (𝓞 ℚ) | (MilneANT.ratPrime v : ZMod m) = a}.HasDirichletDensity (1 / m.totient) :=
  MilneANT.example_8_34_dirichlet m a ha

/-- Helper: a prime of the rationals not dividing `m` is unramified in the cyclotomic field of level `m`. -/
theorem mem_unramifiedPrimes_cyclotomic (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ MilneANT.ratPrime v ∣ m) : v ∈ unramifiedPrimes ℚ L := by
  have hp : (MilneANT.ratPrime v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
  have hpz : Prime (MilneANT.ratPrime v : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hnd : ¬ (MilneANT.ratPrime v : ℤ) ∣ NumberField.discr L := by
    intro h
    have h1 : MilneANT.ratPrime v ∣ (NumberField.discr L).natAbs := by
      simpa [Int.natCast_dvd] using h
    rw [IsCyclotomicExtension.Rat.natAbs_discr m L] at h1
    have h2 : MilneANT.ratPrime v ∣ m ^ m.totient :=
      h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _)))
    exact hv (hp.dvd_of_dvd_pow h2)
  have key := (NumberField.not_dvd_discr_iff_forall_liesOver L (𝓞 L) hpz).mp hnd
  intro Q hQ hQo
  have hpv : ((MilneANT.ratPrime v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have h := (Rat.HeightOneSpectrum.natGenerator_dvd_iff v (n := MilneANT.ratPrime v)).mp dvd_rfl
    obtain ⟨x, hx, hxe⟩ := (Ideal.mem_map_of_equiv _ _).mp h
    have : x = ((MilneANT.ratPrime v : ℕ) : 𝓞 ℚ) :=
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by rw [hxe]; simp)
    rwa [this] at hx
  have hQm : Q.IsMaximal := hQ.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
  have hpQ : (MilneANT.ratPrime v : ℤ) ∈ Q.under ℤ := by
    have h1 : ((MilneANT.ratPrime v : ℕ) : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := by
      rw [← Ideal.LiesOver.over (p := v.asIdeal) (P := Q)]; exact hpv
    rw [Ideal.mem_comap] at h1 ⊢
    simpa using h1
  have hmax : (Ideal.span {(MilneANT.ratPrime v : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime hpz.ne_zero).mpr hpz |>.isMaximal (by simpa using hpz.ne_zero)
  have heq : Ideal.span {(MilneANT.ratPrime v : ℤ)} = Q.under ℤ :=
    hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      (by rw [Ideal.span_singleton_le_iff_mem]; exact hpQ)
  have : Q.LiesOver (Ideal.span {(MilneANT.ratPrime v : ℤ)}) := ⟨heq⟩
  have := key Q hQm inferInstance
  exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q

/-- In the proof of Corollary 2.3 (Milne, *CFT*, V, p. 155): a prime $p \nmid m$ splits in $\mathbb Q(\zeta_m)$ iff
$p \equiv 1 \bmod m$. -/
@[kb "milne2020cft" "Ch. V, Corollary 2.3 (proof: p splits in Q(ζ_m) iff p ≡ 1 mod m)"]
theorem mem_splitPrimes_cyclotomic_iff (m : ℕ) [NeZero m] (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L] [IsGalois ℚ L] (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : ¬ MilneANT.ratPrime v ∣ m) : v ∈ splitPrimes ℚ L ↔ (MilneANT.ratPrime v : ZMod m) = 1 := by
  have hunr := mem_unramifiedPrimes_cyclotomic m L v hv
  obtain ⟨Q⟩ : Nonempty (v.asIdeal.primesOver (𝓞 L)) := inferInstance
  rw [HilbertClassField.mem_splitPrimes_iff, HilbertClassField.splitsCompletelyIn_iff_frobAt_eq_one ℚ L v hunr Q,
    ← orderOf_eq_one_iff, (MilneANT.example_8_18 m L v hv Q).2.2, orderOf_eq_one_iff]

/-- **Corollary 2.3** (Milne, *CFT*, V, p. 155): the primes splitting in $\mathbb Q(\zeta_m)$ have Dirichlet density
$1/\varphi(m)$. -/
@[kb "milne2020cft" "Ch. V, Corollary 2.3"]
theorem cor_2_3 (m : ℕ) [NeZero m] :
    (splitPrimes ℚ (CyclotomicField m ℚ)).HasDirichletDensity (1 / m.totient) := by
  have h := splitPrimes_hasDirichletDensity_unconditional ℚ (CyclotomicField m ℚ)
  rwa [IsCyclotomicExtension.Rat.finrank m (CyclotomicField m ℚ)] at h

/-! ## Theorem 2.4 -/

/-- **Theorem 2.4(a)** (Milne, *CFT*, V, p. 156): $\zeta_K$ extends to a meromorphic function on $\mathrm{Re}(s) > 0$
(the library's `HeckeL.dedekindZetaCont`, holomorphic away from $s = 1$ and equal to $\zeta_K$ for $\mathrm{Re}(s) > 1$),
and $(s-1)\zeta_K(s) \to \frac{2^{r_1}(2\pi)^{r_2}\mathrm{Reg}(K)}{w_K|\Delta_K|^{1/2}}h_K$ as $s \to 1$ (Mathlib's
`NumberField.dedekindZeta_residue_def`). -/
@[kb "milne2020cft" "Ch. V, Theorem 2.4(a)"]
theorem theorem_2_4a (K : Type) [Field K] [NumberField K] :
    (∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ (HeckeL.dedekindZetaCont K) s) ∧
      (∀ s : ℂ, 1 < s.re → HeckeL.dedekindZetaCont K s = dedekindZeta K s) ∧
      Tendsto (fun s => (s - 1) * HeckeL.dedekindZetaCont K s) (𝓝[≠] 1)
        (𝓝 (((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K * regulator K * classNumber K) /
          (torsionOrder K * Real.sqrt |discr K|) : ℝ) : ℂ)) :=
  ⟨fun _ hs => HeckeL.differentiableAt_dedekindZetaCont hs, fun _ hs => HeckeL.dedekindZetaCont_eq hs,
    HeckeL.tendsto_sub_one_mul_dedekindZetaCont⟩

variable {K : Type} [Field K] [NumberField K]

open Classical in
/-- The coefficient $\sum_{N\mathfrak a = n,\ (\mathfrak a, \mathfrak m_0) = 1}\chi(\mathfrak a)$ of $n^{-s}$ in the Weber
$L$-series of a character $\chi$ of $C_\mathfrak m$ (Milne, *CFT*, V, p. 155). -/
def weberCoeff (m : Modulus K) (χ : RayClassGroup m →* ℂˣ) (n : ℕ) : ℂ :=
  ∑ᶠ (𝔞 : Ideal (𝓞 K)) (_ : Ideal.absNorm 𝔞 = n),
    if h : 𝔞 ≠ ⊥ ∧ 𝔞 ⊔ m.finite = ⊤ then (χ (idealRayClass m 𝔞 h.1 h.2) : ℂ) else 0

variable (K) in
/-- **Theorem 2.4(b)** (named statement; Milne, *CFT*, V, Theorem 2.4(b), p. 156; proved in Chapter VI, using the
existence theorem): for a nontrivial character $\chi$ of a ray class group $C_\mathfrak m$, the series
$L(s,\chi) = \sum_{(\mathfrak a,\mathfrak m_0) = 1}\chi(\mathfrak a)N\mathfrak a^{-s}$ (ordered by norm) converges for
$\mathrm{Re}(s) > 0$, and $L(1,\chi) \ne 0$; its sum is the Introduction's `weberLSeries` for $\mathrm{Re}(s) > 1$. -/
@[kb "milne2020cft" "Ch. V, Theorem 2.4(b) (input)"]
structure Theorem2_4b : Prop where
  converges : ∀ (m : Modulus K) (χ : RayClassGroup m →* ℂˣ), χ ≠ 1 →
    ∃ L : ℂ → ℂ, (∀ s : ℂ, 0 < s.re →
        Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, weberCoeff m χ n * (n : ℂ) ^ (-s)) atTop (𝓝 (L s))) ∧
      (∀ s : ℂ, 1 < s.re → L s = weberLSeries m χ s) ∧ L 1 ≠ 0

/-- **Dirichlet density** (Milne, *CFT*, V, §2, p. 156): a set $T$ of prime ideals of $K$ has density $\delta$ iff
$\sum_{\mathfrak p \in T}N\mathfrak p^{-s} \sim \delta\log\frac1{s-1}$ as $s \downarrow 1$. Mathlib's
`NumberField.Set.HasDirichletDensity` divides by $\sum_\mathfrak pN\mathfrak p^{-s}$ instead; the two agree because
$\sum_\mathfrak pN\mathfrak p^{-s} - \log\frac1{s-1}$ stays bounded (`Chebotarev.isBigO_primeIdealZetaSum_sub_log`). -/
@[kb "milne2020cft" "Ch. V, §2, p. 156 (Dirichlet density)"]
theorem hasDirichletDensity_iff_milne (T : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) :
    T.HasDirichletDensity δ ↔
      Tendsto (fun s : ℝ => T.primeIdealZetaSum s / Real.log (1 / (s - 1))) (𝓝[>] 1) (𝓝 δ) := by
  set P : ℝ → ℝ := fun s => (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s with hP
  set ℓ : ℝ → ℝ := fun s => Real.log (1 / (s - 1)) with hℓdef
  have hℓ : Tendsto ℓ (𝓝[>] 1) atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    simp only [one_div]
    refine tendsto_inv_nhdsGT_zero.comp ?_
    have h : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] (1 - 1)) :=
      ((continuous_sub_right (1 : ℝ)).continuousWithinAt.tendsto_nhdsWithin
        (fun s (hs : 1 < s) => show 1 - 1 < s - 1 by linarith))
    simpa using h
  have hlo : (fun _ : ℝ => (1 : ℝ)) =o[𝓝[>] 1] ℓ :=
    (Asymptotics.isLittleO_one_left_iff ℝ).mpr (tendsto_norm_atTop_atTop.comp hℓ)
  have h0 : Tendsto (fun s => (P s - ℓ s) / ℓ s) (𝓝[>] 1) (𝓝 0) :=
    ((isBigO_primeIdealZetaSum_sub_log (F := K)).trans_isLittleO hlo).tendsto_div_nhds_zero
  have hpos : ∀ᶠ s in 𝓝[>] (1 : ℝ), ℓ s ≠ 0 := (hℓ.eventually_gt_atTop 0).mono fun s hs => hs.ne'
  have hr : Tendsto (fun s => P s / ℓ s) (𝓝[>] 1) (𝓝 1) := by
    have := h0.add_const 1
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [hpos] with s hs
    field_simp
    ring
  have hPpos : ∀ᶠ s in 𝓝[>] (1 : ℝ), P s ≠ 0 :=
    ((tendsto_primeIdealZetaSum_univ (F := K)).eventually_gt_atTop 0).mono fun s hs => hs.ne'
  unfold NumberField.Set.HasDirichletDensity
  constructor
  · intro h
    have := h.mul hr
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [hpos, hPpos] with s h1 h2
    simp only [hP, hℓdef] at h1 h2 ⊢
    field_simp
  · intro h
    have := h.mul (hr.inv₀ one_ne_zero)
    rw [inv_one, mul_one] at this
    refine this.congr' ?_
    filter_upwards [hpos, hPpos] with s h1 h2
    simp only [hP, hℓdef] at h1 h2 ⊢
    field_simp

end NumberFieldKB.MilneCFT
