import NumberFieldKB.MilneANT.Ch8Basic
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: natural density implies Dirichlet density

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Milne (p. 147, proof of Theorem 8.31) remarks that "normally one proves this result with a slightly weaker notion of
density". This file proves the comparison: a set of primes with natural density $\delta$ (Definition 8.30,
`HasNaturalDensity`) has Dirichlet density $\delta$ (Mathlib's `NumberField.Set.HasDirichletDensity`).
-/

open NumberField IsDedekindDomain Filter Topology

namespace NumberFieldKB.MilneANT

noncomputable section

-- `K : Type` (house style, as in `NumberFieldKB/Chebotarev`): the divergence of $\sum_{\mathfrak p}N\mathfrak p^{-s}$
-- used below is stated there for fields in `Type`.
variable {K : Type} [Field K] [NumberField K]

/-- The Abel summation weight $u_k(s) = (k+1)^{-s}$. -/
def abelU (s : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1) ^ (-s)

/-- The Abel summation increment $d_k(s) = (k+1)^{-s} - (k+2)^{-s}$. -/
def abelD (s : ℝ) (k : ℕ) : ℝ := abelU s k - abelU s (k + 1)

/-- $(k+1)^{-s}\to0$ for $s>0$. -/
theorem abelU_tendsto {s : ℝ} (hs : 0 < s) : Tendsto (abelU s) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hs).comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

/-- The increments are nonnegative for $s>0$. -/
theorem abelD_nonneg {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 ≤ abelD s k := by
  simp only [abelD, abelU, Nat.cast_add, Nat.cast_one]
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  exact sub_nonneg.2 (Real.rpow_le_rpow_of_nonpos (x := (k : ℝ) + 1) (y := (k : ℝ) + 1 + 1)
    (by linarith) (by linarith) (by linarith))

/-- The increments are at most $1$ for $s>0$. -/
theorem abelD_le_one {s : ℝ} (hs : 0 < s) (k : ℕ) : abelD s k ≤ 1 := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h1 : abelU s k ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h2 : 0 ≤ abelU s (k + 1) := by unfold abelU; positivity
  unfold abelD
  linarith

/-- Telescoping: $\sum_{k\ge j}d_k(s)=(j+1)^{-s}$ for $s>0$. -/
theorem abelD_hasSum_tail {s : ℝ} (hs : 0 < s) (j : ℕ) :
    HasSum (fun k => if j ≤ k then abelD s k else 0) (abelU s j) := by
  have h1 : HasSum (fun k => abelD s (k + j)) (abelU s j) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => abelD_nonneg hs _)]
    have hN : ∀ N : ℕ, ∑ i ∈ Finset.range N, abelD s (i + j) = abelU s j - abelU s (N + j) := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        simp only [abelD]
        have : n + 1 + j = (n + j) + 1 := by omega
        rw [this]; ring
    refine (tendsto_congr hN).2 ?_
    simpa using (tendsto_const_nhds (x := abelU s j)).sub
      ((abelU_tendsto hs).comp (tendsto_add_atTop_nat j))
  have h2 := (hasSum_nat_add_iff (f := fun k => if j ≤ k then abelD s k else 0) j).1
    (by simpa using h1)
  have h0 : ∑ i ∈ Finset.range j, (if j ≤ i then abelD s i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => if_neg (not_le.2 (Finset.mem_range.1 hi))
  rwa [h0, add_zero] at h2

/-- Abel summation in `ℝ≥0∞`: $\sum_{\mathfrak p\in S}N\mathfrak p^{-s}=\sum_k d_k(s)\,\pi_S(k+1)$. -/
theorem primeIdealZetaSum_ofReal (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal (S.primeIdealZetaSum s) =
      ∑' k : ℕ, ENNReal.ofReal (abelD s k) * (primeCount S ((k : ℝ) + 1) : ENNReal) := by
  classical
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun p => (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) with hf
  have hsum : Summable f := QuadFormsKB.NFEuler.summable_normP_rpow (F := K) hs
  have hnn : ∀ p, 0 ≤ f p := fun p => by simp only [hf]; positivity
  have hs0 : 0 < s := by linarith
  rw [Set.primeIdealZetaSum_def]
  change ENNReal.ofReal (∑' p : S, f p) = _
  rw [tsum_subtype S f]
  have hind : Summable (S.indicator f) := hsum.indicator S
  rw [ENNReal.ofReal_tsum_of_nonneg (fun p => Set.indicator_nonneg (fun p _ => hnn p) p) hind]
  set G : HeightOneSpectrum (𝓞 K) → ℕ → ENNReal := fun p k =>
    if p ∈ S ∧ (Ideal.absNorm p.asIdeal : ℝ) ≤ (k : ℝ) + 1 then ENNReal.ofReal (abelD s k) else 0
    with hG
  have step1 : ∀ p, ENNReal.ofReal (S.indicator f p) = ∑' k, G p k := by
    intro p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
      have hne : Ideal.absNorm p.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact p.ne_bot
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have hT := abelD_hasSum_tail hs0 j
      have hfp : f p = abelU s j := by simp [hf, abelU, hj]
      have hcond : ∀ k : ℕ, ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) ≤ (k : ℝ) + 1 ↔ j ≤ k := by
        intro k
        rw [hj]
        constructor
        · intro h
          have : (j : ℝ) ≤ k := by push_cast at h; linarith
          exact_mod_cast this
        · intro h
          have : (j : ℝ) ≤ k := by exact_mod_cast h
          push_cast; linarith
      rw [hfp, ← hT.tsum_eq, ENNReal.ofReal_tsum_of_nonneg
        (fun k => by split_ifs; exacts [abelD_nonneg hs0 k, le_rfl]) hT.summable]
      refine tsum_congr fun k => ?_
      simp only [hG]
      by_cases hk : j ≤ k
      · rw [if_pos hk, if_pos ⟨hp, (hcond k).2 hk⟩]
      · rw [if_neg hk, if_neg (fun h => hk ((hcond k).1 h.2))]; simp
    · rw [Set.indicator_of_notMem hp]
      simp [hG, hp]
  rw [tsum_congr step1, ENNReal.tsum_comm]
  refine tsum_congr fun k => ?_
  set A : Set (HeightOneSpectrum (𝓞 K)) := {p ∈ S | (Ideal.absNorm p.asIdeal : ℝ) ≤ (k : ℝ) + 1}
    with hA
  have hfin : A.Finite := (finite_setOf_absNorm_le ((k : ℝ) + 1)).subset fun p hp => hp.2
  have hGA : ∀ p, G p k = A.indicator (fun _ => ENNReal.ofReal (abelD s k)) p := by
    intro p
    simp only [hG, Set.indicator, hA, Set.mem_setOf_eq]
  rw [tsum_congr hGA, ← tsum_subtype A (fun _ => ENNReal.ofReal (abelD s k))]
  haveI := hfin.fintype
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  rfl

/-- Abel summation in `ℝ`, with summability. -/
theorem primeIdealZetaSum_eq_tsum (S : Set (HeightOneSpectrum (𝓞 K))) {s : ℝ} (hs : 1 < s) :
    Summable (fun k : ℕ => abelD s k * (primeCount S ((k : ℝ) + 1) : ℝ)) ∧
      S.primeIdealZetaSum s = ∑' k : ℕ, abelD s k * (primeCount S ((k : ℝ) + 1) : ℝ) := by
  have h := primeIdealZetaSum_ofReal S hs
  have hd : ∀ k, 0 ≤ abelD s k := fun k => abelD_nonneg (by linarith) k
  set t : ℕ → ℝ := fun k => abelD s k * (primeCount S ((k : ℝ) + 1) : ℝ) with ht
  have tnn : ∀ k, 0 ≤ t k := fun k => mul_nonneg (hd k) (Nat.cast_nonneg _)
  have hte : ∀ k, ENNReal.ofReal (abelD s k) * (primeCount S ((k : ℝ) + 1) : ENNReal) =
      ENNReal.ofReal (t k) := by
    intro k
    simp only [ht]
    rw [ENNReal.ofReal_mul (hd k), ENNReal.ofReal_natCast]
  simp_rw [hte] at h
  have hne : ∑' k, ENNReal.ofReal (t k) ≠ ⊤ := by rw [← h]; exact ENNReal.ofReal_ne_top
  have hsm : Summable t :=
    (ENNReal.summable_toReal hne).congr fun k => ENNReal.toReal_ofReal (tnn k)
  refine ⟨hsm, ?_⟩
  have h2 := ENNReal.ofReal_tsum_of_nonneg tnn hsm
  exact (ENNReal.ofReal_eq_ofReal_iff (S.primeIdealZetaSum_nonneg s) (tsum_nonneg tnn)).1
    (h.trans h2.symm)

/-- **Natural density implies Dirichlet density**: if $S$ has natural density $\delta$ then it has Dirichlet density
$\delta$. The proof is Abel summation: $\sum_{\mathfrak p\in S}N\mathfrak p^{-s} = \sum_{N}\pi_S(N)(N^{-s}-(N+1)^{-s})$,
and the total $\sum_{\mathfrak p}N\mathfrak p^{-s}$ tends to infinity as $s\to1^+$. -/
@[kb "milne2020ant" "v3.08, Thm. 8.31 (proof: natural density is stronger than Dirichlet density), p. 147"]
theorem HasNaturalDensity.hasDirichletDensity {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : HasNaturalDensity S δ) : S.HasDirichletDensity δ := by
  classical
  have hP := NumberFieldKB.Chebotarev.tendsto_primeIdealZetaSum_univ_atTop (F := K)
  have hshift : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have hseq : Tendsto (fun k : ℕ => (primeCount S ((k : ℝ) + 1) : ℝ) /
      primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1)) atTop (𝓝 δ) :=
    h.comp hshift
  have hπseq : Tendsto (fun k : ℕ => primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K)))
      ((k : ℝ) + 1)) atTop atTop := tendsto_primeCount_univ.comp hshift
  unfold NumberField.Set.HasDirichletDensity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  set e : ℕ → ℝ := fun k => (primeCount S ((k : ℝ) + 1) : ℝ) -
    δ * primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1) with he
  have key : ∀ᶠ k : ℕ in atTop, |e k| ≤ ε / 3 * primeCount
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1) := by
    filter_upwards [Metric.tendsto_nhds.1 hseq (ε / 3) hε3, hπseq.eventually_gt_atTop 0] with k hk hpos
    have hb : (0 : ℝ) < primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1) := by
      exact_mod_cast hpos
    rw [Real.dist_eq] at hk
    simp only [he]
    set a : ℝ := (primeCount S ((k : ℝ) + 1) : ℝ)
    set b : ℝ := ((primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1) : ℕ) : ℝ)
    have : a - δ * b = b * (a / b - δ) := by field_simp
    rw [this, abs_mul, abs_of_pos hb, mul_comm]
    exact mul_le_mul_of_nonneg_right hk.le hb.le
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 key
  set G : ℝ := ∑ k ∈ Finset.range K₀, |e k| with hGdef
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hbound : ∀ s : ℝ, 1 < s →
      |S.primeIdealZetaSum s - δ * (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s|
        ≤ G + ε / 3 * (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
    intro s hs
    obtain ⟨hS1, hS2⟩ := primeIdealZetaSum_eq_tsum S hs
    obtain ⟨hU1, hU2⟩ := primeIdealZetaSum_eq_tsum (Set.univ : Set (HeightOneSpectrum (𝓞 K))) hs
    have hs0 : 0 < s := by linarith
    have hdiff : S.primeIdealZetaSum s - δ * (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s
        = ∑' k : ℕ, abelD s k * e k := by
      rw [hS2, hU2, ← tsum_mul_left, ← hS1.tsum_sub (hU1.mul_left δ)]
      exact tsum_congr fun k => by simp only [he]; ring
    have hg1 : HasSum (fun k : ℕ => if k < K₀ then |e k| else 0) G := by
      have : HasSum (fun k : ℕ => if k < K₀ then |e k| else 0)
          (∑ k ∈ Finset.range K₀, if k < K₀ then |e k| else 0) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => if_neg (by simpa using hb))
      rwa [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.1 hk))] at this
    have hg2 := hU1.hasSum.mul_left (ε / 3)
    rw [← hU2] at hg2
    have hg := hg1.add hg2
    rw [hdiff]
    have := tsum_of_norm_bounded (f := fun k : ℕ => abelD s k * e k) hg (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abelD_nonneg hs0 k)]
      have hd0 := abelD_nonneg hs0 k
      have hd1 := abelD_le_one hs0 k
      have hpi : (0 : ℝ) ≤ ((primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      by_cases hk : k < K₀
      · rw [if_pos hk]
        have h1 : abelD s k * |e k| ≤ |e k| := mul_le_of_le_one_left (abs_nonneg _) hd1
        have h2 : 0 ≤ ε / 3 * (abelD s k * primeCount (Set.univ : Set (HeightOneSpectrum (𝓞 K)))
            ((k : ℝ) + 1)) := by positivity
        linarith
      · rw [if_neg hk]
        have h1 := hK₀ k (not_lt.1 hk)
        have h2 : abelD s k * |e k| ≤ abelD s k * (ε / 3 * primeCount
            (Set.univ : Set (HeightOneSpectrum (𝓞 K))) ((k : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h1 hd0
        linarith)
    rwa [Real.norm_eq_abs] at this
  filter_upwards [self_mem_nhdsWithin, hP.eventually_gt_atTop (3 * G / ε)] with s hs hPs
  have hs1 : (1 : ℝ) < s := hs
  set P : ℝ := (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s with hPdef
  have hPpos : 0 < P := lt_of_le_of_lt (by positivity) hPs
  have hGP : G < ε / 3 * P := by
    have := (div_lt_iff₀ hε).1 hPs
    linarith
  have hb := hbound s hs1
  rw [Real.dist_eq]
  have : S.primeIdealZetaSum s / P - δ = (S.primeIdealZetaSum s - δ * P) / P := by
    field_simp
  rw [this, abs_div, abs_of_pos hPpos, div_lt_iff₀ hPpos]
  nlinarith [mul_pos hε hPpos]

end

end NumberFieldKB.MilneANT
