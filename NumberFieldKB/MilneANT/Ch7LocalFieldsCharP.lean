import NumberFieldKB.MilneANT.Ch7LocalFieldsPadic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Data.Nat.Dist
import Mathlib.Topology.Filter

/-!
# Milne, *Algebraic Number Theory*, Remark 7.49(c): first steps for local fields of characteristic $p$

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), bib key `milne2020ant`, Remark 7.49(c), p. 127:
a nonarchimedean local field of characteristic $p \ne 0$ is isomorphic to $k((T))$ for a finite field $k$.

Outline of the proof and what is proved here (namespace `Remark749c`), for $K$ with absolute value $v$ (a local field
in the sense of `IsLocalFieldMilne`):
* `isNonarchimedean_of_ringChar_ne_zero`: in positive characteristic every absolute value is nonarchimedean, since
  $v$ takes only finitely many values on the prime field and these are closed under powers.
* `exists_uniformizer`, `value_eq_zpow`: the closed unit ball is compact, so $\{v<1\}$ has an element $\pi$ of maximal
  absolute value, and the value group is $v(\pi)^{\mathbb Z}$.
* `finite_residue`: finitely many open unit balls cover the closed unit ball (finite residue field).
* `exists_teichmuller` (Teichmüller representatives in characteristic $p$): the algebraic closure $k$ of $\mathbb F_p$
  in $K$ is a finite subfield mapping bijectively onto the residue field. For $a$ in the unit ball, pigeonhole and
  injectivity of Frobenius modulo $\{v<1\}$ give $d \ge 1$ with $a^{p^d} \equiv a$; then $a^{p^{dn}}$ is Cauchy
  (differences are $(a^{p^d}-a)^{p^{dn}}$), and its limit $t$ satisfies $t^{p^d} = t$ and $t \equiv a$.

Remaining for the full Remark 7.49(c): identify $O_K$ with $k[[\pi]]$ and $K$ with $k((\pi))$.
-/

open Polynomial

namespace NumberFieldKB.MilneANT
namespace Remark749c

variable {K : Type*} [Field K]

lemma dist_toAbs (v : AbsoluteValue K ℝ) (x y : K) :
    dist (WithAbs.toAbs v x) (WithAbs.toAbs v y) = v (x - y) := by
  rw [dist_eq_norm]; rfl

/-- In positive characteristic every absolute value is nonarchimedean. -/
theorem isNonarchimedean_of_ringChar_ne_zero (v : AbsoluteValue K ℝ) (h : ringChar K ≠ 0) :
    IsNonarchimedean v := by
  have : CharP K (ringChar K) := ringChar.charP K
  set p := ringChar K with hp
  have hmod : ∀ n : ℕ, (n : K) = ((n % p : ℕ) : K) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n p]
    push_cast
    simp [CharP.cast_eq_zero]
  set M : ℝ := ∑ i ∈ Finset.range p, v (i : K) with hM
  have hbound : ∀ n : ℕ, v (n : K) ≤ M := by
    intro n
    rw [hmod n]
    exact Finset.single_le_sum (f := fun i : ℕ => v (i : K)) (fun i _ => v.nonneg _)
      (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero h)))
  have hle : ∀ n : ℕ, v (n : K) ≤ 1 := by
    intro n
    by_contra hn
    push Not at hn
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt M hn
    have := hbound (n ^ k)
    rw [Nat.cast_pow, map_pow] at this
    linarith
  have : IsUltrametricDist (WithAbs v) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one (fun n => by
      have := hle n
      exact this)
  intro x y
  exact (IsUltrametricDist.isNonarchimedean_norm (R := WithAbs v)) (WithAbs.toAbs v x)
    (WithAbs.toAbs v y)

section loc

variable {v : AbsoluteValue K ℝ}

lemma isUltrametricDist (hv : IsNonarchimedean v) : IsUltrametricDist (WithAbs v) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (fun x y => hv x.ofAbs y.ofAbs)

lemma exists_large (hK : IsLocalFieldMilne v) : ∃ a : K, 1 < v a := by
  obtain ⟨x, hx0, hx1⟩ := hK.isNontrivial
  rcases lt_or_gt_of_ne hx1 with h' | h'
  · refine ⟨x⁻¹, ?_⟩
    rw [map_inv₀]; exact one_lt_inv₀ (v.pos hx0) |>.2 h'
  · exact ⟨x, h'⟩

lemma isCompact_closedBall_one (hK : IsLocalFieldMilne v) :
    IsCompact (Metric.closedBall (0 : WithAbs v) 1) := by
  have := hK.locallyCompact
  obtain ⟨s, hs, hs0⟩ := exists_compact_mem_nhds (0 : WithAbs v)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs0
  have hc : IsCompact (Metric.closedBall (0 : WithAbs v) (ε / 2)) :=
    hs.of_isClosed_subset Metric.isClosed_closedBall
      ((Metric.closedBall_subset_ball (half_lt_self hε)).trans hball)
  obtain ⟨a, ha1⟩ := exists_large hK
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 / ε) ha1
  set b : WithAbs v := WithAbs.toAbs v (a ^ n) with hb
  have hbn : ‖b‖ = v a ^ n := by rw [hb, WithAbs.norm_toAbs_eq, map_pow]
  have hbpos : 0 < ‖b‖ := by rw [hbn]; exact pow_pos (lt_trans zero_lt_one ha1) n
  have hb0 : b ≠ 0 := norm_pos_iff.1 hbpos
  have hsub : Metric.closedBall (0 : WithAbs v) 1 ⊆
      (fun z => b * z) '' Metric.closedBall (0 : WithAbs v) (ε / 2) := by
    intro y hy
    refine ⟨b⁻¹ * y, ?_, by simp [mul_inv_cancel_left₀ hb0]⟩
    rw [mem_closedBall_zero_iff, norm_mul, norm_inv, hbn]
    rw [mem_closedBall_zero_iff] at hy
    have hpos : 0 < v a ^ n := hbn ▸ hbpos
    have h2 : 2 < ε * v a ^ n := by
      have := (div_lt_iff₀ hε).1 hn
      linarith
    calc (v a ^ n)⁻¹ * ‖y‖ ≤ (v a ^ n)⁻¹ * 1 := by gcongr
      _ ≤ ε / 2 := by
        rw [mul_one, inv_le_comm₀ hpos (by positivity)]
        rw [inv_div]; linarith
  exact (hc.image (continuous_const.mul continuous_id)).of_isClosed_subset
    Metric.isClosed_closedBall hsub

lemma isCompact_ball_one (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v) :
    IsCompact (Metric.ball (0 : WithAbs v) 1) := by
  have := isUltrametricDist hv
  exact (isCompact_closedBall_one hK).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
    Metric.ball_subset_closedBall

theorem exists_uniformizer (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v) :
    ∃ π : K, 0 < v π ∧ v π < 1 ∧ ∀ x : K, v x < 1 → v x ≤ v π := by
  obtain ⟨x, hx0, hx1⟩ := hK.isNontrivial
  obtain ⟨y, hy0, hy1⟩ : ∃ y : K, y ≠ 0 ∧ v y < 1 := by
    rcases lt_or_gt_of_ne hx1 with h' | h'
    · exact ⟨x, hx0, h'⟩
    · refine ⟨x⁻¹, inv_ne_zero hx0, ?_⟩
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h'
  have hne : (Metric.ball (0 : WithAbs v) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨z, hz, hmax⟩ := (isCompact_ball_one hv hK).exists_isMaxOn hne
    (continuous_norm.continuousOn)
  have hzy : v y ≤ ‖z‖ := by
    have : WithAbs.toAbs v y ∈ Metric.ball (0 : WithAbs v) 1 := by
      rw [mem_ball_zero_iff, WithAbs.norm_toAbs_eq]; exact hy1
    have := hmax this
    simpa [WithAbs.norm_toAbs_eq] using this
  refine ⟨z.ofAbs, lt_of_lt_of_le (v.pos hy0) hzy, ?_, fun w hw => ?_⟩
  · rw [mem_ball_zero_iff] at hz; exact hz
  · have hw' : WithAbs.toAbs v w ∈ Metric.ball (0 : WithAbs v) 1 := by
      rw [mem_ball_zero_iff, WithAbs.norm_toAbs_eq]; exact hw
    have h' : ‖WithAbs.toAbs v w‖ ≤ ‖z‖ := hmax hw'
    rwa [WithAbs.norm_toAbs_eq] at h'

theorem value_eq_zpow (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v) {π : K}
    (hπ : 0 < v π ∧ v π < 1 ∧ ∀ x : K, v x < 1 → v x ≤ v π) (x : K) (hx : x ≠ 0) :
    ∃ n : ℤ, v x = v π ^ n := by
  obtain ⟨h0, h1, hmax⟩ := hπ
  have hr1 : 1 < (v π)⁻¹ := one_lt_inv₀ h0 |>.2 h1
  have ht : 0 < (v x)⁻¹ := inv_pos.2 (v.pos hx)
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow ht hr1
  rw [inv_zpow', zpow_neg] at hn1
  rw [inv_zpow', zpow_neg] at hn2
  have hpn : 0 < v π ^ n := zpow_pos h0 n
  have hpn1 : 0 < v π ^ (n + 1) := zpow_pos h0 _
  have a1 : v x < v π ^ n := (inv_lt_inv₀ hpn (v.pos hx)).1 hn1
  have a2 : v π ^ (n + 1) ≤ v x := (inv_le_inv₀ (v.pos hx) hpn1).1 hn2
  rcases a2.eq_or_lt with h | h
  · exact ⟨n + 1, h.symm⟩
  · exfalso
    have hπ0 : π ≠ 0 := fun h' => by simp [h'] at h0
    have hy : v (x / π ^ n) = v x / v π ^ n := by rw [map_div₀, map_zpow₀]
    have hy1 : v (x / π ^ n) < 1 := by rw [hy, div_lt_one hpn]; exact a1
    have := hmax _ hy1
    rw [hy, div_le_iff₀ hpn] at this
    rw [zpow_add_one₀ h0.ne'] at h
    linarith

/-- Finitely many open unit balls cover the closed unit ball (finite residue field). -/
theorem finite_residue (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v) :
    ∃ R : Finset K, (∀ r ∈ R, v r ≤ 1) ∧ ∀ x : K, v x ≤ 1 → ∃ r ∈ R, v (x - r) < 1 := by
  classical
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall_one hK)
    (e := 1) one_pos
  refine ⟨htf.toFinset.image WithAbs.ofAbs, ?_, ?_⟩
  · intro r hr
    simp only [Finset.mem_image, Set.Finite.mem_toFinset] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    have := hts hy
    rw [mem_closedBall_zero_iff] at this
    exact this
  · intro x hx
    have hx' : WithAbs.toAbs v x ∈ Metric.closedBall (0 : WithAbs v) 1 := by
      rw [mem_closedBall_zero_iff, WithAbs.norm_toAbs_eq]; exact hx
    have := hcov hx'
    simp only [Set.mem_iUnion] at this
    obtain ⟨y, hy, hxy⟩ := this
    refine ⟨y.ofAbs, Finset.mem_image.2 ⟨y, htf.mem_toFinset.2 hy, rfl⟩, ?_⟩
    rw [Metric.mem_ball] at hxy
    have e : dist (WithAbs.toAbs v x) y = v (x - y.ofAbs) := dist_toAbs v x y.ofAbs
    linarith

end loc

section charp

variable {v : AbsoluteValue K ℝ} {p : ℕ} [Fact p.Prime] [CharP K p]

omit [Fact p.Prime] [CharP K p] in
lemma pow_iter {x : K} {n : ℕ} (h : x ^ p ^ n = x) (j : ℕ) : x ^ p ^ (n * j) = x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, h]

/-- The elements of `K` satisfying `x ^ (p ^ n) = x` for some `n > 0`: the algebraic closure of `𝔽_p` in `K`. -/
lemma exists_frobenius_subfield :
    ∃ k : Subfield K, ∀ x, x ∈ k ↔ ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  refine ⟨{ carrier := {x | ∃ n : ℕ, 0 < n ∧ x ^ p ^ n = x}
            mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_,
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [mul_pow, pow_iter hx m, mul_comm n m, pow_iter hy n]
  · exact ⟨1, one_pos, by simp⟩
  · rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [add_pow_char_pow, pow_iter hx m, mul_comm n m, pow_iter hy n]
  · exact ⟨1, one_pos, by simp [zero_pow hp0]⟩
  · rintro x ⟨n, hn, hx⟩
    refine ⟨n, hn, ?_⟩
    rw [← zero_sub, sub_pow_char_pow, hx, zero_pow (pow_ne_zero _ hp0)]
  · rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [inv_pow, hx]⟩

lemma v_sub_pow (x y : K) (e : ℕ) : v (x ^ p ^ e - y ^ p ^ e) = v (x - y) ^ p ^ e := by
  rw [← sub_pow_char_pow (p := p), map_pow]

lemma lt_one_of_pow_sub_lt {x y : K} {e : ℕ} (h : v (x ^ p ^ e - y ^ p ^ e) < 1) :
    v (x - y) < 1 := by
  rw [v_sub_pow] at h
  by_contra hc
  push Not at hc
  have := one_le_pow₀ (n := p ^ e) hc
  linarith

lemma exists_period (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v) (a : K) (ha : v a ≤ 1) :
    ∃ d : ℕ, 0 < d ∧ v (a ^ p ^ d - a) < 1 := by
  classical
  obtain ⟨R, -, hR⟩ := finite_residue hv hK
  have hex : ∀ n : ℕ, ∃ r ∈ R, v (a ^ p ^ n - r) < 1 := fun n =>
    hR _ (by rw [map_pow]; exact pow_le_one₀ (v.nonneg _) ha |>.trans' (by rfl))
  choose f hfR hf using hex
  have key : ∀ m n : ℕ, m < n → f m = f n → ∃ d : ℕ, 0 < d ∧ v (a ^ p ^ d - a) < 1 := by
    intro m n hmn hfe
    refine ⟨n - m, Nat.sub_pos_of_lt hmn, ?_⟩
    have h1 : v (a ^ p ^ m - a ^ p ^ n) < 1 := by
      have : a ^ p ^ m - a ^ p ^ n = (a ^ p ^ m - f m) + (f n - a ^ p ^ n) := by
        rw [hfe]; ring
      rw [this]
      refine lt_of_le_of_lt (hv _ _) (max_lt (hf m) ?_)
      rw [v.map_sub]; exact hf n
    have h2 : a ^ p ^ n = (a ^ p ^ (n - m)) ^ p ^ m := by
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hmn.le]
    rw [h2] at h1
    have := lt_one_of_pow_sub_lt (p := p) (v := v) h1
    rwa [v.map_sub] at this
  let F : ℕ → R := fun n => ⟨f n, hfR n⟩
  obtain ⟨m, n, hne, hFe⟩ := Finite.exists_ne_map_eq_of_infinite F
  have hfe : f m = f n := congrArg Subtype.val hFe
  rcases lt_or_gt_of_ne hne with h | h
  · exact key m n h hfe
  · exact key n m h hfe.symm

include p in
theorem exists_teichmuller_aux (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v) :
    ∃ k : Subfield K, Finite k ∧ (∀ c : k, c ≠ 0 → v c = 1) ∧
      ∀ x : K, v x ≤ 1 → ∃! c : k, v (x - c) < 1 := by
  classical
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := exists_frobenius_subfield (K := K) (p := p)
  -- nonzero elements of `k` have absolute value one
  have hk1 : ∀ c : K, c ∈ k → c ≠ 0 → v c = 1 := by
    intro c hc hc0
    obtain ⟨n, hn, hcn⟩ := (hk c).1 hc
    have h := congrArg v hcn
    rw [map_pow] at h
    have hs : 0 < v c := v.pos hc0
    have hq : 1 < p ^ n := Nat.one_lt_pow hn.ne' hp1
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have := pow_lt_self_of_lt_one₀ hs h1 hq
      linarith
    · have := lt_self_pow₀ h1 hq
      linarith
  have hsep : ∀ c c' : k, v ((c : K) - c') < 1 → c = c' := by
    intro c c' h
    by_contra hne
    have hne' : (c : K) - c' ≠ 0 := fun h0 => hne (Subtype.ext (sub_eq_zero.1 h0))
    have := hk1 _ (k.sub_mem c.2 c'.2) hne'
    linarith
  have hle1 : ∀ c : k, v (c : K) ≤ 1 := by
    intro c
    by_cases h0 : (c : K) = 0
    · rw [h0]; simp
    · exact (hk1 _ c.2 h0).le
  refine ⟨k, ?_, fun c hc => hk1 c c.2 (by exact_mod_cast hc), ?_⟩
  · obtain ⟨R, -, hR⟩ := finite_residue hv hK
    have hex : ∀ c : k, ∃ r ∈ R, v ((c : K) - r) < 1 := fun c => hR _ (hle1 c)
    choose f hfR hf using hex
    let F : k → R := fun c => ⟨f c, hfR c⟩
    refine Finite.of_injective F (fun c c' hcc => ?_)
    have hfe : f c = f c' := congrArg Subtype.val hcc
    apply hsep
    have : (c : K) - c' = ((c : K) - f c) + (f c' - c') := by rw [hfe]; ring
    rw [this]
    refine lt_of_le_of_lt (hv _ _) (max_lt (hf c) ?_)
    rw [v.map_sub]; exact hf c'
  · intro x hx
    obtain ⟨d, hd, hδ⟩ := exists_period hv hK (p := p) x hx
    set δ := v (x ^ p ^ d - x) with hδdef
    have hδ0 : 0 ≤ δ := v.nonneg _
    have e1 : ∀ n : ℕ, v (x ^ p ^ (d * n) - x ^ p ^ (d * (n + 1))) = δ ^ p ^ (d * n) := by
      intro n
      have : x ^ p ^ (d * (n + 1)) = (x ^ p ^ d) ^ p ^ (d * n) := by
        rw [← pow_mul, ← pow_add, mul_add, mul_one, add_comm]
      rw [this, v_sub_pow, v.map_sub, hδdef]
    let u : ℕ → WithAbs v := fun n => WithAbs.toAbs v (x ^ p ^ (d * n))
    have hdist : ∀ n, dist (u n) (u (n + 1)) = δ ^ p ^ (d * n) := by
      intro n
      exact (dist_toAbs v _ _).trans (e1 n)
    have hbound : ∀ n : ℕ, δ ^ p ^ (d * n) ≤ δ ^ n := by
      intro n
      refine pow_le_pow_of_le_one hδ0 hδ.le ?_
      calc n ≤ p ^ n := (Nat.lt_pow_self hp1).le
        _ ≤ p ^ (d * n) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hp0) (Nat.le_mul_of_pos_left n hd)
    have hsum : Summable (fun n => dist (u n) (u (n + 1))) := by
      refine Summable.of_nonneg_of_le (fun n => dist_nonneg) (fun n => ?_)
        (summable_geometric_of_lt_one hδ0 hδ)
      rw [hdist]; exact hbound n
    have hcau : CauchySeq u := cauchySeq_of_summable_dist hsum
    have := hK.completeSpace
    obtain ⟨t', ht'⟩ := cauchySeq_tendsto_of_complete hcau
    set t : K := t'.ofAbs with ht
    -- fixed point equation
    have hstep : ∀ n, u (n + 1) = (u n) ^ p ^ d := by
      intro n
      show WithAbs.toAbs v (x ^ p ^ (d * (n + 1))) = (WithAbs.toAbs v (x ^ p ^ (d * n))) ^ p ^ d
      have e : x ^ p ^ (d * (n + 1)) = (x ^ p ^ (d * n)) ^ p ^ d := by
        rw [← pow_mul, ← pow_add, mul_add, mul_one]
      rw [e]; rfl
    have h1 : Filter.Tendsto (fun n => u (n + 1)) Filter.atTop (nhds t') :=
      ht'.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun n => (u n) ^ p ^ d) Filter.atTop (nhds (t' ^ p ^ d)) :=
      ht'.pow _
    have hfix : t' ^ p ^ d = t' := by
      have : (fun n => u (n + 1)) = fun n => (u n) ^ p ^ d := funext hstep
      rw [this] at h1
      exact tendsto_nhds_unique h2 h1
    have htk : t ∈ k := (hk t).2 ⟨d, hd, by
      have := congrArg WithAbs.ofAbs hfix
      simpa [ht] using this⟩
    -- congruence to `x`
    have hdiff : ∀ n, v (x - x ^ p ^ (d * n)) < 1 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have : x - x ^ p ^ (d * (n + 1)) =
            (x - x ^ p ^ (d * n)) + (x ^ p ^ (d * n) - x ^ p ^ (d * (n + 1))) := by ring
        rw [this]
        refine lt_of_le_of_lt (hv _ _) (max_lt ih ?_)
        rw [e1]
        exact pow_lt_one₀ hδ0 hδ (pow_ne_zero _ hp0)
    obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.1 ht') 1 one_pos).exists
    have hn' : v (x ^ p ^ (d * n) - t) < 1 := by
      have e : dist (u n) t' = v (x ^ p ^ (d * n) - t) := dist_toAbs v _ t
      linarith
    have hxt : v (x - t) < 1 := by
      have : x - t = (x - x ^ p ^ (d * n)) + (x ^ p ^ (d * n) - t) := by ring
      rw [this]
      exact lt_of_le_of_lt (hv _ _) (max_lt (hdiff n) hn')
    refine ⟨⟨t, htk⟩, hxt, fun c' hc' => ?_⟩
    apply hsep
    have : ((c' : k) : K) - t = (((c' : k) : K) - x) + (x - t) := by ring
    show v ((c' : K) - t) < 1
    rw [this]
    refine lt_of_le_of_lt (hv _ _) (max_lt ?_ hxt)
    rw [v.map_sub]; exact hc'

end charp

/-- **Teichmüller representatives in characteristic $p$** (Milne, Remark 7.49(c), p. 127). In a nonarchimedean local
field $K$ of characteristic $p \ne 0$ there is a finite subfield $k$ (the algebraic closure of $\mathbb F_p$ in $K$)
all of whose nonzero elements have absolute value $1$, such that every element of the closed unit ball is congruent
modulo $\{v < 1\}$ to exactly one element of $k$. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
theorem exists_teichmuller {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (hK : IsLocalFieldMilne v)
    (hp : ringChar K ≠ 0) :
    ∃ (k : Subfield K), Finite k ∧ (∀ c : k, c ≠ 0 → v c = 1) ∧
      ∀ x : K, v x ≤ 1 → ∃! c : k, v (x - c) < 1 := by
  have : CharP K (ringChar K) := ringChar.charP K
  have : NeZero (ringChar K) := ⟨hp⟩
  have : Fact (ringChar K).Prime := CharP.char_is_prime_of_pos K (ringChar K)
  exact exists_teichmuller_aux hv hK

end Remark749c

end NumberFieldKB.MilneANT
