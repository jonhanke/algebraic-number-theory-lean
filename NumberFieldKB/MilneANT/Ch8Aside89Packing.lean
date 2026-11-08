import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Aside89Basic

/-!
# Milne, *Algebraic Number Theory*, Aside 8.9 (Artin–Whaples): the packing bound

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Aside 8.9, p. 138; bib key `milne2020ant`.
E. Artin, *Algebraic Numbers and Algebraic Functions*, Ch. 12.

* `totallyBounded_ball` (P1): if the completion `K_v` is locally compact, the unit ball of `K` is totally bounded;
* `packingBound_of_totallyBounded` (P2): total boundedness of the unit ball gives `PackingBound v` by scaling with a
  power of an element `a` with `0 < v a < 1`;
* `packingBound`: the combination.
-/

namespace NumberFieldKB.MilneANT.Aside89

variable {K : Type*} [Field K]

/-- A nontrivial absolute value has an element with `0 < v a < 1`. -/
theorem exists_pos_lt_one (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    ∃ a : K, 0 < v a ∧ v a < 1 := by
  obtain ⟨b, hb0, hb1⟩ := hv
  have hpos : 0 < v b := v.pos hb0
  rcases lt_or_gt_of_ne hb1 with h | h
  · exact ⟨b, hpos, h⟩
  · refine ⟨b⁻¹, ?_, ?_⟩
    · rw [map_inv₀]; positivity
    · rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h

/-- **P1**: if the completion `K_v` is locally compact, the unit ball of `K` is totally bounded. -/
theorem totallyBounded_ball (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial)
    [LocallyCompactSpace v.Completion] :
    ∀ r : ℝ, 0 < r → ∃ s : Finset K, ∀ x : K, v x ≤ 1 → ∃ y ∈ s, v (x - y) < r := by
  classical
  intro r hr
  obtain ⟨a, ha0, ha1⟩ := exists_pos_lt_one v hv
  let : NontriviallyNormedField v.Completion :=
    { (inferInstance : NormedField v.Completion) with
      non_trivial := by
        refine ⟨((a⁻¹ : K) : v.Completion), ?_⟩
        have : ‖((a⁻¹ : K) : v.Completion)‖ = v a⁻¹ := by
          rw [UniformSpace.Completion.norm_coe]; rfl
        rw [this, map_inv₀]
        exact one_lt_inv₀ ha0 |>.2 ha1 }
  have : ProperSpace v.Completion := ProperSpace.of_locallyCompactSpace v.Completion
  obtain ⟨t, -, htfin, hcov⟩ := finite_cover_balls_of_compact
    (isCompact_closedBall (0 : v.Completion) 1) (half_pos hr)
  have hd : DenseRange ((↑) : WithAbs v → v.Completion) := UniformSpace.Completion.denseRange_coe
  have hex : ∀ c : v.Completion, ∃ y : K, dist ((y : K) : v.Completion) c < r / 2 := by
    intro c
    obtain ⟨z, hz⟩ := Metric.denseRange_iff.1 hd c (r / 2) (half_pos hr)
    exact ⟨WithAbs.ofAbs z, by rw [dist_comm]; simpa using hz⟩
  choose f hf using hex
  refine ⟨htfin.toFinset.image f, fun x hx => ?_⟩
  have hxm : ((x : K) : v.Completion) ∈ Metric.closedBall (0 : v.Completion) 1 := by
    rw [mem_closedBall_zero_iff, UniformSpace.Completion.norm_coe]; exact hx
  have := hcov hxm
  simp only [Set.mem_iUnion] at this
  obtain ⟨c, hc, hxc⟩ := this
  refine ⟨f c, Finset.mem_image.2 ⟨c, htfin.mem_toFinset.2 hc, rfl⟩, ?_⟩
  have h1 := hf c
  have h2 : dist ((x : K) : v.Completion) ((f c : K) : v.Completion) < r := by
    calc _ ≤ dist ((x : K) : v.Completion) c + dist c ((f c : K) : v.Completion) := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by
        apply add_lt_add
        · exact Metric.mem_ball.1 hxc
        · rw [dist_comm]; exact h1
      _ = r := by ring
  have h3 : dist ((x : K) : v.Completion) ((f c : K) : v.Completion) = v (x - f c) := by
    rw [UniformSpace.Completion.dist_eq, dist_eq_norm]
    rfl
  rwa [h3] at h2

/-- Covering of the unit ball by `m ^ k` balls of radius `(v a)^k`. -/
theorem cover_pow (v : AbsoluteValue K ℝ) {a : K} (ha0 : 0 < v a) (s : Finset K)
    (hs : ∀ x : K, v x ≤ 1 → ∃ y ∈ s, v (x - y) < v a) :
    ∀ k : ℕ, ∃ t : Finset K, t.card ≤ s.card ^ k ∧
      ∀ x : K, v x ≤ 1 → ∃ y ∈ t, v (x - y) ≤ v a ^ k := by
  have ha : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha0; exact lt_irrefl _ ha0
  classical
  intro k
  induction k with
  | zero =>
    refine ⟨{0}, by simp, fun x hx => ⟨0, by simp, by simpa using hx⟩⟩
  | succ k ih =>
    obtain ⟨t, htc, hcov⟩ := ih
    refine ⟨(s ×ˢ t).image (fun p => p.1 + a * p.2), ?_, ?_⟩
    · calc _ ≤ (s ×ˢ t).card := Finset.card_image_le
        _ = s.card * t.card := Finset.card_product _ _
        _ ≤ s.card * s.card ^ k := Nat.mul_le_mul_left _ htc
        _ = s.card ^ (k + 1) := by rw [pow_succ, mul_comm]
    · intro x hx
      obtain ⟨y1, hy1, hlt⟩ := hs x hx
      have hx' : v ((x - y1) / a) ≤ 1 := by
        rw [map_div₀, div_le_one ha0]; exact hlt.le
      obtain ⟨y', hy', hv'⟩ := hcov _ hx'
      refine ⟨y1 + a * y', Finset.mem_image.2 ⟨(y1, y'), Finset.mem_product.2 ⟨hy1, hy'⟩, rfl⟩, ?_⟩
      have e : x - (y1 + a * y') = a * ((x - y1) / a - y') := by
        field_simp
        ring
      rw [e, map_mul, pow_succ, mul_comm (v a ^ k)]
      exact mul_le_mul_of_nonneg_left hv' ha0.le

/-- **P2**: total boundedness of the unit ball gives the packing bound (by scaling). -/
theorem packingBound_of_totallyBounded (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial)
    (h : ∀ r : ℝ, 0 < r → ∃ s : Finset K, ∀ x : K, v x ≤ 1 → ∃ y ∈ s, v (x - y) < r) :
    PackingBound v := by
  obtain ⟨a, ha0, ha1⟩ := exists_pos_lt_one v hv
  have ha : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha0; exact lt_irrefl _ ha0
  set ρ := v a with hρ
  obtain ⟨s, hs⟩ := h ρ ha0
  have hm : (1 : ℝ) ≤ (s.card : ℝ) := by
    obtain ⟨y, hy, -⟩ := hs 0 (by simp)
    exact_mod_cast Finset.card_pos.2 ⟨y, hy⟩
  set m : ℝ := (s.card : ℝ) with hmdef
  have hyρ : 1 < 1 / ρ := by rw [lt_div_iff₀ ha0]; linarith
  set κ : ℝ := Real.logb (1 / ρ) m with hκ
  have hκ0 : 0 ≤ κ := Real.logb_nonneg hyρ hm
  have hm_eq : m = (1 / ρ) ^ κ :=
    (Real.rpow_logb (by linarith) hyρ.ne' (by linarith)).symm
  have hC1 : (1 : ℝ) ≤ 2 / ρ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  refine ⟨(2 / ρ ^ 2) ^ κ, κ, by positivity, hκ0, ?_⟩
  intro R ε hε hεR S hSR hSep
  have hR : 0 < R := lt_of_lt_of_le hε hεR
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hR hyρ
  have e : ρ ^ n * (1 / ρ) ^ n = 1 := by
    rw [one_div, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero _ ha0.ne')]
  have e2 : ρ ^ (n + 1) * (1 / ρ) ^ (n + 1) = 1 := by
    rw [one_div, inv_zpow, mul_inv_cancel₀ (zpow_ne_zero _ ha0.ne')]
  set l : ℝ := ρ ^ (n + 1) with hl
  have hlpos : 0 < l := zpow_pos ha0 _
  have hl1 : l * R ≤ 1 := by
    calc l * R ≤ l * (1 / ρ) ^ (n + 1) := mul_le_mul_of_nonneg_left hn2 hlpos.le
      _ = 1 := e2
  have hl2 : ρ < l * R := by
    have h1 : 1 < ρ ^ n * R := by
      calc (1 : ℝ) = ρ ^ n * (1 / ρ) ^ n := e.symm
        _ < ρ ^ n * R := mul_lt_mul_of_pos_left hn1 (zpow_pos ha0 _)
    have : l * R = ρ * (ρ ^ n * R) := by
      rw [hl, zpow_add_one₀ ha0.ne']; ring
    rw [this]
    nlinarith
  set δ : ℝ := l * ε with hδ
  have hδpos : 0 < δ := mul_pos hlpos hε
  have hex : ∃ k : ℕ, 2 * ρ ^ k < δ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (half_pos hδpos) ha1
    exact ⟨k, by linarith⟩
  set k := Nat.find hex with hkdef
  have hk : 2 * ρ ^ k < δ := Nat.find_spec hex
  obtain ⟨t, htc, hcov⟩ := cover_pow v ha0 s hs k
  have hvl : ∀ x : K, v (a ^ (n + 1) * x) = l * v x := by
    intro x
    rw [map_mul, map_zpow₀]
  have hS : ∀ x ∈ S, ∃ y ∈ t, v (a ^ (n + 1) * x - y) ≤ ρ ^ k := by
    intro x hx
    apply hcov
    rw [hvl]
    calc l * v x ≤ l * R := mul_le_mul_of_nonneg_left (hSR x hx) hlpos.le
      _ ≤ 1 := hl1
  choose! c hc using hS
  have hinj : Set.InjOn c S := by
    intro x hx y hy hxy
    by_contra hne
    have hsep := hSep x hx y hy hne
    have h1 := (hc x hx).2
    have h2 := (hc y hy).2
    have h3 : v (a ^ (n + 1) * (x - y)) = l * v (x - y) := hvl _
    have h4 : δ ≤ v (a ^ (n + 1) * (x - y)) := by
      rw [h3, hδ]; exact mul_le_mul_of_nonneg_left hsep hlpos.le
    have h5 : a ^ (n + 1) * (x - y) = (a ^ (n + 1) * x - c x) - (a ^ (n + 1) * y - c y) := by
      rw [hxy]; ring
    have h6 : v ((a ^ (n + 1) * x - c x) - (a ^ (n + 1) * y - c y))
        ≤ v (a ^ (n + 1) * x - c x) + v (a ^ (n + 1) * y - c y) := by
      exact v.sub_le_add _ _
    rw [h5] at h4
    linarith
  have hcard : S.card ≤ t.card :=
    Finset.card_le_card_of_injOn c (fun x hx => (hc x hx).1) hinj
  have hcardR : (S.card : ℝ) ≤ m ^ k := by
    calc (S.card : ℝ) ≤ (t.card : ℝ) := by exact_mod_cast hcard
      _ ≤ ((s.card ^ k : ℕ) : ℝ) := by exact_mod_cast htc
      _ = m ^ k := by push_cast; rfl
  refine hcardR.trans ?_
  have hε1 : 1 ≤ R / ε := by rw [le_div_iff₀ hε]; linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hC1 hκ0) (Real.one_le_rpow hε1 hκ0)
  · have hmin := Nat.find_min hex (m := k - 1) (by omega)
    have hmin' : δ ≤ 2 * ρ ^ (k - 1) := by
      by_contra hcon; exact hmin (not_le.1 hcon)
    have hρk : ρ ^ k = ρ * ρ ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    -- (1/ρ)^k ≤ (2/ρ²) (R/ε)
    have hbig : (1 / ρ) ^ k ≤ 2 / ρ ^ 2 * (R / ε) := by
      have hpk : 0 < ρ ^ k := pow_pos ha0 k
      rw [one_div, inv_pow, inv_le_iff_one_le_mul₀' hpk]
      -- 1 ≤ (2/ρ²)(R/ε) ρ^k
      have h1 : ρ * δ ≤ ρ ^ k * 2 := by rw [hρk]; nlinarith
      have h5 : ρ * ε * ρ < ρ * ε * (l * R) := mul_lt_mul_of_pos_left hl2 (by positivity)
      have h4 : ρ ^ k * (2 / ρ ^ 2 * (R / ε)) = ρ ^ k * 2 * R / (ρ ^ 2 * ε) := by
        field_simp
      rw [h4, le_div_iff₀ (by positivity)]
      have h6 := mul_le_mul_of_nonneg_right h1 hR.le
      rw [hδ] at h6
      nlinarith
    have hm_k : m ^ k = ((1 / ρ) ^ k) ^ κ := by
      rw [hm_eq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast]
    rw [hm_k, ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) hbig hκ0

@[kb "milne2020ant" "v3.08, Aside 8.9, p. 138"]
theorem packingBound (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial)
    [LocallyCompactSpace v.Completion] : PackingBound v :=
  packingBound_of_totallyBounded v hv (totallyBounded_ball v hv)

end NumberFieldKB.MilneANT.Aside89
