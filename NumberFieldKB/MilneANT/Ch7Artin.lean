import Mathlib
import QuadFormsKB.Citation

namespace NumberFieldKB.MilneANT

open Filter Topology

/-- If `c ^ N ≤ (N + 1) * d ^ N` for all positive `N`, then `c ≤ d` (for nonnegative reals). -/
lemma le_of_pow_le_succ_mul_pow {c d : ℝ} (hd : 0 ≤ d)
    (h : ∀ N : ℕ, 1 ≤ N → c ^ N ≤ ((N : ℝ) + 1) * d ^ N) : c ≤ d := by
  by_contra hlt
  rw [not_le] at hlt
  rcases hd.eq_or_lt with hd0 | hdpos
  · subst hd0
    have := h 1 le_rfl
    simp at this
    linarith
  · set r := c / d with hr
    have hr1 : 1 < r := by rw [hr, one_lt_div hdpos]; exact hlt
    have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hr1
    have hev := (ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 / 2 by norm_num)))
    obtain ⟨N, hN1, hN2⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hrpos : 0 < r ^ N := by positivity
    have hN3 : (N : ℝ) ^ 1 / r ^ N < 1 / 2 := hN1
    rw [div_lt_iff₀ hrpos] at hN3
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN2
    have hb := h N hN2
    have hrd : r ^ N * d ^ N = c ^ N := by rw [← mul_pow, hr, div_mul_cancel₀ _ hdpos.ne']
    have hdN : 0 < d ^ N := by positivity
    have : r ^ N ≤ (N : ℝ) + 1 := by
      by_contra hh
      rw [not_le] at hh
      have := mul_lt_mul_of_pos_right hh hdN
      linarith
    simp at hN3
    linarith

/-- **Artin's lemma** (Milne, Remark 7.49(a); E. Artin, *Algebraic Numbers and Algebraic
Functions*, 1967, Chapter 1, Theorem 3): if an absolute value `v` satisfies
`v n = n ^ t` on every natural number `n`, with `t > 0`, then `v ^ (1 / t)` is again an absolute
value. -/
@[kb "milne2020ant" "v3.08, Remark 7.49, p. 127"]
theorem AbsoluteValue.exists_rpow_inv {K : Type*} [Field K] (v : AbsoluteValue K ℝ) {t : ℝ}
    (ht : 0 < t) (hv : ∀ n : ℕ, v (n : K) = (n : ℝ) ^ t) :
    ∃ w : AbsoluteValue K ℝ, ∀ x, w x = v x ^ t⁻¹ := by
  have p : ∀ z : ℝ, 0 ≤ z → ∀ k : ℕ, (z ^ t) ^ k = (z ^ k) ^ t := fun z hz k => by
    rw [← Real.rpow_mul_natCast hz, mul_comm, Real.rpow_natCast_mul hz]
  have key : ∀ x y : K, v (x + y) ^ t⁻¹ ≤ v x ^ t⁻¹ + v y ^ t⁻¹ := by
    intro x y
    set a := v x ^ t⁻¹ with ha
    set b := v y ^ t⁻¹ with hb
    have ha0 : 0 ≤ a := Real.rpow_nonneg (v.nonneg _) _
    have hb0 : 0 ≤ b := Real.rpow_nonneg (v.nonneg _) _
    have hvx : v x = a ^ t := by rw [ha, Real.rpow_inv_rpow (v.nonneg _) ht.ne']
    have hvy : v y = b ^ t := by rw [hb, Real.rpow_inv_rpow (v.nonneg _) ht.ne']
    have hmain : v (x + y) ≤ (a + b) ^ t := by
      apply le_of_pow_le_succ_mul_pow (Real.rpow_nonneg (add_nonneg ha0 hb0) _)
      intro N _
      have hterm : ∀ m ∈ Finset.range (N + 1),
          v (x ^ m * y ^ (N - m) * ((N.choose m : ℕ) : K)) ≤ ((a + b) ^ t) ^ N := by
        intro m hm
        have e : v (x ^ m * y ^ (N - m) * ((N.choose m : ℕ) : K))
            = (a ^ m * b ^ (N - m) * (N.choose m : ℝ)) ^ t := by
          rw [map_mul, map_mul, map_pow, map_pow, hv, hvx, hvy,
            Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
              (by positivity), p a ha0, p b hb0]
        rw [e, p _ (add_nonneg ha0 hb0)]
        apply Real.rpow_le_rpow (by positivity) _ ht.le
        have := Finset.single_le_sum (f := fun m => a ^ m * b ^ (N - m) * (N.choose m : ℝ))
          (fun i _ => by positivity) hm
        rw [← add_pow] at this
        exact this
      calc v (x + y) ^ N = v ((x + y) ^ N) := (map_pow v _ _).symm
        _ = v (∑ m ∈ Finset.range (N + 1), x ^ m * y ^ (N - m) * ((N.choose m : ℕ) : K)) := by
            rw [add_pow]
        _ ≤ ∑ m ∈ Finset.range (N + 1), v (x ^ m * y ^ (N - m) * ((N.choose m : ℕ) : K)) :=
            v.sum_le _ _
        _ ≤ ∑ m ∈ Finset.range (N + 1), ((a + b) ^ t) ^ N := Finset.sum_le_sum hterm
        _ = ((N : ℝ) + 1) * ((a + b) ^ t) ^ N := by simp
    calc v (x + y) ^ t⁻¹ ≤ ((a + b) ^ t) ^ t⁻¹ :=
          Real.rpow_le_rpow (v.nonneg _) hmain (inv_nonneg.2 ht.le)
      _ = a + b := Real.rpow_rpow_inv (add_nonneg ha0 hb0) ht.ne'
  refine ⟨{ toFun := fun x => v x ^ t⁻¹
            map_mul' := fun x y => by
              simp only [map_mul]; exact Real.mul_rpow (v.nonneg _) (v.nonneg _)
            nonneg' := fun x => Real.rpow_nonneg (v.nonneg _) _
            eq_zero' := fun x => by
              rw [Real.rpow_eq_zero (v.nonneg _) (inv_ne_zero ht.ne'), map_eq_zero_iff_eq_zero]
            add_le' := key }, fun x => rfl⟩

/-- The absolute value `v ^ (1 / t)` of Artin's lemma is equivalent to `v`. -/
theorem AbsoluteValue.exists_rpow_inv_isEquiv {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {t : ℝ} (ht : 0 < t) (hv : ∀ n : ℕ, v (n : K) = (n : ℝ) ^ t) :
    ∃ w : AbsoluteValue K ℝ, (∀ x, w x = v x ^ t⁻¹) ∧ w.IsEquiv v := by
  obtain ⟨w, hw⟩ := AbsoluteValue.exists_rpow_inv v ht hv
  refine ⟨w, hw, ?_⟩
  rw [AbsoluteValue.isEquiv_iff_exists_rpow_eq]
  exact ⟨t, ht, funext fun x => by
    show w x ^ t = v x
    rw [hw, Real.rpow_inv_rpow (v.nonneg _) ht.ne']⟩

end NumberFieldKB.MilneANT
