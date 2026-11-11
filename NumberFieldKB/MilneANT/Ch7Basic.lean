import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 7: basic definitions

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (printed page = pdf page − 2).

Definitions shared by the Chapter 7 files: discrete absolute values (prose definition, p. 107) and the valuation ring
$A = \{|a| \le 1\}$ of a nonarchimedean absolute value (Proposition 7.6).
-/

open Filter Topology

namespace NumberFieldKB.MilneANT

variable {K : Type*} [Field K]

/-- **Discrete absolute value** (prose definition, Milne p. 107): $|\cdot|$ is *discrete* when $|K^\times|$ is a
discrete subgroup of $\mathbb R_{>0}$, i.e. the set $\{|x| : x \in K^\times\}$ is discrete in the subspace topology. -/
@[kb "milne2020ant" "v3.08, Ch. 7, definition of a discrete absolute value, p. 107"]
def IsDiscreteAbv (v : AbsoluteValue K ℝ) : Prop :=
  DiscreteTopology (Set.range fun x : Kˣ => v (x : K))

/-- The ring $A = \{a \in K : |a| \le 1\}$ of a nonarchimedean absolute value, as a valuation subring of $K$
(Proposition 7.6). -/
@[kb "milne2020ant" "v3.08, Prop. 7.6, p. 107"]
def absValuationSubring (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) : ValuationSubring K where
  carrier := {a | v a ≤ 1}
  mul_mem' {a b} ha hb := by
    show v (a * b) ≤ 1
    rw [map_mul]
    have ha' : v a ≤ 1 := ha
    have hb' : v b ≤ 1 := hb
    calc v a * v b ≤ 1 * 1 := mul_le_mul ha' hb' (v.nonneg _) zero_le_one
      _ = 1 := one_mul 1
  one_mem' := by simp
  add_mem' {a b} ha hb := (hv a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' a := by
    by_cases h : v a ≤ 1
    · exact Or.inl h
    · right
      show v a⁻¹ ≤ 1
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))

@[simp]
theorem mem_absValuationSubring (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (a : K) :
    a ∈ absValuationSubring v hv ↔ v a ≤ 1 := Iff.rfl

/-- An absolute value that is `≤ 1` on the naturals is nonarchimedean (binomial expansion of `(x+y)^n`). -/
theorem isNonarchimedean_of_natCast_le_one (v : AbsoluteValue K ℝ) (h : ∀ n : ℕ, v n ≤ 1) :
    IsNonarchimedean v := by
  intro x y
  by_contra hlt
  replace hlt := not_le.mp hlt
  set M := max (v x) (v y) with hM
  have hM0 : 0 ≤ M := le_trans (v.nonneg x) (le_max_left _ _)
  have hpos : 0 < v (x + y) := lt_of_le_of_lt hM0 hlt
  have key : ∀ n : ℕ, v (x + y) ^ n ≤ (n + 1) * M ^ n := by
    intro n
    rw [← map_pow, add_pow]
    refine (v.sum_le _ _).trans ?_
    calc ∑ m ∈ Finset.range (n + 1), v (x ^ m * y ^ (n - m) * (n.choose m : K))
        ≤ ∑ m ∈ Finset.range (n + 1), M ^ n := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          rw [map_mul, map_mul, map_pow, map_pow]
          have h1 : v x ^ m ≤ M ^ m := pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _
          have h2 : v y ^ (n - m) ≤ M ^ (n - m) := pow_le_pow_left₀ (v.nonneg _) (le_max_right _ _) _
          have h3 : v (n.choose m : K) ≤ 1 := h _
          calc v x ^ m * v y ^ (n - m) * v (n.choose m : K) ≤ M ^ m * M ^ (n - m) * 1 := by
                gcongr
            _ = M ^ n := by rw [mul_one, ← pow_add, Nat.add_sub_cancel' hm']
      _ = (n + 1) * M ^ n := by simp
  set t := M / v (x + y) with ht
  have ht0 : 0 ≤ t := div_nonneg hM0 hpos.le
  have ht1 : t < 1 := (div_lt_one hpos).2 hlt
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 * t ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 (by rw [abs_of_nonneg ht0]; exact ht1)
  have h2 : Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht1
  have h3 := (h1.add h2)
  rw [add_zero] at h3
  obtain ⟨n, hn⟩ := (h3.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))).exists
  have hpn : 0 < v (x + y) ^ n := pow_pos hpos n
  have h4 : (n + 1) * t ^ n < 1 := by simpa [add_mul] using hn
  have e : (n + 1) * t ^ n = (n + 1) * M ^ n / v (x + y) ^ n := by
    rw [ht, div_pow]; ring
  rw [e, div_lt_one hpn] at h4
  linarith [key n]

end NumberFieldKB.MilneANT
