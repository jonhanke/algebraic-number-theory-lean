/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Nontriviality survives restriction along an integral algebra

A valuation of `L` restricts along `algebraMap K L` to a valuation of `K`, and this file records
that the restriction of a nontrivial valuation is again nontrivial as soon as `L` is integral
over `K`.

Integrality is what makes this true, and it is sharp: without it the restriction can collapse.
The valuation of `K(t)` reading the `t`-adic order restricts to the trivial valuation on `K`.

This is restriction of the *domain*, along a ring map. It is unrelated to
`Valuation.RankOne.isNontrivial_restrict`, which restricts the *value group* of a valuation to its
value subgroup and leaves the domain alone.

## Main results

* `Valuation.isNontrivial_comap_algebraMap`: the restriction of a nontrivial valuation along an
  integral algebra is nontrivial.

## Implementation notes

The proof adapts the vanishing-sum argument of Aaron Liu's
`Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic` in
`Mathlib.RingTheory.Valuation.Algebraic`. That lemma cannot be applied directly, since it needs
the base `K` to be a field, while here `K` is only a commutative ring.

## References

* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005].
-/

public section

namespace Valuation

variable {K L Γ₀ : Type*} [CommRing K] [Ring L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀]

/-- Port shim (not in Mathlib `v4.35.0`): if a finite sum has value `0` and one of its terms has a
nonzero value, two distinct terms have the same nonzero value. -/
theorem exists_map_eq_of_map_sum_eq_zero {R : Type*} [Ring R] (v : Valuation R Γ₀) {ι : Type*}
    {s : Finset ι} {f : ι → R} {j : ι} (hj : j ∈ s) (hfj : v (f j) ≠ 0)
    (hsum : v (∑ i ∈ s, f i) = 0) :
    ∃ i ∈ s, ∃ i' ∈ s, i ≠ i' ∧ v (f i) ≠ 0 ∧ v (f i') ≠ 0 ∧ v (f i) = v (f i') := by
  classical
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun i ↦ v (f i)) ⟨j, hj⟩
  have hi0 : v (f i) ≠ 0 := fun h ↦ hfj (le_antisymm (h ▸ hmax j hj) zero_le)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i' ∈ s.erase i, v (f i') < v (f i) := by
    intro i' hi'
    obtain ⟨hne, hi's⟩ := Finset.mem_erase.mp hi'
    refine lt_of_le_of_ne (hmax i' hi's) fun heq ↦ ?_
    exact hcon i' hi's i hi hne (heq ▸ hi0) hi0 heq
  rw [← Finset.add_sum_erase s f hi, map_add_eq_of_lt_left] at hsum
  · exact hi0 hsum
  · exact map_sum_lt v hi0 hlt

/-- **The restriction of a nontrivial valuation along an integral algebra is nontrivial.** -/
theorem isNontrivial_comap_algebraMap [Algebra.IsIntegral K L] (v : Valuation L Γ₀)
    [v.IsNontrivial] : (v.comap (algebraMap K L)).IsNontrivial := by
  by_contra hcon
  -- a trivial restriction gives every nonzero value on `K` the value `1`
  have htriv (k : K) (hk : v (algebraMap K L k) ≠ 0) : v (algebraMap K L k) = 1 :=
    of_not_not fun h ↦ hcon ⟨k, hk, h⟩
  obtain ⟨x, hx0, hx1⟩ := ‹v.IsNontrivial›.exists_val_nontrivial
  obtain ⟨p, hp, hpx⟩ := Algebra.IsIntegral.isIntegral (R := K) x
  -- in the vanishing sum `p(x) = 0`, two distinct terms share a nonzero value; their
  -- coefficients have value `1`, so two distinct powers of `v x` agree, impossible as
  -- `v x ≠ 0, 1` (adapted from `Valuation.exists_map_pow_eq_map_algebraMap_of_isAlgebraic`)
  rw [Polynomial.eval₂_eq_sum_range] at hpx
  obtain ⟨i, -, j, -, hij, hi, hj, heq⟩ := v.exists_map_eq_of_map_sum_eq_zero
    (Finset.self_mem_range_succ p.natDegree) (by simp [hp.coeff_natDegree, hx0])
    ((congrArg v hpx).trans (map_zero v))
  simp only [map_mul, map_pow] at hi hj heq
  rw [htriv _ (left_ne_zero_of_mul hi), htriv _ (left_ne_zero_of_mul hj), one_mul,
    one_mul] at heq
  exact hij (pow_right_injective₀ (zero_lt_iff.mpr hx0) hx1 heq)

end Valuation

end
