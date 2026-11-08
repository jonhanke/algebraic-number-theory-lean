import NumberFieldKB.WeilBNT.FunctionField.Idele
import Mathlib.FieldTheory.KummerPolynomial

/-!
# A prime element of $k_v$ is not a $p$-th power (towards Weil III.§4, text p.57)

For a place $v$ of the function field $k$ and $\pi\in k_v$ with $v(\pi)=e^{-1}$:

* `not_pow_eq_of_valued_eq`: $\pi$ is not an $n$-th power in $k_v$ for $n\ge2$ (valuations of $n$-th powers lie in
  $e^{n\mathbb Z}$).
* `irreducible_X_pow_sub_C_prime`: for a prime $p$, $X^p-\pi$ is irreducible over $k_v$. Hence for the
  purely inseparable extension $k'=k(\pi^{1/p})$ ($p$ the characteristic), $k'\otimes_kk_v\cong k_v[X]/(X^p-\pi)$ is a
  field: a single place of $k'$ lies over $v$, totally ramified.

This is the local input of Weil's remark that Thm. 4 holds for inseparable $k'$ (III.§4, p.57); the global steps
($[k:k^p]=p$ and $k'=k(\pi^{1/p^n})$, the completion of $k'$ at the place above $v$) are not formalized.
-/

namespace NumberFieldKB.WeilBNT.FF

variable {Fq k : Type*} [Field Fq] [Finite Fq] [Field k] [Algebra Fq k]
  [Algebra (RatFunc Fq) k] [IsScalarTower Fq (RatFunc Fq) k] [FunctionField Fq k]

open Polynomial

namespace Place

/-- An element of valuation $e^{-1}$ is not an $n$-th power for $n\ge2$. -/
theorem not_pow_eq_of_valued_eq (v : Place Fq k) {π : v.Completion} (hπ : Valued.v π = WithZero.exp (-1))
    {n : ℕ} (hn : 2 ≤ n) (b : v.Completion) : b ^ n ≠ π := by
  intro h
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at h
    rw [← h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hv0 : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb0
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v b = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have := congrArg Valued.v h
  rw [map_pow, hm, hπ, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at this
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  rcases le_or_gt 0 m with hm0 | hm0 <;> nlinarith

/-- **$X^p-\pi$ is irreducible over $k_v$** for a prime $p$ and $v(\pi)=e^{-1}$. -/
theorem irreducible_X_pow_sub_C_prime (v : Place Fq k) {π : v.Completion} (hπ : Valued.v π = WithZero.exp (-1))
    {p : ℕ} (hp : p.Prime) : Irreducible (X ^ p - C π) :=
  X_pow_sub_C_irreducible_of_prime hp fun b => v.not_pow_eq_of_valued_eq hπ hp.two_le b

end Place

end NumberFieldKB.WeilBNT.FF
