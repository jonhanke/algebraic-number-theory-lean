import NumberFieldKB.ModularCurves.CuspInfinity
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# $\mathbb Q(t) \to \mathbb C((q))$, $t \mapsto s$, for $s$ with a pole of order $N$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2. Sending $j$ to a Laurent series $s$ with a pole of
order $N \ge 1$ embeds $\mathbb Q(j)$ in $\mathbb C((q))$ (`ratFuncToLaurent`), and the valuation of $\mathbb C((q))$
restricts to the $N$-th power of the valuation of the place $j = \infty$ (`valuation_ratFuncToLaurent`).
-/

open Polynomial

noncomputable section

namespace NumberFieldKB.ModularCurves

variable {s : LaurentSeries ℂ} {N : ℕ}

/-- The $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$ (see `RiemannHurwitz.lean`). -/
local instance (priority := high) ratFuncAlgebraRat'' : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- $p \mapsto p(s)$, $\mathbb Q[t] \to \mathbb C((q))$. -/
def polyToLaurent (s : LaurentSeries ℂ) : ℚ[X] →+* LaurentSeries ℂ := Polynomial.eval₂RingHom (algebraMap ℚ _) s

/-- A rational constant in $\mathbb C((q))$ has valuation at most $1$. -/
theorem valuation_algebraMap_rat_le (c : ℚ) : Valued.v (algebraMap ℚ (LaurentSeries ℂ) c) ≤ 1 := by
  have := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℂ) (D := 0)
    (f := algebraMap ℚ (LaurentSeries ℂ) c)).2
  rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl]
  apply this
  intro n hn
  have h : algebraMap ℚ (LaurentSeries ℂ) c = HahnSeries.C (c : ℂ) := by
    ext m; simp
  rw [h, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega)]

/-- A nonzero rational constant in $\mathbb C((q))$ has valuation $1$. -/
theorem valuation_algebraMap_rat {c : ℚ} (hc : c ≠ 0) : Valued.v (algebraMap ℚ (LaurentSeries ℂ) c) = 1 := by
  have h1 := valuation_algebraMap_rat_le c
  have h2 := valuation_algebraMap_rat_le c⁻¹
  rw [map_inv₀, map_inv₀] at h2
  have hne : Valued.v (algebraMap ℚ (LaurentSeries ℂ) c) ≠ 0 := fun h0 =>
    hc ((algebraMap ℚ (LaurentSeries ℂ)).injective (((Valuation.zero_iff _).1 h0).trans (map_zero _).symm))
  have h3 : 1 ≤ Valued.v (algebraMap ℚ (LaurentSeries ℂ) c) := by
    have := mul_le_mul' (le_refl (Valued.v (algebraMap ℚ (LaurentSeries ℂ) c))) h2
    rwa [mul_one, mul_inv_cancel₀ hne] at this
  exact le_antisymm h1 h3

/-- A nonzero polynomial of degree $n$ in $s$ has a pole of order $nN$. -/
theorem valuation_polyToLaurent (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) {p : ℚ[X]} (hp : p ≠ 0) :
    Valued.v (polyToLaurent s p) = WithZero.exp ((N : ℤ) * p.natDegree) := by
  induction' hn : p.natDegree using Nat.strong_induction_on with n ih generalizing p
  subst hn
  have hdec : p = p.eraseLead + C p.leadingCoeff * X ^ p.natDegree := (eraseLead_add_C_mul_X_pow p).symm
  have hlead : Valued.v (polyToLaurent s (C p.leadingCoeff * X ^ p.natDegree)) =
      WithZero.exp ((N : ℤ) * p.natDegree) := by
    have hc := valuation_algebraMap_rat (leadingCoeff_ne_zero.2 hp)
    have h : polyToLaurent s (C p.leadingCoeff * X ^ p.natDegree) =
        algebraMap ℚ (LaurentSeries ℂ) p.leadingCoeff * s ^ p.natDegree := by
      simp [polyToLaurent]
    rw [h, map_mul, map_pow, hc, hs, one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp [mul_comm]
  by_cases he : p.eraseLead = 0
  · have h0 : p = C p.leadingCoeff * X ^ p.natDegree := by
      rw [he, zero_add] at hdec
      exact hdec
    rw [← h0] at hlead
    exact hlead
  · have h1 := ih _ (eraseLead_natDegree_lt_or_eraseLead_eq_zero p |>.resolve_right he) he rfl
    have hlt : Valued.v (polyToLaurent s p.eraseLead) < Valued.v (polyToLaurent s (C p.leadingCoeff * X ^ p.natDegree)) := by
      rw [h1, hlead, WithZero.exp_lt_exp]
      have := eraseLead_natDegree_lt_or_eraseLead_eq_zero p |>.resolve_right he
      have h2 : ((p.eraseLead.natDegree : ℕ) : ℤ) < p.natDegree := by exact_mod_cast this
      nlinarith
    conv_lhs => rw [hdec, map_add]
    rw [Valuation.map_add_eq_of_lt_right _ hlt, hlead]

theorem polyToLaurent_injective (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) :
    Function.Injective (polyToLaurent s) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have h := valuation_polyToLaurent hs hN hp0
  rw [hp, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

/-- $\mathbb Q(t) \to \mathbb C((q))$, $t \mapsto s$. -/
def ratFuncToLaurent (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) : RatFunc ℚ →+* LaurentSeries ℂ :=
  RatFunc.liftRingHom (polyToLaurent s)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyToLaurent_injective hs hN))

theorem ratFuncToLaurent_algebraMap (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) (p : ℚ[X]) :
    ratFuncToLaurent hs hN (algebraMap ℚ[X] (RatFunc ℚ) p) = polyToLaurent s p := by
  rw [ratFuncToLaurent, RatFunc.liftRingHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- **The valuation of $\mathbb C((q))$ on $\mathbb Q(j)$ is $v_\infty^N$.** -/
theorem valuation_ratFuncToLaurent (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) (x : RatFunc ℚ) :
    Valued.v (ratFuncToLaurent hs hN x) = (TauCeti.Place.infty ℚ).valuation x ^ N := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, map_zero, map_zero, zero_pow (by omega)]
  · rw [ratFuncToLaurent, RatFunc.liftRingHom_apply, map_div₀,
      valuation_polyToLaurent hs hN (RatFunc.num_ne_zero hx),
      valuation_polyToLaurent hs hN x.denom_ne_zero, TauCeti.Place.valuation_infty_apply hx,
      RatFunc.intDegree, ← WithZero.exp_sub, ← WithZero.exp_nsmul]
    congr 1
    push_cast [nsmul_eq_mul]
    ring

end NumberFieldKB.ModularCurves
