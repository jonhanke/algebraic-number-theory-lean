import NumberFieldKB.ModularCurves.FiniteFibre

/-!
# The order valuation at $\tau_0 \in \mathbb H$ restricted to $\mathbb Q(j)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). If $t = j(\tau_0)$ is a root of the irreducible
$q \in \mathbb Q[X]$ and $j - t$ has order $m$ at $\tau_0$, then the order of $r(j)$ at $\tau_0$ is $m\, v_q(r)$ for
every $r \in \mathbb Q(X)$ (`finVal_algebraMap`): at a prime $p$ with $p(t) \ne 0$ it is $0$, and at $p \sim q$ it is
$\operatorname{ord}_t(p) \cdot m = m$ ($t$ is a simple root, $p$ being separable), by `AnalyticAt.analyticOrderAt_comp`.
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- The $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$ (see `RiemannHurwitz.lean`). -/
local instance (priority := high) ratFuncAlgebraRatFin : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (τ₀ : ℍ) {q : ℚ[X]} (hq : Irreducible q) (hroot : aeval (jFun τ₀) q = 0) {m : ℕ}
  (hm : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ₀) (τ₀ : ℂ) = m)

theorem polyFun_eq_comp (p : ℚ[X]) : polyFun p = (fun w : ℂ => aeval w p) ∘ (jFun ∘ ofComplex) :=
  funext fun z => polyFun_apply p z

theorem finVal_polyToMero_of_aeval_ne_zero {p : ℚ[X]} (hp : aeval (jFun τ₀) p ≠ 0) :
    finVal τ₀ (polyToMero τ₀ p) = 1 := by
  rw [finVal, polyToMero_eq_mk, ordVal_mk_of_analyticAt (analyticAt_polyFun p τ₀) (n := 0)]
  · rfl
  · rw [Nat.cast_zero, analyticOrderAt_eq_zero]
    right
    rw [polyFun_apply, ofComplex_apply]
    exact hp

include hq hroot in
theorem associated_of_aeval_eq_zero {p : ℚ[X]} (hp : Irreducible p) (hp0 : aeval (jFun τ₀) p = 0) :
    Associated q p := by
  have hint : IsIntegral ℚ (jFun τ₀) := isAlgebraic_iff_isIntegral.1 ⟨q, hq.ne_zero, hroot⟩
  have h1 := (minpoly.irreducible hint).associated_of_dvd hq (minpoly.dvd ℚ _ hroot)
  have h2 := (minpoly.irreducible hint).associated_of_dvd hp (minpoly.dvd ℚ _ hp0)
  exact h1.symm.trans h2

include hm in
theorem finVal_polyToMero_of_root {p : ℚ[X]} (hp : Irreducible p) (hp0 : aeval (jFun τ₀) p = 0) :
    finVal τ₀ (polyToMero τ₀ p) = WithZero.exp (-(m : ℤ)) := by
  refine ordVal_mk_of_analyticAt (analyticAt_polyFun p τ₀) ?_
  have hf : AnalyticAt ℂ (fun w : ℂ => aeval w p) ((jFun ∘ ofComplex) (τ₀ : ℂ)) :=
    analyticAt_id.aeval_polynomial p
  rw [polyFun_eq_comp, hf.analyticOrderAt_comp (analyticAt_jFun τ₀)]
  have hτ : (jFun ∘ ofComplex) (τ₀ : ℂ) = jFun τ₀ := by simp [ofComplex_apply]
  rw [hτ, hm]
  have h1 : analyticOrderAt (fun w : ℂ => aeval w p) (jFun τ₀) = 1 := by
    refine analyticOrderAt_eq_one_of_zero (by rw [← hτ]; exact hf) hp0 ?_
    rw [Polynomial.deriv_aeval]
    exact hp.separable.aeval_derivative_ne_zero hp0
  rw [h1, one_mul]

include hm in
theorem pos_of_order_eq : 0 < m := by
  have h : analyticOrderAt (fun z => (jFun ∘ ofComplex) z - jFun τ₀) (τ₀ : ℂ) ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨(analyticAt_jFun τ₀).sub analyticAt_const, by simp [ofComplex_apply]⟩
  rw [hm] at h
  exact Nat.pos_of_ne_zero (by exact_mod_cast h)

theorem valuation_adicOfIrreducible_algebraMap {r : ℚ[X]} (hr : r ≠ 0) :
    (Place.adicOfIrreducible hq).valuation (algebraMap ℚ[X] (RatFunc ℚ) r) =
      WithZero.exp (-(multiplicity q r : ℤ)) := by
  rw [Place.valuation_eq_exp_neg_ord _ (RatFunc.algebraMap_ne_zero hr),
    Place.ord_adicOfIrreducible_algebraMap hq hr]

open scoped Classical in
include hq hroot hm in
/-- The order at $\tau_0$ of $r(j)$ is $m\, v_q(r)$, for polynomials. -/
theorem finVal_polyToMero (p : ℚ[X]) :
    finVal τ₀ (polyToMero τ₀ p) = (Place.adicOfIrreducible hq).valuation (algebraMap ℚ[X] (RatFunc ℚ) p) ^ m := by
  have hm0 := pos_of_order_eq τ₀ hm
  induction p using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [zero_pow hm0.ne']
  | h₂ u hu =>
    obtain ⟨a, ha, rfl⟩ := Polynomial.isUnit_iff.1 hu
    rw [finVal_polyToMero_of_aeval_ne_zero τ₀ (by simpa using ha.ne_zero),
      valuation_adicOfIrreducible_algebraMap hq (by simpa using ha.ne_zero)]
    rw [multiplicity_eq_zero_of_not_dvd (fun h => hq.not_isUnit (isUnit_of_dvd_unit h hu))]
    simp
  | h₃ a p ha hp ih =>
    rw [map_mul, map_mul, map_mul, map_mul, mul_pow, ih]
    congr 1
    by_cases hp0 : aeval (jFun τ₀) p = 0
    · rw [finVal_polyToMero_of_root τ₀ hm hp.irreducible hp0, Place.valuation_eq_exp_neg_ord _
        (RatFunc.algebraMap_ne_zero hp.ne_zero), Place.ord_adicOfIrreducible_algebraMap_irreducible hq hp.irreducible,
        ← WithZero.exp_nsmul]
      simp [associated_of_aeval_eq_zero τ₀ hq hroot hp.irreducible hp0]
    · rw [finVal_polyToMero_of_aeval_ne_zero τ₀ hp0, Place.valuation_eq_exp_neg_ord _
        (RatFunc.algebraMap_ne_zero hp.ne_zero), Place.ord_adicOfIrreducible_algebraMap_irreducible hq hp.irreducible,
        ite_eq_right_iff.2 fun hqp => absurd (Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hqp.dvd hroot) hp0]
      simp

include hq hroot hm in
/-- **The order valuation at $\tau_0$ induces $v_q^m$ on $\mathbb Q(j)$**, where $q(j(\tau_0)) = 0$ and $m$ is the
order of $j - j(\tau_0)$ at $\tau_0$. -/
theorem finVal_algebraMap (x : RatFunc ℚ) :
    finVal τ₀ (algebraMap (RatFunc ℚ) (FinField τ₀) x) = (Place.adicOfIrreducible hq).valuation x ^ m := by
  rw [algebraMap_finField, ratToMero, RatFunc.liftRingHom_apply, map_div₀,
    finVal_polyToMero τ₀ hq hroot hm, finVal_polyToMero τ₀ hq hroot hm, ← div_pow, ← map_div₀,
    RatFunc.num_div_denom]

end NumberFieldKB.ModularCurves
