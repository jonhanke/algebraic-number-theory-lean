import NumberFieldKB.ModularCurves.HeckeX0

/-!
# Ramification indices of places of $X_0$ and of primes of $Y_0$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 and Ch. V, §7. For the forgetful map $z \mapsto z$,
$X_0(M) \to X_0(N)$, and a point $Q$ of $Y_0(M)$ over a point $P$ of $Y_0(N)$, the ramification index of places,
$e(Q/P) = \operatorname{ord}_Q(t_P)$ (`ramIndex`), is Mathlib's ramification index of the prime $Q$ of
$\mathcal O(Y_0(M))$ over $\mathcal O(Y_0(N))$ (`ramIndex_toPlace`). This uses Mathlib's
`HeightOneSpectrum.valuation_liesOver`, $v_P(x)^{e} = v_Q(x)$.
-/

open Polynomial IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC

variable {N M : ℕ} [NeZero N] [NeZero M]

/-- The valuation ring of the place of a point of $Y_0$ is the valuation ring of its adic valuation. -/
theorem toPlace_O_eq (P : Y0Point N) : P.toPlace.O = (P.valuation (X0 N)).valuationSubring :=
  valuationSubringAtPrime_eq_valuationSubring P

/-- Milne's $\operatorname{ord}$ at the place of a point of $Y_0$ is the order of the adic valuation. -/
theorem ord_toPlace (P : Y0Point N) {x : X0 N} (hx : x ≠ 0) :
    P.toPlace.ord x = ordV (P.valuation (X0 N)) x := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer (X0 N)
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.zero_ne_coe hπ
  refine PrimeDivisor.ord_eq_ordV _ _ (toPlace_O_eq P) hπ0 ?_ hx
  rw [ordV, hπ, WithZero.log_exp, neg_neg]

/-- The order of a uniformizer is 1. -/
theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.ord_unif {k K : Type*} [Field k] [Field K] [Algebra k K]
    (P : PrimeDivisor k K) :
    P.ord P.unif = 1 :=
  PrimeDivisor.ord_eq_of_rep P (u := 1) (n := 1) (by simp)

theorem _root_.NumberFieldKB.MilneEC.PrimeDivisor.unif_ne_zero {k K : Type*} [Field k] [Field K] [Algebra k K]
    (P : PrimeDivisor k K) :
    P.unif ≠ 0 := by
  obtain ⟨t, ht, e⟩ := P.exists_uniO
  rw [← e]
  exact fun h0 => ht.ne_zero (Subtype.ext h0)

/-- **Ramification indices agree**: for a point $Q$ of $Y_0(M)$ over a point $P$ of $Y_0(N)$ ($z \mapsto z$),
$\operatorname{ord}_Q(t_P)$ is the ramification index of the prime $Q$ over $\mathcal O(Y_0(N))$. -/
theorem ramIndex_toPlace (h : 1 * N ∣ M) (P : Y0Point N) (Q : Y0Point M) (hQ : degeneracyPoint h Q = P) :
    letI := forgetY0Algebra N M h
    ramIndex h P.toPlace Q.toPlace = Q.asIdeal.ramificationIdx (Y0Ring N) := by
  letI := forgetY0Algebra N M h
  letI := forgetAlgebra N M h
  letI : Algebra (Y0Ring N) (X0 M) :=
    ((algebraMap (X0 N) (X0 M)).comp (algebraMap (Y0Ring N) (X0 N))).toAlgebra
  haveI t1 : @IsScalarTower (Y0Ring N) (X0 N) (X0 M) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI t2 : @IsScalarTower (Y0Ring N) (Y0Ring M) (X0 M) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := isTorsionFree_forgetY0 h
  haveI : Q.asIdeal.LiesOver P.asIdeal := ⟨by rw [← hQ]; rfl⟩
  have hv := valuation_liesOver (X0 M) P Q P.toPlace.unif (K := X0 N)
  have ht0 : P.toPlace.unif ≠ 0 := P.toPlace.unif_ne_zero
  have hιt0 : degeneracy N M 1 h P.toPlace.unif ≠ 0 :=
    (map_ne_zero_iff _ (degeneracy N M 1 h).injective).2 ht0
  have h1 : ordV (P.valuation (X0 N)) P.toPlace.unif = 1 := by
    rw [← ord_toPlace P ht0]
    exact P.toPlace.ord_unif
  unfold ramIndex
  refine (ord_toPlace Q hιt0).trans ?_
  change ordV (Q.valuation (X0 M)) (algebraMap (X0 N) (X0 M) P.toPlace.unif) = _
  have hv' : Q.valuation (X0 M) (algebraMap (X0 N) (X0 M) P.toPlace.unif) =
      P.valuation (X0 N) P.toPlace.unif ^ Q.asIdeal.ramificationIdx (Y0Ring N) := hv.symm
  rw [ordV, hv', WithZero.log_pow, nsmul_eq_mul]
  have : -WithZero.log (P.valuation (X0 N) P.toPlace.unif) = 1 := h1
  rw [← mul_neg, this, mul_one]

end NumberFieldKB.ModularCurves
