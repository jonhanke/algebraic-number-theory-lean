import NumberFieldKB.ModularCurves.FiniteValuation

/-!
# $j : X_0(N) \to X_0(1)$ is unramified away from $j = 0, 1728, \infty$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). A place $P$ of $\mathbb Q(j)$ other than
$0, 1728, \infty$ is the place of an irreducible $q \in \mathbb Q[X]$ with a root $t = j(\tau_0) \notin \{0, 1728\}$
(as $j$ is onto). There $j - t$ has a simple zero (`analyticOrderAt_jFun_sub_eq_one`), so the order valuation at
$\tau_0$ induces $v_P^1$ on $\mathbb Q(j)$, and the scaling factor $c$ and the ramification index $e$ of every place
over $P$ satisfy $c\, e = 1$ (`FibreCount.lean`).
-/

open UpperHalfPlane hiding I
open Polynomial Filter Topology TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatRam : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- Every irreducible $q \in \mathbb Q[X]$ has a root of the form $j(\tau_0)$. -/
theorem exists_aeval_jFun_eq_zero {q : ℚ[X]} (hq : Irreducible q) : ∃ τ₀ : ℍ, aeval (jFun τ₀) q = 0 := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ q (degree_pos_of_irreducible hq).ne'
  obtain ⟨τ₀, rfl⟩ := jFun_surjective t
  exact ⟨τ₀, ht⟩

/-- If a rational number $a$ is a root of the irreducible $q$, then $q \sim X - a$. -/
theorem associated_X_sub_C_of_aeval {q : ℚ[X]} (hq : Irreducible q) {a : ℚ} (ha : aeval (a : ℂ) q = 0) :
    Associated (X - C a) q := by
  have h : q.eval a = 0 := by
    have := Polynomial.aeval_algebraMap_apply ℂ a q
    rw [show (algebraMap ℚ ℂ a) = (a : ℂ) from rfl, ha] at this
    have h2 : aeval a q = 0 := (algebraMap ℚ ℂ).injective (by rw [← this, map_zero])
    simpa [aeval_def] using h2
  exact (irreducible_X_sub_C a).associated_of_dvd hq (dvd_iff_isRoot.2 h)

variable (N : ℕ) [NeZero N]

/-- **$j$ is unramified away from $0, 1728, \infty$.** -/
theorem ramificationIdx_eq_one_of_ne (P' : Place ℚ (X0 N)) (h0 : P'.restrict ℚ (RatFunc ℚ) ≠ placeJ0)
    (h1728 : P'.restrict ℚ (RatFunc ℚ) ≠ placeJ1728) (hinf : P'.restrict ℚ (RatFunc ℚ) ≠ Place.infty ℚ) :
    Place.ramificationIdx (RatFunc ℚ) P' = 1 := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  rcases Place.eq_infty_or_exists_eq_adicOfIrreducible (P'.restrict ℚ (RatFunc ℚ)) with h | ⟨q, hq, hP⟩
  · exact absurd h hinf
  obtain ⟨τ₀, hroot⟩ := exists_aeval_jFun_eq_zero hq
  have ht0 : jFun τ₀ ≠ 0 := by
    intro ht
    apply h0
    rw [hP, placeJ0, Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
    have := associated_X_sub_C_of_aeval hq (a := 0) (by rw [Rat.cast_zero]; rw [ht] at hroot; exact hroot)
    simpa using this.symm
  have ht1728 : jFun τ₀ ≠ 1728 := by
    intro ht
    apply h1728
    rw [hP, placeJ1728, Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
    exact (associated_X_sub_C_of_aeval hq (a := 1728)
      (by rw [show ((1728 : ℚ) : ℂ) = 1728 by norm_num, ← ht]; exact hroot)).symm
  have hm := analyticOrderAt_jFun_sub_eq_one τ₀ ht0 ht1728
  have hvF : ∀ x : RatFunc ℚ, finVal τ₀ (algebraMap (RatFunc ℚ) (FinField τ₀) x) =
      (P'.restrict ℚ (RatFunc ℚ)).valuation x ^ (1 : ℕ) := by
    intro x
    rw [hP]
    exact finVal_algebraMap τ₀ hq hroot (m := 1) (by exact_mod_cast hm) x
  obtain ⟨i, hi⟩ := exists_placeOf_eq (isFunctionField_X0 N) hvF (finEmb τ₀ N) (finEmb_injective τ₀ N)
    (card_cosets_eq_finrank N) Nat.one_pos P' rfl
  have hs := scale_mul_ramificationIdx (isFunctionField_X0 N) hvF (finEmb τ₀ N i) Nat.one_pos
  rw [hi] at hs
  have hpos := scale_pos (isFunctionField_X0 N) hvF (finEmb τ₀ N i) Nat.one_pos
  have he := Place.ramificationIdx_pos (RatFunc ℚ) P'
  push_cast at hs
  have : (Place.ramificationIdx (RatFunc ℚ) P' : ℤ) = 1 := by
    have he' : (1 : ℤ) ≤ Place.ramificationIdx (RatFunc ℚ) P' := by exact_mod_cast he
    nlinarith
  exact_mod_cast this

open scoped Classical in
/-- The ramification of $j$ lies over $0, 1728, \infty$ (the hypothesis `hunr` of `genus_formula_of_fibres`). -/
theorem restrict_mem_of_ramified (P' : Place ℚ (X0 N)) (h : 1 < Place.ramificationIdx (RatFunc ℚ) P') :
    P'.restrict ℚ (RatFunc ℚ) ∈ ({placeJ0, placeJ1728, Place.infty ℚ} : Finset (Place ℚ (RatFunc ℚ))) := by
  by_contra hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmem
  rw [ramificationIdx_eq_one_of_ne N P' hmem.1 hmem.2.1 hmem.2.2] at h
  exact lt_irrefl _ h

end NumberFieldKB.ModularCurves
