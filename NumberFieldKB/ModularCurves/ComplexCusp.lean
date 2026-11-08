import NumberFieldKB.ModularCurves.ComplexRamification
import NumberFieldKB.ModularCurves.CuspCountX0

/-!
# The cusps of $\mathbb C(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). The complex version of
`InftyEmbedding.lean`, `CuspFibre.lean` and `CuspScale.lean`: $\mathbb C(j) \to \mathbb C((q))$, $j \mapsto J(q^N)$
induces $v_\infty^N$ (`valuation_ratFuncToLaurentC`); the embeddings $\sigma_c$ of $\mathbb Q(X_0(N))$ into
$\mathbb C((q))$ extend to $\mathbb C(X_0(N))$ (`cuspEmbC`); their images are still supported on
$\gcd(N, a_c^2)\mathbb Z$, so the scaling factor is $\gcd(N, a_c^2)$ (`scale_cuspEmbC`), and the number of cusps of
$\mathbb C(X_0(N))$ is $\nu_\infty = \sum_{g \mid N}\varphi(\gcd(g, N/g))$ (`geomCountC_infty_eq`).
-/

open Polynomial TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatCCusp : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

section Laurent

variable {s : LaurentSeries ℂ} {N : ℕ}

/-- $p \mapsto p(s)$, $\mathbb C[t] \to \mathbb C((q))$. -/
def polyToLaurentC (s : LaurentSeries ℂ) : ℂ[X] →+* LaurentSeries ℂ := Polynomial.eval₂RingHom HahnSeries.C s

theorem valuation_C_le (c : ℂ) : Valued.v (HahnSeries.C c : LaurentSeries ℂ) ≤ 1 := by
  have := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero (K := ℂ) (D := 0)
    (f := (HahnSeries.C c : LaurentSeries ℂ))).2
  rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl]
  apply this
  intro n hn
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (by omega)]

theorem valuation_C {c : ℂ} (hc : c ≠ 0) : Valued.v (HahnSeries.C c : LaurentSeries ℂ) = 1 := by
  have h1 := valuation_C_le c
  have h2 := valuation_C_le c⁻¹
  rw [map_inv₀ (HahnSeries.C : ℂ →+* LaurentSeries ℂ), map_inv₀] at h2
  have hne : Valued.v (HahnSeries.C c : LaurentSeries ℂ) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero (HahnSeries.C : ℂ →+* LaurentSeries ℂ)).2 hc)
  have h3 : 1 ≤ Valued.v (HahnSeries.C c : LaurentSeries ℂ) := by
    have := mul_le_mul' (le_refl (Valued.v (HahnSeries.C c : LaurentSeries ℂ))) h2
    rwa [mul_one, mul_inv_cancel₀ hne] at this
  exact le_antisymm h1 h3

/-- A nonzero polynomial of degree $n$ in $s$ has a pole of order $nN$. -/
theorem valuation_polyToLaurentC (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) {p : ℂ[X]} (hp : p ≠ 0) :
    Valued.v (polyToLaurentC s p) = WithZero.exp ((N : ℤ) * p.natDegree) := by
  induction' hn : p.natDegree using Nat.strong_induction_on with n ih generalizing p
  subst hn
  have hdec : p = p.eraseLead + C p.leadingCoeff * X ^ p.natDegree := (eraseLead_add_C_mul_X_pow p).symm
  have hlead : Valued.v (polyToLaurentC s (C p.leadingCoeff * X ^ p.natDegree)) =
      WithZero.exp ((N : ℤ) * p.natDegree) := by
    have hc := valuation_C (leadingCoeff_ne_zero.2 hp)
    have h : polyToLaurentC s (C p.leadingCoeff * X ^ p.natDegree) =
        HahnSeries.C p.leadingCoeff * s ^ p.natDegree := by
      simp [polyToLaurentC]
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
    have hlt : Valued.v (polyToLaurentC s p.eraseLead) <
        Valued.v (polyToLaurentC s (C p.leadingCoeff * X ^ p.natDegree)) := by
      rw [h1, hlead, WithZero.exp_lt_exp]
      have := eraseLead_natDegree_lt_or_eraseLead_eq_zero p |>.resolve_right he
      have h2 : ((p.eraseLead.natDegree : ℕ) : ℤ) < p.natDegree := by exact_mod_cast this
      nlinarith
    conv_lhs => rw [hdec, map_add]
    rw [Valuation.map_add_eq_of_lt_right _ hlt, hlead]

theorem polyToLaurentC_injective (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) :
    Function.Injective (polyToLaurentC s) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have h := valuation_polyToLaurentC hs hN hp0
  rw [hp, map_zero] at h
  exact WithZero.exp_ne_zero h.symm

/-- $\mathbb C(t) \to \mathbb C((q))$, $t \mapsto s$. -/
def ratFuncToLaurentC (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) : RatFunc ℂ →+* LaurentSeries ℂ :=
  RatFunc.liftRingHom (polyToLaurentC s)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyToLaurentC_injective hs hN))

theorem ratFuncToLaurentC_algebraMap (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) (p : ℂ[X]) :
    ratFuncToLaurentC hs hN (algebraMap ℂ[X] (RatFunc ℂ) p) = polyToLaurentC s p := by
  rw [ratFuncToLaurentC, RatFunc.liftRingHom_apply, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- **The valuation of $\mathbb C((q))$ on $\mathbb C(j)$ is $v_\infty^N$.** -/
theorem valuation_ratFuncToLaurentC (hs : Valued.v s = WithZero.exp (N : ℤ)) (hN : 1 ≤ N) (x : RatFunc ℂ) :
    Valued.v (ratFuncToLaurentC hs hN x) = (TauCeti.Place.infty ℂ).valuation x ^ N := by
  by_cases hx : x = 0
  · subst hx
    rw [map_zero, map_zero, map_zero, zero_pow (by omega)]
  · rw [ratFuncToLaurentC, RatFunc.liftRingHom_apply, map_div₀,
      valuation_polyToLaurentC hs hN (RatFunc.num_ne_zero hx),
      valuation_polyToLaurentC hs hN x.denom_ne_zero, TauCeti.Place.valuation_infty_apply hx,
      RatFunc.intDegree, ← WithZero.exp_sub, ← WithZero.exp_nsmul]
    congr 1
    push_cast [nsmul_eq_mul]
    ring

theorem polyToLaurentC_map (p : ℚ[X]) : polyToLaurentC s (p.map (algebraMap ℚ ℂ)) = polyToLaurent s p := by
  rw [polyToLaurentC, polyToLaurent, coe_eval₂RingHom, coe_eval₂RingHom, eval₂_map]
  congr 1
  exact RingHom.ext_rat _ _

end Laurent

variable (N : ℕ) [NeZero N]

/-- $j \mapsto J(q^N)$ on $\mathbb C(j)$. -/
def jToLaurentC : RatFunc ℂ →+* LaurentSeries ℂ := ratFuncToLaurentC (valuation_jNSer' N) (one_le_N N)

instance : Algebra (RatFunc ℂ) (CuspField N) := (jToLaurentC N).toAlgebra

theorem cuspValC_algebraMap (x : RatFunc ℂ) :
    lVal N (algebraMap (RatFunc ℂ) (CuspField N) x) = (Place.infty ℂ).valuation x ^ N :=
  valuation_ratFuncToLaurentC (valuation_jNSer' N) (one_le_N N) x

theorem jToLaurentC_comp :
    (algebraMap (RatFunc ℂ) (CuspField N)).comp ratFuncQC = algebraMap (RatFunc ℚ) (CuspField N) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X]) (RingHom.ext fun p => ?_)
  change jToLaurentC N (ratFuncQC (algebraMap ℚ[X] (RatFunc ℚ) p)) = jToLaurent N (algebraMap ℚ[X] (RatFunc ℚ) p)
  rw [ratFuncQC_algebraMap, polyQC, RingHom.comp_apply, jToLaurentC, jToLaurent, ratFuncToLaurentC_algebraMap,
    ratFuncToLaurent_algebraMap]
  exact polyToLaurentC_map p

/-- **The embedding $\sigma_c$ of $\mathbb C(X_0(N))$ at the cusp**: $j \mapsto J(q^N)$, $j_N \mapsto Y_c$. -/
def cuspEmbC (c : Cosets N) : X0C N →ₐ[RatFunc ℂ] CuspField N := extC (jToLaurentC_comp N) (cuspEmb N c)

theorem cuspEmbC_injective : Function.Injective (cuspEmbC N) :=
  extC_injective (jToLaurentC_comp N) (cuspEmb_injective N)

theorem cuspEmbC_root (c : Cosets N) : cuspEmbC N c (AdjoinRoot.root _) = ySer N c := by
  rw [cuspEmbC, extC_root, cuspEmb_root]

/-! ### The supports and the scaling factors -/

theorem C_mem_supportMultiples {g : ℕ} (hg : 0 < g) (c : ℂ) : (HahnSeries.C c : LaurentSeries ℂ) ∈ supportMultiples hg := by
  refine mem_supportMultiples_of_coeff hg fun n hn => ?_
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_of_ne]
  rintro rfl
  exact hn (dvd_zero _)

theorem polyToLaurentC_mem {g : ℕ} (hg : 0 < g) {s : LaurentSeries ℂ} (hs : s ∈ supportMultiples hg) (p : ℂ[X]) :
    polyToLaurentC s p ∈ supportMultiples hg := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [polyToLaurentC, coe_eval₂RingHom, eval₂_C]
    exact C_mem_supportMultiples hg a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ =>
    rw [polyToLaurentC, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow]
    exact mul_mem (C_mem_supportMultiples hg a) (pow_mem hs _)

theorem jToLaurentC_mem_cuspSupport (c : Cosets N) (x : RatFunc ℂ) : jToLaurentC N x ∈ cuspSupport N c := by
  rw [← RatFunc.num_div_denom x, map_div₀, jToLaurentC, ratFuncToLaurentC_algebraMap,
    ratFuncToLaurentC_algebraMap]
  exact div_mem (polyToLaurentC_mem _ (jNSer_mem_cuspSupport N c) _)
    (polyToLaurentC_mem _ (jNSer_mem_cuspSupport N c) _)

/-- **The image of $\sigma_c$ on $\mathbb C(X_0(N))$ is supported on $\gcd(N, a_c^2)\mathbb Z$.** -/
theorem cuspEmbC_mem_cuspSupport (c : Cosets N) (x : X0C N) :
    (cuspEmbC N c x : LaurentSeries ℂ) ∈ cuspSupport N c := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have e : cuspEmbC N c (AdjoinRoot.mk _ p) =
        Polynomial.eval₂ (algebraMap (RatFunc ℂ) (CuspField N)) (ySer N c) p := by
      rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, cuspEmbC_root, Polynomial.aeval_def]
    rw [e]
    clear e
    change Polynomial.eval₂ (jToLaurentC N) (qHat (numC N c) / qHat (denC N c)) p ∈ cuspSupport N c
    induction p using Polynomial.induction_on with
    | C a =>
      rw [eval₂_C]
      exact jToLaurentC_mem_cuspSupport N c a
    | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
    | monomial n a _ =>
      rw [eval₂_mul, eval₂_C, eval₂_X_pow]
      exact mul_mem (jToLaurentC_mem_cuspSupport N c a) (pow_mem (ySer_mem_cuspSupport N c) _)

/-- **The scaling factor of $\sigma_c$ on $\mathbb C(X_0(N))$ is $\gcd(N, a_c^2)$.** -/
theorem scale_cuspEmbC (c : Cosets N) :
    scale (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N) = cuspGcd N c := by
  set s := scale (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)
  set Q := placeOf (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)
  have hspos : 0 < s := scale_pos _ _ _ _
  have h1 : (cuspGcd N c : ℤ) ∣ s := by
    obtain ⟨t, ht⟩ := Q.exists_isUniformizer
    have ht1 : Q.ord t = 1 := Q.isUniformizer_iff_ord_eq_one.1 ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht1
    have hv := valuation_apply_eq_exp (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c)
      (one_le_N N) ht0
    have hσ0 : (cuspEmbC N c t : LaurentSeries ℂ) ≠ 0 :=
      (map_ne_zero_iff _ (cuspEmbC N c).toRingHom.injective).2 ht0
    obtain ⟨k, hk⟩ := exists_valuation_eq_of_mem_supportMultiples (cuspGcd_pos N c)
      (cuspEmbC_mem_cuspSupport N c t) hσ0
    have hk' : lVal N (cuspEmbC N c t) = WithZero.exp ((cuspGcd N c : ℤ) * k) := hk
    rw [hv, ht1, mul_one, WithZero.exp_inj] at hk'
    exact ⟨-k, by linarith⟩
  have h2 : s ∣ (cuspGcd N c : ℤ) := by
    have h := scale_extC_dvd (jToLaurentC_comp N) (cuspVal_algebraMap N) (cuspValC_algebraMap N) (cuspEmb N c)
      (one_le_N N)
    rwa [scale_cuspEmb] at h
  exact Int.dvd_antisymm hspos.le (by positivity) h2 h1

/-- The geometric count of the cusps of $\mathbb C(X_0(N))$. -/
theorem geomCountC_infty_eq :
    geomCountC N (TauCeti.Place.infty ℂ) = ∑ g ∈ N.divisors, Nat.totient (Nat.gcd g (N / g)) := by
  have h := mul_sum_relativeDegree_eq (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N)
    (cuspEmbC_injective N) (card_cosets_eq_finrankC N) (one_le_N N)
  simp_rw [scale_cuspEmbC] at h
  have h' : N * geomCountC N (Place.infty ℂ) = ∑ c, cuspGcd N c := by
    rw [geomCountC]
    exact_mod_cast h
  rw [sum_cuspGcd] at h'
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne N)) h'

end NumberFieldKB.ModularCurves
