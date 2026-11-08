import NumberFieldKB.ModularCurves.CuspFibre

/-!
# The widths of the cusps of $X_0(N)$: $c(\sigma_c) = \gcd(N, a_c^2)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf pp. 192–196). With the embeddings
$\sigma_c : \mathbb Q(X_0(N)) \to \mathbb C((q))$ of `CuspFibre.lean` ($j \mapsto J(q^N)$, $j_N \mapsto Y_c$, where
$Y_c$ is the expansion of $j(a_c^2\tau + b_c/d_c)$), the valuation of $\mathbb C((q))$ restricts to
$c(\sigma_c) \operatorname{ord}_{P'_c}$ on $\mathbb Q(X_0(N))$. This file computes $c(\sigma_c) = \gcd(N, a_c^2)$
(`scale_cuspEmb`):

* the image of $\sigma_c$ consists of Laurent series supported on $\gcd(N, a_c^2)\mathbb Z$ (the expansions of
  $J(q^N)$ and of $Y_c$ involve only powers $q^{Nk}$, resp. $q^{a_c^2 k}$), so $\gcd(N, a_c^2) \mid c(\sigma_c)$;
* $c(\sigma_c)\, e(P'_c) = N$ and $Y_c$ has a pole of order exactly $a_c^2$ (`valuation_ySer`), so
  $c(\sigma_c) \mid N$ and $c(\sigma_c) \mid a_c^2$.

Hence the cusp $P'_c$ has ramification index (width) $N / \gcd(N, a_c^2)$ (`ramificationIdx_placeOf_cuspEmb`), and
$N \sum_{P' \mid \infty} f(P') = \sum_c \gcd(N, a_c^2)$ (`mul_geomCount_infty_eq_sum_gcd`).
-/

open UpperHalfPlane hiding I
open Polynomial Complex ModularForm TauCeti
open scoped MatrixGroups WithZero Real

noncomputable section

namespace NumberFieldKB.ModularCurves

open NumberFieldKB.MilneEC.V

/-! ### Supports and valuations of $q$-expansions -/

/-- The expansion of $f(m\tau)$ involves only the powers $q^{mk}$. -/
theorem qHat_scaleN_mem_supportMultiples {m : ℕ} (hm : 1 ≤ m) {f : ℍ → ℂ} (hf : IsQExp f) :
    qHat (scaleN m f) ∈ supportMultiples (g := m) hm := by
  refine mem_supportMultiples_of_coeff hm fun n hn => ?_
  rcases lt_or_ge n 0 with h0 | h0
  · exact ofPowerSeries_coeff_neg _ h0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [qHat, HahnSeries.ofPowerSeries_apply_coeff, qExpansion_scaleN_coeff hm hf]
    have : ¬ m ∣ k := fun h => hn (Int.natCast_dvd_natCast.2 h)
    simp only [dilateCoeff, this, ite_false]

/-- Power series whose coefficients differ by nonzero factors have the same valuation. -/
theorem valuation_ofPowerSeries_eq_of_coeff {F G : PowerSeries ℂ} (u : ℕ → ℂ) (hu : ∀ n, u n ≠ 0)
    (h : ∀ n, F.coeff n = u n * G.coeff n) :
    Valued.v (HahnSeries.ofPowerSeries ℤ ℂ F) = Valued.v (HahnSeries.ofPowerSeries ℤ ℂ G) := by
  classical
  by_cases hG : ∃ n, G.coeff n ≠ 0
  · have hn := Nat.find_spec hG
    have hlt : ∀ i < Nat.find hG, G.coeff i = 0 := fun i hi => not_not.1 (Nat.find_min hG hi)
    rw [valuation_ofPowerSeries hn hlt, valuation_ofPowerSeries (n := Nat.find hG)
      (by rw [h]; exact mul_ne_zero (hu _) hn) (fun i hi => by rw [h, hlt i hi, mul_zero])]
  · push Not at hG
    have hG0 : G = 0 := PowerSeries.ext fun n => by rw [hG n, map_zero]
    have hF0 : F = 0 := PowerSeries.ext fun n => by rw [h, hG n, mul_zero, map_zero]
    rw [hF0, hG0]

/-- A real shift does not change the order at $\infty$ of the expansion of $f(m\tau)$. -/
theorem valuation_qHat_scaleN_shiftR {m : ℕ} (hm : 1 ≤ m) {f : ℍ → ℂ} (hf : IsQExp f) (r : ℝ) :
    Valued.v (qHat (scaleN m (shiftR r f))) = Valued.v (qHat (scaleN m f)) := by
  classical
  refine valuation_ofPowerSeries_eq_of_coeff
    (fun n => if m ∣ n then cexp (2 * π * I * ((n / m : ℕ) : ℂ) * r) else 1)
    (fun n => by split_ifs <;> simp [Complex.exp_ne_zero]) fun n => ?_
  rw [qExpansion_scaleN_coeff hm (hf.shift r), qExpansion_scaleN_coeff hm hf]
  simp only [dilateCoeff]
  split_ifs with hd
  · exact qExpansion_shift_coeff hf r _
  · rw [mul_zero]

/-! ### The image of $\sigma_c$ -/

variable (N : ℕ) [NeZero N]

local instance (priority := high) ratFuncAlgebraRatCuspScale : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

theorem valuation_qHat_numC (c : Cosets N) : Valued.v (qHat (numC N c)) = 1 := by
  rw [numC, valuation_qHat_scaleN_shiftR (one_le_cosetA_sq N c) isQExp_cubeE4,
    valuation_qHat_scaleN_cubeE4 (one_le_cosetA_sq N c)]

theorem valuation_qHat_denC (c : Cosets N) :
    Valued.v (qHat (denC N c)) = WithZero.exp (-((cosetA N c ^ 2 : ℕ) : ℤ)) := by
  rw [denC, valuation_qHat_scaleN_shiftR (one_le_cosetA_sq N c) isQExp_discFun,
    valuation_qHat_scaleN_discFun (one_le_cosetA_sq N c)]

/-- **$Y_c$ has a pole of order $a_c^2$.** -/
theorem valuation_ySer (c : Cosets N) :
    Valued.v (qHat (numC N c) / qHat (denC N c)) = WithZero.exp ((cosetA N c ^ 2 : ℕ) : ℤ) := by
  rw [map_div₀, valuation_qHat_numC, valuation_qHat_denC, one_div, ← WithZero.exp_neg, neg_neg]

theorem ySer_ne_zero (c : Cosets N) : ySer N c ≠ 0 := by
  intro h
  have := valuation_ySer N c
  change ySer N c = (0 : LaurentSeries ℂ) at h
  rw [show qHat (numC N c) / qHat (denC N c) = (0 : LaurentSeries ℂ) from h, map_zero] at this
  exact WithZero.zero_ne_coe this

/-- $\gcd(N, a_c^2)$. -/
def cuspGcd (c : Cosets N) : ℕ := Nat.gcd N (cosetA N c ^ 2)

theorem cuspGcd_pos (c : Cosets N) : 0 < cuspGcd N c := Nat.gcd_pos_of_pos_left _ (one_le_N N)

/-- The subfield of Laurent series supported on $\gcd(N, a_c^2)\mathbb Z$. -/
abbrev cuspSupport (c : Cosets N) : Subfield (LaurentSeries ℂ) := supportMultiples (cuspGcd_pos N c)

theorem jNSer_mem_cuspSupport (c : Cosets N) : jNSer N ∈ cuspSupport N c := by
  have hle := supportMultiples_le (cuspGcd_pos N c) (one_le_N N) (Nat.gcd_dvd_left _ _)
  exact div_mem (hle (qHat_scaleN_mem_supportMultiples (one_le_N N) isQExp_cubeE4))
    (hle (qHat_scaleN_mem_supportMultiples (one_le_N N) isQExp_discFun))

theorem ySer_mem_cuspSupport (c : Cosets N) : qHat (numC N c) / qHat (denC N c) ∈ cuspSupport N c := by
  have hle := supportMultiples_le (cuspGcd_pos N c) (one_le_cosetA_sq N c) (Nat.gcd_dvd_right _ _)
  exact div_mem (hle (qHat_scaleN_mem_supportMultiples _ ((isQExp_cubeE4.shift _))))
    (hle (qHat_scaleN_mem_supportMultiples _ ((isQExp_discFun.shift _))))

theorem polyToLaurent_mem (S : Subfield (LaurentSeries ℂ)) {s : LaurentSeries ℂ} (hs : s ∈ S) (p : ℚ[X]) :
    polyToLaurent s p ∈ S := by
  induction p using Polynomial.induction_on with
  | C a =>
    rw [polyToLaurent, coe_eval₂RingHom, eval₂_C, eq_ratCast]
    exact SubfieldClass.ratCast_mem S a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a _ =>
    rw [polyToLaurent, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow, eq_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem S a) (pow_mem hs _)

theorem jToLaurent_mem_cuspSupport (c : Cosets N) (x : RatFunc ℚ) : jToLaurent N x ∈ cuspSupport N c := by
  rw [← RatFunc.num_div_denom x, map_div₀, jToLaurent, ratFuncToLaurent_algebraMap,
    ratFuncToLaurent_algebraMap]
  exact div_mem (polyToLaurent_mem _ (jNSer_mem_cuspSupport N c) _)
    (polyToLaurent_mem _ (jNSer_mem_cuspSupport N c) _)

/-- **The image of $\sigma_c$ is supported on $\gcd(N, a_c^2)\mathbb Z$.** -/
theorem cuspEmb_mem_cuspSupport (c : Cosets N) (x : X0 N) :
    (cuspEmb N c x : LaurentSeries ℂ) ∈ cuspSupport N c := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    change Polynomial.eval₂ (jToLaurent N) (qHat (numC N c) / qHat (denC N c)) p ∈ cuspSupport N c
    induction p using Polynomial.induction_on with
    | C a =>
      rw [eval₂_C]
      exact jToLaurent_mem_cuspSupport N c a
    | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
    | monomial n a _ =>
      rw [eval₂_mul, eval₂_C, eval₂_X_pow]
      exact mul_mem (jToLaurent_mem_cuspSupport N c a) (pow_mem (ySer_mem_cuspSupport N c) _)

/-! ### The scaling factor -/

/-- **The scaling factor of $\sigma_c$ is $\gcd(N, a_c^2)$.** -/
theorem scale_cuspEmb (c : Cosets N) :
    scale (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N) = cuspGcd N c := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  set s := scale (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N) with hs
  set Q := placeOf (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N)
  have hspos : 0 < s := scale_pos _ _ _ _
  -- $\gcd(N, a^2) \mid s$
  have h1 : (cuspGcd N c : ℤ) ∣ s := by
    obtain ⟨t, ht⟩ := Q.exists_isUniformizer
    have ht1 : Q.ord t = 1 := Q.isUniformizer_iff_ord_eq_one.1 ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht1
    have hv := valuation_apply_eq_exp (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N) ht0
    have hσ0 : (cuspEmb N c t : LaurentSeries ℂ) ≠ 0 := (map_ne_zero_iff _ (cuspEmb N c).toRingHom.injective).2 ht0
    obtain ⟨k, hk⟩ := exists_valuation_eq_of_mem_supportMultiples (cuspGcd_pos N c)
      (cuspEmb_mem_cuspSupport N c t) hσ0
    have hk' : lVal N (cuspEmb N c t) = WithZero.exp ((cuspGcd N c : ℤ) * k) := hk
    rw [hv, ht1, mul_one, WithZero.exp_inj] at hk'
    exact ⟨-k, by linarith⟩
  -- $s \mid N$
  have h2 : s ∣ (N : ℤ) := by
    have := scale_mul_ramificationIdx (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N)
    exact ⟨_, this.symm⟩
  -- $s \mid a^2$
  have h3 : s ∣ ((cosetA N c ^ 2 : ℕ) : ℤ) := by
    have hr0 : (AdjoinRoot.root _ : X0 N) ≠ 0 := by
      intro h0
      have := cuspEmb_root N c
      rw [h0, map_zero] at this
      exact ySer_ne_zero N c this.symm
    have hv := valuation_apply_eq_exp (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N) hr0
    rw [cuspEmb_root] at hv
    change Valued.v (qHat (numC N c) / qHat (denC N c)) = _ at hv
    rw [valuation_ySer, WithZero.exp_inj] at hv
    exact ⟨-Q.ord (AdjoinRoot.root _), by rw [hv]; ring⟩
  have h4 : s ∣ (cuspGcd N c : ℤ) := by
    have := Int.dvd_coe_gcd h2 h3
    rwa [Int.gcd_natCast_natCast] at this
  exact Int.dvd_antisymm hspos.le (by positivity) h4 h1

/-- **The width of the cusp of $\sigma_c$**: $e(P'_c) \gcd(N, a_c^2) = N$. -/
theorem cuspGcd_mul_ramificationIdx (c : Cosets N) :
    (cuspGcd N c : ℤ) * Place.ramificationIdx (RatFunc ℚ)
      (placeOf (isFunctionField_X0 N) (cuspVal_algebraMap N) (cuspEmb N c) (one_le_N N)) = N := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  rw [← scale_cuspEmb]
  exact scale_mul_ramificationIdx _ _ _ _

/-- **The cusps of $X_0(N)$**: $N \sum_{P' \mid \infty} f(P') = \sum_c \gcd(N, a_c^2)$. -/
theorem mul_geomCount_infty_eq_sum_gcd :
    N * geomCount N (Place.infty ℚ) = ∑ c, cuspGcd N c := by
  have h := mul_geomCount_infty_eq_sum_scale N
  simp_rw [scale_cuspEmb] at h
  exact_mod_cast h

end NumberFieldKB.ModularCurves
