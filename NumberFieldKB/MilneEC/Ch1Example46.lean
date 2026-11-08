import NumberFieldKB.MilneEC.Ch1Functions
import Mathlib.NumberTheory.RatFunc.Ostrowski

/-!
# Milne, Elliptic Curves, Chapter I, Example 4.6: the projective line has genus 0

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, §4, Example 4.6 (pdf p. 41), for the function field
`RatFunc k` of the projective line over an algebraically closed field, with the divisors of `Ch1Functions`.
-/

open MvPolynomial
open WithZero

noncomputable section

namespace NumberFieldKB.MilneEC

variable {k : Type*} [Field k]

/-! ### Auxiliary valuation lemmas and the prime divisors of `k(X)` -/

section Valuations

variable {K : Type*} [Field K]

/-- The additive order of a valuation with values in `ℤᵐ⁰`: $-\log w(\varphi)$. -/
def ordV (w : Valuation K ℤᵐ⁰) (φ : K) : ℤ := - WithZero.log (w φ)

theorem ordV_mul (w : Valuation K ℤᵐ⁰) {φ ψ : K} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ordV w (φ * ψ) = ordV w φ + ordV w ψ := by
  unfold ordV
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff w).mpr hφ) ((Valuation.ne_zero_iff w).mpr hψ)]
  ring

theorem ordV_inv (w : Valuation K ℤᵐ⁰) (φ : K) : ordV w φ⁻¹ = - ordV w φ := by
  unfold ordV
  rw [map_inv₀, WithZero.log_inv]

theorem ordV_zpow (w : Valuation K ℤᵐ⁰) (φ : K) (n : ℤ) : ordV w (φ ^ n) = n * ordV w φ := by
  unfold ordV
  rw [map_zpow₀, WithZero.log_zpow, smul_eq_mul]
  ring

theorem ordV_div (w : Valuation K ℤᵐ⁰) {φ ψ : K} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    ordV w (φ / ψ) = ordV w φ - ordV w ψ := by
  rw [div_eq_mul_inv, ordV_mul w hφ (inv_ne_zero hψ), ordV_inv]
  ring

theorem ordV_one (w : Valuation K ℤᵐ⁰) : ordV w 1 = 0 := by
  simp [ordV]

theorem ordV_prod (w : Valuation K ℤᵐ⁰) {ι : Type*} (s : Finset ι) (f : ι → K)
    (hf : ∀ i ∈ s, f i ≠ 0) : ordV w (∏ i ∈ s, f i) = ∑ i ∈ s, ordV w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ordV_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ordV_mul w (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem le_one_iff_ordV (w : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) :
    w x ≤ 1 ↔ 0 ≤ ordV w x := by
  have h0 : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
  unfold ordV
  conv_lhs => rw [← WithZero.exp_log h0, ← WithZero.exp_zero (M := ℤ)]
  rw [WithZero.exp_le_exp]
  omega

theorem lt_one_iff_ordV (w : Valuation K ℤᵐ⁰) {x : K} (hx : x ≠ 0) :
    w x < 1 ↔ 0 < ordV w x := by
  have h0 : w x ≠ 0 := (Valuation.ne_zero_iff w).mpr hx
  unfold ordV
  conv_lhs => rw [← WithZero.exp_log h0, ← WithZero.exp_zero (M := ℤ)]
  rw [WithZero.exp_lt_exp]
  omega

variable [Algebra k K]

theorem PrimeDivisor.ord_eq_of_rep (p : PrimeDivisor k K) {φ : K} {n : ℤ} {u : p.Oˣ}
    (h : φ = ((u : p.O) : K) * p.unif ^ n) : p.ord φ = n := by
  have H : ∃ n : ℤ, ∃ u : p.Oˣ, φ = (u : K) * p.unif ^ n := ⟨n, u, h⟩
  unfold PrimeDivisor.ord
  simp only [H, ↓reduceDIte]
  obtain ⟨u', hu'⟩ := H.choose_spec
  exact p.rep_unique (hu'.symm.trans h)

theorem PrimeDivisor.mem_iff_valuation (p : PrimeDivisor k K) (w : Valuation K ℤᵐ⁰)
    (hO : p.O = w.valuationSubring) (x : K) : x ∈ p.O ↔ w x ≤ 1 := by
  rw [hO]
  exact Valuation.mem_valuationSubring_iff w x

theorem PrimeDivisor.val_unit_eq_one (p : PrimeDivisor k K) (w : Valuation K ℤᵐ⁰)
    (hO : p.O = w.valuationSubring) (u : p.Oˣ) : w ((u : p.O) : K) = 1 := by
  have h1 : w ((u : p.O) : K) ≤ 1 := (p.mem_iff_valuation w hO _).mp (u : p.O).2
  have h2 : w (((u⁻¹ : p.Oˣ) : p.O) : K) ≤ 1 :=
    (p.mem_iff_valuation w hO _).mp ((u⁻¹ : p.Oˣ) : p.O).2
  have h3 : w ((u : p.O) : K) * w (((u⁻¹ : p.Oˣ) : p.O) : K) = 1 := by
    rw [← map_mul]
    have : (((u : p.O) : K) * (((u⁻¹ : p.Oˣ) : p.O) : K)) = 1 :=
      congrArg (fun x : p.O => (x : K)) (u.mul_inv)
    rw [this, map_one]
  have h4 : w ((u : p.O) : K) * w (((u⁻¹ : p.Oˣ) : p.O) : K) ≤ w ((u : p.O) : K) * 1 :=
    mul_le_mul' le_rfl h2
  rw [h3, mul_one] at h4
  exact le_antisymm h1 h4

/-- A prime divisor whose ring is the valuation ring of a `ℤᵐ⁰`-valued valuation `w`, with some
element of `w`-order one, has `ord = ordV w`. -/
theorem PrimeDivisor.ord_eq_ordV (p : PrimeDivisor k K) (w : Valuation K ℤᵐ⁰)
    (hO : p.O = w.valuationSubring) {φ0 : K} (hφ0 : φ0 ≠ 0) (h1 : ordV w φ0 = 1) {φ : K}
    (hφ : φ ≠ 0) : p.ord φ = ordV w φ := by
  have := p.isDVR
  have hmem := p.mem_iff_valuation w hO
  obtain ⟨t, ht, htu⟩ := p.exists_uniO
  have ht0 : p.unif ≠ 0 := by
    rw [← htu]
    intro h0
    exact ht.ne_zero (Subtype.ext h0)
  have hwu := p.val_unit_eq_one w hO
  -- the valuation of the uniformizer
  have hwt1 : w p.unif ≤ 1 := (hmem _).mp (by rw [← htu]; exact t.2)
  have hwt0 : w p.unif ≠ 0 := (Valuation.ne_zero_iff w).mpr ht0
  have hwt2 : w p.unif ≠ 1 := by
    intro h
    apply ht.not_isUnit
    have hinv : p.unif⁻¹ ∈ p.O := (hmem _).mpr (by rw [map_inv₀, h]; simp)
    refine IsUnit.of_mul_eq_one (⟨p.unif⁻¹, hinv⟩ : p.O) ?_
    apply Subtype.ext
    show (t : K) * p.unif⁻¹ = 1
    rw [htu]
    exact mul_inv_cancel₀ ht0
  have hwt3 : w p.unif < 1 := lt_of_le_of_ne hwt1 hwt2
  set c : ℤ := WithZero.log (w p.unif) with hc
  have hwtc : w p.unif = exp c := (WithZero.exp_log hwt0).symm
  have hcneg : c < 0 := by
    have : exp c < exp (0 : ℤ) := by rw [← hwtc]; simpa using hwt3
    exact WithZero.exp_lt_exp.mp this
  have key : ∀ ψ : K, ψ ≠ 0 → ordV w ψ = - c * p.ord ψ := by
    intro ψ hψ
    obtain ⟨n, u, hn⟩ := p.exists_rep hψ
    rw [p.ord_eq_of_rep hn]
    unfold ordV
    rw [hn, map_mul, hwu, one_mul, map_zpow₀, hwtc, WithZero.log_zpow]
    simp
    ring
  have h0 := key φ0 hφ0
  rw [h1] at h0
  have hc1 : c = -1 := by
    have h5 : (-c) * p.ord φ0 = 1 := h0.symm
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ h5) with h6 | h6
    · omega
    · omega
  rw [key φ hφ, hc1]
  ring

end Valuations

section RatFuncPlaces

open Polynomial IsDedekindDomain

theorem alg_ne_zero {f : k[X]} (hf : f ≠ 0) : algebraMap k[X] (RatFunc k) f ≠ 0 :=
  fun h => hf (IsFractionRing.injective k[X] (RatFunc k) (h.trans (map_zero _).symm))

/-- The maximal ideal `(X - a)` of `k[X]`, as a height-one prime. -/
def hs (a : k) : HeightOneSpectrum k[X] where
  asIdeal := Ideal.span {Polynomial.X - Polynomial.C a}
  isPrime := (Ideal.span_singleton_prime (X_sub_C_ne_zero a)).mpr (prime_X_sub_C a)
  ne_bot := by simpa using X_sub_C_ne_zero a

/-- The `(X - a)`-adic valuation of `k(X)`. -/
def wA (a : k) : Valuation (RatFunc k) ℤᵐ⁰ := (hs a).valuation (RatFunc k)

open Classical in
/-- The valuation at infinity of `k(X)`. -/
def wI (k : Type*) [Field k] : Valuation (RatFunc k) ℤᵐ⁰ := RatFunc.inftyValuation k

theorem ordV_wA_X_sub (a : k) :
    ordV (wA a) (algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a)) = 1 := by
  unfold ordV wA
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton (hs a) (X_sub_C_ne_zero a) rfl]
  simp

theorem ordV_wA_poly (a : k) {f : k[X]} (hf : f ≠ 0) :
    ordV (wA a) (algebraMap k[X] (RatFunc k) f) = (f.rootMultiplicity a : ℤ) := by
  obtain ⟨g, hg, hgd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf a
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hgd (dvd_zero _)
  have h1 : ordV (wA a) (algebraMap k[X] (RatFunc k) g) = 0 := by
    unfold ordV wA
    have : (hs a).valuation (RatFunc k) (algebraMap k[X] (RatFunc k) g) = 1 := by
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      intro hmem
      exact hgd (Ideal.mem_span_singleton.mp hmem)
    rw [this]
    simp
  have hX : algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a) ≠ 0 := alg_ne_zero (X_sub_C_ne_zero a)
  generalize f.rootMultiplicity a = m at hg ⊢
  rw [hg, map_mul, map_pow, ordV_mul _ (pow_ne_zero _ hX) (alg_ne_zero hg0), h1,
    ← zpow_natCast, ordV_zpow, ordV_wA_X_sub]
  simp

theorem ordV_wI_poly {f : k[X]} (hf : f ≠ 0) :
    ordV (wI k) (algebraMap k[X] (RatFunc k) f) = - (f.natDegree : ℤ) := by
  unfold ordV wI
  classical
  have : (RatFunc.inftyValuation k) (algebraMap k[X] (RatFunc k) f) = exp (f.natDegree : ℤ) :=
    RatFunc.inftyValuation.polynomial k hf
  rw [this]
  simp

/-- A prime divisor whose residue field is generated by `k` has degree one. -/
theorem PrimeDivisor.deg_eq_one_of_surj {K : Type*} [Field K] [Algebra k K] (p : PrimeDivisor k K)
    (h : ∀ x : p.O, ∃ c : k, ¬ IsUnit (x - p.ofBase c)) : p.deg = 1 := by
  unfold PrimeDivisor.deg
  let _ : Module k (IsLocalRing.ResidueField p.O) :=
    ((IsLocalRing.residue p.O).comp p.ofBase).toModule
  show Module.finrank k (IsLocalRing.ResidueField p.O) = 1
  rw [finrank_eq_one_iff_of_nonzero' (1 : IsLocalRing.ResidueField p.O) one_ne_zero]
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, ?_⟩
  have h0 : IsLocalRing.residue p.O (x - p.ofBase c) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hc
  rw [map_sub, sub_eq_zero] at h0
  show (IsLocalRing.residue p.O (p.ofBase c)) * 1 = _
  rw [mul_one, h0]

theorem alg_C (c : k) : algebraMap k (RatFunc k) c = algebraMap k[X] (RatFunc k) (Polynomial.C c) := by
  rw [IsScalarTower.algebraMap_apply k k[X] (RatFunc k)]
  simp

/-- The prime divisor $\mathcal O_a$ of `k(X)`: the quotients of polynomials with denominator not
vanishing at `a`. -/
def PDa (a : k) : PrimeDivisor k (RatFunc k) where
  O := (wA a).valuationSubring
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff, alg_C]
    exact HeightOneSpectrum.valuation_le_one (hs a) _
  isDVR := inferInstanceAs (IsDiscreteValuationRing ((hs a).valuation (RatFunc k)).valuationSubring)

/-- The prime divisor $\mathcal O_\infty$ of `k(X)`: the quotients of polynomials with numerator of
degree at most the degree of the denominator. -/
def PDinf (k : Type*) [Field k] : PrimeDivisor k (RatFunc k) where
  O := (wI k).valuationSubring
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    classical
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one (RatFunc.inftyValuation k) c
  isDVR := by
    classical
    exact inferInstanceAs (IsDiscreteValuationRing (RatFunc.inftyValuation k).valuationSubring)

theorem PDa_ord (a : k) {φ : RatFunc k} (hφ : φ ≠ 0) : (PDa a).ord φ = ordV (wA a) φ :=
  (PDa a).ord_eq_ordV (wA a) rfl (alg_ne_zero (X_sub_C_ne_zero a)) (ordV_wA_X_sub a) hφ

theorem PDinf_ord {φ : RatFunc k} (hφ : φ ≠ 0) : (PDinf k).ord φ = ordV (wI k) φ := by
  have hX : algebraMap k[X] (RatFunc k) Polynomial.X ≠ 0 := alg_ne_zero Polynomial.X_ne_zero
  refine (PDinf k).ord_eq_ordV (wI k) rfl (inv_ne_zero hX) ?_ hφ
  rw [ordV_inv, ordV_wI_poly Polynomial.X_ne_zero, Polynomial.natDegree_X]
  simp

theorem PrimeDivisor.deg_eq_one_of_valuation {K : Type*} [Field K] [Algebra k K]
    (p : PrimeDivisor k K) (w : Valuation K ℤᵐ⁰) (hO : p.O = w.valuationSubring)
    (h : ∀ x : K, w x ≤ 1 → ∃ c : k, w (x - algebraMap k K c) < 1) : p.deg = 1 := by
  apply p.deg_eq_one_of_surj
  intro x
  obtain ⟨c, hc⟩ := h x ((p.mem_iff_valuation w hO _).mp x.2)
  refine ⟨c, fun hu => ?_⟩
  have h1 := p.val_unit_eq_one w hO hu.unit
  rw [hu.unit_spec] at h1
  have e : ((x - p.ofBase c : p.O) : K) = (x : K) - algebraMap k K c := rfl
  rw [e] at h1
  rw [h1] at hc
  exact lt_irrefl _ hc

theorem exists_c_A (a : k) {P Q : k[X]} (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) (hcop : IsCoprime P Q)
    (hx : wA a (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q) ≤ 1) :
    ∃ c : k, wA a (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q -
      algebraMap k (RatFunc k) c) < 1 := by
  have hx0 : algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q ≠ 0 :=
    div_ne_zero (alg_ne_zero hP0) (alg_ne_zero hQ0)
  rw [le_one_iff_ordV _ hx0, ordV_div _ (alg_ne_zero hP0) (alg_ne_zero hQ0), ordV_wA_poly a hP0,
    ordV_wA_poly a hQ0] at hx
  have hQa : Q.eval a ≠ 0 := by
    intro h
    have hQr : Q.IsRoot a := h
    have h1 : 0 < Q.rootMultiplicity a := (rootMultiplicity_pos hQ0).mpr hQr
    have hPa : ¬ P.IsRoot a := by
      obtain ⟨u, v, huv⟩ := hcop
      intro hP
      have := congrArg (Polynomial.eval a) huv
      have hP' : P.eval a = 0 := hP
      simp [hP', h] at this
    have h2 : P.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hPa
    omega
  have hQm : Q.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hQa
  refine ⟨P.eval a / Q.eval a, ?_⟩
  set c := P.eval a / Q.eval a with hc
  have hQ' := alg_ne_zero (k := k) hQ0
  have hexp : algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q -
      algebraMap k (RatFunc k) c = algebraMap k[X] (RatFunc k) (P - Polynomial.C c * Q) /
        algebraMap k[X] (RatFunc k) Q := by
    rw [alg_C, map_sub, map_mul]
    field_simp
  rw [hexp]
  by_cases hR : P - Polynomial.C c * Q = 0
  · rw [hR]
    simp
  · rw [lt_one_iff_ordV _ (div_ne_zero (alg_ne_zero hR) hQ'), ordV_div _ (alg_ne_zero hR) hQ',
      ordV_wA_poly a hR, ordV_wA_poly a hQ0, hQm]
    have hroot : (P - Polynomial.C c * Q).IsRoot a := by
      show (P - Polynomial.C c * Q).eval a = 0
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hc]
      field_simp
      ring
    have := (rootMultiplicity_pos hR).mpr hroot
    omega

theorem exists_c_I {P Q : k[X]} (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (hx : wI k (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q) ≤ 1) :
    ∃ c : k, wI k (algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q -
      algebraMap k (RatFunc k) c) < 1 := by
  have hx0 : algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q ≠ 0 :=
    div_ne_zero (alg_ne_zero hP0) (alg_ne_zero hQ0)
  rw [le_one_iff_ordV _ hx0, ordV_div _ (alg_ne_zero hP0) (alg_ne_zero hQ0), ordV_wI_poly hP0,
    ordV_wI_poly hQ0] at hx
  have hle : P.natDegree ≤ Q.natDegree := by omega
  refine ⟨P.coeff Q.natDegree / Q.leadingCoeff, ?_⟩
  set c := P.coeff Q.natDegree / Q.leadingCoeff with hc
  have hQ' := alg_ne_zero (k := k) hQ0
  have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hexp : algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q -
      algebraMap k (RatFunc k) c = algebraMap k[X] (RatFunc k) (P - Polynomial.C c * Q) /
        algebraMap k[X] (RatFunc k) Q := by
    rw [alg_C, map_sub, map_mul]
    field_simp
  rw [hexp]
  by_cases hR : P - Polynomial.C c * Q = 0
  · rw [hR]
    simp
  · rw [lt_one_iff_ordV _ (div_ne_zero (alg_ne_zero hR) hQ'), ordV_div _ (alg_ne_zero hR) hQ',
      ordV_wI_poly hR, ordV_wI_poly hQ0]
    have hdeg : (P - Polynomial.C c * Q).degree < Q.degree := by
      rw [Polynomial.degree_eq_natDegree hQ0, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      have hm' : Q.natDegree ≤ m := by exact_mod_cast hm
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      rcases eq_or_lt_of_le hm' with h | h
      · rw [← h, Polynomial.coeff_natDegree, hc]
        field_simp
        ring
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle h),
          Polynomial.coeff_eq_zero_of_natDegree_lt h]
        simp
    have := natDegree_lt_natDegree hR hdeg
    omega

theorem PDa_deg (a : k) : (PDa a).deg = 1 := by
  refine (PDa a).deg_eq_one_of_valuation (wA a) rfl fun x hx => ?_
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have h1 := exists_c_A a (RatFunc.num_ne_zero hx0) (RatFunc.denom_ne_zero x)
    (RatFunc.isCoprime_num_denom x)
  rw [RatFunc.num_div_denom] at h1
  exact h1 hx

theorem PDinf_deg : (PDinf k).deg = 1 := by
  refine (PDinf k).deg_eq_one_of_valuation (wI k) rfl fun x hx => ?_
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have h1 := exists_c_I (RatFunc.num_ne_zero hx0) (RatFunc.denom_ne_zero x)
  rw [RatFunc.num_div_denom] at h1
  exact h1 hx

theorem PrimeDivisor.ext_O {K : Type*} [Field K] [Algebra k K] {p q : PrimeDivisor k K}
    (h : p.O = q.O) : p = q := by
  cases p
  cases q
  simp only at h
  subst h
  rfl

theorem exists_hs_eq [IsAlgClosed k] (u : HeightOneSpectrum k[X]) : ∃ a : k, u = hs a := by
  obtain ⟨q, hq⟩ := (IsPrincipalIdealRing.principal u.asIdeal).principal
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply u.ne_bot
    rw [hq]
    simp
  have hprime : Prime q := by
    have := u.isPrime
    rw [hq] at this
    exact (Ideal.span_singleton_prime hq0).mp this
  have hirr : Irreducible q := hprime.irreducible
  have hdeg : q.degree ≠ 0 := by
    rw [IsAlgClosed.degree_eq_one_of_irreducible k hirr]
    exact one_ne_zero
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root q hdeg
  obtain ⟨r, hr⟩ := (Polynomial.dvd_iff_isRoot).mpr ha
  have hru : IsUnit r := by
    rcases hirr.isUnit_or_isUnit hr with h | h
    · exact absurd h (Polynomial.not_isUnit_X_sub_C a)
    · exact h
  refine ⟨a, ?_⟩
  apply HeightOneSpectrum.ext
  show u.asIdeal = Ideal.span {Polynomial.X - Polynomial.C a}
  rw [hq, hr]
  exact Ideal.span_singleton_mul_right_unit hru _

/-- **Classification of the prime divisors of `k(X)`** for `k` algebraically closed. -/
theorem classify [IsAlgClosed k] (p : PrimeDivisor k (RatFunc k)) :
    p = PDinf k ∨ ∃ a : k, p = PDa a := by
  classical
  have := p.isDVR
  let v : Valuation (RatFunc k) p.O.ValueGroup := p.O.valuation
  have : v.IsTrivialOn k := by
    refine ⟨fun a ha => ?_⟩
    have hunit : IsUnit (⟨algebraMap k (RatFunc k) a, p.algebraMap_mem a⟩ : p.O) := by
      refine IsUnit.of_mul_eq_one (⟨algebraMap k (RatFunc k) a⁻¹, p.algebraMap_mem a⁻¹⟩ : p.O) ?_
      apply Subtype.ext
      show algebraMap k (RatFunc k) a * algebraMap k (RatFunc k) a⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    exact (ValuationSubring.valuation_eq_one_iff _ _).mp hunit
  have : v.IsNontrivial := by
    rw [Valuation.isNontrivial_iff_exists_lt_one]
    obtain ⟨t, ht, htu⟩ := p.exists_uniO
    refine ⟨p.unif, ?_, ?_⟩
    · rw [← htu]
      intro h0
      exact ht.ne_zero (Subtype.ext h0)
    · have hmax : t ∈ IsLocalRing.maximalIdeal p.O := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact ht.not_isUnit
      have := (ValuationSubring.valuation_lt_one_iff p.O t).mp hmax
      rw [← htu]
      exact this
  have hback : ∀ w : Valuation (RatFunc k) ℤᵐ⁰, v.IsEquiv w → p.O = w.valuationSubring := by
    intro w hw
    rw [Valuation.isEquiv_iff_valuationSubring] at hw
    rw [← hw]
    exact (ValuationSubring.valuationSubring_valuation p.O).symm
  rcases RatFunc.valuation_isEquiv_infty_or_adic (v := v) with ⟨h1, _⟩ | ⟨⟨u, hu, _⟩, _⟩
  · left
    exact PrimeDivisor.ext_O (hback _ h1)
  · right
    obtain ⟨a, rfl⟩ := exists_hs_eq u
    exact ⟨a, PrimeDivisor.ext_O (hback _ hu)⟩

theorem ordV_wA_X_sub_ne {a b : k} (h : b ≠ a) :
    ordV (wA b) (algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a)) = 0 := by
  rw [ordV_wA_poly b (X_sub_C_ne_zero a)]
  have : (Polynomial.X - Polynomial.C a).rootMultiplicity b = 0 := by
    apply rootMultiplicity_eq_zero
    intro hr
    apply h
    have : b - a = 0 := by simpa using hr
    exact sub_eq_zero.mp this
  simp [this]

theorem ordV_wI_X_sub (a : k) :
    ordV (wI k) (algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a)) = -1 := by
  rw [ordV_wI_poly (X_sub_C_ne_zero a), natDegree_X_sub_C]
  simp

/-- The prime divisor attached to a point of the projective line `ℙ¹(k) = k ∪ {∞}`. -/
def Ep : Option k → PrimeDivisor k (RatFunc k)
  | none => PDinf k
  | some a => PDa a

/-- The `ordV`-valuation attached to a point of the projective line. -/
def ordP : Option k → RatFunc k → ℤ
  | none => ordV (wI k)
  | some a => ordV (wA a)

theorem Ep_ord (o : Option k) {φ : RatFunc k} (hφ : φ ≠ 0) : (Ep o).ord φ = ordP o φ := by
  cases o
  · exact PDinf_ord hφ
  · exact PDa_ord _ hφ

theorem Ep_deg (o : Option k) : (Ep o).deg = 1 := by
  cases o
  · exact PDinf_deg
  · exact PDa_deg _

theorem Ep_injective : Function.Injective (Ep (k := k)) := by
  have hX : ∀ a : k, algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a) ≠ 0 :=
    fun a => alg_ne_zero (X_sub_C_ne_zero a)
  intro o1 o2 h
  cases o1 with
  | none =>
    cases o2 with
    | none => rfl
    | some a =>
      exfalso
      have h1 := congrArg (fun p => p.ord (algebraMap k[X] (RatFunc k)
        (Polynomial.X - Polynomial.C a))) h
      simp only [Ep] at h1
      rw [PDinf_ord (hX a), PDa_ord a (hX a), ordV_wI_X_sub, ordV_wA_X_sub] at h1
      omega
  | some a =>
    cases o2 with
    | none =>
      exfalso
      have h1 := congrArg (fun p => p.ord (algebraMap k[X] (RatFunc k)
        (Polynomial.X - Polynomial.C a))) h
      simp only [Ep] at h1
      rw [PDinf_ord (hX a), PDa_ord a (hX a), ordV_wI_X_sub, ordV_wA_X_sub] at h1
      omega
    | some b =>
      by_contra hne
      have hne' : a ≠ b := fun e => hne (by rw [e])
      exfalso
      have h1 := congrArg (fun p => p.ord (algebraMap k[X] (RatFunc k)
        (Polynomial.X - Polynomial.C a))) h
      simp only [Ep] at h1
      rw [PDa_ord a (hX a), PDa_ord b (hX a), ordV_wA_X_sub, ordV_wA_X_sub_ne hne'.symm] at h1
      omega

theorem Ep_surjective [IsAlgClosed k] : Function.Surjective (Ep (k := k)) := by
  intro p
  rcases classify p with h | ⟨a, h⟩
  · exact ⟨none, h.symm⟩
  · exact ⟨some a, h.symm⟩

/-- The ring-theoretic integer sequence of a divisor along the finite points. -/
theorem finite_support_some [IsAlgClosed k] (D : Divisor k (RatFunc k)) :
    {a : k | D (Ep (some a)) ≠ 0}.Finite := by
  have hinj : Function.Injective (fun a : k => Ep (some a)) := fun a b h =>
    Option.some_injective _ (Ep_injective h)
  have := D.support.finite_toSet.preimage hinj.injOn
  simpa [Set.preimage, Finsupp.mem_support_iff] using this

/-- The finite set of points `a ∈ k` at which the divisor is nonzero. -/
def Tset [IsAlgClosed k] (D : Divisor k (RatFunc k)) : Finset k :=
  (finite_support_some D).toFinset

theorem mem_Tset [IsAlgClosed k] (D : Divisor k (RatFunc k)) (a : k) :
    a ∈ Tset D ↔ D (Ep (some a)) ≠ 0 := by
  simp [Tset]

/-- The rational function $\prod_a (X - a)^{D(a)}$. -/
def gfun [IsAlgClosed k] (D : Divisor k (RatFunc k)) : RatFunc k :=
  ∏ a ∈ Tset D, (algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a)) ^ (D (Ep (some a)))

theorem gfun_ne_zero [IsAlgClosed k] (D : Divisor k (RatFunc k)) : gfun D ≠ 0 := by
  unfold gfun
  rw [Finset.prod_ne_zero_iff]
  intro a _
  exact zpow_ne_zero _ (alg_ne_zero (X_sub_C_ne_zero a))

theorem ordV_gfun_wA [IsAlgClosed k] (D : Divisor k (RatFunc k)) (b : k) :
    ordV (wA b) (gfun D) = D (Ep (some b)) := by
  classical
  unfold gfun
  rw [ordV_prod _ _ _ (fun a _ => zpow_ne_zero _ (alg_ne_zero (X_sub_C_ne_zero a)))]
  have : ∀ a ∈ Tset D, ordV (wA b) ((algebraMap k[X] (RatFunc k) (Polynomial.X - Polynomial.C a)) ^
      (D (Ep (some a)))) = if a = b then D (Ep (some b)) else 0 := by
    intro a _
    rw [ordV_zpow]
    by_cases hab : a = b
    · subst hab
      rw [ordV_wA_X_sub]
      simp
    · rw [ordV_wA_X_sub_ne (Ne.symm hab)]
      simp [hab]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  by_cases hb : b ∈ Tset D
  · simp [hb]
  · simp only [hb, ite_false]
    have := (mem_Tset D b).not.mp hb
    push Not at this
    exact this.symm

theorem ordV_gfun_wI [IsAlgClosed k] (D : Divisor k (RatFunc k)) :
    ordV (wI k) (gfun D) = - ∑ a ∈ Tset D, D (Ep (some a)) := by
  unfold gfun
  rw [ordV_prod _ _ _ (fun a _ => zpow_ne_zero _ (alg_ne_zero (X_sub_C_ne_zero a)))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [ordV_zpow, ordV_wI_X_sub]
  ring

theorem Divisor_deg_eq [IsAlgClosed k] (D : Divisor k (RatFunc k)) :
    D.deg = ∑ a ∈ Tset D, D (Ep (some a)) + D (Ep none) := by
  classical
  have hinj : Function.Injective (Ep (k := k)) := Ep_injective
  have hsub : D.support ⊆ (insert none ((Tset D).image some)).image Ep := by
    intro p hp
    obtain ⟨o, rfl⟩ := Ep_surjective p
    rw [Finset.mem_image]
    refine ⟨o, ?_, rfl⟩
    cases o with
    | none => simp
    | some a =>
      simp only [Finset.mem_insert, Finset.mem_image, reduceCtorEq, false_or]
      exact ⟨a, (mem_Tset D a).mpr (Finsupp.mem_support_iff.mp hp), rfl⟩
  unfold Divisor.deg
  rw [Finsupp.liftAddHom_apply, Finsupp.sum_of_support_subset D hsub _ (by intro i _; simp),
    Finset.sum_image (fun x _ y _ h => hinj h), Finset.sum_insert (by simp),
    Finset.sum_image (fun x _ y _ h => Option.some_injective _ h)]
  simp only [zmultiplesHom_apply, Ep_deg, Nat.cast_one, smul_eq_mul, mul_one]
  ring

theorem mem_L_iff [IsAlgClosed k] (D : Divisor k (RatFunc k)) (φ : RatFunc k) :
    φ ∈ D.L ↔ φ = 0 ∨ ∀ o : Option k, 0 ≤ ordP o φ + D (Ep o) := by
  by_cases hφ : φ = 0
  · simp only [hφ, true_or, iff_true]
    exact D.L.zero_mem
  · constructor
    · intro h
      right
      intro o
      have := ((Ep o).mul_unif_zpow_mem_iff hφ (D (Ep o))).mp (h (Ep o))
      rwa [Ep_ord o hφ] at this
    · rintro (h | h)
      · exact absurd h hφ
      · intro p
        obtain ⟨o, rfl⟩ := Ep_surjective p
        exact ((Ep o).mul_unif_zpow_mem_iff hφ _).mpr (by rw [Ep_ord o hφ]; exact h o)

theorem poly_of_regular [IsAlgClosed k] {ψ : RatFunc k} (hψ : ψ ≠ 0)
    (h : ∀ a : k, 0 ≤ ordV (wA a) ψ) :
    ∃ P : k[X], P ≠ 0 ∧ ψ = algebraMap k[X] (RatFunc k) P := by
  have hP0 : ψ.num ≠ 0 := RatFunc.num_ne_zero hψ
  have hQ0 : ψ.denom ≠ 0 := RatFunc.denom_ne_zero ψ
  have hcop := RatFunc.isCoprime_num_denom ψ
  have hQdeg : ψ.denom.natDegree = 0 := by
    by_contra hne
    have hd : ψ.denom.degree ≠ 0 := by
      intro h0
      exact hne (natDegree_eq_of_degree_eq_some h0)
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_root ψ.denom hd
    have h1 := h a
    have e : ordV (wA a) ψ = ordV (wA a) (algebraMap k[X] (RatFunc k) ψ.num /
        algebraMap k[X] (RatFunc k) ψ.denom) := by rw [RatFunc.num_div_denom]
    rw [e, ordV_div _ (alg_ne_zero hP0) (alg_ne_zero hQ0), ordV_wA_poly a hP0,
      ordV_wA_poly a hQ0] at h1
    have h2 : 0 < ψ.denom.rootMultiplicity a := (rootMultiplicity_pos hQ0).mpr ha
    have hPa : ¬ ψ.num.IsRoot a := by
      obtain ⟨u, v, huv⟩ := hcop
      intro hP
      have := congrArg (Polynomial.eval a) huv
      have hP' : ψ.num.eval a = 0 := hP
      have hQ' : ψ.denom.eval a = 0 := ha
      simp [hP', hQ'] at this
    have h3 : ψ.num.rootMultiplicity a = 0 := rootMultiplicity_eq_zero hPa
    omega
  have hQC : ψ.denom = Polynomial.C (ψ.denom.coeff 0) := eq_C_of_natDegree_eq_zero hQdeg
  have hc : ψ.denom.coeff 0 ≠ 0 := by
    intro h0
    rw [h0] at hQC
    simp at hQC
    exact hQ0 hQC
  refine ⟨Polynomial.C (ψ.denom.coeff 0)⁻¹ * ψ.num, ?_, ?_⟩
  · exact mul_ne_zero (by simpa using hc) hP0
  · conv_lhs => rw [← RatFunc.num_div_denom ψ]
    rw [map_mul, ← alg_C, map_inv₀, div_eq_inv_mul]
    congr 2
    rw [hQC, ← alg_C]
    simp

theorem mem_L_iff_poly [IsAlgClosed k] (D : Divisor k (RatFunc k)) (φ : RatFunc k) :
    φ ∈ D.L ↔ ∃ P : k[X], P.degree < ((D.deg + 1).toNat : WithBot ℕ) ∧
      φ = algebraMap k[X] (RatFunc k) P * (gfun D)⁻¹ := by
  have hg := gfun_ne_zero D
  have hdeg := Divisor_deg_eq D
  rw [mem_L_iff]
  constructor
  · rintro (h0 | hall)
    · exact ⟨0, by simp, by simp [h0]⟩
    · by_cases hφ : φ = 0
      · exact ⟨0, by simp, by simp [hφ]⟩
      have hψ : φ * gfun D ≠ 0 := mul_ne_zero hφ hg
      have hreg : ∀ a : k, 0 ≤ ordV (wA a) (φ * gfun D) := by
        intro a
        rw [ordV_mul _ hφ hg, ordV_gfun_wA]
        exact hall (some a)
      obtain ⟨P, hP0, hP⟩ := poly_of_regular hψ hreg
      refine ⟨P, ?_, ?_⟩
      · have h1 := hall none
        have h2 : ordV (wI k) (φ * gfun D) = ordV (wI k) φ + ordV (wI k) (gfun D) :=
          ordV_mul _ hφ hg
        rw [hP, ordV_wI_poly hP0, ordV_gfun_wI] at h2
        simp only [ordP] at h1
        rw [Polynomial.degree_eq_natDegree hP0]
        have : P.natDegree < (D.deg + 1).toNat := by omega
        exact_mod_cast this
      · rw [← hP]
        field_simp
  · rintro ⟨P, hP, rfl⟩
    by_cases hP0 : P = 0
    · left
      simp [hP0]
    · right
      have hPa := alg_ne_zero (k := k) hP0
      intro o
      cases o with
      | none =>
        simp only [ordP]
        rw [ordV_mul _ hPa (inv_ne_zero hg), ordV_inv, ordV_gfun_wI, ordV_wI_poly hP0]
        rw [Polynomial.degree_eq_natDegree hP0] at hP
        have : P.natDegree < (D.deg + 1).toNat := by exact_mod_cast hP
        omega
      | some b =>
        simp only [ordP]
        rw [ordV_mul _ hPa (inv_ne_zero hg), ordV_inv, ordV_gfun_wA, ordV_wA_poly b hP0]
        simp

/-- Division by `gfun D`, from polynomials of degree less than `m` to `k(X)`. -/
def Lam [IsAlgClosed k] (D : Divisor k (RatFunc k)) (m : ℕ) :
    Polynomial.degreeLT k m →ₗ[k] RatFunc k :=
  (LinearMap.mulRight k (gfun D)⁻¹).comp
    ((IsScalarTower.toAlgHom k k[X] (RatFunc k)).toLinearMap.comp (Polynomial.degreeLT k m).subtype)

theorem Lam_apply [IsAlgClosed k] (D : Divisor k (RatFunc k)) (m : ℕ)
    (P : Polynomial.degreeLT k m) :
    Lam D m P = algebraMap k[X] (RatFunc k) (P : k[X]) * (gfun D)⁻¹ := rfl

theorem Lam_injective [IsAlgClosed k] (D : Divisor k (RatFunc k)) (m : ℕ) :
    Function.Injective (Lam D m) := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  rw [Lam_apply] at hP
  have hg := inv_ne_zero (gfun_ne_zero D)
  have h1 : algebraMap k[X] (RatFunc k) (P : k[X]) = 0 := by
    rcases mul_eq_zero.mp hP with h | h
    · exact h
    · exact absurd h hg
  have h2 : (P : k[X]) = 0 :=
    IsFractionRing.injective k[X] (RatFunc k) (h1.trans (map_zero _).symm)
  exact Subtype.ext h2

theorem range_Lam [IsAlgClosed k] (D : Divisor k (RatFunc k)) :
    LinearMap.range (Lam D (D.deg + 1).toNat) = D.L := by
  ext φ
  rw [LinearMap.mem_range, mem_L_iff_poly]
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P, Polynomial.mem_degreeLT.mp P.2, (Lam_apply D _ P).symm⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨⟨P, Polynomial.mem_degreeLT.mpr hP⟩, Lam_apply D _ _⟩

theorem L_equiv [IsAlgClosed k] (D : Divisor k (RatFunc k)) :
    Nonempty (Polynomial.degreeLT k (D.deg + 1).toNat ≃ₗ[k] D.L) :=
  ⟨(LinearEquiv.ofInjective _ (Lam_injective D _)).trans (LinearEquiv.ofEq _ _ (range_Lam D))⟩

theorem ell_eq [IsAlgClosed k] (D : Divisor k (RatFunc k)) :
    FiniteDimensional k D.L ∧ D.ell = (D.deg + 1).toNat := by
  obtain ⟨e⟩ := L_equiv D
  refine ⟨LinearEquiv.finiteDimensional e, ?_⟩
  unfold Divisor.ell
  rw [← e.finrank_eq, (Polynomial.degreeLTEquiv k _).finrank_eq, Module.finrank_fin_fun]

end RatFuncPlaces


/-- **Example 4.6** (p. 41): the projective line has genus 0.  Its function field is $k(X)$ (`RatFunc k`);
for `k` algebraically closed, $\ell(D) = \deg D + 1$ for $\deg D \geq -1$ and $L(D)$ is finite-dimensional for
every `D` (Milne computes $\ell(D) = \deg D + 1$ for $D = \sum r_i [a_i]$, $r_i > 0$). -/
@[kb "milne2006ec" "Ch. I, Ex. 4.6, pdf p. 41"]
theorem example_4_6 [IsAlgClosed k] : IsGenus k (RatFunc k) 0 := by
  intro D
  obtain ⟨hfd, hell⟩ := ell_eq D
  refine ⟨hfd, ?_, ?_⟩
  · rw [hell]
    omega
  · intro h
    rw [hell]
    omega

end NumberFieldKB.MilneEC

end
