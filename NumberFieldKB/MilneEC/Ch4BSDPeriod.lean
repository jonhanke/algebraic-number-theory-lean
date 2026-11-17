import NumberFieldKB.MilneEC.Ch4BSD
import NumberFieldKB.MilneEC.Ch4MinimalTransport
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Milne's period against Formal Conjectures' global period (closing `PeriodComparison`)

For an elliptic curve $E$ over $\mathbb Q$ given by an equation minimal at every prime (`IsMinimalOverRat`),
Formal Conjectures' global period $\Omega(E) = (|\Delta| / N(\mathfrak D_E))^{1/12}\prod_v\Omega_v(E)$ is Milne's
$\Omega = \int_{E(\mathbb R)}|\omega|$ (Milne, *Elliptic Curves*, IV, Conjecture 10.5, pdf p. 173):

* `isMinimal_adicCompletion`: the equation stays minimal over the adic completion of $\mathbb Q$ at $p$, through
  Mathlib's isomorphism $\mathbb Q_p \cong \mathbb Q_{(p)}^\wedge$ (`Rat.HeightOneSpectrum.adicCompletion.padicEquiv`);
* `minimalDiscriminantExponent_eq`: so the exponent of $p$ in the minimal discriminant is $\operatorname{ord}_p\Delta$;
* `absNorm_minimalDiscriminant`: so $N(\mathfrak D_E) = |\Delta|$ and the correction factor is $1$;
* `prod_infinitePlace_rat`: $\mathbb Q$ has one infinite place, real, with embedding the inclusion
  $\mathbb Q \to \mathbb R$;
* `periodComparison`: the named statement `PeriodComparison` holds.
-/

open WeierstrassCurve IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace NumberFieldKB.MilneEC

variable (E : WeierstrassCurve ℚ)

/-- The normalized valuation of $\mathbb Q_p$ at a nonzero integer. -/
theorem valuation_padicInt_ne_zero (p : ℕ) [Fact p.Prime] (z : ℤ_[p]) (hz : z ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p] (z : ℚ_[p]) =
      WithZero.exp (-(z.valuation : ℤ)) := by
  have hp : Irreducible (p : ℤ_[p]) := PadicInt.irreducible_p
  have hpv : (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation (p : ℤ_[p]) =
      WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hp.ne_zero ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hp)
  have hu : (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).intValuation
      ((PadicInt.unitCoeff hz : ℤ_[p]ˣ) : ℤ_[p]) = 1 :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 (IsLocalRing.notMem_maximalIdeal.mpr (PadicInt.unitCoeff hz).isUnit)
  have h := PadicInt.unitCoeff_spec hz
  have : (z : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] z := rfl
  rw [this, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  conv_lhs => rw [h]
  rw [map_mul, map_pow, hu, hpv, one_mul, ← WithZero.exp_nsmul]
  congr 1
  simp

theorem valuation_padicInt_int (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : n ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p] (n : ℚ_[p]) =
      WithZero.exp (-(padicValInt p n : ℤ)) := by
  have hz : ((n : ℤ_[p])) ≠ 0 := by exact_mod_cast hn
  have h := valuation_padicInt_ne_zero p (n : ℤ_[p]) hz
  have h2 : ((n : ℤ_[p]) : ℚ_[p]) = (n : ℚ_[p]) := by push_cast; rfl
  rw [h2] at h
  rw [h]
  congr 2
  have := Padic.valuation_intCast (p := p) n
  rw [← this, ← PadicInt.valuation_coe, h2]

theorem valuation_padic_rat (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : q ≠ 0) :
    (IsDiscreteValuationRing.maximalIdeal ℤ_[p]).valuation ℚ_[p] (q : ℚ_[p]) =
      WithZero.exp (-(padicValRat p q)) := by
  have hn : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hd : (q.den : ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have : (q : ℚ_[p]) = (q.num : ℚ_[p]) / ((q.den : ℤ) : ℚ_[p]) := by
    rw [Rat.cast_def]; push_cast; rfl
  rw [this, map_div₀, valuation_padicInt_int p _ hn, valuation_padicInt_int p _ hd,
    ← WithZero.exp_sub]
  congr 1
  simp [padicValRat]
  ring

/-- An equation minimal at every prime has an integral discriminant. -/
theorem exists_int_Δ_of_isMinimalOverRat (hmin : IsMinimalOverRat E) : ∃ d : ℤ, (d : ℚ) = E.Δ := by
  have hval : ∀ (p : ℕ) [Fact p.Prime], 0 ≤ padicValRat p E.Δ := by
    intro p _
    haveI := hmin p
    obtain ⟨r, hr⟩ := Δ_integral_of_isIntegral ℤ_[p] (E.baseChange ℚ_[p])
    have hΔ : (E.baseChange ℚ_[p]).Δ = (E.Δ : ℚ_[p]) := by
      simp [baseChange, map_Δ]
    have h1 : ‖(E.Δ : ℚ_[p])‖ ≤ 1 := by
      rw [← hΔ, ← hr]; exact r.2
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast] at h1
    exact h1
  refine ⟨E.Δ.num, ?_⟩
  have hden : E.Δ.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact p.Prime := ⟨hp⟩
    have h := hval p
    have hnd : ¬ p ∣ E.Δ.num.natAbs := fun hh =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_one (by
        simpa [E.Δ.reduced.gcd_eq_one] using Nat.dvd_gcd hh hpd))
    have h1 : padicValNat p E.Δ.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hnd
    have h2 : 1 ≤ padicValNat p E.Δ.den := one_le_padicValNat_of_dvd E.Δ.den_nz hpd
    simp only [padicValRat, padicValInt, Int.natAbs_natCast] at h
    omega
  exact_mod_cast (Rat.den_eq_one_iff _).mp hden

/-- Minimality over $\mathbb Z_p$ transports to the integers of the adic completion of $\mathbb Q$ at $p$. -/
theorem isMinimal_adicCompletion (hmin : IsMinimalOverRat E) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (E.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ) := by
  haveI : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
  let e : v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v] := (adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv
  let eR : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  have he : ∀ r : v.adicCompletionIntegers ℚ,
      e (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) =
        algebraMap ℤ_[primesEquiv v] ℚ_[primesEquiv v] (eR r) := fun r => rfl
  rw [MinimalTransport.isMinimal_map_iff e eR he]
  have : (E.baseChange (v.adicCompletion ℚ)).map (e : _ →+* _) = E.baseChange ℚ_[primesEquiv v] :=
    map_baseChange (R := ℚ) (S := ℚ) E (adicCompletion.padicEquiv v).toAlgEquiv.toAlgHom
  rw [this]
  exact hmin _

/-- For an equation minimal at every prime, the exponent of $v \leftrightarrow p$ in Formal Conjectures' minimal
discriminant is $\operatorname{ord}_p\Delta$. -/
theorem minimalDiscriminantExponent_eq (hmin : IsMinimalOverRat E) (v : HeightOneSpectrum (𝓞 ℚ)) :
    FormalConjectures.minimalDiscriminantExponent E v = (padicValRat (primesEquiv v : ℕ) E.Δ).toNat := by
  haveI : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
  have hM := isMinimal_adicCompletion E hmin v
  have hM2 := ((E.baseChange (v.adicCompletion ℚ)).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose_spec
  have h := MinimalTransport.valuation_Δ_eq_of_isMinimal (R := v.adicCompletionIntegers ℚ)
    (W := E.baseChange (v.adicCompletion ℚ))
    ((E.baseChange (v.adicCompletion ℚ)).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose
  let e : v.adicCompletion ℚ ≃+* ℚ_[primesEquiv v] := (adicCompletion.padicEquiv v).toAlgEquiv.toRingEquiv
  let eR : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  have he : ∀ r : v.adicCompletionIntegers ℚ,
      e (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) =
        algebraMap ℤ_[primesEquiv v] ℚ_[primesEquiv v] (eR r) := fun r => rfl
  have hv := MinimalTransport.valuation_map_of_ringEquiv e eR he (E.baseChange (v.adicCompletion ℚ)).Δ
  have hΔ : e (E.baseChange (v.adicCompletion ℚ)).Δ = (E.Δ : ℚ_[primesEquiv v]) := by
    have : (E.baseChange (v.adicCompletion ℚ)).Δ = algebraMap ℚ (v.adicCompletion ℚ) E.Δ := by
      simp [baseChange, map_Δ]
    rw [this]
    exact (adicCompletion.padicEquiv v).toAlgEquiv.commutes E.Δ
  rw [hΔ] at hv
  unfold FormalConjectures.minimalDiscriminantExponent
  simp only [WeierstrassCurve.minimal]
  rw [h, ← hv]
  by_cases h0 : E.Δ = 0
  · simp [h0]
  · rw [valuation_padic_rat _ _ h0]
    simp

theorem asIdeal_eq_span_primesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {(((primesEquiv v : ℕ)) : 𝓞 ℚ)} := by
  ext x
  rw [Ideal.mem_span_singleton]
  have h1 : x ∈ v.asIdeal ↔ Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) x ∈
      v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) :=
    (Ideal.apply_mem_of_equiv_iff).symm
  rw [h1, ← span_natGenerator, Ideal.mem_span_singleton,
    ← map_dvd_iff (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]
  simp only [map_natCast]
  rfl

theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal.absNorm = (primesEquiv v : ℕ) := by
  rw [asIdeal_eq_span_primesEquiv v, Ideal.absNorm_span_singleton]
  have : (((primesEquiv v : ℕ)) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) ((primesEquiv v : ℕ) : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap]
  have hr : Module.finrank ℤ (𝓞 ℚ) = 1 := by
    rw [RingOfIntegers.rank]; exact Module.finrank_self ℚ
  rw [hr]
  simp

/-- For an equation minimal at every prime, the norm of the minimal discriminant ideal is $|\Delta|$. -/
theorem absNorm_minimalDiscriminant [E.IsElliptic] (hmin : IsMinimalOverRat E) :
    ((FormalConjectures.minimalDiscriminant E).absNorm : ℝ) = |(E.Δ : ℝ)| := by
  obtain ⟨d, hd⟩ := exists_int_Δ_of_isMinimalOverRat E hmin
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact E.isUnit_Δ.ne_zero (by simpa using hd.symm)
  have hm : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  have hexp : ∀ v : HeightOneSpectrum (𝓞 ℚ), FormalConjectures.minimalDiscriminantExponent E v =
      padicValNat (primesEquiv v : ℕ) d.natAbs := by
    intro v
    haveI : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
    rw [minimalDiscriminantExponent_eq E hmin v, ← hd]
    have : padicValRat (primesEquiv v : ℕ) (d : ℚ) = (padicValNat (primesEquiv v : ℕ) d.natAbs : ℤ) := by
      rw [padicValRat.of_int]; rfl
    rw [this]; simp
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) =>
      v.asIdeal ^ FormalConjectures.minimalDiscriminantExponent E v).Finite := by
    have hT : {v : HeightOneSpectrum (𝓞 ℚ) | ((primesEquiv v : ℕ)) ∈ (d.natAbs.divisors : Set ℕ)}.Finite :=
      (d.natAbs.divisors.finite_toSet).preimage
        (((Subtype.val_injective (p := fun p : ℕ => p.Prime)).comp
          (primesEquiv (R := 𝓞 ℚ)).injective).injOn)
    refine hT.subset fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv
    have hn : FormalConjectures.minimalDiscriminantExponent E v ≠ 0 := by
      intro h0; rw [h0, pow_zero] at hv; exact hv rfl
    rw [hexp] at hn
    have : (primesEquiv v : ℕ) ∣ d.natAbs := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hn)
    simpa [hm] using this
  unfold FormalConjectures.minimalDiscriminant
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) (by simp), map_prod]
  have key : ∏ v ∈ hfin.toFinset, (v.asIdeal ^ FormalConjectures.minimalDiscriminantExponent E v).absNorm
      = d.natAbs := by
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hm]
    rw [Finsupp.prod]
    refine Finset.prod_bij (fun v _ => (primesEquiv v : ℕ)) ?_ ?_ ?_ ?_
    · intro v hv
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hv
      have hn : FormalConjectures.minimalDiscriminantExponent E v ≠ 0 := by
        intro h0; rw [h0, pow_zero] at hv; exact hv rfl
      rw [hexp] at hn
      haveI : Fact (primesEquiv v : ℕ).Prime := ⟨(primesEquiv v).2⟩
      simp only [Nat.support_factorization]
      exact Nat.mem_primeFactors.mpr ⟨(primesEquiv v).2, dvd_of_one_le_padicValNat
        (Nat.one_le_iff_ne_zero.mpr hn), hm⟩
    · intro a _ b _ h
      exact (primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)
    · intro p hp
      simp only [Nat.support_factorization] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      haveI : Fact p.Prime := ⟨hpp⟩
      let q : Nat.Primes := ⟨p, hpp⟩
      obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), primesEquiv v = q :=
        ⟨(primesEquiv (R := 𝓞 ℚ)).symm q, Equiv.apply_symm_apply _ _⟩
      have hvp : (primesEquiv v : ℕ) = p := congrArg Subtype.val hv
      refine ⟨v, ?_, hvp⟩
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport]
      intro h1
      have h2 := congrArg Ideal.absNorm h1
      rw [map_pow, absNorm_asIdeal, hexp, map_one, hvp] at h2
      have : 1 < p ^ padicValNat p d.natAbs :=
        Nat.one_lt_pow (one_le_padicValNat_of_dvd hm hpd |> Nat.pos_iff_ne_zero.mp) hpp.one_lt
      omega
    · intro v _
      rw [map_pow, absNorm_asIdeal, hexp, Nat.factorization_def _ (primesEquiv v).2]
  rw [key]
  have : (E.Δ : ℝ) = (d : ℝ) := by rw [← hd]; norm_cast
  rw [this, Nat.cast_natAbs, Int.cast_abs]

open scoped Classical in
/-- The product over the infinite places of $\mathbb Q$ in Formal Conjectures' `period` is the real period of
$E$ over $\mathbb R$. -/
theorem prod_infinitePlace_rat :
    (∏ v : InfinitePlace ℚ, if hv : v.IsReal then
        FormalConjectures.realPeriod (E.map (InfinitePlace.embedding_of_isReal hv))
      else FormalConjectures.complexPeriod (E.map v.embedding)) = realPeriodOf E := by
  have hr : (default : InfinitePlace ℚ).IsReal := Rat.isReal_infinitePlace
  rw [Fintype.prod_unique, dif_pos hr, realPeriodOf]
  congr 2
  exact Subsingleton.elim _ _

/-- **Milne's $\Omega$ is Formal Conjectures' global period** for an equation minimal at every prime. -/
theorem period_eq_realPeriodOf [E.IsElliptic] (hmin : IsMinimalOverRat E) :
    FormalConjectures.period E = realPeriodOf E := by
  unfold FormalConjectures.period
  rw [prod_infinitePlace_rat, absNorm_minimalDiscriminant E hmin, Algebra.norm_self]
  have h0 : (E.Δ : ℝ) ≠ 0 := by
    have := E.isUnit_Δ.ne_zero
    simpa using this
  simp [div_self (abs_ne_zero.mpr h0)]

/-- The named statement `PeriodComparison` holds. -/
theorem periodComparison : PeriodComparison :=
  ⟨fun E _ hmin => (period_eq_realPeriodOf E hmin).symm⟩

end NumberFieldKB.MilneEC
