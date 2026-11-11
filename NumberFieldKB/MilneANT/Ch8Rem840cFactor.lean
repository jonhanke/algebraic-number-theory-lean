import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch8Rem840cBasic

/-!
# Milne, *Algebraic Number Theory*, Remark 8.40(c): factorization of rational primes in `L` and `M`

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 8.40(c), p. 150; bib key `milne2020ant`.

For `p ∤ 6`, the exponent of `θ = ⁸√a` is prime to `p` (the conductor contains `8a`), so by the Kummer-Dedekind
bijection the primes of `ℚ(⁸√a)` above `p` correspond to the monic irreducible factors of `X⁸ - a` mod `p`,
with the same ramification index and residue degree. Since `16` is an eighth power mod `p`, the substitution
`X ↦ cX` identifies the factorizations of `X⁸ - 3` and `X⁸ - 48` mod `p`.
-/

open Polynomial NumberField UniqueFactorizationMonoid

namespace NumberFieldKB.MilneANT.Rem840c

/-- 16 is an eighth power modulo every odd prime: 16 = (√2)^8 = (√-2)^8 = (1+i)^8. -/
theorem exists_pow_eight_eq_sixteen (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ∃ c : ZMod p, c ^ 8 = 16 := by
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h | h | h | h
  · obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_two_iff hp).2 (Or.inl h)
    refine ⟨s, ?_⟩
    have : s ^ 8 = (s * s) ^ 4 := by ring
    rw [this, ← hs]; norm_num
  · obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_neg_two_iff hp).2 (Or.inr h)
    refine ⟨s, ?_⟩
    have : s ^ 8 = (s * s) ^ 4 := by ring
    rw [this, ← hs]; norm_num
  · obtain ⟨i, hi⟩ := (ZMod.exists_sq_eq_neg_one_iff (p := p)).2 (by omega)
    refine ⟨1 + i, ?_⟩
    have h2 : (1 + i) ^ 2 = 2 * i := by linear_combination (-1 : ZMod p) * hi
    have h4 : i ^ 4 = 1 := by
      have : i ^ 4 = (i * i) ^ 2 := by ring
      rw [this, ← hi]; norm_num
    calc (1 + i) ^ 8 = ((1 + i) ^ 2) ^ 4 := by ring
      _ = 16 * i ^ 4 := by rw [h2]; ring
      _ = 16 := by rw [h4]; ring
  · obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_two_iff hp).2 (Or.inr h)
    refine ⟨s, ?_⟩
    have : s ^ 8 = (s * s) ^ 4 := by ring
    rw [this, ← hs]; norm_num

/-- The exponent (Mathlib `RingOfIntegers.exponent`) of `θ` is prime to every `p ∤ 8a`. -/
theorem not_dvd_exponent (a : ℤ) [Fact (Irreducible (polyQ a))] (p : ℕ) [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ 8 * a) : ¬ p ∣ RingOfIntegers.exponent (theta a) := by
  have : Module.Finite ℚ (AdjoinRoot (polyQ a)) :=
    (AdjoinRoot.powerBasis (polyQ_monic a).ne_zero).finite
  have : NumberField (AdjoinRoot (polyQ a)) := ⟨⟩
  have hx : Algebra.adjoin ℚ {algebraMap (𝓞 (AdjoinRoot (polyQ a))) (AdjoinRoot (polyQ a)) (theta a)} = ⊤ :=
    AdjoinRoot.adjoinRoot_eq_top
  have hmul := conductor_mul_differentIdeal ℤ ℚ (AdjoinRoot (polyQ a)) (theta a) hx
  have hmem : aeval (theta a) (derivative (minpoly ℤ (theta a))) ∈ conductor ℤ (theta a) := by
    have : aeval (theta a) (derivative (minpoly ℤ (theta a))) ∈
        conductor ℤ (theta a) * differentIdeal ℤ (𝓞 (AdjoinRoot (polyQ a))) := by
      rw [hmul]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left this
  have hθ8 : (theta a) ^ 8 = (a : 𝓞 (AdjoinRoot (polyQ a))) := by
    exact Subtype.ext (root_pow_eight a)
  have h8a : ((8 * a : ℤ) : 𝓞 (AdjoinRoot (polyQ a))) ∈ conductor ℤ (theta a) := by
    have := Ideal.mul_mem_right (theta a) _ hmem
    rw [minpoly_theta] at this
    have e : aeval (theta a) (derivative (polyZ a)) * theta a = ((8 * a : ℤ) : 𝓞 (AdjoinRoot (polyQ a))) := by
      simp only [polyZ, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_pow,
        aeval_X, map_natCast]
      push_cast
      linear_combination 8 * hθ8
    rwa [e] at this
  rw [RingOfIntegers.not_dvd_exponent_iff, codisjoint_iff, eq_top_iff]
  have hcop : IsCoprime (p : ℤ) (8 * a) :=
    ((Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).irreducible.coprime_iff_not_dvd).2 hp
  have hsup : Ideal.span {(8 * a : ℤ)} ⊔ Ideal.span {(p : ℤ)} = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
    exact hcop.symm
  rw [← hsup]
  refine sup_le_sup_right ?_ _
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
  simpa using h8a

section Transport

variable {F : Type*} [Field F] [DecidableEq F]

/-- Forward map on normalized factors under a degree-preserving multiplicative equivalence. -/
theorem normalize_mem_factors (ψ : F[X] ≃* F[X]) (hdeg : ∀ q, (ψ q).natDegree = q.natDegree)
    {f g : F[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : Associated (ψ g) f) (e d : ℕ) {Q : F[X]}
    (hQ : Q ∈ (normalizedFactors g).toFinset ∧ multiplicity Q g = e ∧ Q.natDegree = d) :
    normalize (ψ Q) ∈ (normalizedFactors f).toFinset ∧
      multiplicity (normalize (ψ Q)) f = e ∧ (normalize (ψ Q)).natDegree = d := by
  obtain ⟨h1, h2, h3⟩ := hQ
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg] at h1
  obtain ⟨hirr, hmon, hdvd⟩ := h1
  have hψ0 : ψ Q ≠ 0 := by
    intro h; rw [map_eq_zero_iff _ ψ.injective] at h; exact hirr.ne_zero h
  have hass : Associated (normalize (ψ Q)) (ψ Q) := normalize_associated _
  refine ⟨?_, ?_, ?_⟩
  · rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hf]
    refine ⟨hass.irreducible_iff.2 ((MulEquiv.irreducible_iff ψ).2 hirr),
      Polynomial.monic_normalize hψ0, ?_⟩
    exact hass.dvd.trans ((map_dvd ψ hdvd).trans hfg.dvd)
  · rw [← multiplicity_eq_of_associated_left hass, ← multiplicity_eq_of_associated_right hfg,
      multiplicity_map_eq, h2]
  · rw [Polynomial.natDegree_normalize, hdeg, h3]

/-- Transport of the factors of given multiplicity and degree along `ψ`. -/
theorem ncard_factors_congr (ψ : F[X] ≃* F[X]) (hdeg : ∀ q, (ψ q).natDegree = q.natDegree)
    {f g : F[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : Associated (ψ g) f) (e d : ℕ) :
    {Q : F[X] | Q ∈ (normalizedFactors g).toFinset ∧ multiplicity Q g = e ∧ Q.natDegree = d}.ncard =
      {Q : F[X] | Q ∈ (normalizedFactors f).toFinset ∧ multiplicity Q f = e ∧ Q.natDegree = d}.ncard := by
  have hdeg' : ∀ q, (ψ.symm q).natDegree = q.natDegree := fun q => by
    rw [← hdeg (ψ.symm q), MulEquiv.apply_symm_apply]
  have hfg' : Associated (ψ.symm f) g := by
    have := hfg.symm.map ψ.symm
    simpa using this
  apply Set.ncard_congr (fun Q _ => normalize (ψ Q))
  · intro Q hQ
    exact normalize_mem_factors ψ hdeg hf hg hfg e d hQ
  · intro Q1 Q2 h1 h2 h
    have hirr1 := h1.1
    have hirr2 := h2.1
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg] at hirr1 hirr2
    have hass : Associated (ψ Q1) (ψ Q2) :=
      ((normalize_associated (ψ Q1)).symm.trans (h ▸ Associated.refl _)).trans (normalize_associated _)
    have : Associated Q1 Q2 := by simpa using hass.map ψ.symm
    exact Polynomial.eq_of_monic_of_associated hirr1.2.1 hirr2.2.1 this
  · intro R hR
    have hR' := hR
    have hRm := hR.1
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hf] at hRm
    have hψ0 : ψ.symm R ≠ 0 := by
      intro h; rw [map_eq_zero_iff _ ψ.symm.injective] at h; exact hRm.1.ne_zero h
    have hmem := normalize_mem_factors ψ.symm hdeg' hg hf hfg' e d hR'
    refine ⟨normalize (ψ.symm R), hmem, ?_⟩
    have hass : Associated (ψ (normalize (ψ.symm R))) R := by
      have := (normalize_associated (ψ.symm R)).map ψ
      simpa using this
    show normalize (ψ (normalize (ψ.symm R))) = R
    rw [normalize_eq_normalize_iff.2 ⟨hass.dvd, hass.symm.dvd⟩]
    exact (Polynomial.normalize_eq_self_iff_monic hRm.1.ne_zero).2 hRm.2.1

end Transport

/-- Kummer-Dedekind: counting primes above `p` by `(e, f)` equals counting the matching factors mod `p`. -/
theorem ncard_primes {K : Type} [Field K] [NumberField K] (θ : 𝓞 K) (p : ℕ) [Fact p.Prime]
    (hp : ¬ p ∣ RingOfIntegers.exponent θ) (e f : ℕ) :
    {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) | P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f}.ncard =
      {Q : (ZMod p)[X] |
        Q ∈ (normalizedFactors ((minpoly ℤ θ).map (Int.castRingHom (ZMod p)))).toFinset ∧
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) = e ∧ Q.natDegree = f}.ncard := by
  have key : ∀ x, ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
      (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp x) : Ideal (𝓞 K)) = x := fun x => by
    simp
  apply Set.ncard_congr (fun P hP => (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp ⟨P, hP.1⟩).1)
  · intro P hP
    set x : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := ⟨P, hP.1⟩ with hx
    have hQ := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp x).2
    refine ⟨hQ, ?_, ?_⟩
    · have h := NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
      rw [← hP.2.1, ← h]
      congr 1
      exact key x
    · have h := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ
      rw [← hP.2.2, ← h]
      congr 1
      exact key x
  · intro P1 P2 h1 h2 h
    have := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).injective (Subtype.ext h)
    exact congrArg Subtype.val this
  · intro Q hQ
    refine ⟨((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ.1⟩ : Ideal (𝓞 K)),
      ⟨((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ.1⟩).2, ?_, ?_⟩, ?_⟩
    · rw [NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ.1]
      exact hQ.2.1
    · rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ.1]
      exact hQ.2.2
    · simp

theorem map_polyZ (a : ℤ) (p : ℕ) :
    (polyZ a).map (Int.castRingHom (ZMod p)) = X ^ 8 - C (a : ZMod p) := by
  simp [polyZ]

@[kb "milne2020ant" "v3.08, Rem. 8.40(c), p. 150"]
theorem ncard_eq (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (e f : ℕ) :
    {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 L) | P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f}.ncard =
      {P ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 M) | P.ramificationIdx ℤ = e ∧ P.inertiaDeg ℤ = f}.ncard := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_pow_eight_eq_sixteen p h2
  have h16 : (16 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((16 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have : p ∣ 2 ^ 4 := by simpa using h'
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h16
    rw [← hc]; norm_num
  have h2' : ¬ p ∣ 2 := fun h => h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have h3' : ¬ p ∣ 3 := fun h => h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  have h8' : ¬ p ∣ 8 := fun h => h2' (hp.dvd_of_dvd_pow (n := 3) (by simpa using h))
  have h6' : ¬ p ∣ 6 := fun h => by
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 by simpa using h) with h | h
    exacts [h2' h, h3' h]
  have hpL : ¬ (p : ℤ) ∣ 8 * 3 := fun h => by
    have h' : (p : ℤ) ∣ ((8 * 3 : ℕ) : ℤ) := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).1 (Int.natCast_dvd_natCast.1 h') with h | h
    exacts [h8' h, h3' h]
  have hpM : ¬ (p : ℤ) ∣ 8 * 48 := fun h => by
    have h' : (p : ℤ) ∣ ((8 * (6 * 8) : ℕ) : ℤ) := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).1 (Int.natCast_dvd_natCast.1 h') with h | h
    · exact h8' h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      exacts [h6' h, h8' h]
  rw [ncard_primes (theta 3) p (not_dvd_exponent 3 p hpL) e f,
    ncard_primes (theta 48) p (not_dvd_exponent 48 p hpM) e f, minpoly_theta, minpoly_theta,
    map_polyZ, map_polyZ]
  let _ : Invertible c := invertibleOfNonzero hc0
  let ψ : (ZMod p)[X] ≃* (ZMod p)[X] := (algEquivCMulXAddC c 0).toRingEquiv.toMulEquiv
  have hψ : ∀ q, ψ q = q.comp (C c * X + C 0) := fun q => by
    show aeval (C c * X + C 0) q = _
    rw [comp_eq_aeval]
  have hdeg : ∀ q, (ψ q).natDegree = q.natDegree := fun q => by
    rw [hψ, natDegree_comp]
    simp [natDegree_C_mul_X c hc0]
  have hf : (X ^ 8 - C ((3 : ℤ) : ZMod p) : (ZMod p)[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have hg : (X ^ 8 - C ((48 : ℤ) : ZMod p) : (ZMod p)[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have hψg : ψ (X ^ 8 - C ((48 : ℤ) : ZMod p)) = C 16 * (X ^ 8 - C ((3 : ℤ) : ZMod p)) := by
    rw [hψ]
    simp only [sub_comp, pow_comp, X_comp, C_comp]
    have h8 : (C c * X + C 0) ^ 8 = C 16 * X ^ 8 := by
      rw [map_zero, add_zero, mul_pow, ← C_pow, hc]
    rw [h8, mul_sub, ← C_mul]
    push_cast
    norm_num
  have hfg : Associated (ψ (X ^ 8 - C ((48 : ℤ) : ZMod p))) (X ^ 8 - C ((3 : ℤ) : ZMod p)) := by
    rw [hψg]
    exact associated_unit_mul_left _ _ (isUnit_C.2 (Ne.isUnit h16))
  exact (ncard_factors_congr ψ hdeg hf hg hfg e f).symm

end NumberFieldKB.MilneANT.Rem840c
