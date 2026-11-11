import NumberFieldKB.MilneCFT.Ch8.Example101Chi0
import NumberFieldKB.MilneCFT.Ch8.Example101ChiD
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three

/-!
# Auxiliary facts for Milne, *CFT*, VIII, Example 10.1

The values at the inert and split primes: norms, complex conjugation through an embedding, and the power residue
symbol at an inert prime.
-/

open NumberField IsDedekindDomain NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.Ch8

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace NumberFieldKB.MilneCFT.Ch8.Ex101

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

theorem norm_intCast (n : ℤ) : Algebra.norm ℤ ((n : ℤ) : 𝓞 K) = n ^ 2 := by
  have h : ((n : ℤ) : 𝓞 K) = algebraMap ℤ (𝓞 K) n := by simp
  rw [h, Algebra.norm_algebraMap, TauCeti.finrank_ringOfIntegers_three]

/-- An element of $\mathcal O_K$ of norm $p$ (a prime) does not divide an integer prime to $p$. -/
theorem not_dvd_of_norm {p : ℕ} (hp : p.Prime) {π : 𝓞 K} (hπ : Algebra.norm ℤ π = p) {D : ℤ}
    (hD : ¬ (p : ℤ) ∣ D) : ¬ π ∣ (D : 𝓞 K) := by
  intro h
  have h1 := map_dvd (Algebra.norm ℤ) h
  rw [hπ, norm_intCast] at h1
  exact hD ((Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow h1)

/-- Complex conjugation on $\mathcal O_K$ is complex conjugation through any embedding. -/
theorem sigma_conj (σ : K →+* ℂ) (x : 𝓞 K) :
    σ ((CubicTC.conj x : 𝓞 K) : K) = starRingEnd ℂ (σ (x : K)) := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  obtain ⟨a, b, hx, hc⟩ := CubicTC.conj_eq x
  set η : 𝓞 K := hζ.toInteger with hη
  set z : ℂ := σ ((η : 𝓞 K) : K) with hz
  have h3 : z ^ 3 = 1 := by
    have h' : (((η ^ 3 : 𝓞 K)) : K) = 1 := by
      rw [hη, hζ.toInteger_cube_eq_one]; simp
    push_cast at h'
    rw [hz, ← map_pow, h', map_one]
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at h3; norm_num at h3
  have hn : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h3 (by norm_num)
  have hz2 : starRingEnd ℂ z = z ^ 2 := by
    have h1 : z * starRingEnd ℂ z = 1 := by
      rw [Complex.mul_conj, ← Complex.sq_norm, hn]; simp
    apply mul_left_cancel₀ hz0
    rw [h1, ← pow_succ']
    exact h3.symm
  rw [hc, hx]
  push_cast
  simp only [map_add, map_mul, map_pow, map_intCast]
  rw [← hz, hz2]


theorem norm_sigma_of_norm (σ : K →+* ℂ) {π : 𝓞 K} {p : ℕ} (hπ : Algebra.norm ℤ π = p) :
    ‖σ (π : K)‖ = Real.sqrt p := by
  obtain ⟨n, h1, h2⟩ := CubicTC.mul_conj π
  have hn : n = p := by rw [← h2, hπ]
  subst hn
  have h3 := congrArg (fun y : 𝓞 K => σ (y : K)) h1
  push_cast at h3
  simp only [map_mul, sigma_conj] at h3
  rw [Complex.mul_conj] at h3
  have h4 : Complex.normSq (σ (π : K)) = (p : ℝ) := by
    have : ((Complex.normSq (σ (π : K)) : ℝ) : ℂ) = ((p : ℝ) : ℂ) := by
      rw [h3]; simp
    exact_mod_cast this
  rw [← Complex.sq_norm] at h4
  rw [← h4, Real.sqrt_sq (norm_nonneg _)]

/-- A generator of a height-one prime is prime. -/
theorem prime_of_span {v : HeightOneSpectrum (𝓞 K)} {π : 𝓞 K} (h : v.asIdeal = Ideal.span {π}) : Prime π := by
  have h0 : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at h
    exact v.ne_bot h
  rw [← Ideal.span_singleton_prime h0, ← h]
  exact v.isPrime

/-- A generator $\equiv 1 \bmod 3$ of a prime is prime to $3$. -/
theorem not_dvd_three {π : 𝓞 K} (hπ : Prime π) (h : (3 : 𝓞 K) ∣ π - 1) : ¬ π ∣ 3 := by
  intro h3
  have h1 : π ∣ π - 1 := h3.trans h
  have : π ∣ 1 := by
    have := dvd_sub (dvd_refl π) h1
    simpa using this
  exact hπ.not_isUnit (isUnit_of_dvd_one this)

theorem three_notMem_of_gen {v : HeightOneSpectrum (𝓞 K)} {π : 𝓞 K} (h : v.asIdeal = Ideal.span {π})
    (h3 : (3 : 𝓞 K) ∣ π - 1) : ((3 : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  rw [h, Ideal.mem_span_singleton]
  simpa using not_dvd_three (prime_of_span h) h3

theorem notMem_Sset_of_gen {v : HeightOneSpectrum (𝓞 K)} {π : 𝓞 K} {D : ℤ}
    (h : v.asIdeal = Ideal.span {π}) (h3 : ((3 : ℕ) : 𝓞 K) ∉ v.asIdeal) (hD : ¬ π ∣ (D : 𝓞 K)) :
    v ∉ Sset 3 {(D : K)} := by
  rw [notMem_Sset_iff]
  refine ⟨h3, ?_⟩
  have := (v.valuation_eq_one_iff_notMem (K := K) (r := (D : 𝓞 K))).2 (by
    rw [h, Ideal.mem_span_singleton]; exact hD)
  simpa using this


/-- At an inert prime $p \equiv 2 \bmod 3$ the cubic residue symbol of an integer prime to $p$ is $1$. -/
theorem powerResidue_inert {D : ℤ} {p : ℕ} (hp : p.Prime) (hp3 : p % 3 = 2) (hpD : ¬ (p : ℤ) ∣ D)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.span {(p : 𝓞 K)})
    (hvS : v ∉ Sset 3 {(D : K)}) : powerResidue 3 (D : K) v = 1 := by
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  refine (powerResidue_unique 3 (by norm_num) _ hζ (D : K) v hvS 1 ⟨by simp, ?_⟩).symm
  have hN : Ideal.absNorm v.asIdeal = p ^ 2 := by
    rw [hv, Ideal.absNorm_span_singleton]
    have : ((p : 𝓞 K)) = (((p : ℤ)) : 𝓞 K) := by simp
    rw [this, norm_intCast]
    simp
  obtain ⟨k, hk⟩ : ∃ k, p = 3 * k + 2 := ⟨p / 3, by omega⟩
  have hm : (p ^ 2 - 1) / 3 = (p - 1) * (k + 1) := by
    have e : p ^ 2 - 1 = 3 * ((p - 1) * (k + 1)) := by
      have hp1 : p - 1 = 3 * k + 1 := by omega
      rw [hp1]
      apply Nat.sub_eq_of_eq_add
      rw [hk]; ring
    rw [e]; omega
  rw [hN, hm]
  have hirr : Irreducible (p : ℤ) := (Nat.prime_iff_prime_int.1 hp).irreducible
  have hcop : IsCoprime D (p : ℤ) := ((Irreducible.coprime_iff_not_dvd hirr).2 hpD).symm
  have hfermat := Int.ModEq.pow_card_sub_one_eq_one hp hcop
  have h1 : D ^ ((p - 1) * (k + 1)) ≡ 1 [ZMOD p] := by
    rw [pow_mul]
    simpa using hfermat.pow (k + 1)
  have h2 : (p : ℤ) ∣ 1 - D ^ ((p - 1) * (k + 1)) := (Int.modEq_iff_dvd.1 h1)
  have h3 : (p : 𝓞 K) ∣ ((1 - D ^ ((p - 1) * (k + 1)) : ℤ) : 𝓞 K) := by
    have := map_dvd (Int.castRingHom (𝓞 K)) h2
    simpa using this
  have hmem : ((1 - D ^ ((p - 1) * (k + 1)) : ℤ) : 𝓞 K) ∈ v.asIdeal := by
    rw [hv, Ideal.mem_span_singleton]; exact h3
  have := (v.valuation_lt_one_iff_mem (K := K) _).2 hmem
  simpa using this

end NumberFieldKB.MilneCFT.Ch8.Ex101
