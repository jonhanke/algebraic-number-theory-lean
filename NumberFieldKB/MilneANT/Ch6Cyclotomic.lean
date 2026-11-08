import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 6: cyclotomic fields (the items not in Mathlib)

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers.

* **Remark 6.3(a)** (`remark_6_3_a_sign`, `remark_6_3_a_odd_iff`): for $\zeta$ a primitive $n$th root of $1$ with
  $n > 2$, the sign of $\operatorname{disc}(\mathbb Q[\zeta]/\mathbb Q)$ is $(-1)^s$ with
  $s = [\mathbb Q[\zeta]:\mathbb Q]/2$; for $n = p^r > 2$, $s = (p-1)p^{r-1}/2$ is odd iff $p^r = 4$ or
  $p \equiv 3 \pmod 4$.
* **Remark 6.3(b)** (`remark_6_3_b`): $\mathbb Q[\zeta] \cap \mathbb Q[\zeta'] = \mathbb Q$ for $\zeta$, $\zeta'$
  primitive $p^r$th and $q^s$th roots of $1$, $p \ne q$ primes.
* **Lemma 6.5**: see `Ch6Compositum.lean`.
* **Maximal real subfield** (running text, p. 101–102; `maximalRealSubfield_eq_adjoin`): for $n > 2$,
  $\mathbb Q[\zeta]$ is a CM field whose maximal totally real subfield is $\mathbb Q[\zeta]^+ = \mathbb Q[\zeta +
  \zeta^{-1}]$ (CM: Mathlib's `IsCyclotomicExtension.Rat.isCMField`).
* **Proposition 6.7** (`proposition_6_7`, `proposition_6_7_indexRealUnits`): for $n$ a prime power ($n > 2$),
  every unit of $\mathbb Q[\zeta_n]$ is $\zeta' v$ with $\zeta'$ a root of $1$ and $v$ a unit of
  $\mathbb Q[\zeta_n]^+$. Milne proves only the case of odd prime powers; the statement here is the full one.
-/

open NumberField IntermediateField

namespace NumberFieldKB.MilneANT

/-- **Remark 6.3(a), sign.** For $\zeta$ a primitive $n$th root of $1$ with $n > 2$ (so $\zeta \ne \pm 1$ and
$\mathbb Q[\zeta] \ne \mathbb Q$), the sign of the discriminant of $\mathbb Q[\zeta]$ is $(-1)^s$ with
$s = [\mathbb Q[\zeta]:\mathbb Q]/2$. -/
@[kb "milne2020ant" "v3.08, Remark 6.3(a), p. 99"]
theorem remark_6_3_a_sign {n : ℕ} [NeZero n] (hn : 2 < n) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] :
    (discr K).sign = (-1) ^ (Module.finrank ℚ K / 2) := by
  rw [sign_discr, IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two n,
    IsCyclotomicExtension.Rat.finrank (k := n) K]

/-- **Remark 6.3(a), parity.** If $p^r > 2$ with $p$ prime, then $[\mathbb Q[\zeta_{p^r}]:\mathbb Q]/2 =
(p-1)p^{r-1}/2$ is odd if and only if $p^r = 4$ or $p \equiv 3 \pmod 4$. -/
@[kb "milne2020ant" "v3.08, Remark 6.3(a), p. 99"]
theorem remark_6_3_a_odd_iff {p r : ℕ} (hp : p.Prime) (h : 2 < p ^ r) :
    Odd ((p ^ r).totient / 2) ↔ p ^ r = 4 ∨ p % 4 = 3 := by
  have hr : r ≠ 0 := by rintro rfl; simp at h
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [Nat.totient_prime_pow_succ hp]
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rcases r with _ | _ | r
    · simp at h
    · norm_num
    · have e : 2 ^ (r + 2) * (2 - 1) / 2 = 2 ^ (r + 1) := by
        rw [pow_succ _ (r+1)]; simp
      rw [e]
      have h8 : ¬ (2:ℕ) ^ (r + 2 + 1) = 4 := by
        rw [pow_succ]; have : 1 ≤ 2 ^ (r+2) := Nat.one_le_two_pow
        have : 2 ^ 2 ≤ 2 ^ (r+2) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      simp only [h8, false_or]
      constructor
      · intro ho; exfalso; rw [pow_succ] at ho; exact absurd ho (by simp [Nat.odd_mul])
      · intro h; omega
  · have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
    have hodd' : Odd (p ^ r) := hodd.pow
    obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
    have h1 : p ^ r * (p - 1) / 2 = p ^ r * m := by
      have : p ^ r * (p - 1) = 2 * (p ^ r * m) := by
        rw [hm]; simp; ring
      rw [this]; omega
    rw [h1, Nat.odd_mul]
    have h4 : ¬ p ^ (r+1) = 4 := by
      intro h4
      have : Odd (p ^ (r+1)) := hodd.pow
      rw [h4] at this; exact absurd this (by decide)
    simp only [h4, false_or, hodd', true_and, Nat.odd_iff]
    omega

/-- Over a field of characteristic zero, $\mathbb Q[\zeta]$ is a cyclotomic extension of $\mathbb Q$ for $\zeta$ a
primitive $n$th root of $1$. -/
theorem adjoin_isCyclotomicExtension_rat {L : Type*} [Field L] [CharZero L] {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ := by
  have halg : IsAlgebraic ℚ ζ := (hζ.isIntegral (NeZero.pos n)).tower_top.isAlgebraic
  change IsCyclotomicExtension {n} ℚ (ℚ⟮ζ⟯).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
  exact hζ.adjoin_isCyclotomicExtension ℚ

/-- **Remark 6.3(b).** Let $\zeta$ and $\zeta'$ be primitive $p^r$th and $q^s$th roots of $1$ in a field $L$ of
characteristic zero (Milne: in $\mathbb C$). If $p$ and $q$ are distinct primes, then
$\mathbb Q[\zeta] \cap \mathbb Q[\zeta'] = \mathbb Q$. -/
@[kb "milne2020ant" "v3.08, Remark 6.3(b), p. 99"]
theorem remark_6_3_b {L : Type*} [Field L] [CharZero L] {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ζ ζ' : L} (hζ : IsPrimitiveRoot ζ (p ^ r)) (hζ' : IsPrimitiveRoot ζ' (q ^ s)) :
    ℚ⟮ζ⟯ ⊓ ℚ⟮ζ'⟯ = ⊥ := by
  have hcop : Nat.Coprime (p ^ r) (q ^ s) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  have hp0 : NeZero (p ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hq0 : NeZero (q ^ s) := ⟨pow_ne_zero _ hq.ne_zero⟩
  have hN0 : NeZero (p ^ r * q ^ s) := ⟨mul_ne_zero hp0.out hq0.out⟩
  have hcomm : Commute ζ ζ' := Commute.all _ _
  have hξ : IsPrimitiveRoot (ζ * ζ') (p ^ r * q ^ s) := by
    rw [IsPrimitiveRoot.iff_orderOf, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [← hζ.eq_orderOf, ← hζ'.eq_orderOf]; exact hcop), ← hζ.eq_orderOf, ← hζ'.eq_orderOf]
  have hAc : IsCyclotomicExtension {p ^ r} ℚ ℚ⟮ζ⟯ := adjoin_isCyclotomicExtension_rat hζ
  have hBc : IsCyclotomicExtension {q ^ s} ℚ ℚ⟮ζ'⟯ := adjoin_isCyclotomicExtension_rat hζ'
  have hXc : IsCyclotomicExtension {p ^ r * q ^ s} ℚ ℚ⟮ζ * ζ'⟯ := adjoin_isCyclotomicExtension_rat hξ
  have hfA : Module.finrank ℚ ℚ⟮ζ⟯ = (p ^ r).totient := IsCyclotomicExtension.Rat.finrank _ _
  have hfB : Module.finrank ℚ ℚ⟮ζ'⟯ = (q ^ s).totient := IsCyclotomicExtension.Rat.finrank _ _
  have hfX : Module.finrank ℚ ℚ⟮ζ * ζ'⟯ = (p ^ r * q ^ s).totient :=
    IsCyclotomicExtension.Rat.finrank _ _
  have fdA : FiniteDimensional ℚ ℚ⟮ζ⟯ :=
    (IsCyclotomicExtension.numberField {p ^ r} ℚ ℚ⟮ζ⟯).to_finiteDimensional
  have fdB : FiniteDimensional ℚ ℚ⟮ζ'⟯ :=
    (IsCyclotomicExtension.numberField {q ^ s} ℚ ℚ⟮ζ'⟯).to_finiteDimensional
  have hle : ℚ⟮ζ * ζ'⟯ ≤ ℚ⟮ζ⟯ ⊔ ℚ⟮ζ'⟯ := by
    rw [adjoin_simple_le_iff]
    exact mul_mem ((le_sup_left : ℚ⟮ζ⟯ ≤ ℚ⟮ζ⟯ ⊔ ℚ⟮ζ'⟯) (mem_adjoin_simple_self ℚ ζ))
      ((le_sup_right : ℚ⟮ζ'⟯ ≤ ℚ⟮ζ⟯ ⊔ ℚ⟮ζ'⟯) (mem_adjoin_simple_self ℚ ζ'))
  have : FiniteDimensional ℚ ↥(ℚ⟮ζ⟯ ⊔ ℚ⟮ζ'⟯) := IntermediateField.finiteDimensional_sup _ _
  have h1 := IntermediateField.finrank_le_of_le_right hle
  have h2 := IntermediateField.finrank_sup_le ℚ⟮ζ⟯ ℚ⟮ζ'⟯
  have hD : Module.finrank ℚ ↥(ℚ⟮ζ⟯ ⊔ ℚ⟮ζ'⟯) = Module.finrank ℚ ℚ⟮ζ⟯ * Module.finrank ℚ ℚ⟮ζ'⟯ := by
    rw [hfX, Nat.totient_mul hcop, ← hfA, ← hfB] at h1
    omega
  exact (IntermediateField.LinearDisjoint.of_finrank_sup hD).inf_eq_bot

/-- **$\mathbb Q[\zeta]^+$ is the maximal real subfield** (Milne, running text before Proposition 6.7, p. 101–102).
For $\zeta$ a primitive $n$th root of $1$, $n > 2$, generating $K$, the field $\mathbb Q[\zeta]^+ =
\mathbb Q[\zeta + \zeta^{-1}]$ is the maximal real subfield $K^+$ of $K$ (the elements fixed by complex
conjugation under every embedding into $\mathbb C$, Mathlib's `maximalRealSubfield`). Together with Mathlib's
`IsCyclotomicExtension.Rat.isCMField` this is Milne's "$\mathbb Q[\zeta]$ is a CM field with maximal totally
real subfield $\mathbb Q[\zeta]^+$". -/
@[kb "milne2020ant" "v3.08, Units in cyclotomic fields, pp. 101-102"]
theorem maximalRealSubfield_eq_adjoin {n : ℕ} [NeZero n] (hn : 2 < n) {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (ℚ⟮ζ + ζ⁻¹⟯).toSubfield = maximalRealSubfield K := by
  have := IsCyclotomicExtension.Rat.isCMField K (S := {n}) ⟨n, rfl, hn⟩
  set M : IntermediateField ℚ K := (maximalRealSubfield K).toIntermediateField
    (fun q => by
      rw [mem_maximalRealSubfield_iff]; intro φ; simp) with hM
  have hMmem : ∀ x, x ∈ M ↔ x ∈ maximalRealSubfield K := fun x => Iff.rfl
  have ha : ζ + ζ⁻¹ ∈ M := by
    rw [hMmem, mem_maximalRealSubfield_iff]
    intro φ
    have h1 : ‖φ ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one
      (by rw [← map_pow, hζ.pow_eq_one, map_one]) (NeZero.ne n)
    have h2 := Complex.inv_eq_conj h1
    simp only [map_add, map_inv₀, star_add]
    rw [h2]
    simp [add_comm]
  have hle : ℚ⟮ζ + ζ⁻¹⟯ ≤ M := adjoin_simple_le_iff.mpr ha
  set E : IntermediateField ℚ K := ℚ⟮ζ + ζ⁻¹⟯ with hE
  have htop : (E⟮ζ⟯ : IntermediateField E K).restrictScalars ℚ = ⊤ := by
    refine eq_top_iff.mpr ?_
    have : ℚ⟮ζ⟯ = ⊤ :=
      adjoin_eq_top_of_algebra _ _ (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
    rw [← this, adjoin_simple_le_iff]
    exact mem_adjoin_simple_self E ζ
  have htop' : (E⟮ζ⟯ : IntermediateField E K) = ⊤ := by
    rw [← restrictScalars_eq_top_iff (K := ℚ)]; exact htop
  have hdeg : Module.finrank E K ≤ 2 := by
    have hint : IsIntegral E ζ := (Algebra.IsIntegral.isIntegral ζ)
    have h1 : Module.finrank E E⟮ζ⟯ = (minpoly E ζ).natDegree := adjoin.finrank hint
    rw [htop'] at h1
    rw [← IntermediateField.finrank_top', h1]
    have hp : (Polynomial.X ^ 2 - Polynomial.C (⟨ζ + ζ⁻¹, mem_adjoin_simple_self ℚ _⟩ : E) *
        Polynomial.X + 1 : Polynomial E) ≠ 0 := by
      intro h
      have := congrArg (fun p => p.coeff 2) h
      simp [Polynomial.coeff_one] at this
    have hr : Polynomial.aeval ζ (Polynomial.X ^ 2 - Polynomial.C
        (⟨ζ + ζ⁻¹, mem_adjoin_simple_self ℚ _⟩ : E) * Polynomial.X + 1 : Polynomial E) = 0 := by
      have hz : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
      simp
      field_simp
      ring
    have := minpoly.degree_le_of_ne_zero E ζ hp hr
    have hm : (Polynomial.X ^ 2 - Polynomial.C (⟨ζ + ζ⁻¹, mem_adjoin_simple_self ℚ _⟩ : E) *
        Polynomial.X + 1 : Polynomial E).natDegree = 2 := by
      compute_degree!
    exact (Polynomial.natDegree_le_natDegree this).trans hm.le
  have hK : Module.finrank ℚ K = Module.finrank ℚ E * Module.finrank E K :=
    (Module.finrank_mul_finrank ℚ E K).symm
  have hK2 : Module.finrank ℚ K = Module.finrank ℚ (maximalRealSubfield K) * 2 := by
    rw [← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K]
    exact (Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K).symm
  have heq : E = M := by
    refine eq_of_le_of_finrank_le hle ?_
    have : Module.finrank ℚ M = Module.finrank ℚ (maximalRealSubfield K) := rfl
    rw [this]
    have := Module.finrank_pos (R := ℚ) (M := E)
    nlinarith
  rw [heq]
  rfl

/-- The square of the norm to $\mathbb Q$ of a unit of the ring of integers is $1$. -/
theorem norm_unit_sq_eq_one {K : Type*} [Field K] [NumberField K] (v : (𝓞 K)ˣ) :
    (Algebra.norm ℚ ((v : 𝓞 K) : K)) ^ 2 = 1 := by
  have h1 : IsIntegral ℤ (Algebra.norm ℚ ((v : 𝓞 K) : K)) :=
    Algebra.isIntegral_norm ℚ (v : 𝓞 K).isIntegral_coe
  have h2 : IsIntegral ℤ (Algebra.norm ℚ (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) :=
    Algebra.isIntegral_norm ℚ ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K).isIntegral_coe
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  have hab : (Algebra.norm ℚ ((v : 𝓞 K) : K)) *
      Algebra.norm ℚ (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
    rw [← map_mul]
    have : ((v : 𝓞 K) : K) * (((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
      simp
    rw [this, map_one]
  rw [← ha, ← hb] at hab
  have hab' : a * b = 1 := by
    have : ((a * b : ℤ) : ℚ) = 1 := by simpa using hab
    exact_mod_cast this
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab' with rfl | rfl
  · rw [← ha]; simp
  · rw [← ha]; simp

/-- For a prime power $n > 2$, the norm of $\zeta - 1$ to $\mathbb Q$ is a prime. -/
theorem norm_zeta_sub_one {n : ℕ} [NeZero n] (hpow : IsPrimePow n) (hn : 2 < n) {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ∃ p : ℕ, p.Prime ∧ Algebra.norm ℚ (ζ - 1) = p := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  refine ⟨p, hp, ?_⟩
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
      rcases k with _ | j
      · simp at hn
      · exact ⟨j, rfl⟩
    have := hζ.norm_sub_one_two (K := ℚ) (L := K) (k := j + 2) (by omega)
      (Polynomial.cyclotomic.irreducible_rat (by positivity))
    simpa using this
  · exact hζ.norm_sub_one_of_prime_ne_two (K := ℚ) (L := K)
      (Polynomial.cyclotomic.irreducible_rat (by positivity)) h2

/-- For a prime power $n > 2$, $-\zeta$ generates the group of roots of unity of $\mathbb Q[\zeta]$. -/
theorem orderOf_neg_zeta {n : ℕ} [NeZero n] (hpow : IsPrimePow n) (hn : 2 < n) {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    orderOf (-ζ) = Units.torsionOrder K := by
  rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := n) (K := K)]
  by_cases hev : Even n
  · simp only [hev, ↓reduceIte]
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
    have hp2 : p = 2 := by
      have : 2 ∣ p ^ k := hev.two_dvd
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.prime_two.dvd_of_dvd_pow this)).symm
    subst hp2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := by
      rcases k with _ | _ | j
      · simp at hk
      · simp at hn
      · exact ⟨j, rfl⟩
    have hh : IsPrimitiveRoot (ζ ^ (2 ^ (j + 1))) 2 := by
      have := hζ.pow_of_dvd (p := 2 ^ (j + 1)) (by positivity) (pow_dvd_pow 2 (by omega))
      rwa [show 2 ^ (j + 2) / 2 ^ (j + 1) = 2 by
        rw [pow_succ 2 (j + 1), Nat.mul_div_cancel_left _ (by positivity)]] at this
    have hneg := hh.eq_neg_one_of_two_right
    have hcop : (2 ^ (j + 1) + 1).Coprime (2 ^ (j + 2)) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_two_right, Nat.odd_iff]
      rw [pow_succ]; omega
    have h3 := (hζ.pow_of_coprime _ hcop).eq_orderOf
    rw [pow_succ ζ (2 ^ (j + 1)), hneg, neg_one_mul] at h3
    rw [← h3, pow_succ]
  · simp only [hev, ↓reduceIte]
    have hodd : Odd n := Nat.not_even_iff_odd.mp hev
    have hcomm : Commute (-1 : K) ζ := Commute.all _ _
    have hc : Nat.Coprime (orderOf (-1 : K)) (orderOf ζ) := by
      rw [orderOf_neg_one, ← hζ.eq_orderOf]
      simp only [ringChar.eq_zero]
      exact Nat.coprime_two_left.mpr hodd
    have := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hc
    rw [neg_one_mul, orderOf_neg_one, ← hζ.eq_orderOf] at this
    simpa using this

/-- In a finite commutative group of even order, two elements of maximal order differ by a square. -/
theorem exists_eq_mul_sq_of_orderOf {G : Type*} [CommGroup G] [Finite G] (hev : Even (Nat.card G))
    (z g : G) (hz : orderOf z = Nat.card G) (hg : orderOf g = Nat.card G) :
    ∃ η : G, g = z * η ^ 2 := by
  have hN : 0 < Nat.card G := Nat.card_pos
  have hB : ∀ η : G, orderOf (η ^ 2) ≠ Nat.card G := by
    intro η h
    have hm : orderOf η ∣ Nat.card G := orderOf_dvd_natCard η
    have hle : orderOf η ≤ Nat.card G := Nat.le_of_dvd hN hm
    rw [orderOf_pow' η two_ne_zero] at h
    have h1 : orderOf η / Nat.gcd (orderOf η) 2 ≤ orderOf η := Nat.div_le_self _ _
    have h2 : orderOf η = Nat.card G := by omega
    rw [h2, Nat.gcd_eq_right (even_iff_two_dvd.mp hev)] at h
    omega
  have hzt : Subgroup.zpowers z = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hz]
  obtain ⟨j, hj⟩ : g ∈ Subgroup.zpowers z := hzt ▸ Subgroup.mem_top g
  obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
  · exfalso
    replace hj : z ^ (2 * i) = g := hj
    apply hB (z ^ i)
    rw [← zpow_natCast, ← zpow_mul, mul_comm i, Nat.cast_ofNat, hj, hg]
  · replace hj : z ^ (2 * i + 1) = g := hj
    refine ⟨z ^ i, ?_⟩
    rw [← hj, zpow_add_one, ← zpow_natCast (z ^ i), ← zpow_mul, mul_comm i]
    simp [mul_comm]

/-- For a prime power $n > 2$, $-\zeta$ is a root of unity of the ring of integers, of maximal order. -/
theorem exists_torsion_neg_zeta {n : ℕ} [NeZero n] (hpow : IsPrimePow n) (hn : 2 < n) {K : Type*}
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ∃ z : Units.torsion K, (((z : (𝓞 K)ˣ) : 𝓞 K) : K) = -ζ ∧ orderOf z = Units.torsionOrder K := by
  have hI : IsPrimitiveRoot hζ.toInteger n := hζ.toInteger_isPrimitiveRoot
  have hu : IsUnit hζ.toInteger := hI.isUnit (NeZero.ne n)
  set ε : (𝓞 K)ˣ := hu.unit with hε
  have hεn : ε ^ n = 1 := by
    ext
    simp [hε, hI.pow_eq_one]
  have hmem : -ε ∈ Units.torsion K := by
    show -ε ∈ CommGroup.torsion (𝓞 K)ˣ
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨2 * n, by have := NeZero.pos n; omega, ?_⟩
    rw [pow_mul, neg_sq, ← pow_mul, mul_comm, pow_mul, hεn, one_pow]
  have hco : (((-ε : (𝓞 K)ˣ) : 𝓞 K) : K) = -ζ := by
    simp [hε]
    exact hζ.coe_toInteger
  refine ⟨⟨-ε, hmem⟩, hco, ?_⟩
  rw [Subgroup.orderOf_mk, ← orderOf_units, ← orderOf_neg_zeta hpow hn hζ, ← hco]
  exact (orderOf_injective (algebraMap (𝓞 K) K).toMonoidHom
    (FaithfulSMul.algebraMap_injective (𝓞 K) K) _).symm

/-- Proof of the index form of Proposition 6.7: if the index were $2$, a unit $u$ with $u/\bar u$ a generator of
the roots of unity would give $w = u/((\zeta-1)\eta)$ in $K^+$ with $N(w) = q^2$ and $N(\zeta - 1) = p$, and then
$p$ would be a rational square. -/
theorem indexRealUnits_eq_one_of_isPrimePow {n : ℕ} [NeZero n] (hpow : IsPrimePow n) (hn : 2 < n)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.Rat.isCMField K (S := {n}) ⟨n, rfl, hn⟩
    IsCMField.indexRealUnits K = 1 := by
  have := IsCyclotomicExtension.Rat.isCMField K (S := {n}) ⟨n, rfl, hn⟩
  rcases IsCMField.indexRealUnits_eq_one_or_two K with h | h
  · exact h
  exfalso
  obtain ⟨u, hu⟩ := (IsCMField.indexRealUnits_eq_two_iff K).mp h
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  set ζ := IsCyclotomicExtension.zeta n ℚ K with hζdef
  obtain ⟨z, hzK, hzo⟩ := exists_torsion_neg_zeta hpow hn hζ
  set g := IsCMField.unitsMulComplexConjInv K u with hgdef
  have hgo : orderOf g = Units.torsionOrder K := by
    rw [← Nat.card_zpowers, hu]
    exact Subgroup.card_top
  have hev : Even (Nat.card (Units.torsion K)) := Units.even_torsionOrder K
  obtain ⟨η, hη⟩ := exists_eq_mul_sq_of_orderOf hev z g hzo hgo
  set a : K := ((u : 𝓞 K) : K) with ha
  set e : K := (((η : (𝓞 K)ˣ) : 𝓞 K) : K) with he
  have hz_c : IsCMField.complexConj K (-ζ) = (-ζ)⁻¹ := by
    have := IsCMField.complexConj_torsion K z
    have hzK' : (algebraMap (𝓞 K) K) ((z : (𝓞 K)ˣ) : 𝓞 K) = -ζ := hzK
    rwa [hzK'] at this
  have he_c : IsCMField.complexConj K e = e⁻¹ := IsCMField.complexConj_torsion K η
  have hcζ : IsCMField.complexConj K ζ = ζ⁻¹ := by
    rw [map_neg, inv_neg] at hz_c
    exact neg_injective hz_c
  have hgK : (((g : (𝓞 K)ˣ) : 𝓞 K) : K) = a * (IsCMField.complexConj K a)⁻¹ := by
    have := congrArg (fun x : (𝓞 K)ˣ => ((x : 𝓞 K) : K))
      (IsCMField.unitsMulComplexConjInv_apply K u)
    simpa using this
  have hgη : (((g : (𝓞 K)ˣ) : 𝓞 K) : K) = (-ζ) * e ^ 2 := by
    have := congrArg (fun x : Units.torsion K => (((x : (𝓞 K)ˣ) : 𝓞 K) : K)) hη
    simpa [hzK] using this
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by omega))
  have ha0 : a ≠ 0 := fun h => u.ne_zero (Subtype.ext h)
  have he0 : e ≠ 0 := fun h => (η : (𝓞 K)ˣ).ne_zero (Subtype.ext h)
  have hca0 : IsCMField.complexConj K a ≠ 0 := by simpa using ha0
  have hrel : a = -ζ * e ^ 2 * IsCMField.complexConj K a := by
    have h1 := hgK.symm.trans hgη
    field_simp at h1
    linear_combination h1
  set w : K := a / ((ζ - 1) * e) with hwdef
  have hζ1' : ζ⁻¹ - 1 ≠ 0 := by
    intro h
    apply hζ1
    field_simp at h
    linear_combination -h
  have hw : IsCMField.complexConj K w = w := by
    rw [hwdef, map_div₀, map_mul, map_sub, map_one, hcζ, he_c]
    have h1ζ : 1 - ζ ≠ 0 := by intro h; apply hζ1; linear_combination -h
    conv_rhs => rw [hrel]
    field_simp
    ring
  have hwK : w ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K w).mp hw
  obtain ⟨p, hp, hNp⟩ := norm_zeta_sub_one hpow hn hζ
  set w' : maximalRealSubfield K := ⟨w, hwK⟩ with hw'
  have hnorm : Algebra.norm ℚ w = (Algebra.norm ℚ w') ^ 2 := by
    rw [← Algebra.norm_norm (S := maximalRealSubfield K) (R := ℚ) (a := w)]
    have : w = algebraMap (maximalRealSubfield K) K w' := rfl
    rw [this, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, map_pow]
  have hmul : a = w * ((ζ - 1) * e) := by
    rw [hwdef]; field_simp
  have hNa : Algebra.norm ℚ a = (Algebra.norm ℚ w') ^ 2 * p * Algebra.norm ℚ e := by
    conv_lhs => rw [hmul]
    rw [map_mul, map_mul, hNp, hnorm]; ring
  set q := Algebra.norm ℚ w' with hq
  have h1 : (q ^ 2 * p) ^ 2 = 1 := by
    have hu1 := norm_unit_sq_eq_one u
    have he1 := norm_unit_sq_eq_one (η : (𝓞 K)ˣ)
    calc (q ^ 2 * p) ^ 2 = (q ^ 2 * p * Algebra.norm ℚ e) ^ 2 := by
          rw [mul_pow (q ^ 2 * p), he1, mul_one]
      _ = 1 := by rw [← hNa]; exact hu1
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have h2 : q ^ 2 * p = 1 := (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).mp h1
  have hq0 : q ≠ 0 := by
    rintro h; rw [h] at h2; simp at h2
  have hsq : IsSquare (p : ℚ) := ⟨q⁻¹, by field_simp; linarith⟩
  exact hp.prime.not_isSquare (Rat.isSquare_natCast_iff.mp hsq)

/-- **Proposition 6.7.** Assume that $n$ is a prime power, $n > 2$, and let $\zeta$ be a primitive $n$th root of
$1$ generating $K = \mathbb Q[\zeta]$. Then every unit $u$ of $\mathbb Q[\zeta]$ can be written $u = \zeta' v$
with $\zeta'$ a root of unity and $v$ a unit of $\mathbb Q[\zeta]^+ = \mathbb Q[\zeta + \zeta^{-1}]$.
Milne proves only the case of odd prime powers; here $n = 2^k$ ($k \ge 2$) is included. -/
@[kb "milne2020ant" "v3.08, Proposition 6.7, p. 102"]
theorem proposition_6_7 {n : ℕ} [NeZero n] (hpow : IsPrimePow n) (hn : 2 < n) {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (u : (𝓞 K)ˣ) :
    ∃ η ∈ Units.torsion K, ∃ v : (𝓞 K)ˣ, ((v : 𝓞 K) : K) ∈ ℚ⟮ζ + ζ⁻¹⟯ ∧ u = η * v := by
  have := IsCyclotomicExtension.Rat.isCMField K (S := {n}) ⟨n, rfl, hn⟩
  have hidx := indexRealUnits_eq_one_of_isPrimePow hpow hn K
  have htop : IsCMField.realUnits K ⊔ Units.torsion K = ⊤ := Subgroup.index_eq_one.mp hidx
  have hu : u ∈ IsCMField.realUnits K ⊔ Units.torsion K := htop ▸ Subgroup.mem_top u
  obtain ⟨v, hv, η, hη, huv⟩ := Subgroup.mem_sup.mp hu
  refine ⟨η, hη, v, ?_, by rw [← huv, mul_comm]⟩
  obtain ⟨v', hv'⟩ := (IsCMField.mem_realUnits_iff K v).mp hv
  have hmem : ((v : 𝓞 K) : K) ∈ maximalRealSubfield K := by
    rw [← hv']
    have : (((algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) (v' : 𝓞 (maximalRealSubfield K)) : 𝓞 K)) : K)
        = ((((v' : 𝓞 (maximalRealSubfield K)) : maximalRealSubfield K)) : K) := rfl
    simpa using this ▸ SetLike.coe_mem (((v' : 𝓞 (maximalRealSubfield K)) : maximalRealSubfield K))
  rw [← maximalRealSubfield_eq_adjoin hn hζ] at hmem
  exact hmem

/-- **Proposition 6.7, index form.** For $n > 2$ a prime power, the index of $\mu(K)\,U_{K^+}$ in $U_K$
(Mathlib's `IsCMField.indexRealUnits`, which is $1$ or $2$ by Proposition 5.12) is $1$. -/
@[kb "milne2020ant" "v3.08, Proposition 6.7, p. 102"]
theorem proposition_6_7_indexRealUnits {n : ℕ} [NeZero n] (hpow : IsPrimePow n) (hn : 2 < n) (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.Rat.isCMField K (S := {n}) ⟨n, rfl, hn⟩
    IsCMField.indexRealUnits K = 1 :=
  indexRealUnits_eq_one_of_isPrimePow hpow hn K

end NumberFieldKB.MilneANT
