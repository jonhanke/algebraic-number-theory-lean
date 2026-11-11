import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 6: citations of the results in Mathlib

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.
Locators give Milne's printed page numbers (pdf page − 2).

When Mathlib states a result in Milne's form, the Mathlib declaration is tagged (`attribute [kb ...]`); when the
forms differ, a short theorem restates it in Milne's form. The other Chapter 6 items are in
`Ch6Cyclotomic.lean`, `Ch6Compositum.lean`, `Ch6Fermat.lean` and `Ch6FermatThm.lean`.

* Lemma 6.1, Proposition 6.2(a)–(c), Theorem 6.4, Remark 6.6(b),(c), and the prose definitions (primitive root of
  unity, cyclotomic polynomial, Bernoulli numbers): tagged Mathlib declarations.
* Proposition 6.2(d) (`proposition_6_2_d`, `proposition_6_2_d_unramified`), Theorem 6.4(c)
  (`theorem_6_4_c_ramified`), Remark 6.6(a) (`remark_6_6_a`): restated.
-/

open NumberField

namespace NumberFieldKB.MilneANT

attribute [kb "milne2020ant" "v3.08, Lemma 6.1, p. 95"] IsPrimitiveRoot.pow_iff_coprime

attribute [kb "milne2020ant" "v3.08, Proposition 6.2(a) and Theorem 6.4(a), pp. 96, 99"]
  IsCyclotomicExtension.Rat.finrank
attribute [kb "milne2020ant" "v3.08, Proposition 6.2(b), p. 96"]
  IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
attribute [kb "milne2020ant" "v3.08, Proposition 6.2(c), p. 96 (1 - ζ is prime)"]
  IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one
attribute [kb "milne2020ant" "v3.08, Proposition 6.2(c), p. 96 ((p) = (1 - ζ)^φ(p^r))"]
  IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow

/-- **Proposition 6.2(d), discriminant.** For $\zeta$ a primitive $p^r$th root of $1$ ($r \ge 1$) and
$K = \mathbb Q[\zeta]$, the discriminant of $\mathcal O_K$ over $\mathbb Z$ is $\pm p^c$ with
$c = p^{r-1}(pr - r - 1)$. Mathlib computes the discriminant of the power basis of $\zeta - 1$
(`IsCyclotomicExtension.Rat.discr_prime_pow'`) and of $K$ in general (`IsCyclotomicExtension.Rat.discr`). -/
@[kb "milne2020ant" "v3.08, Proposition 6.2(d), p. 96"]
theorem proposition_6_2_d (p r : ℕ) [Fact p.Prime] (hr : 1 ≤ r) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p ^ r} ℚ K] :
    discr K = (p : ℤ) ^ (p ^ (r - 1) * (p * r - r - 1)) ∨ discr K = -(p : ℤ) ^ (p ^ (r - 1) * (p * r - r - 1)) := by
  obtain ⟨r, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have h := IsCyclotomicExtension.Rat.discr_prime_pow_succ p r K
  have hexp : p ^ r * ((p - 1) * (r + 1) - 1) = p ^ (r + 1 - 1) * (p * (r + 1) - (r + 1) - 1) := by
    have : (p - 1) * (r + 1) = p * (r + 1) - (r + 1) := by
      rw [Nat.sub_mul, one_mul]
    simp [this]
  rw [hexp] at h
  rcases neg_one_pow_eq_or ℤ (p ^ r * (p - 1) / 2) with h1 | h1 <;> rw [h1] at h
  · left; simpa using h
  · right; simpa using h

/-- **Proposition 6.2(d), ramification.** $p$ is the only prime that ramifies in $\mathbb Q[\zeta_{p^r}]$: every
prime ideal over a prime $\ell \ne p$ has ramification index $1$. Mathlib:
`IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`. -/
@[kb "milne2020ant" "v3.08, Proposition 6.2(d), p. 96"]
theorem proposition_6_2_d_unramified (p r ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (K : Type*)
    [Field K] [NumberField K] [IsCyclotomicExtension {p ^ r} ℚ K] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(ℓ : ℤ)})] : P.ramificationIdx ℤ = 1 := by
  have hne : ¬ ℓ ∣ p ^ r := fun hd =>
    hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 ((Fact.out : ℓ.Prime).dvd_of_dvd_pow hd))
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (p := ℓ) (m := p ^ r) K P hne

attribute [kb "milne2020ant" "v3.08, Theorem 6.4(a), p. 99"] Polynomial.cyclotomic.irreducible_rat
attribute [kb "milne2020ant" "v3.08, Theorem 6.4(b), p. 99"]
  IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton IsPrimitiveRoot.integralPowerBasis
attribute [kb "milne2020ant" "v3.08, Theorem 6.4(c), p. 99 (primes not dividing n are unramified)"]
  IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
attribute [kb "milne2020ant" "v3.08, Theorem 6.4(c), p. 99 (e = φ(p^r) for n = p^r m)"]
  IsCyclotomicExtension.Rat.ramificationIdxIn_eq IsCyclotomicExtension.Rat.inertiaDegIn_eq

/-- **Theorem 6.4(c), first assertion.** If a prime $p$ ramifies in $\mathbb Q[\zeta_n]$ (some prime ideal over
$p$ has ramification index $> 1$), then $p \mid n$. -/
@[kb "milne2020ant" "v3.08, Theorem 6.4(c), p. 99"]
theorem theorem_6_4_c_ramified {n : ℕ} [NeZero n] (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (h : 1 < P.ramificationIdx ℤ) : p ∣ n := by
  by_contra hp
  have := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (p := p) (m := n) K P hp
  omega

/-- **Remark 6.6(a).** If a prime $p$ divides $n$, then $p$ ramifies in $\mathbb Q[\zeta_n]$ (the ramification
index of the primes over $p$, Mathlib's `ramificationIdxIn`, is $> 1$) except when $p = 2$ and $n = 2 \cdot$(odd
number). -/
@[kb "milne2020ant" "v3.08, Remark 6.6(a), p. 100"]
theorem remark_6_6_a {n : ℕ} [NeZero n] (p : ℕ) [Fact p.Prime] (hp : p ∣ n) (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    1 < (Ideal.span {(p : ℤ)}).ramificationIdxIn (𝓞 K) ↔ ¬ (p = 2 ∧ n % 4 = 2) := by
  obtain ⟨e, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p (Fact.out : p.Prime).ne_one
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    refine ⟨e - 1, ?_⟩
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · subst h0; simp at hn; subst hn; exact absurd hp hm
    · omega
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq n K hn hm]
  have h2 := (Fact.out : p.Prime).two_le
  rcases Nat.eq_or_lt_of_le h2 with h | h
  · subst h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [pow_zero, zero_add, pow_one] at hn ⊢
      have : n % 4 = 2 := by omega
      simp [this]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have h4 : n % 4 = 0 := by
        rw [hn, show 2 ^ (j + 1 + 1) = 4 * 2 ^ j by ring]
        simp [Nat.mul_assoc]
      have : 1 < 2 ^ (j + 1) * (2 - 1) := by
        have := Nat.one_lt_two_pow (n := j + 1) (by omega)
        omega
      simp [h4]
  · have : 1 < p ^ k * (p - 1) := by
      have : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
      have : 2 ≤ p - 1 := by omega
      nlinarith
    have : p ≠ 2 := by omega
    simp [*]

attribute [kb "milne2020ant" "v3.08, Remark 6.6(b), p. 100 (μ(ℚ[ζ_n]) has order n or 2n)"]
  IsCyclotomicExtension.Rat.torsionOrder_eq
attribute [kb "milne2020ant" "v3.08, Remark 6.6(c), p. 101 (discriminant of a compositum; Mathlib's hypothesis: coprime different ideals and linear disjointness)"]
  NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
attribute [kb "milne2020ant" "v3.08, Remark 6.6(c), p. 101 (discriminant of ℚ[ζ_n])"]
  IsCyclotomicExtension.Rat.discr

/-! ### Prose definitions of Chapter 6 -/

attribute [kb "milne2020ant" "v3.08, Ch. 6, primitive n-th root of 1, p. 95"] IsPrimitiveRoot
attribute [kb "milne2020ant" "v3.08, Ch. 6, cyclotomic polynomial, p. 96"] Polynomial.cyclotomic
/- Milne's Bernoulli numbers ($t/(e^t - 1) = \sum B_n t^n/n!$, so $B_1 = -1/2$) are Mathlib's `bernoulli`
(`bernoulliPowerSeries`), not `bernoulli'` (which has $B_1 = 1/2$). -/
attribute [kb "milne2020ant" "v3.08, Ch. 6, Bernoulli numbers, p. 101"] bernoulli bernoulliPowerSeries

end NumberFieldKB.MilneANT
