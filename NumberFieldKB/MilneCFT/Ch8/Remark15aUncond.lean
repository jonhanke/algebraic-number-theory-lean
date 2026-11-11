import NumberFieldKB.MilneCFT.Ch8.Remark15aBridge
import NumberFieldKB.MilneCFT.Ch8.Remark15aAlgebra
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Milne, *CFT*, VIII, Remark 1.5 (a), unconditionally

**Proved here:** `remark1_5a : Remark1_5a K` (for a finite set `S` of primes and `n ≥ 1`, the group `P(n, S)` of
elements that are `n`-th powers at every finite prime outside `S` is `K^{×n}` or `K^{×n} ⊔ a₀ K^{×n}`; Artin–Tate X,
Theorem 1) and `remark1_5aRat : Remark1_5aRat` (`P(8, S) = ℚ^{×8} ⊔ 16 ℚ^{×8}` when `2 ∈ S`).

Proof: for a prime power `q = p^r` and `a, a' ∈ P(q, S)`, every element of `Gal(M/K)`, `M = K(ζ_q, a^{1/q}, a'^{1/q})`,
fixes a root `ζ^i α` (Chebotarev, `forall_fixed_of_mem_powSet`), and the algebra of `Remark15aAlgebra.lean` gives:
`a ∈ K^{×q}` for `p` odd, and one of `a, a', a/a'` in `K^{×q}` for `p = 2`. For general `n = 2^r m`, `m` odd, elements of
`P(n, S)` are `m`-th powers (coprime prime powers combine, `exists_pow_mul_of_coprime`) of elements of `P(2^r, S)`
(`mem_powSet_of_pow_mem`).
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.R15a

variable {K : Type} [Field K] [NumberField K]

theorem exists_units_pow {q : ℕ} (hq : 0 < q) {a : Kˣ} {b : K} (hb : b ^ q = (a : K)) :
    ∃ c : Kˣ, c ^ q = a := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hq.ne'] at hb
    exact a.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, Units.ext (by simpa using hb)⟩

/-- **Prime powers: the dichotomy in `Kˣ`.** -/
theorem powSet_prime_pow_dichotomy {p r : ℕ} (hp : p.Prime) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) {a a' : Kˣ} (ha : a ∈ powSet (p ^ r) S) (ha' : a' ∈ powSet (p ^ r) S) :
    (∃ b : Kˣ, b ^ (p ^ r) = a) ∨ (∃ b : Kˣ, b ^ (p ^ r) = a') ∨ ∃ b : Kˣ, b ^ (p ^ r) * a' = a := by
  have hq : 0 < p ^ r := pow_pos hp.pos r
  obtain ⟨M, _, _, _, _, _, ζ, α, α', hζ, hα, hα'⟩ := exists_splitting (K := K) hq (a : K) (a' : K)
  have hfa := forall_fixed_of_mem_powSet hq hζ hS ha hα
  have hfa' := forall_fixed_of_mem_powSet hq hζ hS ha' hα'
  rcases dichotomy hp hζ a.ne_zero a'.ne_zero hα hα' hfa hfa' with ⟨b, hb⟩ | ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl (exists_units_pow hq hb)
  · exact Or.inr (Or.inl (exists_units_pow hq hb))
  · have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hq.ne', zero_mul] at hb
      exact a.ne_zero hb.symm
    refine Or.inr (Or.inr ⟨Units.mk0 b hb0, Units.ext ?_⟩)
    simpa using hb

/-- **Odd prime powers.** -/
theorem powSet_odd_prime_pow {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) {a : Kˣ} (ha : a ∈ powSet (p ^ r) S) : ∃ b : Kˣ, b ^ (p ^ r) = a := by
  have hq : 0 < p ^ r := pow_pos hp.pos r
  obtain ⟨M, _, _, _, _, _, ζ, α, -, hζ, hα, -⟩ := exists_splitting (K := K) hq (a : K) (a : K)
  obtain ⟨b, hb⟩ := pow_of_odd hp hp2 hζ hα (forall_fixed_of_mem_powSet hq hζ hS ha hα)
  exact exists_units_pow hq hb

/-- **Odd exponents: `P(m, S) = K^{×m}`.** -/
theorem powSet_odd {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) :
    ∀ m : ℕ, Odd m → ∀ a ∈ powSet m S, ∃ b : Kˣ, b ^ m = a := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hodd a ha
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow' hk.ne').2 even_two)
    exact powSet_odd_prime_pow hp hp2 hS ha
  | zero => intro h; exact absurd h (by decide)
  | one => intro _ a _; exact ⟨a, pow_one a⟩
  | coprime m₁ m₂ _ _ hcop ih₁ ih₂ =>
    intro hodd a ha
    obtain ⟨c₁, hc₁⟩ := ih₁ (Nat.Odd.of_mul_left hodd) a (mem_powSet_of_dvd (Dvd.intro _ rfl) ha)
    obtain ⟨c₂, hc₂⟩ := ih₂ (Nat.Odd.of_mul_right hodd) a (mem_powSet_of_dvd (Dvd.intro_left _ rfl) ha)
    obtain ⟨z, hz⟩ := exists_pow_mul_of_coprime hcop (hc₁.trans hc₂.symm)
    exact ⟨z, hz.trans hc₁⟩

/-- **The dichotomy for every exponent.** -/
theorem powSet_dichotomy {n : ℕ} (hn : 0 < n) {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite)
    {a a' : Kˣ} (ha : a ∈ powSet n S) (ha' : a' ∈ powSet n S) :
    (∃ b : Kˣ, b ^ n = a) ∨ (∃ b : Kˣ, b ^ n = a') ∨ ∃ b : Kˣ, b ^ n * a' = a := by
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨c, hc⟩ := powSet_odd hS m hm a (mem_powSet_of_dvd (Dvd.intro_left _ rfl) ha)
  obtain ⟨c', hc'⟩ := powSet_odd hS m hm a' (mem_powSet_of_dvd (Dvd.intro_left _ rfl) ha')
  have hcop : Nat.Coprime m (2 ^ r) := (Nat.coprime_two_right.2 hm).pow_right r
  have hcS : c ∈ powSet (2 ^ r) S :=
    mem_powSet_of_pow_mem hcop (hc ▸ mem_powSet_of_dvd (Dvd.intro _ rfl) ha)
  have hcS' : c' ∈ powSet (2 ^ r) S :=
    mem_powSet_of_pow_mem hcop (hc' ▸ mem_powSet_of_dvd (Dvd.intro _ rfl) ha')
  rcases powSet_prime_pow_dichotomy Nat.prime_two hS hcS hcS' with ⟨b, hb⟩ | ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨b, by rw [← hc, ← hb, pow_mul]⟩
  · exact Or.inr (Or.inl ⟨b, by rw [← hc', ← hb, pow_mul]⟩)
  · exact Or.inr (Or.inr ⟨b, by rw [← hc, ← hc', ← hb, mul_pow, pow_mul]⟩)

/-- **Remark VIII.1.5 (a)** (Artin–Tate X, Theorem 1), unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Remark 1.5 (a), p. 230"]
theorem remark1_5a : Remark1_5a K := by
  refine ⟨fun n hn S hS => ?_⟩
  by_cases h : powSet n S ⊆ Set.range (fun b : Kˣ => b ^ n)
  · left
    refine Set.Subset.antisymm h ?_
    rintro _ ⟨b, rfl⟩
    exact pow_mem_powSet n S b
  · right
    obtain ⟨a₀, ha₀, ha₀n⟩ := Set.not_subset.1 h
    refine ⟨a₀, Set.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
    · rcases powSet_dichotomy hn hS ha ha₀ with hb | hb | ⟨b, hb⟩
      · exact Or.inl hb
      · exact absurd hb ha₀n
      · exact Or.inr ⟨b, by rw [← hb, mul_comm]⟩
    · rcases ha with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact pow_mem_powSet n S b
      · exact mul_mem_powSet ha₀ (pow_mem_powSet n S b)

theorem sixteenUnit_not_pow : ¬ ∃ b : ℚˣ, b ^ 8 = sixteenUnit := by
  rintro ⟨b, hb⟩
  apply sixteen_not_eighth_power_rat
  refine ⟨(b : ℚ), ?_⟩
  have := congrArg (fun u : ℚˣ => (u : ℚ)) hb
  simpa [sixteenUnit] using this

/-- **Remark VIII.1.5 (a), the example `ℚ`, `n = 8`**, unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Remark 1.5 (a), p. 230 (P(8,S) for Q)"]
theorem remark1_5aRat : Remark1_5aRat := by
  refine ⟨fun S hS h2 => ?_⟩
  have h16 := sixteen_mem_powSet S h2
  rcases (remark1_5a (K := ℚ)).dichotomy 8 (by norm_num) S hS with h | ⟨a₀, h⟩
  · rw [h] at h16
    exact absurd h16 sixteenUnit_not_pow
  · rw [h]
    have h16' := h16
    rw [h] at h16'
    rcases h16' with h1 | ⟨b, hb⟩
    · exact absurd h1 sixteenUnit_not_pow
    · congr 1
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨c * b⁻¹, by
          simp only at hb
          show sixteenUnit * (c * b⁻¹) ^ 8 = a₀ * c ^ 8
          rw [← hb, mul_pow, inv_pow, mul_comm (c ^ 8), ← mul_assoc, mul_assoc a₀, mul_inv_cancel, mul_one]⟩
      · rintro ⟨c, rfl⟩
        exact ⟨b * c, by
          simp only at hb
          show a₀ * (b * c) ^ 8 = sixteenUnit * c ^ 8
          rw [← hb, mul_pow, mul_assoc]⟩

end NumberFieldKB.MilneCFT.Ch8.R15a
