import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import QuadFormsKB.Citation

/-!
# Milne, *Algebraic Number Theory*, Chapter 3: discrete valuations

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), pp. 55–56; bib key `milne2020ant`.

Milne's discrete valuation is an additive surjection-up-to-scaling $v : K^\times \to \mathbb Z$ with
$v(a+b) \ge \min(v(a), v(b))$. Mathlib's counterpart is a valuation `v : Valuation K ℤᵐ⁰` with values in
$\mathbb Z \cup \{0\}$ written multiplicatively: Milne's $v(a) = m$ corresponds to
`v a = WithZero.coe (Multiplicative.ofAdd (-m))` (Mathlib's convention makes elements of positive order small).

* `IsNormalizedDiscreteValuation` (a definition in prose, p. 55): $v$ is normalized if $v(K^\times) = \mathbb Z$.
* **Example 3.26** (`example_3_26_a`, `example_3_26_b`, `example_3_26_c`).
-/

open Multiplicative WithZero

namespace NumberFieldKB.MilneANT

/-- **Normalized discrete valuation** (Milne p. 55, a definition in prose). A valuation $v$ on a field $K$ with values
in $\mathbb Z \cup \{0\}$ (Mathlib's `ℤᵐ⁰`, Milne's $\mathbb Z \cup \{\infty\}$ written multiplicatively) is a
normalized discrete valuation if every integer is a value, i.e. $v : K^\times \to \mathbb Z$ is surjective. -/
@[kb "milne2020ant" "v3.08, Ch. 3, definition in prose (normalized discrete valuation), p. 55"]
def IsNormalizedDiscreteValuation {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) : Prop :=
  ∀ m : ℤ, ∃ x : K, v x = (ofAdd m : Multiplicative ℤ)

/-- **Example 3.26 (a).** For meromorphic functions $f, g$ at a point $P \in \mathbb C$, the order
$\mathrm{ord}_P$ (Mathlib's `meromorphicOrderAt`, valued in $\mathbb Z \cup \{\infty\}$, $\infty$ for the zero germ)
satisfies $\mathrm{ord}_P(fg) = \mathrm{ord}_P f + \mathrm{ord}_P g$,
$\mathrm{ord}_P(f+g) \ge \min(\mathrm{ord}_P f, \mathrm{ord}_P g)$, and $\mathrm{ord}_P(z - P) = 1$: it is a
normalized discrete valuation on the meromorphic functions. (Mathlib has no field of meromorphic functions on a
connected open set; the valuation properties are stated for germs at $P$.) -/
@[kb "milne2020ant" "v3.08, Example 3.26 (a), p. 55"]
theorem example_3_26_a {f g : ℂ → ℂ} {P : ℂ} (hf : MeromorphicAt f P) (hg : MeromorphicAt g P) :
    meromorphicOrderAt (f * g) P = meromorphicOrderAt f P + meromorphicOrderAt g P ∧
      min (meromorphicOrderAt f P) (meromorphicOrderAt g P) ≤ meromorphicOrderAt (f + g) P ∧
      meromorphicOrderAt (fun z => z - P) P = 1 :=
  ⟨meromorphicOrderAt_mul hf hg, meromorphicOrderAt_add hf hg, meromorphicOrderAt_id_sub_const⟩

private theorem normalized_adic {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (v : IsDedekindDomain.HeightOneSpectrum A) :
    IsNormalizedDiscreteValuation (v.valuation K) := by
  intro m
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  refine ⟨π ^ (-m), ?_⟩
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp [WithZero.exp]

/-- **Example 3.26 (b).** Let $A$ be a principal ideal domain with field of fractions $K$ and $\pi$ a prime element.
Writing $c \in K^\times$ as $c = \pi^m a/b$ with $a, b \in A$ prime to $\pi$, $v(c) = m$ defines a normalized discrete
valuation on $K$. Here $v$ is the valuation of the prime ideal $(\pi)$ (Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation`), and $v(c) = m$ reads `v c = ofAdd (-m)`. -/
@[kb "milne2020ant" "v3.08, Example 3.26 (b), p. 55"]
theorem example_3_26_b {A K : Type*} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] (π : A) (hπ : Prime π) :
    ∃ v : IsDedekindDomain.HeightOneSpectrum A, v.asIdeal = Ideal.span {π} ∧
      IsNormalizedDiscreteValuation (v.valuation K) ∧
      ∀ (m : ℤ) (a b : A), ¬ π ∣ a → ¬ π ∣ b →
        v.valuation K (algebraMap A K π ^ m * algebraMap A K a / algebraMap A K b) =
          (ofAdd (-m) : Multiplicative ℤ) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  let v : IsDedekindDomain.HeightOneSpectrum A :=
    ⟨Ideal.span {π}, (Ideal.span_singleton_prime hπ0).mpr hπ, by
      simpa using hπ0⟩
  have hv : v.asIdeal = Ideal.span {π} := rfl
  have key : v.valuation K (algebraMap A K π) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_singleton hπ0 hv
  have hnd : ∀ a : A, ¬ π ∣ a → v.valuation K (algebraMap A K a) = 1 := by
    intro a ha
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem, hv]
    rwa [Ideal.mem_span_singleton]
  refine ⟨v, hv, normalized_adic v, ?_⟩
  intro m a b ha hb
  rw [map_div₀, map_mul, map_zpow₀, key, hnd a ha, hnd b hb, ← WithZero.exp_zsmul]
  simp [WithZero.exp]

/-- **Example 3.26 (c).** For a nonzero prime $\mathfrak p$ of a Dedekind domain $A$ with field of fractions $K$, the
exponent $\mathrm{ord}_{\mathfrak p}(c)$ of $\mathfrak p$ in the factorization of $(c)$ is a normalized discrete
valuation on $K$ (Mathlib's adic valuation `IsDedekindDomain.HeightOneSpectrum.valuation`). -/
@[kb "milne2020ant" "v3.08, Example 3.26 (c), p. 56"]
theorem example_3_26_c {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (v : IsDedekindDomain.HeightOneSpectrum A) :
    IsNormalizedDiscreteValuation (v.valuation K) :=
  normalized_adic v

end NumberFieldKB.MilneANT
