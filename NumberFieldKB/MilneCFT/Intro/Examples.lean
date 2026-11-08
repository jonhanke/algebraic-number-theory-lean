import NumberFieldKB.MilneCFT.Intro.Theorems

/-!
# Examples and exercises of the Introduction (Milne, *Class Field Theory*, Introduction)

Concrete computations for specific quadratic and biquadratic fields, stated as named statements (they are
computations with class groups and ramification of specific fields, out of reach of this job; nothing here is
assumed by other results). A specific field such as $\mathbb Q[\sqrt 6]$ is given as an arbitrary number field $F$
of degree $2$ containing a square root of $6$ (any two such are isomorphic).

* Example 0.6 / Exercise 0.14 (`Example06`), Example 0.7 (`Example07`), Exercise 0.11 (`Exercise011`),
  Exercise 0.12 (`Exercise012`), Exercise 0.15 (`Exercise015`).
-/

open NumberField IsDedekindDomain
open NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField

noncomputable section

namespace NumberFieldKB.MilneCFT

/-- **Example 0.6 / Exercise 0.14** (named statement; Milne, *CFT*, Introduction): $\mathbb Q[\sqrt 6]$ has class
number $1$ (so it is its own Hilbert class field), its narrow class group has order $2$, and
$\mathbb Q[\sqrt{-2}, \sqrt{-3}]$ is a quadratic extension of it unramified at all finite primes but ramified at both
infinite primes.

Correction (2026-11-05): the field was formalized earlier as $\mathbb Q[\sqrt 2, \sqrt 3]$, which
makes the statement false ($\mathbb Q[\sqrt 2,\sqrt 3]$ is totally real, so no infinite place ramifies, and the prime
above $2$ ramifies in it). The extension with the stated properties is $\mathbb Q[\sqrt{-2}, \sqrt{-3}]$ (discriminant
$24^2$, totally complex), the narrow Hilbert class field of $\mathbb Q[\sqrt 6]$. To be checked against the book's
wording before recording a book erratum [unverified]. -/
@[kb "milne2020cft" "Introduction, Example 0.6 and Exercise 0.14 (input)"]
structure Example06 : Prop where
  classNumber_eq : ∀ (F : Type) [Field F] [NumberField F], Module.finrank ℚ F = 2 → (∃ s : F, s ^ 2 = 6) →
    classNumber F = 1
  narrow_card : ∀ (F : Type) [Field F] [NumberField F], Module.finrank ℚ F = 2 → (∃ s : F, s ^ 2 = 6) →
    Nat.card (RayClassGroup (narrowModulus F)) = 2
  unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank ℚ F = 2 → (∃ s : F, s ^ 2 = 6) → Module.finrank F E = 2 → (∃ a b : E, a ^ 2 = -2 ∧ b ^ 2 = -3) →
    (∀ v : HeightOneSpectrum (𝓞 F), v ∈ unramifiedPrimes F E) ∧
      ∀ w : NumberField.InfinitePlace F, InfinitePlace.RamifiesIn E w

/-- **Example 0.7** (named statement; Milne, *CFT*, Introduction): let $p_1, \dots, p_t$ be distinct odd primes,
$p_i^* = (-1)^{(p_i-1)/2}p_i$ and $d = p_1^* \cdots p_t^*$. Then $L = K[\sqrt{p_1^*}, \dots, \sqrt{p_{t-1}^*}]$ is
unramified over $K = \mathbb Q[\sqrt d]$ at all finite primes, of degree $2^{t-1}$; hence the narrow class group
$C^+$ of $K$ satisfies $(C^+ : C^{+2}) \ge 2^{t-1}$. -/
@[kb "milne2020cft" "Introduction, Example 0.7 (input)"]
structure Example07 : Prop where
  narrow_index : ∀ (t : ℕ) (p : Fin t → ℕ), Function.Injective p → (∀ i, (p i).Prime ∧ p i ≠ 2) →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    (∃ s : K, s ^ 2 = ∏ i, ((-1 : ℚ) ^ ((p i - 1) / 2) * (p i : ℚ) : K)) →
    2 ^ (t - 1) ≤ (Subgroup.closure {x : RayClassGroup (narrowModulus K) | ∃ y, x = y ^ 2}).index

/-- **Exercise 0.11** (named statement; Milne, *CFT*, Introduction, a precise form): for a quadratic field
$L = \mathbb Q[\sqrt D]$ ($D$ a squarefree integer $\ne 0, 1$), whether an odd prime $p \nmid D$ splits in $L$ is
determined by $p \bmod 4|D|$, through a subgroup of $(\mathbb Z/4|D|)^\times$ (quadratic reciprocity). -/
@[kb "milne2020cft" "Introduction, Exercise 0.11 (input)"]
structure Exercise011 : Prop where
  splits_iff : ∀ (D : ℤ), Squarefree D → D ≠ 1 → ∀ (L : Type) [Field L] [NumberField L],
    Module.finrank ℚ L = 2 → (∃ s : L, s ^ 2 = D) →
    ∃ H : Subgroup (ZMod (4 * D.natAbs))ˣ, ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ D →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} →
        (v ∈ splitPrimes ℚ L ↔ ∃ u ∈ H, (u : ZMod (4 * D.natAbs)) = p)

/-- **Exercise 0.12** (named statement; Milne, *CFT*, Introduction): $\mathbb Q[\sqrt 5, \sqrt{-1}]$ is the Hilbert
class field of $\mathbb Q[\sqrt{-5}]$. -/
@[kb "milne2020cft" "Introduction, Exercise 0.12 (input)"]
structure Exercise012 : Prop where
  isHilbertClassField : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E], Module.finrank ℚ F = 2 → (∃ s : F, s ^ 2 = -5) → Module.finrank F E = 2 →
    (∃ a b : E, a ^ 2 = 5 ∧ b ^ 2 = -1) → IsHilbertClassField F E

/-- **Exercise 0.15** (named statement; Milne, *CFT*, Introduction): for $L = \mathbb Q[\sqrt{-1}, \sqrt 5]$,
(a) only $2$, $5$ and $\infty$ ramify in $L$; (c) for $\mathfrak m = (20)\infty$, $p \mapsto (p, L/\mathbb Q)$ defines
an isomorphism $C_\mathfrak m/H \cong \mathrm{Gal}(L/\mathbb Q)$ for some $H \subseteq C_\mathfrak m$. (Part (b), the
computation of $(p, L/\mathbb Q)$ for $p \ne 2, 5$, is the explicit form of the map in (c).) -/
@[kb "milne2020cft" "Introduction, Exercise 0.15 (input)"]
structure Exercise015 : Prop where
  ramified : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], Module.finrank ℚ L = 4 →
    (∃ a b : L, a ^ 2 = -1 ∧ b ^ 2 = 5) → ∀ v : HeightOneSpectrum (𝓞 ℚ),
      v ∉ unramifiedPrimes ℚ L ↔ (v.asIdeal = Ideal.span {(2 : 𝓞 ℚ)} ∨ v.asIdeal = Ideal.span {(5 : 𝓞 ℚ)})
  artin : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L], Module.finrank ℚ L = 4 →
    (∃ a b : L, a ^ 2 = -1 ∧ b ^ 2 = 5) → ∀ (m : Modulus ℚ), m.finite = Ideal.span {(20 : 𝓞 ℚ)} →
      m.infinite = {v | v.IsReal} →
      ∃ ψ : RayClassGroup m →* Gal(L/ℚ), Function.Surjective ψ ∧
        ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ m.finite) (Q : v.asIdeal.primesOver (𝓞 L)),
          ψ (rayClass m v hv) = frobAt ℚ L v Q

end NumberFieldKB.MilneCFT
