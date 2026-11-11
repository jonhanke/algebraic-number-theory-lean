import NumberFieldKB.MilneCFT.Ch6.Remark42aNatural
import NumberFieldKB.TauCetiPort.NumberTheory.Chebotarev.PrimeCounting.PrimesCongruent
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Milne, *Class Field Theory*, VI, Remark 4.2 (a): the natural-density half, unconditionally

The prime number theorem over $\mathbb Q$ (`R42.pnt`) is Tau Ceti's prime number theorem in arithmetic progressions
`NumberField.Chebotarev.tendsto_primeCount_primesCongruent` at level $m = 1$. With `R42.not_natural_of_pnt` it shows
that the primes with leading decimal digit $1$ have no natural density (`remark_4_2a_not_natural`), the second half
of the named statement `Remark4_2a`. The first half (Dirichlet density $\log_{10}2$ in Milne's bounded-difference
sense) needs the prime number theorem with an error term $O(x/\log^2 x)$, not available here.
-/

open Filter Topology IsDedekindDomain NumberField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch6.R42

/-- Tau Ceti's prime count is ours. -/
theorem tauCeti_primeCount_eq (S : Set (HeightOneSpectrum (𝓞 ℚ))) (x : ℝ) :
    TauCeti.primeCount ℚ S x = (NumberFieldKB.MilneANT.primeCount S x : ℝ) := by
  classical
  rw [TauCeti.primeCount_eq_card, NumberFieldKB.MilneANT.primeCount, ← Set.ncard_coe_finset]
  congr 2
  ext v
  simp [and_comm]

/-- **The prime number theorem** over $\mathbb Q$: $\pi(x)/(x/\log x) \to 1$. -/
theorem pnt : PNT := by
  have h := NumberField.Chebotarev.tendsto_primeCount_primesCongruent 1 0
    (isUnit_of_subsingleton _)
  have hset : {p : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm p.asIdeal % 1 = 0 % 1} = Set.univ := by
    ext p; simp [Nat.mod_one]
  rw [hset] at h
  simp only [Nat.totient_one, Nat.cast_one, div_one] at h
  refine h.congr fun x => ?_
  rw [tauCeti_primeCount_eq]

end NumberFieldKB.MilneCFT.Ch6.R42

namespace NumberFieldKB.MilneCFT.Ch6

/-- **Remark 4.2 (a), second half** (Milne, *CFT*, VI, p. 194): the primes with leading decimal digit $1$ have no
natural density. -/
@[kb "milne2020cft" "Ch. VI, Remark 4.2 (a) (no natural density)"]
theorem remark_4_2a_not_natural (δ : ℝ) :
    ¬ NumberFieldKB.MilneANT.HasNaturalDensity leadingDigitOnePrimes δ :=
  R42.not_natural_of_pnt R42.pnt δ

end NumberFieldKB.MilneCFT.Ch6
