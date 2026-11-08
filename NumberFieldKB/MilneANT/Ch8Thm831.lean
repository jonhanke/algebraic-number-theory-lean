import NumberFieldKB.MilneANT.Ch8Chebotarev
import NumberFieldKB.TauCetiPort.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount

/-!
# Milne, *Algebraic Number Theory*, Theorem 8.31: Chebotarev with natural density, proved

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`,
Theorem 8.31, p. 147.

The named statement `Theorem8_31` (natural density) is proved here from Tau Ceti's
`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`
(`NumberFieldKB/TauCetiPort/NumberTheory/Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean`, ported from Tau Ceti,
Apache License 2.0). Tau Ceti proves it by a prime ideal theorem for Hecke characters of ray class groups
(Wiener–Ikehara Tauberian theorem), Brauer–Deuring reduction to the cyclic case and cyclotomic twisting.

Two comparison lemmas connect the conventions:
* `frobSet_eq_frobeniusPrimeSet`: the library's Chebotarev set `NumberFieldKB.Chebotarev.frobSet` (unramified primes with
  Frobenius class `C`) is Tau Ceti's `NumberField.Chebotarev.frobeniusPrimeSet` (primes with Artin symbol `C`).
* `primeCount_eq_tauCeti`: the library's `primeCount` (an `ncard`) cast to `ℝ` is Tau Ceti's `TauCeti.primeCount`
  (a sum of the indicator over the primes of norm at most `x`).
Hence `hasNaturalDensity_iff_tauCeti`: the two natural densities agree.
-/

open NumberField IsDedekindDomain Filter Topology
open NumberFieldKB.Chebotarev

namespace NumberFieldKB.MilneANT

noncomputable section

/-- The library's prime count (`ncard`) and Tau Ceti's (`TauCeti.primeCount`, a real-valued sum) agree. -/
theorem primeCount_eq_tauCeti {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (x : ℝ) : (primeCount S x : ℝ) = TauCeti.primeCount K S x := by
  classical
  rw [TauCeti.primeCount_eq_card, primeCount]
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext 𝔭
  simp [TauCeti.mem_normLE, and_comm]

/-- The library's natural density (Milne, Definition 8.30) is Tau Ceti's `NumberField.Set.HasNaturalDensity`. -/
theorem hasNaturalDensity_iff_tauCeti {K : Type*} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (δ : ℝ) :
    HasNaturalDensity S δ ↔ NumberField.Set.HasNaturalDensity S δ := by
  rw [NumberField.Set.hasNaturalDensity_def, HasNaturalDensity]
  simp only [primeCount_eq_tauCeti]

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- The library's Chebotarev set (unramified primes with Frobenius class `C`) is Tau Ceti's `frobeniusPrimeSet` (primes
with Artin symbol `C`, the Artin symbol being defined exactly at the unramified primes). -/
theorem frobSet_eq_frobeniusPrimeSet (C : ConjClasses Gal(L/K)) :
    frobSet K L C = NumberField.Chebotarev.frobeniusPrimeSet K L C := by
  ext 𝔭
  rw [NumberField.Chebotarev.mem_frobeniusPrimeSet_iff]
  have hclass : ∀ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = frobClass K L 𝔭 := by
    intro hur
    set Q₀ : 𝔭.asIdeal.primesOver (𝓞 L) := Classical.arbitrary _
    haveI := Q₀.2.1
    haveI := Q₀.2.2
    rw [frobClass_eq_mk_frobAt K L 𝔭 Q₀]
    exact artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q₀.1 _ (isArithFrobAt_frobAt K L 𝔭 Q₀)
  constructor
  · rintro ⟨hun, hC⟩
    have hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q :=
      fun Q hQ hQ' => hun Q hQ hQ'
    exact ⟨hur, (hclass hur).trans hC⟩
  · rintro ⟨hur, hC⟩
    exact ⟨fun Q hQ hQ' => @hur Q hQ hQ', (hclass hur).symm.trans hC⟩

/-- **Theorem 8.31 (Chebotarev density theorem, natural density)**, proved: for a finite Galois extension $L/K$ of
number fields and a conjugacy class $C$ of $\mathrm{Gal}(L/K)$, the primes of $K$ unramified in $L$ with Frobenius
class $C$ have natural density $|C|/[L:K]$. From Tau Ceti's
`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`. -/
@[kb "milne2020ant" "v3.08, Thm. 8.31, p. 147"]
theorem thm_8_31 (C : ConjClasses Gal(L/K)) :
    HasNaturalDensity (frobSet K L C) (Nat.card C.carrier / Nat.card Gal(L/K)) := by
  rw [hasNaturalDensity_iff_tauCeti, frobSet_eq_frobeniusPrimeSet]
  exact NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet K L C

/-- The named statement `Theorem8_31` (Milne, Theorem 8.31, natural density) holds unconditionally. -/
@[kb "milne2020ant" "v3.08, Thm. 8.31, p. 147"]
theorem theorem8_31 : Theorem8_31 :=
  ⟨fun K L _ _ _ _ _ _ C => thm_8_31 K L C⟩

end

end NumberFieldKB.MilneANT
