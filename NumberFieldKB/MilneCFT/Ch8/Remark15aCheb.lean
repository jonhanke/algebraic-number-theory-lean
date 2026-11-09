import Mathlib
import NumberFieldKB.TauCetiPort.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
import NumberFieldKB.TauCetiPort.NumberTheory.Chebotarev.FrobeniusPrimeSet

/-!
# Chebotarev: every Galois element is a Frobenius element outside a finite set

For Milne, *CFT*, VIII, Remark 1.5 (a). From Tau Ceti's natural-density Chebotarev theorem
(`NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`): the set of primes with Frobenius class `[σ]` has
positive density, hence is infinite, and `exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk` realizes `σ` itself.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.R15a

/-- **Chebotarev: every element is a Frobenius element away from a finite set.** -/
theorem exists_isArithFrobAt_notMem {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [IsGalois K M] (σ : M ≃ₐ[K] M)
    (A : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ A ∧ ∃ (Q : Ideal (𝓞 M)) (_ : Q.IsPrime)
      (_ : Q.LiesOver v.asIdeal), IsArithFrobAt (𝓞 K) σ Q := by
  have hd := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet K M (ConjClasses.mk σ)
  have hpos : ((Nat.card (ConjClasses.mk σ).carrier : ℝ) / Nat.card (M ≃ₐ[K] M)) ≠ 0 := by
    have h1 : 0 < Nat.card (ConjClasses.mk σ).carrier :=
      Nat.card_pos_iff.mpr ⟨⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩, Set.finite_coe_iff.mpr (Set.toFinite _)⟩
    have h2 : 0 < Nat.card (M ≃ₐ[K] M) := Nat.card_pos
    positivity
  have hinf := hd.infinite hpos
  obtain ⟨v, hv, hvA⟩ := (hinf.sdiff A.finite_toSet).nonempty
  obtain ⟨Q, hQ⟩ := NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hv
  exact ⟨v, hvA, Q.1, Q.2.1, Q.2.2, hQ⟩

end NumberFieldKB.MilneCFT.Ch8.R15a
