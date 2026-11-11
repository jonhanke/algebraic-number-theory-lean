import NumberFieldKB.HilbertClassField.Artin
import NumberFieldKB.MilneCFT.Ch7.IdealReciprocityKer
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.ClassFields.RayClassField
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# The Hilbert class field, unconditionally (from Tau Ceti's class field theory)

The two named inputs of `NumberFieldKB/HilbertClassField/Artin.lean` are proved here, so the Hilbert class field
exists for every number field and the statement `HilbertClassFieldInput K` holds
(`hilbertClassFieldExists`, `hilbertClassFieldInput`):

* `unramifiedArtinReciprocityInput`: from Milne's Introduction, Theorem 0.8 (`MilneCFT.ArtinReciprocity`, proved from
  Chapter V's reciprocity law `reciprocityLaw_ideal_of_idelic`, itself from the idèlic reciprocity law
  `MilneCFT.idelicReciprocity`, proved from Tau Ceti). An abelian extension unramified at every place has a defining
  modulus with $\mathfrak m_0 = (1)$ and $\mathfrak m_\infty = \emptyset$, whose ray class group is the class group
  (`rayClassGroupEquivClassGroup`).
* `hilbertClassFieldDegreeInput`: Tau Ceti's Hilbert class field `TauCeti.ClassFieldTheory.hilbertClassField K` (the
  ray class field of the trivial modulus, ported), of degree $h_K$ (`finrank_hilbertClassField`), unramified at the
  finite primes (`isUnramifiedAt_hilbertClassField`) and at the infinite places (the instance
  `isUnramifiedAtInfinitePlaces_hilbertClassField`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev NumberFieldKB.MilneCFT

namespace NumberFieldKB.HilbertClassField

variable (K : Type) [Field K] [NumberField K]

/-- A modulus whose finite part has no prime divisor has finite part $(1)$. -/
theorem modulus_finite_eq_top (m : Modulus K) (h : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite) :
    m.finite = ⊤ := by
  by_contra hne
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal m.finite hne
  have hP0 : P ≠ ⊥ := fun h0 => m.finite_ne_bot (le_bot_iff.mp (h0 ▸ hle))
  exact h ⟨P, hP.isPrime, hP0⟩ (Ideal.dvd_iff_le.mpr hle)

/-- **Artin reciprocity for abelian extensions unramified at every place, proved**: the named input
`UnramifiedArtinReciprocityInput K`, from Milne's Theorem 0.8 (proved from Tau Ceti's global reciprocity). -/
@[kb "milne2020cft" "Introduction, Theorem 0.8 for m = 1 (Artin reciprocity for unramified abelian extensions)"]
theorem unramifiedArtinReciprocityInput : UnramifiedArtinReciprocityInput K := by
  refine ⟨fun H _ _ _ _ hab hunr hinf => ?_⟩
  have hAR : ArtinReciprocity K := artinReciprocity_of_reciprocityLaw (K := K) (reciprocityLaw_ideal_of_idelic (K := K) (idelicReciprocity K))
  obtain ⟨m, hm0, hminf, ψ, -, hψ, -⟩ := hAR.exists_artin H hab
  have hnd : ∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ m.finite := fun v hv => (hm0 v).1 hv (hunr v)
  have h0 : m.finite = ⊤ := modulus_finite_eq_top K m hnd
  have hinf0 : m.infinite = ∅ := by
    ext w
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hw
    obtain ⟨hr, w', hw', hc⟩ := (hminf w).1 hw
    have hu := hinf.isUnramified w'
    exact (InfinitePlace.not_isUnramified_iff.mpr ⟨hc, by rw [hw']; exact hr⟩) hu
  refine ⟨ψ.comp (rayClassGroupEquivClassGroup m h0 hinf0).symm.toMonoidHom, fun 𝔭 Q => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← rayClassGroupEquivClassGroup_rayClass m h0 hinf0 𝔭 (hnd 𝔭),
    MulEquiv.symm_apply_apply]
  exact hψ 𝔭 (hnd 𝔭) Q

/-- **An abelian extension unramified at every place, of degree the class number, proved**: the named input
`HilbertClassFieldDegreeInput K`, from Tau Ceti's Hilbert class field (ported). -/
@[kb "neukirch1999" "Ch. VI, §6: the Hilbert class field has degree h_K and is unramified [unverified locator]"]
theorem hilbertClassFieldDegreeInput : HilbertClassFieldDegreeInput K := by
  let H := TauCeti.ClassFieldTheory.hilbertClassField K
  refine ⟨⟨H, inferInstance, inferInstance, inferInstance, inferInstance, fun σ τ => IsMulCommutative.is_comm.comm σ τ, fun 𝔭 => ?_,
    inferInstance, TauCeti.ClassFieldTheory.finrank_hilbertClassField K⟩⟩
  intro P hP hlo
  haveI := hlo
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  exact TauCeti.ClassFieldTheory.isUnramifiedAt_hilbertClassField K ⟨P, hP, hP0⟩

/-- **The Hilbert class field exists**, for every number field. -/
@[kb "neukirch1999" "Ch. VI, §6-7: existence of the Hilbert class field, Cl_K ≅ Gal(H|K) [unverified locator]"]
theorem hilbertClassFieldExists : HilbertClassFieldExists K :=
  hilbertClassFieldExists_of_inputs (unramifiedArtinReciprocityInput K) (hilbertClassFieldDegreeInput K)

/-- **`HilbertClassFieldInput K`, proved for every number field**. -/
@[kb "neukirch1999" "VI.7.3: a prime splitting completely in the Hilbert class field is principal [unverified locator]"]
theorem hilbertClassFieldInput : HilbertClassFieldInput K :=
  hilbertClassFieldInput_of_inputs (unramifiedArtinReciprocityInput K) (hilbertClassFieldDegreeInput K)

end NumberFieldKB.HilbertClassField
