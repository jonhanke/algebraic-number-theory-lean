import NumberFieldKB.MilneCFT.Ch7.KeyCase
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VII §6 (p. 215): a cyclic degree-$p$ extension embeds in a Kummer extension

If $L/K$ is Galois of prime degree $p$ and $K$ contains a primitive $p$-th root of $1$, then $L = K[a^{1/p}]$; choosing
$S$ so large that $a$ is an $S$-unit, $L\subseteq M = K[U(S)^{1/p}]$ (`exists_kummer_embedding`).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
open Polynomial IntermediateField

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- **Milne, *CFT*, Chapter VII, p. 215**: a Galois extension $L/K$ of prime degree $p$ (with $\zeta_p\in K$) embeds
over $K$ into a Kummer extension $M = K[U(S)^{1/p}]$ for a suitable finite $S$. -/
theorem exists_kummer_embedding (hKum : KummerAppendix K) {p : ℕ} (hp : p.Prime)
    (hζ : ∃ ζ : K, IsPrimitiveRoot ζ p)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hcard : Nat.card Gal(L/K) = p) :
    ∃ (S : Set (HeightOneSpectrum (𝓞 K))) (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M)
      (_ : IsGalois K M), (∀ σ τ : Gal(M/K), σ * τ = τ * σ) ∧ KummerSetting p S M ∧
      Module.finrank K M = (powMonoidHom p : Kˣ →* Kˣ).range.relIndex (S.unit K) ∧
      ∃ _φ : L →ₐ[K] M, True := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfr : Module.finrank K L = p := by rw [← IsGalois.card_aut_eq_finrank K L]; exact hcard
  have hcyc : IsCyclic Gal(L/K) := isCyclic_of_prime_card hcard
  obtain ⟨ζ, hζp⟩ := hζ
  have hK : (primitiveRoots (Module.finrank K L) K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots (by rw [hfr]; exact hp.pos)).2 (by rw [hfr]; exact hζp)⟩
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic K L hK
  have hirr := irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα
  rw [hfr] at ha hirr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hα0 : α = 0 := by
      have : α ^ p = 0 := by rw [← ha]; simp
      exact pow_eq_zero_iff hp.ne_zero |>.1 this
    subst hα0
    have : (⊤ : IntermediateField K L) = ⊥ := by
      rw [← hα]; simp
    have h1 : Module.finrank K L = 1 := by
      rw [← IntermediateField.finrank_top' (F := K) (E := L), this]; exact IntermediateField.finrank_bot
    rw [hfr] at h1
    exact hp.one_lt.ne' h1
  obtain ⟨S₁, hS₁fin, hS₁cl⟩ := exists_finite_classGroup_generators K
  set S : Set (HeightOneSpectrum (𝓞 K)) :=
    ({v | (p : 𝓞 K) ∈ v.asIdeal} ∪ S₁) ∪ {v | v.valuation K a ≠ 1} with hSdef
  have hfin1 : {v : HeightOneSpectrum (𝓞 K) | v.valuation K a ≠ 1}.Finite := by
    refine ((HeightOneSpectrum.Support.finite (𝓞 K) a).union
      (HeightOneSpectrum.Support.finite (𝓞 K) a⁻¹)).subset ?_
    intro v hv
    rcases lt_or_gt_of_ne hv with h | h
    · right
      show 1 < v.valuation K a⁻¹
      rw [map_inv₀]
      exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 (by simpa using ha0), h⟩
    · left; exact h
  have hSfin : S.Finite := ((finite_primes_dvd K p hp.ne_zero).union hS₁fin).union hfin1
  have hSdvd : ∀ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal → v ∈ S :=
    fun v hv => Or.inl (Or.inl hv)
  have hScl : Subgroup.closure ((fun v => primeClass K v) '' S) = ⊤ := by
    rw [eq_top_iff, ← hS₁cl]
    exact Subgroup.closure_mono (Set.image_mono (fun v hv => Or.inl (Or.inr hv)))
  obtain ⟨M, iF, iN, iA, iG, hc, hset, hfrM⟩ := hKum.exists_ext p S hp ⟨ζ, hζp⟩ hSfin hSdvd hScl
  refine ⟨S, M, iF, iN, iA, iG, hc, hset, hfrM, ?_⟩
  have hu : Units.mk0 a ha0 ∈ S.unit K := by
    intro v hv
    by_contra hne
    exact hv (Or.inr hne)
  obtain ⟨y, hy⟩ := hset.roots _ hu
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hmin : minpoly K α = (X ^ p - C a : K[X]) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic hirr
    · simp [ha]
    · exact monic_X_pow_sub_C a hp.ne_zero
  have hroot : y ∈ (minpoly K α).aroots M := by
    rw [mem_aroots]
    refine ⟨(minpoly.monic hint).ne_zero, ?_⟩
    rw [hmin]
    simpa [Units.val_mk0] using sub_eq_zero.2 hy
  let e : L ≃ₐ[K] K⟮α⟯ := IntermediateField.topEquiv.symm.trans (IntermediateField.equivOfEq hα.symm)
  exact ⟨((IntermediateField.algHomAdjoinIntegralEquiv K hint).symm ⟨y, hroot⟩).comp e.toAlgHom, trivial⟩

end NumberFieldKB.MilneCFT.Ch7
