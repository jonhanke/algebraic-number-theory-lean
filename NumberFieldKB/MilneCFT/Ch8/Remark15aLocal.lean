import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.Minpoly
import Mathlib.RingTheory.SimpleRing.Principal
import NumberFieldKB.TauCetiPort.RingTheory.Frobenius.PowerResidue
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Frobenius.Kummer.LocalUnit
import NumberFieldKB.TauCetiPort.RingTheory.DedekindDomain.AdicValuation.Power

/-!
# Frobenius elements and local `n`-th powers, with the roots of unity in the top field

For Milne, *CFT*, VIII, Remark 1.5 (a).

* `exists_pow_mul_fixed_of_isLocalPow`: let `σ` be an arithmetic Frobenius at `Q | v` in a Galois extension
  `M/K` of number fields, `ζ ∈ M` a primitive `n`-th root of unity, `v ∤ n`, `a ∈ K` a `v`-unit that is an
  `n`-th power in `K_v`, and `α^n = a` in `M`. Then `σ` fixes one of the roots `ζ^i α`. (Variant of Tau Ceti
  `IsArithFrobAt.apply_eq_self_iff_exists_pow_eq_adicCompletion`, which needs `ζ ∈ K`.) Proof modulo `Q`: `a` is
  an `n`-th power `y^n` modulo `v` (Tau Ceti `exists_pow_eq_adicCompletion_iff`), so `α ≡ ζ^j y`, and
  `σ (ζ^{-j} α) ≡ (ζ^{-j}α)^{Nv} ≡ y^{Nv} ≡ y ≡ ζ^{-j} α`; two `n`-th roots of `a` congruent modulo `Q` are
  equal (`TauCeti.eq_one_of_pow_eq_one_of_sub_one_mem`).
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.R15a


/-- Ring-level exists_pow_mul_fixed_of_residue_pow: if `a = x ^ n` is an `n`-th power residue, a Frobenius fixes some
`ζ ^ i * x`, with `ζ` a primitive `n`-th root of unity in the top ring. -/
theorem exists_pow_mul_fixed_of_residue_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsDomain S]
    {φ : S →ₐ[R] S} {Q : Ideal S} [Q.IsPrime] (H : φ.IsArithFrobAt Q) {n : ℕ} {ζ : S}
    (hζ : IsPrimitiveRoot ζ n) (hn : (n : S) ∉ Q) {x : S} {c : R}
    (hx : x ^ n = algebraMap R S c) (hc : algebraMap R S c ∉ Q) {P : Ideal R}
    (hP : Q.under R = P)
    (hb : ∃ b : R ⧸ P, b ^ n = Ideal.Quotient.mk _ c) :
    ∃ i : ℕ, φ (ζ ^ i * x) = ζ ^ i * x := by
  subst hP
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have hnpos := Nat.pos_of_ne_zero hn0
  obtain ⟨b, hb⟩ := hb
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hYc : algebraMap R S y ^ n - algebraMap R S c ∈ Q := by
    have h1 : y ^ n - c ∈ Q.under R := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hb, sub_self]
    have h2 := Ideal.mem_comap.mp h1
    simpa [map_sub, map_pow] using h2
  have hYQ : algebraMap R S y ∉ Q := fun h => hc (by
    have := Q.sub_mem (Q.pow_mem_of_mem h n hnpos) hYc
    simpa using this)
  have hζbar : IsPrimitiveRoot (Ideal.Quotient.mk Q ζ) n := by
    refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl => ?_⟩
    rw [← map_pow, ← map_one (Ideal.Quotient.mk Q), Ideal.Quotient.eq] at hl
    exact hζ.dvd_of_pow_eq_one l (TauCeti.eq_one_of_pow_eq_one_of_sub_one_mem hn
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) hl)
  have hroot : Ideal.Quotient.mk Q x ∈
      Polynomial.nthRoots n (Ideal.Quotient.mk Q (algebraMap R S y) ^ n) := by
    rw [Polynomial.mem_nthRoots hnpos]
    have h1 : Ideal.Quotient.mk Q (x ^ n) = Ideal.Quotient.mk Q (algebraMap R S y ^ n) := by
      rw [Ideal.Quotient.eq, hx]
      have := Q.neg_mem hYc
      rwa [neg_sub] at this
    simpa only [map_pow] using h1
  rw [hζbar.nthRoots_eq rfl, Multiset.mem_map] at hroot
  obtain ⟨i, hi, hxi⟩ := hroot
  have hi' : i ≤ n := (Multiset.mem_range.mp hi).le
  have hx'Y : ζ ^ (n - i) * x - algebraMap R S y ∈ Q := by
    rw [← Ideal.Quotient.eq, map_mul, map_pow, ← hxi, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel hi', hζbar.pow_eq_one, one_mul]
  refine ⟨n - i, ?_⟩
  have hζn : (ζ ^ (n - i)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hx'n : (ζ ^ (n - i) * x) ^ n = algebraMap R S c := by
    rw [mul_pow, hζn, one_mul, hx]
  generalize ζ ^ (n - i) * x = x' at hx'Y hx'n ⊢
  have hfin := H.finite_quotient
  have hqy : y ^ Nat.card (R ⧸ Q.under R) - y ∈ Q.under R := by
    have : (Q.under R).IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain (R ⧸ Q.under R))
    let : Field (R ⧸ Q.under R) := Ideal.Quotient.field _
    have := Fintype.ofFinite (R ⧸ Q.under R)
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  have h3 : algebraMap R S y ^ Nat.card (R ⧸ Q.under R) - algebraMap R S y ∈ Q := by
    simpa [map_sub, map_pow] using Ideal.mem_comap.mp hqy
  have h1 := H x'
  have h2 : x' ^ Nat.card (R ⧸ Q.under R) - algebraMap R S y ^ Nat.card (R ⧸ Q.under R) ∈ Q := by
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow x' (algebraMap R S y) (Nat.card (R ⧸ Q.under R))
    rw [ht]
    exact Q.mul_mem_right _ hx'Y
  have hF : φ x' - x' ∈ Q := by
    have := Q.add_mem (Q.add_mem (Q.add_mem h1 h2) h3) (Q.neg_mem hx'Y)
    convert this using 1
    ring
  have hr : φ x' ∈ Polynomial.nthRoots n (algebraMap R S c) := by
    rw [Polynomial.mem_nthRoots hnpos, ← map_pow, hx'n, AlgHom.commutes]
  rw [hζ.nthRoots_eq hx'n, Multiset.mem_map] at hr
  obtain ⟨k, -, hk⟩ := hr
  have hmem : (ζ ^ k - 1) * x' ∈ Q := by
    have : (ζ ^ k - 1) * x' = φ x' - x' := by rw [sub_mul, one_mul, hk]
    rw [this]
    exact hF
  have hx'Q : x' ∉ Q := fun h => hc (hx'n ▸ Q.pow_mem_of_mem h n hnpos)
  have h1k := TauCeti.eq_one_of_pow_eq_one_of_sub_one_mem hn
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
    ((Ideal.IsPrime.mem_or_mem ‹_› hmem).resolve_right hx'Q)
  rw [← hk, h1k, one_mul]

/-- **A Frobenius fixes some root of a local power.** -/
theorem exists_pow_mul_fixed_of_isLocalPow {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] {σ : M ≃ₐ[K] M} {Q : Ideal (𝓞 M)} [Q.IsPrime]
    {v : HeightOneSpectrum (𝓞 K)} [Q.LiesOver v.asIdeal] (hσ : IsArithFrobAt (𝓞 K) σ Q) {n : ℕ}
    {ζ : M} (hζ : IsPrimitiveRoot ζ n) (hn : (n : 𝓞 K) ∉ v.asIdeal) {a : K} {α : M}
    (ha : v.valuation K a = 1) (hα : α ^ n = algebraMap K M a)
    (hloc : ∃ b : v.adicCompletion K, b ^ n = algebraMap K (v.adicCompletion K) a) :
    ∃ i : ℕ, σ (ζ ^ i * α) = ζ ^ i * α := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  obtain ⟨d, c, β, hd, hcunit, hc, hβ, hpow⟩ :=
    v.exists_integral_pow_eq_of_valuation_eq_one hn0 ha hα
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
    intro h
    exact hd (by simp [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 K) K).mp h])
  let ζ' : 𝓞 M := ⟨ζ, hζ.isIntegral (Nat.pos_of_ne_zero hn0)⟩
  have hζ' : IsPrimitiveRoot ζ' n :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 M) M) (by exact hζ)
      (FaithfulSMul.algebraMap_injective (𝓞 M) M)
  have hn' : (n : 𝓞 M) ∉ Q :=
    fun h ↦ hn ((Ideal.mem_of_liesOver Q v.asIdeal _).mpr (by simpa using h))
  have hcQ : algebraMap (𝓞 K) (𝓞 M) c ∉ Q :=
    fun h ↦ hcunit ((Ideal.mem_of_liesOver Q v.asIdeal _).mpr h)
  obtain ⟨b, hb⟩ := hloc
  have hlocal : ∃ x : v.adicCompletion K,
      x ^ n = algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K c) := by
    refine ⟨algebraMap (𝓞 K) (v.adicCompletion K) d * b, ?_⟩
    rw [hc, map_mul, map_pow, mul_pow, hb, IsScalarTower.algebraMap_apply (𝓞 K) K
      (v.adicCompletion K)]
  have hres := (v.exists_pow_eq_adicCompletion_iff (K := K) hn hcunit).mp
    (by
      obtain ⟨x, hx⟩ := hlocal
      exact ⟨x, hx.trans (IsScalarTower.algebraMap_apply (𝓞 K) K (v.adicCompletion K) c).symm⟩)
  obtain ⟨i, hi⟩ := exists_pow_mul_fixed_of_residue_pow hσ hζ' hn' hpow hcQ (Q.over_def v.asIdeal).symm hres
  refine ⟨i, ?_⟩
  have hi' : σ • (ζ' ^ i * β) = ζ' ^ i * β := hi
  have hD : σ (algebraMap (𝓞 K) M d) = algebraMap (𝓞 K) M d := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K M, AlgEquiv.commutes]
  have hD0 : algebraMap (𝓞 K) M d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K M]
    exact (map_ne_zero (algebraMap K M)).mpr hdK
  have h : σ (algebraMap (𝓞 M) M (ζ' ^ i * β)) = algebraMap (𝓞 M) M (ζ' ^ i * β) := by
    rw [← NumberField.algebraMap_smul_eq_apply, hi']
  have e1 : algebraMap (𝓞 M) M (ζ' ^ i * β) = ζ ^ i * (algebraMap (𝓞 K) M d * α) := by
    rw [map_mul, map_pow]
    change ζ ^ i * (β : M) = _
    rw [hβ]
  rw [e1] at h
  have h2 : σ (algebraMap (𝓞 K) M d * (ζ ^ i * α)) = algebraMap (𝓞 K) M d * (ζ ^ i * α) := by
    have e : algebraMap (𝓞 K) M d * (ζ ^ i * α) = ζ ^ i * (algebraMap (𝓞 K) M d * α) := by ring
    rw [e]
    exact h
  rw [map_mul, hD] at h2
  exact mul_left_cancel₀ hD0 h2

end NumberFieldKB.MilneCFT.Ch8.R15a
