import NumberFieldKB.MilneCFT.Ch8.ReciprocityLaw
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.PowerResidueSymbol.Ideal
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Milne's power residue symbol and Tau Ceti's

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, §5, pp. 244–247
(the symbols $(a/\mathfrak p)$, $(a/b)$).

Milne's symbol `powerResidue n a v` (`Reciprocity.lean`) is defined by the congruence
$\mu \equiv a^{(N\mathfrak p - 1)/n} \pmod{\mathfrak p}$, $\mu^n = 1$; Tau Ceti's `Ideal.powerResidueSymbol` by the same
congruence in $\mathcal O_K / \mathfrak p$. They agree (`powerResidue_eq_powerResidueSymbolIdeal`). Consequently the
symbol at a principal ideal $(x)$, `Ideal.powerResidueSymbolIdeal (span {x})`, is Milne's `powerResidueElt n y x`
when $x$ is prime to $n y$ (`powerResidueSymbolIdeal_eq_powerResidueElt`).
-/

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

variable {K : Type} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity (𝓞 K) n]

/-- **Milne's symbol at a prime is Tau Ceti's**: for a prime $\mathfrak p = v$ not dividing $n$ and
$a \in \mathcal O_K \setminus \mathfrak p$, `powerResidue n a v` is Tau Ceti's symbol $(a/\mathfrak p)_n$. -/
theorem powerResidue_eq_powerResidueSymbolIdeal {ζ : K} (hζ : IsPrimitiveRoot ζ n) (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) {a : 𝓞 K} (ha : a ∉ v.asIdeal) :
    powerResidue n (a : K) v =
      ((Ideal.powerResidueSymbolIdeal v.asIdeal n (Ideal.Quotient.mk _ a) : 𝓞 K) : K) := by
  haveI := v.isMaximal
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hval : v.valuation K (a : K) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := K) (r := a)).2 ha
  have hvS : v ∉ Sset n {(a : K)} := (notMem_Sset_iff v n (a : K)).2 ⟨hnv, hval⟩
  have hN : (Ideal.absNorm v.asIdeal).Coprime n := by
    have h := dvd_absNorm_sub_one v hn hζ hnv
    have h1 : 1 ≤ Ideal.absNorm v.asIdeal := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      rw [Ideal.absNorm_eq_zero_iff] at h0
      exact v.ne_bot h0
    have h2 : Ideal.absNorm v.asIdeal = (Ideal.absNorm v.asIdeal - 1) + 1 := by omega
    rw [h2]
    obtain ⟨k, hk⟩ := h
    rw [hk]
    exact (Nat.coprime_mul_left_add_left 1 n k).mpr (Nat.coprime_one_left n)
  have hxne : Ideal.Quotient.mk v.asIdeal a ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact ha
  rw [Ideal.powerResidueSymbolIdeal_of_isMaximal]
  have hpow := Ideal.powerResidueSymbol_pow_eq_one hN hxne
  have hm : Ideal.Quotient.mk v.asIdeal (Ideal.powerResidueSymbol v.asIdeal n (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk v.asIdeal (a ^ ((Ideal.absNorm v.asIdeal - 1) / n)) := by
    rw [Ideal.mk_powerResidueSymbol hN hxne, map_pow]
  refine (powerResidue_unique n hn _ hζ (a : K) v hvS _ ⟨?_, ?_⟩).symm
  · have h := congrArg (fun z : 𝓞 K => (z : K)) hpow
    simpa using h
  · have h := (v.valuation_lt_one_iff_mem (K := K)
      (Ideal.powerResidueSymbol v.asIdeal n (Ideal.Quotient.mk _ a) -
        a ^ ((Ideal.absNorm v.asIdeal - 1) / n))).2 (Ideal.Quotient.eq.mp hm)
    simpa using h

/-- Finite support of $v \mapsto g(v)^{\mathrm{ord}_v I}$. -/
theorem mulSupport_zpow_count_finite (g : HeightOneSpectrum (𝓞 K) → K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    (Function.mulSupport fun v => g v ^ FractionalIdeal.count K v I).Finite := by
  refine (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).subset ?_
  intro v hv h
  apply hv
  simp [h]

theorem zpow_add_of_nonneg (x : K) {c d : ℤ} (hc : 0 ≤ c) (hd : 0 ≤ d) : x ^ (c + d) = x ^ c * x ^ d := by
  obtain ⟨c', rfl⟩ := Int.eq_ofNat_of_zero_le hc
  obtain ⟨d', rfl⟩ := Int.eq_ofNat_of_zero_le hd
  rw [← Nat.cast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

/-- The symbol at a nonzero ideal $I$ is the product of the symbols at the primes, with the multiplicities of
$I$ (on any class; both sides vanish when $y$ is not prime to $I$). -/
theorem powerResidueSymbolIdeal_eq_finprod (y : 𝓞 K) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ((Ideal.powerResidueSymbolIdeal I n (Ideal.Quotient.mk _ y) : 𝓞 K) : K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K),
        ((Ideal.powerResidueSymbolIdeal v.asIdeal n (Ideal.Quotient.mk _ y) : 𝓞 K) : K) ^
          FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ u hu =>
    rw [Ideal.isUnit_iff.mp hu, Ideal.powerResidueSymbolIdeal_top]
    simp [FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
  | h₃ J P hJ hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    rw [Ideal.powerResidueSymbolIdeal_mul_right hP0 hJ]
    push_cast
    set w : HeightOneSpectrum (𝓞 K) := ⟨P, Ideal.isPrime_of_prime hP, hP0⟩
    have hcount : ∀ v : HeightOneSpectrum (𝓞 K),
        FractionalIdeal.count K v ((P : FractionalIdeal (𝓞 K)⁰ K) * (J : FractionalIdeal (𝓞 K)⁰ K)) =
          FractionalIdeal.count K v (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) +
            FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
      intro v
      rw [FractionalIdeal.count_mul K v]
      · exact FractionalIdeal.coeIdeal_ne_zero.mpr hP0
      · exact FractionalIdeal.coeIdeal_ne_zero.mpr hJ
    have hPfac : ((Ideal.powerResidueSymbolIdeal P n (Ideal.Quotient.mk _ y) : 𝓞 K) : K) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((Ideal.powerResidueSymbolIdeal v.asIdeal n (Ideal.Quotient.mk _ y) : 𝓞 K) : K) ^
            FractionalIdeal.count K v (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [finprod_eq_single _ w]
      · rw [FractionalIdeal.count_self, zpow_one]
      · intro v hv
        rw [FractionalIdeal.count_maximal_coprime K v (Ne.symm hv), zpow_zero]
    refine (congrArg₂ (· * ·) hPfac (ih hJ)).trans ?_
    rw [← finprod_mul_distrib (by exact mulSupport_zpow_count_finite _ _)
      (by exact mulSupport_zpow_count_finite _ _)]
    refine finprod_congr fun v => ?_
    rw [hcount v]
    exact (zpow_add_of_nonneg _ (FractionalIdeal.count_coe_nonneg K v _)
      (FractionalIdeal.count_coe_nonneg K v _)).symm

/-- **The symbol at a principal ideal through Milne's symbols**: for $x \ne 0$ prime to $n$ and to $y$,
$(y/(x))_n = \prod_{v} (y/\mathfrak p_v)^{\mathrm{ord}_v x}$ = `powerResidueElt n y x`. -/
theorem powerResidueSymbolIdeal_eq_powerResidueElt {ζ : K} (hζ : IsPrimitiveRoot ζ n) {x y : 𝓞 K} (hx : x ≠ 0)
    (hxy : IsCoprime x y) (hxn : IsCoprime x (n : 𝓞 K)) :
    ((Ideal.powerResidueSymbolIdeal (Ideal.span {x}) n (Ideal.Quotient.mk _ y) : 𝓞 K) : K) =
      powerResidueElt n (y : K) (x : K) := by
  classical
  have hxI : Ideal.span {x} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [powerResidueSymbolIdeal_eq_finprod y _ hxI, powerResidueElt]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.coeIdeal_span_singleton]
  change _ = if v ∈ Sset n {(y : K)} then (1 : K) else
    powerResidue n (y : K) v ^ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K))
  by_cases hxv : x ∈ v.asIdeal
  · have hyv : y ∉ v.asIdeal := by
      intro hy
      obtain ⟨u, w, h⟩ := hxy
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
        (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left u hxv) (v.asIdeal.mul_mem_left w hy)))
    have hnv : (n : 𝓞 K) ∉ v.asIdeal := by
      intro hn
      obtain ⟨u, w, h⟩ := hxn
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
        (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left u hxv) (v.asIdeal.mul_mem_left w hn)))
    have hvS : v ∉ Sset n {(y : K)} :=
      (notMem_Sset_iff v n (y : K)).2 ⟨hnv, (v.valuation_eq_one_iff_notMem (K := K) (r := y)).2 hyv⟩
    rw [if_neg hvS, powerResidue_eq_powerResidueSymbolIdeal hζ v hnv hyv]
  · have h0 : FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 :=
      count_eq_zero_of_val v _ (by simpa using hx) ((v.valuation_eq_one_iff_notMem (K := K) (r := x)).2 hxv)
    change _ ^ FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = _
    rw [h0, zpow_zero]
    split_ifs <;> simp
end NumberFieldKB.MilneCFT.Ch8.Eisenstein
