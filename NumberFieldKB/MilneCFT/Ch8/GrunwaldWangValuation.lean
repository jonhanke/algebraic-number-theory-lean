import NumberFieldKB.MilneCFT.Ch8.GrunwaldWangCyclic
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Cyclotomic.Ramification
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Grunwald–Wang, special case: elements of `P(n, S)` have valuation divisible by `n` away from `2`

**Proved here:** `GW.exists_valuation_eq_of_mem_powSet`: if `a ∈ P(n, S)` (`S` finite) and `v` is a finite place not
above `2`, then `v(a) ≡ 0 mod n`.

Proof. Write `n = 2^r m`, `m` odd: `a = c^m` with `c ∈ P(2^r, S)` (`R15a.powSet_odd`, `R15a.mem_powSet_of_pow_mem`).
For `q = 2^r`, in `M = K(ζ_q, c^{1/q})` every automorphism fixes some root `ζ^i α` (`R15a.forall_fixed_of_mem_powSet`),
so every automorphism fixing `ζ` fixes `α` (`R15a.fix_of_fixes_zeta`) and `α ∈ F = K(ζ)`. The extension `F/K` is
cyclotomic of level `q`, unramified above `v` (`isUnramifiedAt_of_natCast_notMem`), so for a prime `Q` of `F` above `v`,
`v(c) = Q(c) = q · Q(α)`.
-/

open IsDedekindDomain NumberField

namespace NumberFieldKB.MilneCFT.Ch8.GW

variable {K : Type} [Field K] [NumberField K]

/-- **Valuations of elements of `P(n, S)` away from `2`.** -/
theorem exists_valuation_eq_of_mem_powSet {n : ℕ} (hn : 0 < n) {S : Set (HeightOneSpectrum (𝓞 K))}
    (hS : S.Finite) {a : Kˣ} (ha : a ∈ powSet n S) (v : HeightOneSpectrum (𝓞 K))
    (hv : (2 : 𝓞 K) ∉ v.asIdeal) :
    ∃ k : ℤ, v.valuation K (a : K) = WithZero.exp ((n : ℤ) * k) := by
  classical
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨c, hc⟩ := R15a.powSet_odd hS m hm a (R15a.mem_powSet_of_dvd (Dvd.intro_left _ rfl) ha)
  have hcop : Nat.Coprime m (2 ^ r) := (Nat.coprime_two_right.2 hm).pow_right r
  have hcS : c ∈ powSet (2 ^ r) S :=
    R15a.mem_powSet_of_pow_mem hcop (hc ▸ R15a.mem_powSet_of_dvd (Dvd.intro _ rfl) ha)
  have hq : 0 < 2 ^ r := pow_pos two_pos r
  have : NeZero (2 ^ r) := ⟨hq.ne'⟩
  obtain ⟨M, _, _, _, _, _, ζ, α, -, hζ, hα, -⟩ := R15a.exists_splitting (K := K) hq (c : K) (c : K)
  have hfa := R15a.forall_fixed_of_mem_powSet hq hζ hS hcS hα
  let E := IntermediateField.adjoin K {ζ}
  have : IsCyclotomicExtension {2 ^ r} K E := hζ.intermediateField_adjoin_isCyclotomicExtension K
  have hζE : ζ ∈ E := IntermediateField.mem_adjoin_simple_self K ζ
  -- α ∈ E
  have hαE : α ∈ E := by
    have : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
    have hb : α ∈ (⊥ : IntermediateField E M) := by
      rw [IsGalois.mem_bot_iff_fixed]
      intro τ
      let τ' : M ≃ₐ[K] M := τ.restrictScalars K
      have h1 : τ' ζ = ζ := τ.commutes ⟨ζ, hζE⟩
      exact R15a.fix_of_fixes_zeta hζ hq hfa τ' h1
    obtain ⟨x, hx⟩ := IntermediateField.mem_bot.1 hb
    rw [← hx]
    exact x.2
  let α' : E := ⟨α, hαE⟩
  have hα'0 : α' ≠ 0 := by
    intro h
    have h0 : α = 0 := congrArg Subtype.val h
    have : algebraMap K M (c : K) = 0 := by rw [← hα, h0]; exact zero_pow hq.ne'
    exact c.ne_zero ((map_eq_zero _).1 this)
  have hα'q : α' ^ (2 ^ r) = algebraMap K E (c : K) := by
    apply Subtype.ext
    exact hα
  -- prime of E above v
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
  let w : HeightOneSpectrum (𝓞 E) := ⟨P, hP.isPrime, hP0⟩
  have : w.asIdeal.LiesOver v.asIdeal := hPv
  have hnot : ((2 ^ r : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro h
    apply hv
    have h' : (2 : 𝓞 K) ^ r ∈ v.asIdeal := by exact_mod_cast h
    exact v.isPrime.mem_of_pow_mem r h'
  have : Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal :=
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E (2 ^ r) hnot w.asIdeal
  have he : w.asIdeal.ramificationIdx (𝓞 K) = 1 := Ideal.ramificationIdx_eq_one _ _
  have hval := HeightOneSpectrum.valuation_liesOver (A := 𝓞 K) (K := K) E v w (c : K)
  rw [he, pow_one, ← hα'q, map_pow] at hval
  have hw0 : w.valuation E α' ≠ 0 := (Valuation.ne_zero_iff _).2 hα'0
  refine ⟨WithZero.log (w.valuation E α'), ?_⟩
  have hac : (a : K) = (c : K) ^ m := by rw [← hc]; simp
  rw [hac, map_pow, hval, ← pow_mul]
  conv_lhs => rw [← WithZero.exp_log hw0, ← WithZero.exp_nsmul]
  congr 1

end NumberFieldKB.MilneCFT.Ch8.GW
