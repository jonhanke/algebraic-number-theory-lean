import Mathlib.NumberTheory.Multiplicity
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Auxiliary lemmas for `lemma_7_3` (Milne, *CFT*, Chapter VII, p. 220)

Strategy.  Take `E = K(ζ_N)` with `N = ∏_{ℓ ∈ T} ℓ^{r ℓ}` and a character `χ : (ℤ/N)ˣ → ℂˣ` of nearly maximal
order with `χ(-1) = -1`; let `L ⊆ E` be the fixed field of `ker (χ ∘ autToPow)`.  Then `Gal(L/K)` embeds in `ℂˣ`
(hence is cyclic), `L` is totally complex (complex conjugation maps to `-1`), and the local degrees are controlled by
Mathlib's description of ramification in `ℚ(ζ_N)`.
-/

open NumberField

namespace NumberFieldKB.MilneCFT.Ch7.Lemma73

/-! ### Group theory -/

/-- A character of `(ℤ/N)ˣ` with `χ(-1) = -1` and range of size at least a quarter of the exponent. -/
theorem exists_char (N : ℕ) [NeZero N] (h4 : 4 ∣ N) :
    ∃ χ : (ZMod N)ˣ →* ℂˣ, χ (-1) = -1 ∧
      Monoid.exponent (ZMod N)ˣ ≤ 4 * Nat.card χ.range := by
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent
    (Monoid.ExponentExists.of_finite (G := (ZMod N)ˣ))
  obtain ⟨E⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity (ZMod N)ˣ ℂ
  set e := Monoid.exponent (ZMod N)ˣ with he
  have he0 : 0 < e := Monoid.exponent_pos.2 Monoid.ExponentExists.of_finite
  set χ₁ : (ZMod N)ˣ →* ℂˣ := E.symm g with hχ₁
  have ho : orderOf χ₁ = e := by rw [hχ₁, MulEquiv.orderOf_eq, hg]
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (ZMod 4)ˣ ℂ (a := -1) (by decide)
  have hsq : ∀ v : (ZMod 4)ˣ, v ^ 2 = 1 := by decide
  have hφ' : φ (-1) = -1 := by
    have h2 : (φ (-1)) ^ 2 = 1 := by rw [← map_pow, hsq, map_one]
    have h3 : ((φ (-1) : ℂˣ) : ℂ) * ((φ (-1) : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← sq, h2]; rfl
    rcases mul_self_eq_one_iff.1 h3 with h | h
    · exact absurd (Units.ext h) hφ
    · exact Units.ext (by simpa using h)
  set ψ : (ZMod N)ˣ →* ℂˣ := φ.comp (ZMod.unitsMap h4) with hψ
  have hψ1 : ψ (-1) = -1 := by
    rw [hψ, MonoidHom.comp_apply]
    have : ZMod.unitsMap h4 (-1 : (ZMod N)ˣ) = -1 := by
      exact Units.ext (by simp [ZMod.unitsMap])
    rw [this, hφ']
  have hψ2 : ∀ u, ψ u ^ 2 = 1 := by
    intro u
    simp only [hψ, MonoidHom.comp_apply]
    rw [← map_pow, hsq, map_one]
  refine ⟨χ₁ ^ 2 * ψ, ?_, ?_⟩
  · have h1 : (χ₁ ^ 2) (-1) = 1 := by
      rw [MonoidHom.pow_apply, ← map_pow]
      simp
    rw [MonoidHom.mul_apply, h1, hψ1, one_mul]
  · set χ := χ₁ ^ 2 * ψ with hχ
    have hχ2 : χ ^ 2 = χ₁ ^ 4 := by
      refine MonoidHom.ext fun u => ?_
      simp only [hχ, MonoidHom.pow_apply, MonoidHom.mul_apply]
      rw [mul_pow, hψ2, mul_one, ← pow_mul]
    have hpow : χ ^ Nat.card χ.range = 1 := by
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact orderOf_dvd_iff_pow_eq_one.1
        (Subgroup.orderOf_dvd_natCard χ.range (MonoidHom.mem_range.2 ⟨u, rfl⟩))
    have hpos : 0 < Nat.card χ.range := Nat.card_pos
    have hd : orderOf (χ ^ 2) ∣ Nat.card χ.range :=
      (orderOf_pow_dvd 2).trans (orderOf_dvd_of_pow_eq_one hpow)
    have hle := Nat.le_of_dvd hpos hd
    rw [hχ2, orderOf_pow' _ (by norm_num), ho] at hle
    have hg4 : Nat.gcd e 4 ≤ 4 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_right _ _)
    have hdv : e = Nat.gcd e 4 * (e / Nat.gcd e 4) :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
    calc e = Nat.gcd e 4 * (e / Nat.gcd e 4) := hdv
      _ ≤ 4 * (e / Nat.gcd e 4) := Nat.mul_le_mul_right _ hg4
      _ ≤ 4 * Nat.card χ.range := Nat.mul_le_mul_left _ hle

/-- `φ(N) ≤ (∏ ℓ²) λ(N)` for `N = ∏ ℓ^{r ℓ}`. -/
theorem card_units_le (T : Finset ℕ) (hT : ∀ ℓ ∈ T, ℓ.Prime) (r : ℕ → ℕ) :
    Nat.card (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ ≤
      (∏ ℓ ∈ T, ℓ ^ 2) * Monoid.exponent (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ := by
  classical
  have hcop : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → Nat.Coprime (a ^ r a) (b ^ r b) := fun a ha b hb hab =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (hT a ha) (hT b hb)).2 hab)
  have hN : (∏ ℓ ∈ T, ℓ ^ r ℓ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ℓ hℓ => pow_ne_zero _ (hT ℓ hℓ).ne_zero
  haveI : NeZero (∏ ℓ ∈ T, ℓ ^ r ℓ) := ⟨hN⟩
  -- totient of product
  have htot : ∀ S ⊆ T, Nat.totient (∏ ℓ ∈ S, ℓ ^ r ℓ) = ∏ ℓ ∈ S, Nat.totient (ℓ ^ r ℓ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert a S haS ih =>
      intro hS
      rw [Finset.prod_insert haS, Finset.prod_insert haS, Nat.totient_mul, ih]
      · exact fun x hx => hS (Finset.mem_insert_of_mem hx)
      · refine Nat.Coprime.prod_right fun b hb => hcop a (hS (Finset.mem_insert_self _ _)) b
          (hS (Finset.mem_insert_of_mem hb)) ?_
        rintro rfl; exact haS hb
  -- divisibility of product
  have hdvdprod : ∀ (z : ℕ) (S : Finset ℕ), S ⊆ T → (∀ ℓ ∈ S, ℓ ^ (r ℓ - 2) ∣ z) →
      (∏ ℓ ∈ S, ℓ ^ (r ℓ - 2)) ∣ z := by
    intro z S
    induction S using Finset.induction_on with
    | empty => intro _ _; simp
    | insert a S haS ih =>
      intro hS hz
      rw [Finset.prod_insert haS]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hz a (Finset.mem_insert_self _ _))
        (ih (fun x hx => hS (Finset.mem_insert_of_mem hx))
          fun x hx => hz x (Finset.mem_insert_of_mem hx))
      refine Nat.Coprime.prod_right fun b hb => ?_
      have hb' := hS (Finset.mem_insert_of_mem hb)
      have ha' := hS (Finset.mem_insert_self _ _)
      have hne : a ≠ b := by rintro rfl; exact haS hb
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hT a ha') (hT b hb')).2 hne)
  have hcar : Nat.card (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ = Nat.totient (∏ ℓ ∈ T, ℓ ^ r ℓ) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hexp : Monoid.exponent (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ =
      ArithmeticFunction.carmichael (∏ ℓ ∈ T, ℓ ^ r ℓ) :=
    (ArithmeticFunction.carmichael_eq_exponent hN).symm
  have hexp_pos : 0 < Monoid.exponent (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ :=
    Monoid.exponent_pos.2 Monoid.ExponentExists.of_finite
  have hW : (∏ ℓ ∈ T, ℓ ^ (r ℓ - 2)) ∣ Monoid.exponent (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ := by
    rw [hexp]
    refine hdvdprod _ T subset_rfl fun ℓ hℓ => ?_
    refine Dvd.dvd.trans ?_ (ArithmeticFunction.carmichael_dvd
      (Finset.dvd_prod_of_mem (fun ℓ => ℓ ^ r ℓ) hℓ))
    have hp := hT ℓ hℓ
    by_cases h2 : ℓ = 2
    · subst h2
      by_cases hk : r 2 = 2
      · rw [hk]; simp
      · rw [ArithmeticFunction.carmichael_two_pow_of_ne_two hk]
    · rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two _ hp h2]
      rcases Nat.eq_zero_or_pos (r ℓ) with h0 | h0
      · rw [h0]; simp
      · rw [Nat.totient_prime_pow hp h0]
        exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
  have hWle := Nat.le_of_dvd hexp_pos hW
  rw [hcar, htot T subset_rfl]
  have hpt : ∀ ℓ ∈ T, Nat.totient (ℓ ^ r ℓ) ≤ ℓ ^ 2 * ℓ ^ (r ℓ - 2) := by
    intro ℓ hℓ
    have hp := hT ℓ hℓ
    have hl2 := hp.two_le
    rcases Nat.eq_zero_or_pos (r ℓ) with h0 | h0
    · rw [h0]; simp
      exact Nat.one_le_pow _ _ (by omega)
    · rw [Nat.totient_prime_pow hp h0]
      rcases Nat.lt_or_ge (r ℓ) 2 with h1 | h1
      · have : r ℓ = 1 := by omega
        have h5 : ℓ - 1 ≤ ℓ ^ 2 := by nlinarith [Nat.sub_le ℓ 1]
        rw [this]; simpa using h5
      · obtain ⟨j, hj⟩ : ∃ j, r ℓ = j + 2 := ⟨r ℓ - 2, by omega⟩
        rw [hj]
        simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_right]
        calc ℓ ^ (j + 2 - 1) * (ℓ - 1) = ℓ ^ (j + 1) * (ℓ - 1) := rfl
          _ ≤ ℓ ^ (j + 1) * ℓ := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = ℓ ^ 2 * ℓ ^ j := by ring
  calc ∏ ℓ ∈ T, Nat.totient (ℓ ^ r ℓ) ≤ ∏ ℓ ∈ T, (ℓ ^ 2 * ℓ ^ (r ℓ - 2)) :=
        Finset.prod_le_prod' hpt
    _ = (∏ ℓ ∈ T, ℓ ^ 2) * ∏ ℓ ∈ T, ℓ ^ (r ℓ - 2) := Finset.prod_mul_distrib
    _ ≤ _ := Nat.mul_le_mul_left _ hWle

/-- The character of `(ℤ/N)ˣ` used to cut out the cyclic field. -/
theorem exists_char_ker (T : Finset ℕ) (hT : ∀ ℓ ∈ T, ℓ.Prime) (h2 : 2 ∈ T) (r : ℕ → ℕ)
    (hr : ∀ ℓ ∈ T, 2 ≤ r ℓ) :
    ∃ χ : (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ →* ℂˣ, χ (-1) = -1 ∧
      Nat.card χ.ker ≤ 4 * ∏ ℓ ∈ T, ℓ ^ 2 := by
  have hN : (∏ ℓ ∈ T, ℓ ^ r ℓ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ℓ hℓ => pow_ne_zero _ (hT ℓ hℓ).ne_zero
  haveI : NeZero (∏ ℓ ∈ T, ℓ ^ r ℓ) := ⟨hN⟩
  have h4 : 4 ∣ ∏ ℓ ∈ T, ℓ ^ r ℓ := by
    have : (2 : ℕ) ^ 2 ∣ 2 ^ r 2 := pow_dvd_pow _ (hr 2 h2)
    exact (by norm_num : (4 : ℕ) = 2 ^ 2) ▸
      this.trans (Finset.dvd_prod_of_mem (fun ℓ => ℓ ^ r ℓ) h2)
  obtain ⟨χ, h1, h2'⟩ := exists_char _ h4
  refine ⟨χ, h1, ?_⟩
  have hc := card_units_le T hT r
  have hm := Subgroup.card_ker_mul_card_range χ
  have hpos : 0 < Nat.card χ.range := Nat.card_pos
  have : Nat.card χ.ker * Nat.card χ.range ≤ (4 * ∏ ℓ ∈ T, ℓ ^ 2) * Nat.card χ.range := by
    rw [hm]
    calc Nat.card (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ
        ≤ (∏ ℓ ∈ T, ℓ ^ 2) * Monoid.exponent (ZMod (∏ ℓ ∈ T, ℓ ^ r ℓ))ˣ := hc
      _ ≤ (∏ ℓ ∈ T, ℓ ^ 2) * (4 * Nat.card χ.range) := Nat.mul_le_mul_left _ h2'
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

/-! ### Arithmetic -/

/-- Lifting the exponent: `ℓ^(r-c) ∣ ord_M(p)` when `ℓ^r ∣ M`. -/
theorem pow_dvd_orderOf (ℓ p r M : ℕ) [Fact ℓ.Prime] [Fact p.Prime] (hne : ℓ ≠ p) (hM : ℓ ^ r ∣ M) :
    ℓ ^ (r - padicValNat ℓ (p ^ (2 * (ℓ - 1)) - 1)) ∣ orderOf (p : ZMod M) := by
  have hℓ : ℓ.Prime := Fact.out
  have hp : p.Prime := Fact.out
  set d := orderOf (p : ZMod M) with hd
  by_cases hd0 : d = 0
  · rw [hd0]; exact dvd_zero _
  have h1 : (p : ZMod M) ^ d = 1 := pow_orderOf_eq_one _
  have h2 : p ^ d ≡ 1 [MOD M] := by
    have : ((p ^ d : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) := by push_cast; exact h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this
  have hpd : 1 ≤ p ^ d := Nat.one_le_pow _ _ hp.pos
  have h3 : ℓ ^ r ∣ p ^ d - 1 := dvd_trans hM ((Nat.modEq_iff_dvd' hpd).mp h2.symm)
  have hp2 := hp.two_le
  have hℓ2 := hℓ.two_le
  have hpk : 1 < p ^ (2 * (ℓ - 1)) := Nat.one_lt_pow (by omega) (by omega)
  have h4 : ℓ ^ r ∣ (p ^ (2 * (ℓ - 1))) ^ d - 1 := by
    have : (p ^ (2 * (ℓ - 1))) ^ d = (p ^ d) ^ (2 * (ℓ - 1)) := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [this]
    have := Nat.sub_dvd_pow_sub_pow (p ^ d) 1 (2 * (ℓ - 1))
    rw [one_pow] at this
    exact dvd_trans h3 this
  have hlt : 1 < (p ^ (2 * (ℓ - 1))) ^ d := Nat.one_lt_pow hd0 hpk
  have hN : (p ^ (2 * (ℓ - 1))) ^ d - 1 ≠ 0 := by omega
  have h5 : r ≤ padicValNat ℓ ((p ^ (2 * (ℓ - 1))) ^ d - 1) :=
    (padicValNat_dvd_iff_le hN).mp h4
  have key : padicValNat ℓ ((p ^ (2 * (ℓ - 1))) ^ d - 1)
      = padicValNat ℓ (p ^ (2 * (ℓ - 1)) - 1) + padicValNat ℓ d := by
    by_cases h2l : ℓ = 2
    · subst h2l
      have hpodd : Odd p := hp.odd_of_ne_two (Ne.symm hne)
      have hpn : ¬ 2 ∣ p := by
        rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]; exact not_not.mpr hpodd
      have hev : 2 ∣ p - 1 := by
        obtain ⟨k, hk⟩ := hpodd
        omega
      have hE := padicValNat.pow_two_sub_pow (x := p) (y := 1) (by omega) (by simpa using hev)
        hpn (n := 2 * d) (by omega) (even_two_mul d)
      rw [one_pow] at hE
      have e1 : (p ^ (2 * (2 - 1))) ^ d = p ^ (2 * d) := by
        rw [← pow_mul]
      have e2 : p ^ (2 * (2 - 1)) - 1 = (p + 1) * (p - 1) := by
        have : 1 ≤ p := by omega
        have h1p : 1 ≤ p ^ (2 * (2 - 1)) := hpk.le
        zify [this, h1p]
        ring
      have hp1 : p + 1 ≠ 0 := by omega
      have hp1' : p - 1 ≠ 0 := by omega
      have e3 : padicValNat 2 (2 * d) = 1 + padicValNat 2 d := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [padicValNat.mul (by norm_num) hd0]; simp
      rw [e1, e2]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [padicValNat.mul hp1 hp1']
      rw [e3] at hE
      omega
    · have hodd : Odd ℓ := hℓ.odd_of_ne_two h2l
      have hcop : Nat.Coprime p ℓ := (Nat.coprime_primes hp hℓ).mpr (Ne.symm hne)
      have hf : p ^ (ℓ - 1) ≡ 1 [MOD ℓ] := by
        have := Nat.ModEq.pow_totient hcop
        rwa [Nat.totient_prime hℓ] at this
      have hu : p ^ (2 * (ℓ - 1)) ≡ 1 [MOD ℓ] := by
        have := hf.pow 2
        rwa [one_pow, ← pow_mul, mul_comm] at this
      have hxy : ℓ ∣ p ^ (2 * (ℓ - 1)) - 1 := (Nat.modEq_iff_dvd' hpk.le).mp hu.symm
      have hx : ¬ ℓ ∣ p ^ (2 * (ℓ - 1)) := by
        intro h
        have := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h)
        exact hne this
      have := padicValNat.pow_sub_pow (p := ℓ) hodd (x := p ^ (2 * (ℓ - 1))) (y := 1) hpk
        (by simpa using hxy) hx hd0
      rwa [one_pow] at this
  rw [key] at h5
  have h6 : r - padicValNat ℓ (p ^ (2 * (ℓ - 1)) - 1) ≤ padicValNat ℓ d := by omega
  exact dvd_trans (pow_dvd_pow ℓ h6) pow_padicValNat_dvd

/-- The local degree `e f` of a prime of `ℚ(ζ_N)` above `p` is divisible by a large power of `ℓ`. -/
theorem pow_dvd_ef_cyclo (ℓ p r N : ℕ) [Fact ℓ.Prime] [Fact p.Prime] [NeZero N]
    (E₀ : Type) [Field E₀] [NumberField E₀] [IsCyclotomicExtension {N} ℚ E₀] (hr : ℓ ^ r ∣ N)
    (P : Ideal (𝓞 E₀)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ℓ ^ (r - 1 - padicValNat ℓ (p ^ (2 * (ℓ - 1)) - 1)) ∣ P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
  set c := padicValNat ℓ (p ^ (2 * (ℓ - 1)) - 1) with hc
  have hℓ : ℓ.Prime := Fact.out
  have hp : p.Prime := Fact.out
  by_cases hpN : p ∣ N
  · obtain ⟨k, m, hm, hN⟩ : ∃ k m, ¬ p ∣ m ∧ N = p ^ (k + 1) * m := by
      have hN0 : N ≠ 0 := NeZero.ne N
      obtain ⟨j, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 p hp.ne_one
      have hj : j ≠ 0 := by
        rintro rfl
        simp at hN
        exact hm (hN ▸ hpN)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      exact ⟨k, m, hm, hN⟩
    have he := IsCyclotomicExtension.Rat.ramificationIdx_eq N E₀ P hN hm
    have hf := IsCyclotomicExtension.Rat.inertiaDeg_eq N E₀ P hN hm
    rw [he, hf]
    by_cases hlp : ℓ = p
    · subst hlp
      have hr' : r ≤ k + 1 := by
        by_contra h
        have h1 : ℓ ^ (k + 1 + 1) ∣ N := (pow_dvd_pow ℓ (by omega)).trans hr
        rw [hN, pow_succ] at h1
        have := (Nat.mul_dvd_mul_iff_left (pow_pos hℓ.pos _)).mp h1
        exact hm this
      have : ℓ ^ (r - 1 - c) ∣ ℓ ^ k := pow_dvd_pow ℓ (by omega)
      exact this.trans ((Dvd.intro _ rfl : ℓ ^ k ∣ ℓ ^ k * (ℓ - 1)).mul_right _)
    · have hcop : Nat.Coprime (ℓ ^ r) (p ^ (k + 1)) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes hℓ hp).mpr hlp)
      rw [hN] at hr
      have hrm : ℓ ^ r ∣ m := hcop.dvd_of_dvd_mul_left hr
      have := pow_dvd_orderOf ℓ p r m hlp hrm
      have h2 : ℓ ^ (r - 1 - c) ∣ ℓ ^ (r - c) := pow_dvd_pow ℓ (by omega)
      exact (h2.trans this).trans (Dvd.intro_left _ rfl)
  · have he := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd p E₀ P hpN
    have hf := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p E₀ P hpN
    rw [he, hf, one_mul]
    by_cases hlp : ℓ = p
    · subst hlp
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp
      · exact absurd (dvd_trans (dvd_pow_self ℓ hr0.ne') hr) hpN
    · have := pow_dvd_orderOf ℓ p r N hlp hr
      exact (pow_dvd_pow ℓ (by omega)).trans this

/-! ### The field `L` -/

namespace Fld

open IsDedekindDomain

variable (K : Type) [Field K] [NumberField K] (N : ℕ) [NeZero N]

/-- `E = K(ζ_N)`. -/
abbrev E := CyclotomicField N K

noncomputable instance : IsGalois K (E K N) := IsCyclotomicExtension.isGalois {N} K (E K N)

/-- The cyclotomic character `Gal(K(ζ_N)/K) → (ℤ/N)ˣ`. -/
noncomputable def phi : (E K N ≃ₐ[K] E K N) →* (ZMod N)ˣ :=
  (IsCyclotomicExtension.zeta_spec N K (E K N)).autToPow K

theorem phi_injective : Function.Injective (phi K N) :=
  (IsCyclotomicExtension.zeta_spec N K (E K N)).autToPow_injective K

/-- The kernel of `χ ∘ phi`. -/
noncomputable def Hsub (χ : (ZMod N)ˣ →* ℂˣ) : Subgroup (E K N ≃ₐ[K] E K N) :=
  (χ.comp (phi K N)).ker

/-- The fixed field of `Hsub`. -/
noncomputable def Lfld (χ : (ZMod N)ˣ →* ℂˣ) : IntermediateField K (E K N) :=
  IntermediateField.fixedField (Hsub K N χ)

variable (χ : (ZMod N)ˣ →* ℂˣ)

instance : (Hsub K N χ).Normal := MonoidHom.normal_ker _

instance : IsGalois K (Lfld K N χ) := IsGalois.of_fixedField_normal_subgroup (Hsub K N χ)

instance : NumberField (Lfld K N χ) := inferInstance

theorem isCyclic_gal : IsCyclic ((Lfld K N χ) ≃ₐ[K] (Lfld K N χ)) := by
  have e := IsGalois.normalAutEquivQuotient (Hsub K N χ)
  let f := QuotientGroup.kerLift (χ.comp (phi K N))
  have hf : Function.Injective ((Units.coeHom ℂ).comp f) :=
    Units.val_injective.comp (QuotientGroup.kerLift_injective _)
  exact e.isCyclic.mp (isCyclic_of_injective_ringHom _ hf)

theorem phi_apply_zeta (σ : E K N ≃ₐ[K] E K N) :
    (IsCyclotomicExtension.zeta N K (E K N)) ^ ((phi K N σ : ZMod N)).val =
      σ (IsCyclotomicExtension.zeta N K (E K N)) :=
  (IsCyclotomicExtension.zeta_spec N K (E K N)).autToPow_spec K σ

theorem phi_eq_neg_one (σ : E K N ≃ₐ[K] E K N)
    (h : σ (IsCyclotomicExtension.zeta N K (E K N)) =
      (IsCyclotomicExtension.zeta N K (E K N))⁻¹) :
    phi K N σ = -1 := by
  have hζ := IsCyclotomicExtension.zeta_spec N K (E K N)
  have h1 := phi_apply_zeta K N σ
  rw [h] at h1
  have h2 : (IsCyclotomicExtension.zeta N K (E K N)) ^ (((phi K N σ : ZMod N)).val + 1) = 1 := by
    rw [pow_succ, h1, inv_mul_cancel₀]
    exact hζ.ne_zero (NeZero.ne N)
  have h3 : N ∣ ((phi K N σ : ZMod N)).val + 1 := hζ.dvd_of_pow_eq_one _ h2
  have h4 : ((((phi K N σ : ZMod N)).val + 1 : ℕ) : ZMod N) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 h3
  push_cast at h4
  rw [ZMod.natCast_zmod_val] at h4
  apply Units.ext
  simpa using eq_neg_of_add_eq_zero_left h4

/-- `L` is totally complex: complex conjugation maps to `-1`, which is not in the kernel of `χ`. -/
theorem Lfld_complex (hχ : χ (-1) ≠ 1) (hN : 3 ≤ N) :
    ∀ w : InfinitePlace (Lfld K N χ), w.IsComplex := by
  intro w
  by_contra hw
  rw [InfinitePlace.not_isComplex_iff_isReal] at hw
  haveI : IsGalois (Lfld K N χ) (E K N) := IsGalois.tower_top_of_isGalois K (Lfld K N χ) (E K N)
  obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := Lfld K N χ) (K := E K N) w
  set ζ := IsCyclotomicExtension.zeta N K (E K N) with hζdef
  have hζ : IsPrimitiveRoot ζ N := IsCyclotomicExtension.zeta_spec N K (E K N)
  have hWc : W.IsComplex := by
    by_contra hWc
    rw [InfinitePlace.not_isComplex_iff_isReal] at hWc
    have h1 : (W.embedding ζ) ^ N = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    have h2 : (W.embedding ζ) ^ 2 = 1 := by
      have hx := InfinitePlace.embedding_of_isReal_apply hWc ζ
      set x : ℝ := InfinitePlace.embedding_of_isReal hWc ζ
      rw [← hx] at h1 ⊢
      have h1' : x ^ N = 1 := by exact_mod_cast h1
      rcases pow_eq_one_iff_cases.1 h1' with h | h | ⟨h, _⟩
      · omega
      · rw [h]; simp
      · rw [h]; simp
    have h3 : ζ ^ 2 = 1 := by
      apply (W.embedding).injective
      rw [map_pow, h2, map_one]
    have := hζ.dvd_of_pow_eq_one 2 h3
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hram : W.IsRamified (Lfld K N χ) :=
    InfinitePlace.isRamified_iff.mpr ⟨hWc, by
      have hW' : W.comap (algebraMap (Lfld K N χ) (E K N)) = w := hW
      rw [hW']; exact hw⟩
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_isConj_of_isRamified
    (φ := W.embedding) (by rwa [InfinitePlace.mk_embedding])
  have hnorm : ‖W.embedding ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) (NeZero.ne N)
  have hσζ : σ ζ = ζ⁻¹ := by
    apply W.embedding.injective
    rw [hσ.eq, map_inv₀]
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hnorm]
    simp
  let σK : E K N ≃ₐ[K] E K N := σ.restrictScalars K
  have hσK : σK (IsCyclotomicExtension.zeta N K (E K N)) =
      (IsCyclotomicExtension.zeta N K (E K N))⁻¹ := hσζ
  have hphi : phi K N σK = -1 := phi_eq_neg_one K N σK hσK
  have hmem : σK ∈ Hsub K N χ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Hsub K N χ)]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  have : χ (phi K N σK) = 1 := hmem
  rw [hphi] at this
  exact hχ this

section chain
variable {A B C D B' : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D] [CommRing B']
  [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B C] [Algebra C D]
  [Algebra A B'] [Algebra B' D]
  [IsScalarTower A B C] [IsScalarTower A C D] [IsScalarTower A B' D]
  [Module.Flat B C] [Module.Flat C D] [Module.Flat B' D]

/-- Tower bookkeeping for `e f`. -/
theorem ef_chain (Q' : Ideal D) (Q : Ideal C) (v : Ideal B) (q' : Ideal B')
    [Q'.LiesOver Q] [Q.LiesOver v] [Q'.LiesOver q'] :
    q'.ramificationIdx A * q'.inertiaDeg A ∣
      (Q.ramificationIdx B * Q.inertiaDeg B) *
        ((v.ramificationIdx A * v.inertiaDeg A) * (Q'.ramificationIdx C * Q'.inertiaDeg C)) := by
  have h1 : q'.ramificationIdx A ∣ Q'.ramificationIdx A := Ideal.ramificationIdx_below_dvd q' Q'
  have h2 : q'.inertiaDeg A ∣ Q'.inertiaDeg A := Ideal.inertiaDeg_below_dvd q' Q'
  have h3 : Q'.ramificationIdx A = Q.ramificationIdx A * Q'.ramificationIdx C :=
    Ideal.ramificationIdx_tower Q Q'
  have h4 : Q'.inertiaDeg A = Q.inertiaDeg A * Q'.inertiaDeg C :=
    Ideal.inertiaDeg_tower Q Q'
  have h5 : Q.ramificationIdx A = v.ramificationIdx A * Q.ramificationIdx B :=
    Ideal.ramificationIdx_tower v Q
  have h6 : Q.inertiaDeg A = v.inertiaDeg A * Q.inertiaDeg B :=
    Ideal.inertiaDeg_tower v Q
  have := mul_dvd_mul h1 h2
  refine this.trans ?_
  rw [h3, h4, h5, h6]
  exact ⟨1, by ring⟩

end chain

theorem ef_le_finrank {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (q : Ideal S) [q.IsPrime] :
    q.ramificationIdx R * q.inertiaDeg R ≤ Module.finrank R S := by
  haveI : Fintype ((q.under R).primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) (q.under R)).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank (q.under R) S]
  exact Finset.single_le_sum (f := fun q : (q.under R).primesOver S =>
    q.1.ramificationIdx R * q.1.inertiaDeg R) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨q, inferInstance, inferInstance⟩)

/-- The cyclotomic subfield `ℚ(ζ_N)` of `E = K(ζ_N)`. -/
noncomputable def E0 : IntermediateField ℚ (E K N) :=
  IntermediateField.adjoin ℚ {IsCyclotomicExtension.zeta N K (E K N)}

instance : IsCyclotomicExtension {N} ℚ (E0 K N) :=
  (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _
    (IsCyclotomicExtension.zeta_spec N K (E K N))).mpr rfl

/-- The key divisibility: a large power of `ℓ` divides `e f` of `Q` times two bounded factors. -/
theorem key (p ℓ r : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hr : ℓ ^ r ∣ N)
    (Q : Ideal (𝓞 (Lfld K N χ))) [Q.IsPrime]
    (hQ : (Q.under (𝓞 K)).under ℤ = Ideal.span {(p : ℤ)}) :
    ∃ a b : ℕ, 0 < a ∧ a ≤ Module.finrank ℚ K ∧ 0 < b ∧ b ≤ Nat.card (Hsub K N χ) ∧
      ℓ ^ (r - 1 - padicValNat ℓ (p ^ (2 * (ℓ - 1)) - 1)) ∣
        (Q.ramificationIdx (𝓞 K) * Q.inertiaDeg (𝓞 K)) * (a * b) := by
  obtain ⟨Q', -, hQ'prime, hQ'under⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (R := 𝓞 (Lfld K N χ)) (S := 𝓞 (E K N)) Q ⊥ (by simp [Ideal.under])
  haveI := hQ'prime
  haveI : Q'.LiesOver Q := ⟨hQ'under.symm⟩
  set v : Ideal (𝓞 K) := Q.under (𝓞 K) with hv
  haveI : v.IsPrime := Ideal.IsPrime.under _ _
  haveI : Q.LiesOver v := ⟨rfl⟩
  set q' : Ideal (𝓞 (E0 K N)) := Q'.under (𝓞 (E0 K N)) with hq'
  haveI : q'.IsPrime := Ideal.IsPrime.under _ _
  haveI : Q'.LiesOver q' := ⟨rfl⟩
  haveI : q'.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨?_⟩
    have e0 : v.under ℤ = Q.under ℤ :=
      Ideal.under_under (A := ℤ) (B := 𝓞 K) (C := 𝓞 (Lfld K N χ)) Q
    have e1 : (Q'.under (𝓞 (Lfld K N χ))).under ℤ = Q'.under ℤ :=
      Ideal.under_under (A := ℤ) (B := 𝓞 (Lfld K N χ)) (C := 𝓞 (E K N)) Q'
    have e2 : q'.under ℤ = Q'.under ℤ :=
      Ideal.under_under (A := ℤ) (B := 𝓞 (E0 K N)) (C := 𝓞 (E K N)) Q'
    rw [← hQ, e0, e2, ← e1, hQ'under]
  have h1 := pow_dvd_ef_cyclo ℓ p r N (E0 K N) hr q'
  have h2 := ef_chain (A := ℤ) (B := 𝓞 K) (C := 𝓞 (Lfld K N χ)) (D := 𝓞 (E K N))
    (B' := 𝓞 (E0 K N)) Q' Q v q'
  refine ⟨v.ramificationIdx ℤ * v.inertiaDeg ℤ,
    Q'.ramificationIdx (𝓞 (Lfld K N χ)) * Q'.inertiaDeg (𝓞 (Lfld K N χ)), ?_, ?_, ?_, ?_,
    h1.trans h2⟩
  · exact Nat.mul_pos (v.ramificationIdx_pos ℤ) (v.inertiaDeg_pos ℤ)
  · have := ef_le_finrank (R := ℤ) (S := 𝓞 K) v
    rwa [NumberField.RingOfIntegers.rank] at this
  · exact Nat.mul_pos (Q'.ramificationIdx_pos _) (Q'.inertiaDeg_pos _)
  · have := ef_le_finrank (R := 𝓞 (Lfld K N χ)) (S := 𝓞 (E K N)) Q'
    rw [← IsFractionRing.finrank_eq (𝓞 (Lfld K N χ)) (Lfld K N χ) (𝓞 (E K N)) (E K N)] at this
    exact this.trans (IntermediateField.finrank_fixedField_eq_card (Hsub K N χ)).le

theorem card_Hsub_le : Nat.card (Hsub K N χ) ≤ Nat.card χ.ker := by
  have hf : Function.Injective
      (fun h : Hsub K N χ => (⟨phi K N h.1, MonoidHom.mem_ker.2 h.2⟩ : χ.ker)) := by
    intro a b hab
    apply Subtype.ext
    apply phi_injective K N
    exact congrArg Subtype.val hab
  exact Nat.card_le_card_of_injective _ hf

theorem exists_prime_under (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
  haveI := v.isPrime
  have hP : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under _ _
  rcases Ideal.isPrime_int_iff.mp hP with h | h
  · exact absurd (Ideal.IsIntegral.eq_bot_of_under_eq_bot ℤ h) v.ne_bot
  · exact h

/-- The assembled statement: a cyclic, totally complex subfield `L` of some `K(ζ_N)` with prescribed
divisibility of local degrees. -/
theorem exists_field (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (hm : 0 < m) :
    ∃ (N : ℕ) (_ : NeZero N) (L : IntermediateField K (E K N)),
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧ (∀ w : InfinitePlace L, w.IsComplex) ∧
      ∀ v ∈ S, ∀ Q : v.asIdeal.primesOver (𝓞 L),
        m ∣ Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) := by
  classical
  set n := Module.finrank ℚ K with hn
  set T : Finset ℕ := insert 2 m.primeFactors with hT_def
  have hT : ∀ ℓ ∈ T, ℓ.Prime := by
    intro ℓ hℓ
    rcases Finset.mem_insert.1 hℓ with rfl | h
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors h
  have h2 : 2 ∈ T := Finset.mem_insert_self _ _
  set C : ℕ := 4 * ∏ ℓ ∈ T, ℓ ^ 2 with hC
  choose pOf hpOf hpU using exists_prime_under K
  set r : ℕ → ℕ := fun ℓ => padicValNat ℓ m + C + n + 3 +
    ∑ v ∈ S, padicValNat ℓ (pOf v ^ (2 * (ℓ - 1)) - 1) with hr
  have hr2 : ∀ ℓ ∈ T, 2 ≤ r ℓ := fun ℓ _ => by simp only [hr]; omega
  obtain ⟨χ, hχ1, hχC⟩ := exists_char_ker T hT h2 r hr2
  have hN0 : (∏ ℓ ∈ T, ℓ ^ r ℓ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ℓ hℓ => pow_ne_zero _ (hT ℓ hℓ).ne_zero
  haveI : NeZero (∏ ℓ ∈ T, ℓ ^ r ℓ) := ⟨hN0⟩
  have hN3 : 3 ≤ ∏ ℓ ∈ T, ℓ ^ r ℓ := by
    have h8 : 2 ^ 3 ≤ 2 ^ r 2 := Nat.pow_le_pow_right (by norm_num) (by simp only [hr]; omega)
    have hle := Finset.single_le_prod' (s := T) (f := fun ℓ => ℓ ^ r ℓ)
      (fun ℓ hℓ => Nat.one_le_pow _ _ (hT ℓ hℓ).pos) h2
    omega
  have hχne : χ (-1) ≠ 1 := by
    rw [hχ1]
    intro h
    have := congrArg Units.val h
    norm_num at this
  refine ⟨∏ ℓ ∈ T, ℓ ^ r ℓ, inferInstance, Lfld K _ χ, inferInstance, isCyclic_gal K _ χ,
    Lfld_complex K _ χ hχne hN3, ?_⟩
  intro v hv Q
  haveI : Q.1.IsPrime := Q.2.1
  have hQover : Q.1.LiesOver v.asIdeal := Q.2.2
  have hQ : (Q.1.under (𝓞 K)).under ℤ = Ideal.span {((pOf v : ℕ) : ℤ)} := by
    rw [← hQover.over]
    exact hpU v
  by_cases hX : Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K) = 0
  · rw [hX]; exact dvd_zero m
  refine (Nat.factorization_prime_le_iff_dvd hm.ne' hX).mp ?_
  intro ℓ hℓ
  by_cases hℓm : ℓ ∣ m
  · have hℓT : ℓ ∈ T :=
      Finset.mem_insert_of_mem (Nat.mem_primeFactors.2 ⟨hℓ, hℓm, hm.ne'⟩)
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    haveI : Fact (pOf v).Prime := ⟨hpOf v⟩
    have hrN : ℓ ^ r ℓ ∣ ∏ ℓ ∈ T, ℓ ^ r ℓ := Finset.dvd_prod_of_mem (fun ℓ => ℓ ^ r ℓ) hℓT
    obtain ⟨a, b, ha0, ha, hb0, hb, hdiv⟩ := key K _ χ (pOf v) ℓ (r ℓ) hrN Q.1 hQ
    have hbC : b ≤ C := hb.trans ((card_Hsub_le K _ χ).trans hχC)
    have hc : padicValNat ℓ (pOf v ^ (2 * (ℓ - 1)) - 1) ≤
        ∑ w ∈ S, padicValNat ℓ (pOf w ^ (2 * (ℓ - 1)) - 1) :=
      Finset.single_le_sum (f := fun w => padicValNat ℓ (pOf w ^ (2 * (ℓ - 1)) - 1))
        (fun _ _ => Nat.zero_le _) hv
    have hfm : m.factorization ℓ = padicValNat ℓ m := Nat.factorization_def m hℓ
    have hexp : m.factorization ℓ + C + n ≤
        r ℓ - 1 - padicValNat ℓ (pOf v ^ (2 * (ℓ - 1)) - 1) := by
      simp only [hr]; omega
    have hdiv' : ℓ ^ (m.factorization ℓ + C + n) ∣
        (Q.1.ramificationIdx (𝓞 K) * Q.1.inertiaDeg (𝓞 K)) * (a * b) :=
      (pow_dvd_pow ℓ hexp).trans hdiv
    have hab0 : a * b ≠ 0 := (Nat.mul_pos ha0 hb0).ne'
    have hle := (hℓ.pow_dvd_iff_le_factorization (mul_ne_zero hX hab0)).mp hdiv'
    rw [Nat.factorization_mul hX hab0, Nat.factorization_mul ha0.ne' hb0.ne'] at hle
    simp only [Finsupp.add_apply] at hle
    have h1 : a.factorization ℓ ≤ n := (Nat.factorization_lt ℓ ha0.ne').le.trans ha
    have h3 : b.factorization ℓ ≤ C := (Nat.factorization_lt ℓ hb0.ne').le.trans hbC
    omega
  · rw [Nat.factorization_eq_zero_of_not_dvd hℓm]
    exact Nat.zero_le _

end Fld

end NumberFieldKB.MilneCFT.Ch7.Lemma73
