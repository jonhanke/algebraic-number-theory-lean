import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Nat.Prime.Defs
import QuadFormsKB.Citation
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Milne, *Class Field Theory*, Chapter VIII §5: application to Fermat's equation

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §5,
printed pp. 249–250 (printed page = pdf page − 9).

* **Theorem 5.14** (Furtwängler): named statement `Theorem5_14` (Milne derives it from the power reciprocity law and
  the explicit Hilbert pairing of Proposition 5.12). Proved unconditionally as `Eisenstein.theorem5_14`
  (Ch8/Eisenstein/Furtwangler.lean), from Eisenstein reciprocity (`Eisenstein.eisensteinReciprocity`).
* **Corollary 5.15** (Wieferich's condition): proved from Theorem 5.14 (`cor_5_15`); unconditionally
  `Eisenstein.cor_5_15_unconditional`.
-/

namespace NumberFieldKB.MilneCFT.Ch8

/-- **Theorem 5.14** (named statement; Milne, *CFT*, VIII, Theorem 5.14, p. 249; Furtwängler, see Hasse 1970, II, 22):
let $p$ be an odd prime and $x, y, z$ relatively prime positive integers with $p \nmid xyz$ and $x^p + y^p = z^p$.
Then $q^{p-1} \equiv 1 \pmod{p^2}$ for every prime $q$ dividing $xyz$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.14, p. 249 (Furtwängler; proved, Eisenstein.theorem5_14)"]
structure Theorem5_14 : Prop where
  cong : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z →
    Nat.gcd (Nat.gcd x y) z = 1 → ¬ p ∣ x * y * z → x ^ p + y ^ p = z ^ p →
      ∀ q : ℕ, q.Prime → q ∣ x * y * z → q ^ (p - 1) ≡ 1 [MOD p ^ 2]

/-- **Corollary 5.15, Wieferich's condition** (Milne, *CFT*, VIII, Corollary 5.15, p. 250; from Theorem 5.14): if
$X^p + Y^p = Z^p$ ($p$ an odd prime) has a solution in positive integers none of which is divisible by $p$, then
$2^{p-1} \equiv 1 \pmod{p^2}$. (Divide by $\gcd(x,y)$ to get a relatively prime solution; one of its entries is even.) -/
@[kb "milne2020cft" "Ch. VIII, Corollary 5.15, p. 250 (Wieferich)"]
theorem cor_5_15 (h : Theorem5_14) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y z : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpz : ¬ p ∣ z) (hxyz : x ^ p + y ^ p = z ^ p) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ 2] := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set g := Nat.gcd x y with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left y hx
  obtain ⟨x', hx'⟩ : g ∣ x := Nat.gcd_dvd_left x y
  obtain ⟨y', hy'⟩ : g ∣ y := Nat.gcd_dvd_right x y
  have hgz : g ∣ z := by
    have : g ^ p ∣ z ^ p := by
      rw [← hxyz]
      exact dvd_add (pow_dvd_pow_of_dvd (Nat.gcd_dvd_left x y) p) (pow_dvd_pow_of_dvd (Nat.gcd_dvd_right x y) p)
    exact (Nat.pow_dvd_pow_iff hp0).mp this
  obtain ⟨z', hz'⟩ := hgz
  have hcop : Nat.gcd x' y' = 1 := by
    have : Nat.gcd (x / g) (y / g) = 1 := Nat.coprime_div_gcd_div_gcd hg0
    have hx'' : x / g = x' := by rw [hx', Nat.mul_div_cancel_left _ hg0]
    have hy'' : y / g = y' := by rw [hy', Nat.mul_div_cancel_left _ hg0]
    rwa [hx'', hy''] at this
  have heq : x' ^ p + y' ^ p = z' ^ p := by
    have h1 : g ^ p * (x' ^ p + y' ^ p) = g ^ p * z' ^ p := by
      rw [mul_add, ← mul_pow, ← mul_pow, ← mul_pow, ← hx', ← hy', ← hz', hxyz]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hg0 p) h1
  have hx'0 : 0 < x' := Nat.pos_of_ne_zero (by rintro rfl; simp at hx'; omega)
  have hy'0 : 0 < y' := Nat.pos_of_ne_zero (by rintro rfl; simp at hy'; omega)
  have hz'0 : 0 < z' := Nat.pos_of_ne_zero (by rintro rfl; simp at hz'; omega)
  have hnd : ¬ p ∣ x' * y' * z' := by
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact hpx (hx' ▸ dvd_mul_of_dvd_right h g)
      · exact hpy (hy' ▸ dvd_mul_of_dvd_right h g)
    · exact hpz (hz' ▸ dvd_mul_of_dvd_right h g)
  have h2 : 2 ∣ x' * y' * z' := by
    by_contra hcon
    have hx2 : ¬ 2 ∣ x' := fun h => hcon (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
    have hy2 : ¬ 2 ∣ y' := fun h => hcon (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
    have hz2 : ¬ 2 ∣ z' := fun h => hcon (dvd_mul_of_dvd_right h _)
    have ex : Odd (x' ^ p) := (Nat.odd_iff.mpr (by omega)).pow
    have ey : Odd (y' ^ p) := (Nat.odd_iff.mpr (by omega)).pow
    have ez : Odd (z' ^ p) := (Nat.odd_iff.mpr (by omega)).pow
    have : Even (z' ^ p) := heq ▸ ex.add_odd ey
    exact (Nat.not_even_iff_odd.mpr ez) this
  have hg1 : Nat.gcd (Nat.gcd x' y') z' = 1 := by rw [hcop, Nat.gcd_one_left]
  exact h.cong p hp hp2 x' y' z' hx'0 hy'0 hz'0 hg1 hnd heq 2 Nat.prime_two h2

end NumberFieldKB.MilneCFT.Ch8
