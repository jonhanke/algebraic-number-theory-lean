import NumberFieldKB.MilneCFT.Ch8.Fermat

/-!
# Furtwängler's theorem: reduction of the natural-number statement to an integral one

`Theorem5_14` (Milne, *CFT*, VIII, Theorem 5.14) for positive $x, y, z$ follows from the integral statement "if
$a^p + b^p = c^p$ with $a, b$ coprime, $p \nmid abc$, and $q$ is a prime dividing $b$, then
$q^{p-1}\equiv 1 \pmod{p^2}$", applied to $(y, x, z)$, $(x, y, z)$ or $(x, -z, -y)$ according as $q$ divides
$x$, $y$ or $z$. Both statements are proved unconditionally in Ch8/Eisenstein/Furtwangler.lean
(`Eisenstein.furtwanglerInt`, `Eisenstein.theorem5_14`).
-/

namespace NumberFieldKB.MilneCFT.Ch8

/-- A common divisor of `x` and `y` in `x^p + y^p = z^p` divides `z`. -/
lemma gcd_xy_dvd_z {p x y z : ℕ} (hp : p ≠ 0) (h : x ^ p + y ^ p = z ^ p) {d : ℕ} (hx : d ∣ x) (hy : d ∣ y) :
    d ∣ z := by
  have : d ^ p ∣ z ^ p := by
    rw [← h]; exact dvd_add (pow_dvd_pow_of_dvd hx p) (pow_dvd_pow_of_dvd hy p)
  exact (Nat.pow_dvd_pow_iff hp).mp this

/-- A common divisor of `x` and `z` in `x^p + y^p = z^p` divides `y`. -/
lemma gcd_xz_dvd_y {p x y z : ℕ} (hp : p ≠ 0) (h : x ^ p + y ^ p = z ^ p) {d : ℕ} (hx : d ∣ x) (hz : d ∣ z) :
    d ∣ y := by
  have h1 : d ^ p ∣ x ^ p + y ^ p := by rw [h]; exact pow_dvd_pow_of_dvd hz p
  have : d ^ p ∣ y ^ p := (Nat.dvd_add_right (pow_dvd_pow_of_dvd hx p)).mp h1
  exact (Nat.pow_dvd_pow_iff hp).mp this

/-- A common divisor of `y` and `z` in `x^p + y^p = z^p` divides `x`. -/
lemma gcd_yz_dvd_x {p x y z : ℕ} (hp : p ≠ 0) (h : x ^ p + y ^ p = z ^ p) {d : ℕ} (hy : d ∣ y) (hz : d ∣ z) :
    d ∣ x := by
  have h1 : d ^ p ∣ x ^ p + y ^ p := by rw [h]; exact pow_dvd_pow_of_dvd hz p
  have : d ^ p ∣ x ^ p := (Nat.dvd_add_left (pow_dvd_pow_of_dvd hy p)).mp h1
  exact (Nat.pow_dvd_pow_iff hp).mp this

/-- **Furtwängler's theorem, integral form** (named statement; Milne, *CFT*, VIII, Theorem 5.14, in the form of
Ireland–Rosen, Chapter 14, §5): if $p$ is an odd prime, $a^p + b^p = c^p$ with $a, b$ coprime integers and
$p \nmid abc$, then $q^{p-1}\equiv 1 \pmod{p^2}$ for every prime $q$ dividing $b$. Proved from Eisenstein
reciprocity in `FurtwanglerEisenstein.lean` (`furtwanglerInt_of_eisensteinReciprocity`); proved unconditionally as
`Eisenstein.furtwanglerInt` (Ch8/Eisenstein/Furtwangler.lean). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.14 (integral form)"]
structure FurtwanglerInt : Prop where
  cong : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ a b c : ℤ, a ^ p + b ^ p = c ^ p → IsCoprime a b →
    ¬ (p : ℤ) ∣ a → ¬ (p : ℤ) ∣ b → ¬ (p : ℤ) ∣ c → ∀ q : ℕ, q.Prime → (q : ℤ) ∣ b →
      q ^ (p - 1) ≡ 1 [MOD p ^ 2]

/-- Reduction of `Theorem5_14` to the integral statement with $q \mid b$. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.14 (from the integral form)"]
theorem theorem5_14_of_int (HI : FurtwanglerInt) : Theorem5_14 := by
  have H := HI.cong
  refine ⟨fun p hp hp2 x y z hx hy hz hg hpxyz h q hq hqxyz => ?_⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have cxy : Nat.Coprime x y := by
    have : Nat.gcd x y ∣ 1 := hg ▸ Nat.dvd_gcd dvd_rfl
      (gcd_xy_dvd_z hp0 h (Nat.gcd_dvd_left x y) (Nat.gcd_dvd_right x y))
    exact Nat.dvd_one.mp this
  have cxz : Nat.Coprime x z := by
    have hd := gcd_xz_dvd_y hp0 h (Nat.gcd_dvd_left x z) (Nat.gcd_dvd_right x z)
    have : Nat.gcd x z ∣ 1 := hg ▸ Nat.dvd_gcd (Nat.dvd_gcd (Nat.gcd_dvd_left x z) hd) (Nat.gcd_dvd_right x z)
    exact Nat.dvd_one.mp this
  have hpx : ¬ p ∣ x := fun d => hpxyz (Dvd.dvd.mul_right (Dvd.dvd.mul_right d y) z)
  have hpy : ¬ p ∣ y := fun d => hpxyz (Dvd.dvd.mul_right (Dvd.dvd.mul_left d x) z)
  have hpz : ¬ p ∣ z := fun d => hpxyz (Dvd.dvd.mul_left d (x * y))
  have hZ : (x : ℤ) ^ p + (y : ℤ) ^ p = (z : ℤ) ^ p := by exact_mod_cast h
  have hpxZ : ¬ (p : ℤ) ∣ (x : ℤ) := by rwa [Int.natCast_dvd_natCast]
  have hpyZ : ¬ (p : ℤ) ∣ (y : ℤ) := by rwa [Int.natCast_dvd_natCast]
  have hpzZ : ¬ (p : ℤ) ∣ (z : ℤ) := by rwa [Int.natCast_dvd_natCast]
  rcases (Nat.Prime.dvd_mul hq).mp hqxyz with hqxy | hqz
  · rcases (Nat.Prime.dvd_mul hq).mp hqxy with hqx | hqy
    · exact H p hp hp2 (y : ℤ) (x : ℤ) (z : ℤ) (by rw [add_comm]; exact hZ)
        (Nat.isCoprime_iff_coprime.mpr cxy.symm) hpyZ hpxZ hpzZ q hq (Int.natCast_dvd_natCast.mpr hqx)
    · exact H p hp hp2 (x : ℤ) (y : ℤ) (z : ℤ) hZ (Nat.isCoprime_iff_coprime.mpr cxy) hpxZ hpyZ hpzZ q hq
        (Int.natCast_dvd_natCast.mpr hqy)
  · refine H p hp hp2 (x : ℤ) (-(z : ℤ)) (-(y : ℤ)) ?_
      (Nat.isCoprime_iff_coprime.mpr cxz |>.neg_right) (by simpa using hpxZ) (by simpa using hpzZ)
      (by simpa using hpyZ) q hq (by simpa using Int.natCast_dvd_natCast.mpr hqz)
    rw [hodd.neg_pow, hodd.neg_pow]
    linear_combination hZ

end NumberFieldKB.MilneCFT.Ch8
