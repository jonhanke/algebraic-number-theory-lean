import NumberFieldKB.MilneCFT.Ch8.Eisenstein.Reciprocity
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs

/-!
# Furtwängler's theorem and Wieferich's criterion, unconditionally

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII, Theorem 5.14
and Corollary 5.15 (pp. 249–250); K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*,
Chapter 14, §5.

With the Eisenstein reciprocity law proved (`eisensteinReciprocity`), the reductions
`furtwanglerInt_of_eisensteinReciprocity` and `theorem5_14_of_eisensteinReciprocity` (FurtwanglerEisenstein.lean)
and `cor_5_15` (Fermat.lean) become unconditional.
-/

namespace NumberFieldKB.MilneCFT.Ch8.Eisenstein

/-- **Furtwängler's theorem, integral form** (the named statement `FurtwanglerInt`), unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.14 (integral form; proved)"]
theorem furtwanglerInt : FurtwanglerInt :=
  furtwanglerInt_of_eisensteinReciprocity eisensteinReciprocity

/-- **Milne, *CFT*, VIII, Theorem 5.14** (Furtwängler; the named statement `Theorem5_14`), unconditionally. -/
@[kb "milne2020cft" "Ch. VIII, Theorem 5.14, p. 249 (proved)"]
theorem theorem5_14 : Theorem5_14 :=
  theorem5_14_of_int furtwanglerInt

/-- **Milne, *CFT*, VIII, Corollary 5.15** (Wieferich's condition), unconditionally: if $X^p + Y^p = Z^p$ ($p$ an
odd prime) has a solution in positive integers none of which is divisible by $p$, then
$2^{p-1} \equiv 1 \pmod{p^2}$. -/
@[kb "milne2020cft" "Ch. VIII, Corollary 5.15, p. 250 (Wieferich; unconditional)"]
theorem cor_5_15_unconditional (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (x y z : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (hpx : ¬ p ∣ x) (hpy : ¬ p ∣ y) (hpz : ¬ p ∣ z) (hxyz : x ^ p + y ^ p = z ^ p) :
    2 ^ (p - 1) ≡ 1 [MOD p ^ 2] :=
  cor_5_15 theorem5_14 p hp hp2 x y z hx hy hz hpx hpy hpz hxyz

end NumberFieldKB.MilneCFT.Ch8.Eisenstein
