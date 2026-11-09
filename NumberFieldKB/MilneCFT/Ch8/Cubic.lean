import NumberFieldKB.MilneCFT.Ch8.Reciprocity

/-!
# Milne, *Class Field Theory*, Chapter VIII §5: cubic reciprocity and Exercise 5.16

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VIII §5,
printed pp. 249–250 (printed page = pdf page − 9).

* **Example 5.13** (cubic reciprocity, Eisenstein): named statement `Example5_13`, the main law for the power residue
  symbol `powerResidueElt 3` of Chapter VIII (the supplementary laws are damaged in the extracted text and not
  stated).
* **Exercise 5.16**: named statement `Exercise5_16`.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

/-- **Example 5.13, the cubic reciprocity law** (named statement; Milne, *CFT*, VIII, Example 5.13, p. 249;
Eisenstein): let $K = \mathbb Q[\zeta]$ with $\zeta$ a primitive cube root of $1$ (any number field $K$ of degree $2$
containing one), so $\mathcal O_K = \mathbb Z[\zeta]$. If $a, b \in \mathcal O_K$ are relatively prime and
$\equiv \pm1 \pmod{3\mathcal O_K}$, then $(a/b) = (b/a)$ for the cubic residue symbol (`powerResidueElt 3`). -/
@[kb "milne2020cft" "Ch. VIII, Example 5.13, p. 249 (cubic reciprocity; input)"]
structure Example5_13 : Prop where
  law : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ ζ : K, IsPrimitiveRoot ζ 3 →
    ∀ a b : 𝓞 K, a ≠ 0 → b ≠ 0 → IsCoprime a b →
      (a - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ a + 1 ∈ Ideal.span {(3 : 𝓞 K)}) →
      (b - 1 ∈ Ideal.span {(3 : 𝓞 K)} ∨ b + 1 ∈ Ideal.span {(3 : 𝓞 K)}) →
        powerResidueElt 3 (a : K) (b : K) = powerResidueElt 3 (b : K) (a : K)

/-- **Exercise 5.16** (named statement; Milne, *CFT*, VIII, Exercise 5.16, p. 250; classical, Gauss/Jacobi): for a
prime $p \equiv 1 \pmod 3$, $2$ is a cube modulo $p$ iff $p = x^2 + 27y^2$ for integers $x, y$. -/
@[kb "milne2020cft" "Ch. VIII, Exercise 5.16, p. 250 (input)"]
structure Exercise5_16 : Prop where
  iff : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    ((∃ x : ZMod p, x ^ 3 = 2) ↔ ∃ x y : ℤ, (p : ℤ) = x ^ 2 + 27 * y ^ 2)

end NumberFieldKB.MilneCFT.Ch8
