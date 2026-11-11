import NumberFieldKB.MilneANT.Ch7HenselResultant
import NumberFieldKB.MilneANT.Ch7HenselDiscr
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Milne, *Algebraic Number Theory*, Remark 7.37: the discriminant form of Hensel's lemma, unconditionally

Source: J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020), Remark 7.37, pp. 122–123 (citing Cassels 1986,
Chapter 4 and p. 107); bib key `milne2020ant`.

**`remark7_37Discriminant`** combines `remark7_37Resultant` (the resultant form, proved by Newton iteration in
`Ch7HenselResultant.lean`) with `remark7_37Discriminant_of_resultant` (the discriminant hypothesis implies the
resultant one, `Ch7HenselDiscr.lean`).
-/

open IsLocalRing

namespace NumberFieldKB.MilneANT

/-- **Remark 7.37, discriminant form** (proved, unconditionally): over a complete discrete valuation ring, if
$\lVert f - g_0 h_0 \rVert < |\operatorname{disc} f|$ then $f$ factors with degrees $\deg g_0$, $\deg h_0$. -/
@[kb "milne2020ant" "v3.08, Remark 7.37, p. 123"]
theorem remark7_37Discriminant (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] : Remark7_37Discriminant A :=
  remark7_37Discriminant_of_resultant A (remark7_37Resultant A)

end NumberFieldKB.MilneANT
