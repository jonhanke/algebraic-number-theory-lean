import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import QuadFormsKB.Citation

/-!
# Milne, *Class Field Theory*, Chapter VI: common notation

Milne's region $D(b,\delta,\varepsilon)$ of uniform convergence of Dirichlet series and Euler products (Chapter VI,
Proposition 2.1, p. 185; Lemma 4.3, p. 195).
-/

namespace NumberFieldKB.MilneCFT.Ch6

/-- Milne's region $D(b,\delta,\varepsilon) = \{s : \mathrm{Re}\,s \ge b+\delta,\ |\arg(s-b)| \le \pi/2-\varepsilon\}$
(Milne, *CFT*, Chapter VI, Proposition 2.1, p. 185). -/
def sectorD (b δ ε : ℝ) : Set ℂ :=
  {s : ℂ | b + δ ≤ s.re ∧ |Complex.arg (s - b)| ≤ Real.pi / 2 - ε}

end NumberFieldKB.MilneCFT.Ch6
