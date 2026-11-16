import NumberFieldKB.MilneEC.Ch4Rank
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Milne, Elliptic Curves, Chapter IV, Exercise 5.9

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Exercise 5.9 (pdf p. 139).  The
exercise asks for proofs (by the 2-descent of Proposition 5.6); the claimed results are recorded as named statements,
not proved here.  The curves are `cubicCurve`: $Y^2 = X^3 - 4X = (X + 2)X(X - 2)$ and
$Y^2 = X^3 - p^2X = (X + p)X(X - p)$.
-/

namespace NumberFieldKB.MilneEC

/-- **Exercise 5.9 (1)** (pdf p. 139), a named statement: $E(\mathbb{Q})$ is finite for $E : Y^2 = X^3 - 4X$. -/
@[kb "milne2006ec" "Ch. IV, Exercise 5.9 (1), pdf p. 139"]
structure Exercise5_9_1 : Prop where
  finite : Finite (cubicCurve (-2) 0 2).toAffine.Point

/-- **Exercise 5.9 (2)** (pdf p. 139), a named statement: for an odd prime $p$ the rank $r$ of $E(\mathbb{Q})$,
$E : Y^2 = X^3 - p^2X$, satisfies $r \le 2$ if $p \equiv 1 \pmod 8$, $r = 0$ if $p \equiv 3 \pmod 8$, and $r \le 1$
otherwise. -/
@[kb "milne2006ec" "Ch. IV, Exercise 5.9 (2), pdf p. 139"]
structure Exercise5_9_2 : Prop where
  rank_bound : ∀ p : ℕ, p.Prime → p ≠ 2 →
    (p % 8 = 1 → rank (cubicCurve (-(p : ℤ)) 0 p) ≤ 2) ∧
      (p % 8 = 3 → rank (cubicCurve (-(p : ℤ)) 0 p) = 0) ∧
      (p % 8 = 5 ∨ p % 8 = 7 → rank (cubicCurve (-(p : ℤ)) 0 p) ≤ 1)

end NumberFieldKB.MilneEC
