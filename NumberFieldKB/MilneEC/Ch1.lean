import NumberFieldKB.MilneEC.Ch1Affine
import NumberFieldKB.MilneEC.Ch1Examples
import NumberFieldKB.MilneEC.Ch1Intersection
import NumberFieldKB.MilneEC.Ch1IntersectionExists
import NumberFieldKB.MilneEC.Ch1Resultant
import NumberFieldKB.MilneEC.Ch1Projective
import NumberFieldKB.MilneEC.Ch1Unconditional
import NumberFieldKB.MilneEC.Ch1Rational
import NumberFieldKB.MilneEC.Ch1GroupLaw
import NumberFieldKB.MilneEC.Ch1Functions
import NumberFieldKB.MilneEC.Ch1Example46
import NumberFieldKB.MilneEC.Ch1Maps
import NumberFieldKB.MilneEC.Ch1MapsCounterexample
import NumberFieldKB.MilneEC.Ch1Descent
import NumberFieldKB.MilneEC.Ch1Weierstrass
import NumberFieldKB.MilneEC.Ch1Bezout
import NumberFieldKB.MilneEC.Ch1NinePoint
import NumberFieldKB.MilneEC.Ch1Remark113
import NumberFieldKB.MilneEC.Ch1Assoc
import Mathlib.Tactic.MinImports

/-!
# Milne, Elliptic Curves, Chapter I (plane curves)

J. S. Milne, *Elliptic Curves* (2006, `milne2006ec`), the Introduction and Chapter I.

* `Ch1Affine`, `Ch1Examples`: affine plane curves, nonsingular points, multiplicity, tangent lines;
  Examples 1.1, 1.2, 1.5, 1.6, Remark 1.4.
* `Ch1Intersection`, `Ch1IntersectionExists`: intersection numbers; Proposition 1.8 (proved), Remark 1.9,
  Lemma 1.11, Examples 1.10, 1.12; Remark 1.13 (named).
* `Ch1Resultant`: resultants, Propositions 1.22, 1.24, 1.26, Corollary 1.25, Example 1.23.
* `Ch1Projective`, `Ch1Unconditional`: projective plane curves, Exercise 1.17, Examples 1.15, 1.16, 1.20,
  Remark 1.21; Bezout's theorem 1.18 (named).
* `Ch1Rational`: congruent numbers, heights, $p$-adic numbers, Legendre and Hasse–Minkowski, Hensel's lemma.
* `Ch1GroupLaw`: the chord and tangent construction, Theorem 3.1 (associativity named), Proposition 3.2 and
  Mordell's Theorem 2.1 (named), Remark 4.11.
* `Ch1Functions`, `Ch1Example46`: coordinate rings and function fields, Remark 4.2, divisors, $L(D)$, Riemann's
  theorem (named), genus, Picard groups; Example 4.6 (proved).
* `Ch1Maps`: regular maps, Lemma 4.15, Proposition 4.16, Examples 4.17, 4.20, 4.25; 4.18, 4.19, 4.23, 4.24,
  4.26 (named).
* `Ch1MapsCounterexample`: the named statement `Prop4_18` is false as stated (uniqueness over every field;
  counterexample over $\mathbb F_3$, `not_prop4_18`); corrected statement `Prop4_18Corrected`.
* `Ch1Descent`: Example 5.1, descent (Propositions 5.2, 5.3, Remark 5.4 named; 5.5 proved from them).
* `Ch1Weierstrass`: comparison with Mathlib's Weierstrass curves.
-/
