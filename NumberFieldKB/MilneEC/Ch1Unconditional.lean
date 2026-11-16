import NumberFieldKB.MilneEC.Ch1IntersectionExists
import NumberFieldKB.MilneEC.Ch1Projective
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Milne, Elliptic Curves, Chapter I: unconditional forms

The results stated with the hypothesis `Prop1_8` (existence in Proposition 1.8), which is proved in
`Ch1IntersectionExists` (`prop1_8_holds`), restated without it.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

/-- **Proposition 1.8** (p. 16), unconditional: there is a unique map $I : \mathcal F(k) \to \mathbb N$
with the properties (a)–(e). -/
@[kb "milne2006ec" "Ch. I, Prop. 1.8, pdf p. 16"]
theorem prop_1_8' (k : Type) [Field k] :
    (∃ I : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ, IsIntersectionNumber I) ∧
    ∀ I J : MvPolynomial (Fin 2) k → MvPolynomial (Fin 2) k → ℕ,
      IsIntersectionNumber I → IsIntersectionNumber J →
      ∀ f g, NoCommonFactorAtOrigin f g → I f g = J f g :=
  prop_1_8 prop1_8_holds k

/-- **Example 1.12** (p. 18), unconditional: the origin is a cusp of $Y^2 = X^3$. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.12, pdf p. 18"]
theorem example_1_12_isCusp' (k : Type) [Field k] :
    IsCusp (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) ((0, 0) : k × k) :=
  example_1_12_isCusp prop1_8_holds k

/-- **Example 1.20** (p. 22), unconditional. -/
@[kb "milne2006ec" "Ch. I, Ex. 1.20, pdf p. 22"]
theorem example_1_20' {k : Type} [Field k] (a b : k) :
    projIntersectionNumber (X 2) (weierstrassCubic a b) (pointAtInfinity k) = 3 ∧
    polarLine (weierstrassCubic a b) (pointAtInfinity k).rep =
      C ((pointAtInfinity k).rep 1 ^ 2) * X 2 ∧
    IsFlex (weierstrassCubic a b) (pointAtInfinity k) :=
  example_1_20 prop1_8_holds a b

end NumberFieldKB.MilneEC
