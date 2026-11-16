import NumberFieldKB.MilneEC.Ch1Projective

/-!
# Tangent lines given by linear forms

Definitions shared by the files of the proof of associativity of the chord and tangent law (Milne,
*Elliptic Curves*, Theorem I.3.1).

* `linCoeff ℓ j`: the coefficient of `X j` in a linear form `ℓ`;
* `IsTangentForm F ℓ X`: `ℓ` is the tangent line of `F` at `X` (the gradient of `F` at `X` is a multiple of
  the coefficient vector of `ℓ`);
* `lineThrough p q`: the linear form of the line through `p` and `q` (the cross product $p \times q$).
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

/-- The coefficient of `X j` in a linear form. -/
noncomputable def linCoeff (ℓ : MvPolynomial (Fin 3) K) (j : Fin 3) : K :=
  ℓ.coeff (Finsupp.single j 1)

/-- `ℓ` is the tangent line of `F` at `X`: the gradient of `F` at the representative of `X` is a multiple
of the coefficient vector of `ℓ`. -/
def IsTangentForm (F ℓ : MvPolynomial (Fin 3) K) (X : ℙ K (Fin 3 → K)) : Prop :=
  ∃ c : K, ∀ j, aeval X.rep (pderiv j F) = c * linCoeff ℓ j

/-- The line through `p` and `q`: the linear form with coefficient vector the cross product $p \times q$. -/
noncomputable def lineThrough (p q : Fin 3 → K) : MvPolynomial (Fin 3) K :=
  C (p 1 * q 2 - p 2 * q 1) * X 0 + C (p 2 * q 0 - p 0 * q 2) * X 1 +
    C (p 0 * q 1 - p 1 * q 0) * X 2

end NumberFieldKB.MilneEC.Bezout
