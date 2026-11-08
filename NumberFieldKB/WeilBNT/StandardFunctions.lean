import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import QuadFormsKB.Citation

/-!
# Weil, *Basic Number Theory*, VII.§2, Def. 2: standard functions on a real vector space

$E$ is a finite-dimensional real vector space, written in coordinates as $\mathbb R^n$ (`Fin n → ℝ`; indices are
0-based). A *standard function* on $E$ is $e\mapsto p(e)\exp(-q(e))$ with $p$ a (complex) polynomial function and $q$ a
positive definite quadratic form (`IsStandardFunction`).

* `isStandardFunction_gaussian`: $e\mapsto\exp(-q(e))$ is standard ($p=1$).
* `IsStandardFunction.mul_poly`: multiplying a standard function by a polynomial gives a standard function.
-/

noncomputable section

namespace NumberFieldKB.WeilBNT

variable {n : ℕ}

/-- **Weil, VII.§2, Def. 2**: $\Phi$ is a standard function on $\mathbb R^n$ if $\Phi(e)=P(e)\exp(-Q(e))$ for a complex
polynomial $P$ in the coordinates and a positive definite real quadratic form $Q$. -/
@[kb "weil1973bnt" "Ch. VII, §2, Def. 2"]
def IsStandardFunction (Φ : (Fin n → ℝ) → ℂ) : Prop :=
  ∃ (P : MvPolynomial (Fin n) ℂ) (Q : QuadraticForm ℝ (Fin n → ℝ)), Q.PosDef ∧
    ∀ e, Φ e = MvPolynomial.eval (fun i => (e i : ℂ)) P * Complex.exp (-(Q e : ℂ))

theorem isStandardFunction_gaussian {Q : QuadraticForm ℝ (Fin n → ℝ)} (hQ : Q.PosDef) :
    IsStandardFunction fun e => Complex.exp (-(Q e : ℂ)) :=
  ⟨1, Q, hQ, fun e => by simp⟩

theorem IsStandardFunction.mul_poly {Φ : (Fin n → ℝ) → ℂ} (hΦ : IsStandardFunction Φ)
    (R : MvPolynomial (Fin n) ℂ) :
    IsStandardFunction fun e => MvPolynomial.eval (fun i => (e i : ℂ)) R * Φ e := by
  obtain ⟨P, Q, hQ, h⟩ := hΦ
  exact ⟨R * P, Q, hQ, fun e => by simp only [h, map_mul, mul_assoc]⟩

end NumberFieldKB.WeilBNT
