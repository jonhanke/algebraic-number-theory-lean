import NumberFieldKB.ModularCurves.Genus
import NumberFieldKB.ModularCurves.DivisorsX0

/-!
# The genus of $X_0(N)$ and its divisors of functions

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. I, §4 and Ch. V, §2. The function field $\mathbb Q(X_0(N))$
(`X0 N`) is a function field of one variable over $\mathbb Q$ (`isFunctionField_X0`) with exact constant field
$\mathbb Q$ (`isIntegrallyClosedIn_X0`, from `X0Field.eq_algebraMap_of_isAlgebraic`). So the general results of
`ModularCurves/Genus.lean` apply: Riemann's theorem with the genus of $X_0(N)$ (`isGenus_X0`), Riemann–Roch
(`riemannRoch_X0`), and the divisor of a nonzero function on $X_0(N)$ has degree 0 (`deg_eq_zero_of_isDivisorOf_X0`).
Hence the principal divisors lie in $\mathrm{Div}^0$ (`principalDivisors_le_divisorsDegZero`), and
$J_0(N)(\mathbb Q) = \mathrm{Pic}^0$ (`Pic0X0 N`) is the quotient of the degree-0 divisors by all principal divisors.
-/

open NumberFieldKB.MilneEC

noncomputable section

namespace NumberFieldKB.MilneEC

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- Over a function field, principal divisors have degree 0 (Milne, p. 45): the subgroup they generate lies in
$\mathrm{Div}^0$. -/
theorem principalDivisors_le_divisorsDegZero (hF : TauCeti.IsFunctionField k K) :
    principalDivisors (k := k) (K := K) ≤ divisorsDegZero := by
  rw [principalDivisors, AddSubgroup.closure_le]
  rintro D ⟨h, hD⟩
  exact deg_eq_zero_of_isDivisorOf hF hD

end NumberFieldKB.MilneEC

namespace NumberFieldKB.ModularCurves

variable (N : ℕ) [NeZero N]

/-- $\mathbb Q(X_0(N))$ is a function field of one variable over $\mathbb Q$ (Tau Ceti's predicate). -/
theorem isFunctionField_X0 : TauCeti.IsFunctionField ℚ (X0 N) := by
  have : @IsScalarTower ℚ (RatFunc ℚ) (X0 N) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  have hR : TauCeti.IsFunctionField ℚ (RatFunc ℚ) := by
    convert TauCeti.IsFunctionField.ratFunc ℚ
    exact Subsingleton.elim _ _
  exact hR.finite_extension

/-- **$\mathbb Q$ is the exact constant field of $X_0(N)$** (Milne V §2), in the form `IsIntegrallyClosedIn`. -/
theorem isIntegrallyClosedIn_X0 : IsIntegrallyClosedIn ℚ (X0 N) := by
  rw [isIntegrallyClosedIn_iff]
  refine ⟨(algebraMap ℚ (X0 N)).injective, fun {x} hx => ?_⟩
  obtain ⟨q, hq⟩ := X0Field.eq_algebraMap_of_isAlgebraic (prop2_4' N) x hx.isAlgebraic
  exact ⟨q, hq.symm⟩

/-- **Riemann's theorem for $X_0(N)$** (Milne, Theorem 4.13): the genus `genus ℚ (X0 N)` satisfies
$\ell(D) \ge \deg D + 1 - g$, with equality for $\deg D > 2g - 2$. -/
@[kb "milne2006ec" "Ch. V, §2, the genus of X_0(N) (running text), pdf p. 196"]
theorem isGenus_X0 : IsGenus ℚ (X0 N) (genus ℚ (X0 N)) :=
  isGenus_genus (isFunctionField_X0 N) (isIntegrallyClosedIn_X0 N)

/-- The genus of $X_0(N)$ is Tau Ceti's genus of its function field, a natural number. -/
theorem genus_X0_eq : genus ℚ (X0 N) = TauCeti.genus ℚ (X0 N) :=
  genus_eq_tauCetiGenus (isFunctionField_X0 N) (isIntegrallyClosedIn_X0 N)

/-- **Riemann–Roch for $X_0(N)$** (Milne, Remark 4.7 (a)). -/
theorem riemannRoch_X0 :
    ∃ W : Divisor ℚ (X0 N), W.deg = 2 * genus ℚ (X0 N) - 2 ∧
      ∀ D : Divisor ℚ (X0 N), (D.ell : ℤ) = D.deg + 1 - genus ℚ (X0 N) + (W - D).ell :=
  riemannRoch (isFunctionField_X0 N) (isIntegrallyClosedIn_X0 N)

/-- **The divisor of a nonzero function on $X_0(N)$ has degree 0** (Milne, p. 45). -/
@[kb "milne2006ec" "Ch. I, §4, div(h) is a divisor of degree zero, pdf p. 45"]
theorem deg_eq_zero_of_isDivisorOf_X0 {D : Divisor ℚ (X0 N)} {h : X0 N} (hD : IsDivisorOf D h) : D.deg = 0 :=
  deg_eq_zero_of_isDivisorOf (isFunctionField_X0 N) hD

/-- Principal divisors of $X_0(N)$ have degree 0, so $J_0(N)(\mathbb Q) = \mathrm{Pic}^0$ is
$\mathrm{Div}^0 / \mathrm{Princ}$. -/
theorem principalDivisors_le_divisorsDegZero_X0 :
    principalDivisors (k := ℚ) (K := X0 N) ≤ divisorsDegZero :=
  principalDivisors_le_divisorsDegZero (isFunctionField_X0 N)

end NumberFieldKB.ModularCurves
