import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.FormalGroup.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2PadicDefs
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Milne, *Elliptic Curves*, Chapter II: isogenies (§1) and the formal group of $E$ over $\mathbb Q_p$ (Remark 4.3)

Source: J. S. Milne, *Elliptic Curves*, second edition (course notes `ectext6`, 2006), bib key `milne2006ec`.
Locators give pdf pages (printed page = pdf page − 8).

**Isogenies.** Mathlib has no regular maps of curves. A nonconstant regular map $E \to E'$ of nonsingular projective
curves is dominant, so it induces a $k$-embedding of function fields $k(E') \to k(E)$; conversely every
$k$-algebra homomorphism $k(E') \to k(E)$ (necessarily injective) comes from a unique nonconstant regular map,
because $E$ is nonsingular and $E'$ is complete (Milne I §4: the category of nonsingular projective curves with
nonconstant maps is anti-equivalent to that of function fields of transcendence degree one). So "$E$ and $E'$ are
isogenous" is stated as the existence of a $k$-algebra homomorphism of function fields.

**Formal groups.** Mathlib's `FormalGroup R` with `FormalGroup.IsComm` is exactly the definition in Remark 4.3
(one-parameter commutative formal group law over $R$).
-/

namespace NumberFieldKB.MilneEC.II

open WeierstrassCurve

variable {k : Type*} [Field k]

/-- Elliptic curves $E$, $E'$ are *isogenous* (pdf p. 57) if there is a nonconstant regular map $E \to E'$; such
maps correspond to $k$-algebra homomorphisms of function fields $k(E') \to k(E)$ (module docstring). -/
@[kb "milne2006ec" "Ch. II, §1, Isogenies (definition in prose), pdf p. 57"]
def Isogenous (E E' : WeierstrassCurve k) : Prop :=
  Nonempty (E'.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)

/-- Every elliptic curve is isogenous to itself (the identity map). -/
theorem Isogenous.refl (E : WeierstrassCurve k) : Isogenous E E :=
  ⟨AlgHom.id k _⟩

/-- Isogenies compose. -/
theorem Isogenous.trans {E E' E'' : WeierstrassCurve k} (h : Isogenous E E') (h' : Isogenous E' E'') :
    Isogenous E E'' :=
  ⟨h.some.comp h'.some⟩

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

/-- The value $F(s, t) = \sum_{i,j} a_{ij}s^it^j \in \mathbb Q_p$ of a power series in two variables over
$\mathbb Z_p$ (it converges for $s, t \in p\mathbb Z_p$, Remark 4.3). -/
noncomputable def evalFormal (F : MvPowerSeries (Fin 2) ℤ_[p]) (s t : ℚ_[p]) : ℚ_[p] :=
  ∑' n : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff n F : ℤ_[p]) : ℚ_[p]) * s ^ n 0 * t ^ n 1

/-- **Remark 4.3** (pdf p. 72), as a named statement (Silverman 1986, Chap. IV): an elliptic curve
$E : Y^2Z = X^3 + aXZ^2 + bZ^3$ over $\mathbb Q_p$ ($a, b \in \mathbb Z_p$) defines a commutative formal group $F$
over $\mathbb Z_p$, and there is a map $\psi : p\mathbb Z_p \to E^1(\mathbb Q_p)$, $t \mapsto (x(t) : y(t) : 1)$, which
is a bijection carrying the group law $F$ on $p\mathbb Z_p$ to the group law of $E^1(\mathbb Q_p)$. The parameter is
normalised by $x'(\psi(t)) = t$ (Silverman's parameter is $-x/y$; replacing $F(s, t)$ by $-F(-s, -t)$ passes from
one to the other). -/
@[kb "milne2006ec" "Ch. II, Remark 4.3, pdf p. 72"]
structure Remark4_3 : Prop where
  formalGroup : ∀ (p : ℕ) [Fact p.Prime] (a b : ℤ_[p]), 4 * a ^ 3 + 27 * b ^ 2 ≠ 0 →
    ∃ (F : FormalGroup ℤ_[p]) (ψ : ℚ_[p] → (curveQp a b).toAffine.Point), F.IsComm ∧
      Set.BijOn ψ {t | ‖t‖ < 1} (E1 a b) ∧ (∀ t, ‖t‖ < 1 → xPrime (ψ t) = t) ∧
      ∀ s t, ‖s‖ < 1 → ‖t‖ < 1 → ψ (evalFormal F.toPowerSeries s t) = ψ s + ψ t

end NumberFieldKB.MilneEC.II
