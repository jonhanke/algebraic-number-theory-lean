import Mathlib
import QuadFormsKB.Citation

/-!
# Milne, Elliptic Curves, Chapter I, Section 1: affine plane curves

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter I, Section 1 ("Basic
definitions; Bezout's theorem"), the subsections on affine plane curves.  Locators give the pdf page of
the text `ectext6` (printed page = pdf page − 8).

Conventions.
* A polynomial in two variables over `k` is an element of `MvPolynomial (Fin 2) k`; Milne's $X$ is
  `X 0` and his $Y$ is `X 1` (indices are 0-based).
* For a field `K` containing `k` (a `k`-algebra `K`), a point of the plane with coordinates in `K` is a
  pair `(x, y) : K × K`, and the value of `f` at it is `evalAt f (x, y) = aeval ![x, y] f`.
* Milne identifies an affine plane curve with the class of its equation up to a nonzero constant
  (footnote 1, p. 14).  Here a curve is given by its equation `f`, the predicate `IsAffinePlaneCurve f`
  says that `f` is admissible, and `affinePoints_C_mul` shows that `f` and `c • f` have the same points.
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC

section Defs

variable {k : Type*} [Field k]

/-- The value of a polynomial in two variables over `k` at a point `(x, y)` with coordinates in a
`k`-algebra `K`. -/
noncomputable def evalAt {K : Type*} [CommRing K] [Algebra k K] (f : MvPolynomial (Fin 2) k)
    (P : K × K) : K :=
  aeval ![P.1, P.2] f

/-- The polynomial `f` regarded as a polynomial with coefficients in a field `K` containing `k`. -/
noncomputable abbrev baseChange {σ : Type*} (K : Type*) [CommRing K] [Algebra k K]
    (f : MvPolynomial σ k) : MvPolynomial σ K :=
  map (algebraMap k K) f

/-- **Affine plane curve** (p. 14): a nonconstant polynomial `f ∈ k[X, Y]` with no repeated factor in
$k^{\mathrm{al}}[X, Y]$ defines an affine plane curve $C_f$ over `k`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of affine plane curve, pdf p. 14"]
def IsAffinePlaneCurve (f : MvPolynomial (Fin 2) k) : Prop :=
  f.totalDegree ≠ 0 ∧ Squarefree (baseChange (AlgebraicClosure k) f)

/-- The points of $C_f$ with coordinates in a field `K` containing `k` (p. 14):
$C_f(K) = \{(x, y) \in K^2 \mid f(x, y) = 0\}$. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of C_f(K), pdf p. 14"]
def affinePoints (f : MvPolynomial (Fin 2) k) (K : Type*) [Field K] [Algebra k K] : Set (K × K) :=
  {P | evalAt f P = 0}

/-- For `c ≠ 0` the curves $C_f$ and $C_{cf}$ have the same points in every field (p. 14). -/
@[kb "milne2006ec" "Ch. I, §1, C_f = C_{cf}, pdf p. 14"]
theorem affinePoints_C_mul (f : MvPolynomial (Fin 2) k) {c : k} (hc : c ≠ 0) (K : Type*) [Field K]
    [Algebra k K] : affinePoints (C c * f) K = affinePoints f K := by
  ext P
  simp [affinePoints, evalAt, hc]

/-- An affine plane curve $C_f$ is **irreducible** if `f` is irreducible in `k[X, Y]` (p. 14). -/
@[kb "milne2006ec" "Ch. I, §1, Def. of irreducible curve, pdf p. 14"]
def IsIrreducibleCurve (f : MvPolynomial (Fin 2) k) : Prop := Irreducible f

/-- An affine plane curve $C_f$ is **geometrically irreducible** if `f` remains irreducible over
$k^{\mathrm{al}}$ (p. 14). -/
@[kb "milne2006ec" "Ch. I, §1, Def. of geometrically irreducible curve, pdf p. 14"]
def IsGeometricallyIrreducible (f : MvPolynomial (Fin 2) k) : Prop :=
  Irreducible (baseChange (AlgebraicClosure k) f)

/-- The **irreducible components** of $C_f$ (p. 14) are the curves $C_g$ for the irreducible factors
`g` of `f` (each up to a nonzero constant). -/
@[kb "milne2006ec" "Ch. I, §1, Def. of irreducible components, pdf p. 14"]
def IsComponent (f g : MvPolynomial (Fin 2) k) : Prop := Irreducible g ∧ g ∣ f

/-- The partial derivative $\partial f/\partial X$. -/
noncomputable abbrev dX (f : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k := pderiv 0 f

/-- The partial derivative $\partial f/\partial Y$. -/
noncomputable abbrev dY (f : MvPolynomial (Fin 2) k) : MvPolynomial (Fin 2) k := pderiv 1 f

/-- **Nonsingular point** (p. 14): a point `P` of $C_f(K)$ is nonsingular if at least one of the
partial derivatives $\partial f/\partial X$, $\partial f/\partial Y$ is nonzero at `P`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of nonsingular point, pdf p. 14"]
def IsNonsingularPoint (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : Prop :=
  P ∈ affinePoints f K ∧ (evalAt (dX f) P ≠ 0 ∨ evalAt (dY f) P ≠ 0)

/-- A point of $C_f(K)$ which is not nonsingular is **singular** (p. 15). -/
@[kb "milne2006ec" "Ch. I, §1, Def. of singular point, pdf p. 15"]
def IsSingularPoint (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : Prop :=
  P ∈ affinePoints f K ∧ evalAt (dX f) P = 0 ∧ evalAt (dY f) P = 0

/-- The **tangent line** to $C_f$ at a nonsingular point $P = (a, b)$ (p. 14):
$(\partial f/\partial X)_P (X - a) + (\partial f/\partial Y)_P (Y - b) = 0$, as a polynomial over `K`. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of tangent line at a nonsingular point, pdf p. 14"]
noncomputable def tangentLine (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : MvPolynomial (Fin 2) K :=
  C (evalAt (dX f) P) * (X 0 - C P.1) + C (evalAt (dY f) P) * (X 1 - C P.2)

/-- **Nonsingular curve** (p. 15): all the points of $C_f(k^{\mathrm{al}})$ are nonsingular. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of nonsingular curve, pdf p. 15"]
def IsNonsingularCurve (f : MvPolynomial (Fin 2) k) : Prop :=
  ∀ P ∈ affinePoints f (AlgebraicClosure k), IsNonsingularPoint f P

theorem isSingularPoint_iff_not_nonsingular (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K]
    [Algebra k K] {P : K × K} (hP : P ∈ affinePoints f K) :
    IsSingularPoint f P ↔ ¬ IsNonsingularPoint f P := by
  simp [IsSingularPoint, IsNonsingularPoint, hP]

/-! ### Multiplicity and tangent lines at a singular point -/

/-- The Taylor expansion of `f` at $P = (a, b)$: the polynomial $f(X + a, Y + b)$ over `K`, whose
homogeneous component of degree `i` is Milne's $f_i$ (p. 16). -/
noncomputable def translate (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : MvPolynomial (Fin 2) K :=
  aeval ![X 0 + C P.1, X 1 + C P.2] f

/-- The order of a polynomial: the least degree of a nonzero homogeneous component (0 for the zero
polynomial). -/
noncomputable def order {σ K : Type*} [CommSemiring K] (g : MvPolynomial σ K) : ℕ :=
  sInf {i | homogeneousComponent i g ≠ 0}

/-- The lowest-degree form of a polynomial: its homogeneous component of least degree. -/
noncomputable def lowestForm {σ K : Type*} [CommSemiring K] (g : MvPolynomial σ K) :
    MvPolynomial σ K :=
  homogeneousComponent (order g) g

/-- **Multiplicity** of a point `P` on $C_f$ (p. 16): the degree `m` of the first nonzero term $f_m$ of
the Taylor expansion of `f` at `P`.  A point of multiplicity 2 is a **double point**. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of multiplicity m_P(C), pdf p. 16"]
noncomputable def multiplicityAt (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : ℕ :=
  order (translate f P)

/-- **Tangent lines** at `P` (p. 16): the lines $L = 0$, $L = cX + dY \neq 0$ a linear form over a
field `Ω` containing `K` (Milne takes $k^{\mathrm{al}}$), dividing the lowest form $f_m$ of the Taylor
expansion at `P`; the line in the plane is $L(X - a, Y - b) = 0$. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of tangent lines at a point, pdf p. 16"]
def IsTangentAt (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K] (P : K × K)
    {Ω : Type*} [Field Ω] [Algebra K Ω] (L : MvPolynomial (Fin 2) Ω) : Prop :=
  L ≠ 0 ∧ L.IsHomogeneous 1 ∧ L ∣ baseChange Ω (lowestForm (translate f P))

/-- **Ordinary singularity** and **node** (p. 16): a singular point `P` is an ordinary singularity if
the tangent lines at `P` are distinct, i.e. the lowest form $f_m$ has no repeated factor over an
algebraic closure; an ordinary double point is a node. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of ordinary singularity, pdf p. 16"]
def IsOrdinarySingularity (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K]
    (P : K × K) : Prop :=
  IsSingularPoint f P ∧ Squarefree (baseChange (AlgebraicClosure K) (lowestForm (translate f P)))

/-- A **node** (p. 16) is an ordinary double point. -/
@[kb "milne2006ec" "Ch. I, §1, Def. of node, pdf p. 16"]
def IsNode (f : MvPolynomial (Fin 2) k) {K : Type*} [Field K] [Algebra k K] (P : K × K) : Prop :=
  IsOrdinarySingularity f P ∧ multiplicityAt f P = 2

end Defs

end NumberFieldKB.MilneEC
