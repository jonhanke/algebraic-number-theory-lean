import NumberFieldKB.MilneEC.Ch1Projective

/-!
# Bezout's theorem: shared definitions

Milne, *Elliptic Curves* (`milne2006ec`), Chapter I, Theorem 1.18 (Bezout), proved after Fulton 1969,
Chapter 5. This file holds the definitions shared by the files of the proof:

* `pointIdeal p`: the maximal ideal of the point `p = (a, b)` in `K[X, Y]`;
* `LocalRingAt p`: the local ring $\mathcal O_p = K[X, Y]_{(X - a, Y - b)}$;
* `numAt f g p`: $\dim_K \mathcal O_p/(f, g)$, Fulton's intersection number at `p` (it equals
  `intersectionNumberAt f g p`, which translates `p` to the origin first; see `Ch1BezoutLocal`);
* `linSubst A F`: the linear substitution $F(A\vec x)$ in a form in three variables (matrices act on column
  vectors, as everywhere in this library).
-/

open MvPolynomial

namespace NumberFieldKB.MilneEC.Bezout

variable {K : Type*} [Field K]

/-- The maximal ideal of the point `p = (a, b)` in `K[X, Y]`: the polynomials vanishing at `p`. -/
noncomputable def pointIdeal (p : K × K) : Ideal (MvPolynomial (Fin 2) K) :=
  RingHom.ker (aeval ![p.1, p.2] : MvPolynomial (Fin 2) K →ₐ[K] K)

instance pointIdeal_isPrime (p : K × K) : (pointIdeal p).IsPrime :=
  RingHom.ker_isPrime _

/-- The local ring $\mathcal O_p$ of the plane at the point `p` (Fulton 1969, §2.4). -/
abbrev LocalRingAt (p : K × K) := Localization.AtPrime (pointIdeal p)

/-- The quotient $\mathcal O_p/(f, g)$. -/
abbrev LocalQuotientAt (f g : MvPolynomial (Fin 2) K) (p : K × K) :=
  LocalRingAt p ⧸ Ideal.span {algebraMap _ (LocalRingAt p) f, algebraMap _ (LocalRingAt p) g}

/-- Fulton's intersection number at a point `p`: $\dim_K \mathcal O_p/(f, g)$ (`Module.finrank`, so 0
when the dimension is infinite). -/
noncomputable def numAt (f g : MvPolynomial (Fin 2) K) (p : K × K) : ℕ :=
  Module.finrank K (LocalQuotientAt f g p)

/-- The linear substitution $F(A\vec x)$: the variable `X i` is replaced by $\sum_j A_{ij} X_j$. -/
noncomputable def linSubst (A : Matrix (Fin 3) (Fin 3) K) (F : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 3) K :=
  bind₁ (fun i => ∑ j, C (A i j) * X j) F

/-- The common zeros of `f` and `g` in $K^2$. -/
def commonZeros (f g : MvPolynomial (Fin 2) K) : Set (K × K) :=
  {p | evalAt f p = 0 ∧ evalAt g p = 0}

end NumberFieldKB.MilneEC.Bezout
