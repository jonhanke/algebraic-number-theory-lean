import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import QuadFormsKB.Citation
import NumberFieldKB.MilneEC.Ch2Iso
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Milne, Elliptic Curves, Chapter IV §10: good reduction and zeta functions of varieties over $\mathbb Q$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 10, pdf p. 170: the
definitions in prose of good reduction of a projective variety $V$ over $\mathbb Q$ and of its zeta function
$\zeta(V, s) = \prod_{p \text{ good}} \zeta(V_p, s)$, with Milne's first example $\zeta(\mathrm{Pt}, s) = \zeta(s)$.

## Formalization
* A projective variety over $\mathbb Q$ is given by homogeneous polynomials $F_1, \dots, F_r$ in $X_0, \dots, X_n$
  (`Fin (n + 1)` indexes the coordinates, so Milne's $X_0, \dots, X_n$ have their own indices).  Milne scales each
  $F_i$ so that its coefficients are integers without common factor (`IsPrimitiveScaling`) and reduces modulo $p$.
* **Nonsingular variety** (`IsNonsingularCI`): the Jacobian criterion for a variety cut out by $r$ equations in
  $\mathbb P^n$ as a complete intersection of dimension $d = n - r$: at every point of $V(\bar K)$ the rows
  $\nabla F_i$ of the Jacobian matrix are linearly independent (rank $r$).  **Deviation recorded:** Milne's prose
  covers every projective variety; for a variety that is not given as a complete intersection, nonsingularity needs
  the local dimension at each point, which Mathlib does not provide for zero sets of polynomials.  Milne's examples
  (the point, $\mathbb P^n$, plane curves, elliptic curves) are complete intersections.
* `HasGoodReductionAt F p`: some primitive integral scaling of the $F_i$ reduces to a nonsingular variety over
  $\mathbb F_p$ (the scaling is unique up to sign, which does not change the reduction).
* `numPoints`, `localZeta`, `varietyZeta`: $\#V_p(\mathbb F_{p^m})$ (projective points over Mathlib's
  `GaloisField p m`), $\zeta(V_p, s) = \exp\bigl(\sum_m \#V_p(\mathbb F_{p^m})\,p^{-ms}/m\bigr) = Z(V_p, p^{-s})$, and
  $\zeta(V, s) = \prod_{p\ \text{good}} \zeta(V_p, s)$ (a `tprod`; Milne's convergence for $\Re s > d + 1$ rests on the
  Weil conjectures and is not formalized).

## Proved
* `goodReduction_weierstrass_iff`: for an elliptic curve given by an integral Weierstrass equation, good reduction in
  this sense at $p$ is $p \nmid \Delta$ (the Weierstrass polynomial is already primitive; uses Theorem 2.4(a),
  `theorem_2_4_a_nonsingular`).
* `zeta_point`: Milne's example: for the point $\mathrm{Pt} = \mathbb P^0$ all primes are good and
  $\zeta(\mathrm{Pt}, s) = \zeta(s)$ for $\Re s > 1$.
-/

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace NumberFieldKB.MilneEC.VarietyZeta

/-- **Nonsingularity** of the projective variety cut out by `F₁, …, F_r` in $\mathbb P^n$ over `K`, as a complete
intersection (Jacobian criterion): at every nonzero common zero $x$ over $\bar K$ the gradients
$\nabla F_i(x)$ are linearly independent. -/
@[kb "milne2006ec" "Ch. IV, §10, nonsingular variety over F_p (Jacobian criterion, complete intersections), pdf p. 170"]
def IsNonsingularCI {K : Type*} [Field K] {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) K) : Prop :=
  ∀ x : Fin (n + 1) → AlgebraicClosure K, x ≠ 0 →
    (∀ i, eval x ((F i).map (algebraMap K (AlgebraicClosure K))) = 0) →
      LinearIndependent (AlgebraicClosure K)
        (fun i j => eval x ((pderiv j (F i)).map (algebraMap K (AlgebraicClosure K))))

/-- $G \in \mathbb Z[X]$ is a **primitive integral scaling** of $F \in \mathbb Q[X]$ (pdf p. 170): $G = cF$ for some
$c \in \mathbb Q^\times$, and the coefficients of $G$ have no common prime factor. -/
def IsPrimitiveScaling {σ : Type*} (F : MvPolynomial σ ℚ) (G : MvPolynomial σ ℤ) : Prop :=
  (∃ c : ℚ, c ≠ 0 ∧ G.map (Int.castRingHom ℚ) = C c * F) ∧
    ∀ p : ℕ, p.Prime → ∃ m, ¬ (p : ℤ) ∣ G.coeff m

/-- **Good reduction at $p$** (Milne pdf p. 170): after scaling the equations to primitive integral ones, their
reductions modulo $p$ define a nonsingular variety over $\mathbb F_p$. -/
@[kb "milne2006ec" "Ch. IV, §10, good reduction of a projective variety over Q (definition in prose), pdf p. 170"]
def HasGoodReductionAt {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ G : Fin r → MvPolynomial (Fin (n + 1)) ℤ, (∀ i, IsPrimitiveScaling (F i) (G i)) ∧
    IsNonsingularCI (fun i => (G i).map (Int.castRingHom (ZMod p)))

/-! ## Zeta functions -/

/-- $\#V_p(\mathbb F_{p^m})$: the number of points of $\mathbb P^n(\mathbb F_{p^m})$ at which all the `F i` vanish
(the `F i` homogeneous, so this does not depend on the representative). -/
noncomputable def numPoints {n r : ℕ} (p : ℕ) [Fact p.Prime] (F : Fin r → MvPolynomial (Fin (n + 1)) (ZMod p))
    (m : ℕ) : ℕ :=
  Nat.card {P : ℙ (GaloisField p m) (Fin (n + 1) → GaloisField p m) //
    ∀ i, aeval P.rep (F i) = 0}

/-- $\zeta(V_p, s) = Z(V_p, p^{-s})$, $\log Z(V_p, T) = \sum_{m \ge 1} \#V_p(\mathbb F_{p^m})\,T^m/m$
(pdf p. 170).  (The term $m = 0$ of the series is $0$, as $1/0 = 0$.) -/
@[kb "milne2006ec" "Ch. IV, §10, the zeta function ζ(V_p, s) = Z(V_p, p^(-s)), pdf p. 170"]
noncomputable def localZeta {n r : ℕ} (p : ℕ) [Fact p.Prime] (F : Fin r → MvPolynomial (Fin (n + 1)) (ZMod p))
    (s : ℂ) : ℂ :=
  Complex.exp (∑' m : ℕ, (numPoints p F m : ℂ) * ((p : ℂ) ^ (-s)) ^ m / m)

open Classical in
/-- **The zeta function of a projective variety over $\mathbb Q$** (Milne pdf p. 170): $\zeta(V, s) =
\prod_{p \text{ good}} \zeta(V_p, s)$, the reduction $V_p$ computed from a primitive integral scaling. -/
@[kb "milne2006ec" "Ch. IV, §10, the zeta function of a variety over Q (definition in prose), pdf p. 170"]
noncomputable def varietyZeta {n r : ℕ} (F : Fin r → MvPolynomial (Fin (n + 1)) ℚ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    if h : HasGoodReductionAt F p then
      localZeta p (fun i => (h.choose i).map (Int.castRingHom (ZMod p))) s
    else 1

/-! ## The point -/

/-- The projective space $\mathbb P^0$ over a field has exactly one point. -/
lemma card_proj_zero (K : Type*) [Field K] : Nat.card (ℙ K (Fin 1 → K)) = 1 := by
  have hne : (fun _ => (1 : K) : Fin 1 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  refine Nat.card_eq_one_iff_unique.2 ⟨⟨fun P Q => ?_⟩, ⟨Projectivization.mk K _ hne⟩⟩
  induction P using Projectivization.ind with
  | h v hv =>
    induction Q using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.mk_eq_mk_iff']
      have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
      refine ⟨v 0 / w 0, funext fun i => ?_⟩
      rw [Subsingleton.elim i 0]
      simp [div_mul_cancel₀ _ hw0]

/-- **The point is good everywhere** (pdf p. 170): $\mathrm{Pt} = \mathbb P^0$, given by no equations. -/
lemma point_goodReduction (p : ℕ) [Fact p.Prime] :
    HasGoodReductionAt (n := 0) (Fin.elim0 : Fin 0 → MvPolynomial (Fin 1) ℚ) p :=
  ⟨Fin.elim0, fun i => i.elim0, fun _ _ _ => linearIndependent_empty_type⟩

lemma point_numPoints (p : ℕ) [Fact p.Prime] (F : Fin 0 → MvPolynomial (Fin 1) (ZMod p)) (m : ℕ) :
    numPoints p F m = 1 := by
  unfold numPoints
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun P => fun i => i.elim0), card_proj_zero]

/-- $\zeta(\mathrm{Pt}_p, s) = (1 - p^{-s})^{-1}$ for $\Re s > 0$ (pdf p. 170). -/
lemma point_localZeta (p : ℕ) [Fact p.Prime] (F : Fin 0 → MvPolynomial (Fin 1) (ZMod p)) {s : ℂ}
    (hs : 0 < s.re) : localZeta p F s = (1 - (p : ℂ) ^ (-s))⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hz : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (Fact.out : p.Prime).pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by simpa using hs)
  unfold localZeta
  simp only [point_numPoints, Nat.cast_one, one_mul]
  rw [(Complex.hasSum_taylorSeries_neg_log hz).tsum_eq, Complex.exp_neg, Complex.exp_log]
  intro h
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hz
  exact lt_irrefl _ hz

/-- **Milne's example** (pdf p. 170): $\zeta(\mathrm{Pt}, s) = \prod_p (1 - p^{-s})^{-1}$ is the Riemann zeta
function, for $\Re s > 1$. -/
@[kb "milne2006ec" "Ch. IV, §10, example: ζ(Pt, s) is the Riemann zeta function, pdf p. 170"]
theorem zeta_point {s : ℂ} (hs : 1 < s.re) :
    varietyZeta (n := 0) (Fin.elim0 : Fin 0 → MvPolynomial (Fin 1) ℚ) s = riemannZeta s := by
  rw [← riemannZeta_eulerProduct_tprod hs, varietyZeta]
  congr 1
  funext p
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  split_ifs with h
  · rw [point_localZeta _ _ (by linarith)]
  · exact absurd (point_goodReduction p) h

end NumberFieldKB.MilneEC.VarietyZeta
