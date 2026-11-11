import NumberFieldKB.ModularCurves.ComplexCusp
import NumberFieldKB.ModularCurves.RiemannHurwitz
import Mathlib.RingTheory.Henselian
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int

/-!
# The genus of $\mathbb C(X_0(N))$ equals the genus of $\mathbb Q(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2–3 (pdf pp. 196–199). Corollary 3.4 uses the genus of the
compact Riemann surface $X_0(N)$, whose function field is $\mathbb C(X_0(N)) = \mathbb C(j, j_N)$, while the genus
formula was proved for $\mathbb Q(X_0(N))$. Tau Ceti's genus invariance under constant field extension is
for algebraic extensions only, and $\mathbb C/\mathbb Q$ is transcendental; here the genus of $\mathbb C(X_0(N))$ is
computed directly, by Riemann–Hurwitz for $j$ over $\mathbb C$ with the same fibre counts:
$12\,g(\mathbb C(X_0(N))) = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$ (`genus_formula_X0C`), hence
$g(\mathbb C(X_0(N))) = g(\mathbb Q(X_0(N)))$ (`genus_X0C_eq`).
-/

open TauCeti Polynomial

noncomputable section

namespace NumberFieldKB.ModularCurves

variable (N : ℕ) [NeZero N]

theorem placeJ0C_ne_placeJ1728C : placeJ0C ≠ placeJ1728C := by
  rw [placeJ0C, placeJ1728C, Ne, Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
  rintro ⟨u, hu⟩
  have hc := congrArg (Polynomial.eval 0) hu
  norm_num at hc

theorem placeJ0C_ne_infty : placeJ0C ≠ Place.infty ℂ := Place.adicOfIrreducible_ne_infty _

theorem placeJ1728C_ne_infty : placeJ1728C ≠ Place.infty ℂ := Place.adicOfIrreducible_ne_infty _

theorem degree_placeJ0C : placeJ0C.degree = 1 := by
  rw [placeJ0C, Place.degree_adicOfIrreducible, natDegree_X]

theorem degree_placeJ1728C : placeJ1728C.degree = 1 := by
  rw [placeJ1728C, Place.degree_adicOfIrreducible, natDegree_X_sub_C]

open scoped Classical in
/-- **The genus formula for $\mathbb C(X_0(N))$**: $12 g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$. -/
@[kb "milne2006ec" "Ch. V, §2, the genus formula for X_0(N) over C, pdf p. 196"]
theorem genus_formula_X0C :
    12 * (TauCeti.genus ℂ (X0C N) : ℤ) = 12 + (CongruenceSubgroup.Gamma0 N).index - 3 * nu2 N - 4 * nu3 N -
      6 * ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d)) := by
  have h := two_mul_genus_sub_two_eq_sum_fibres (isIntegrallyClosedIn_X0C N)
    ({placeJ0C, placeJ1728C, Place.infty ℂ} : Finset (Place ℂ (RatFunc ℂ)))
    (fun P' hP' => restrictC_mem_of_ramified N P' hP')
  rw [Finset.sum_insert (by simp [placeJ0C_ne_placeJ1728C, placeJ0C_ne_infty]),
    Finset.sum_insert (by simp [placeJ1728C_ne_infty]), Finset.sum_singleton,
    degree_placeJ0C, degree_placeJ1728C, Place.degree_infty, finrank_X0C] at h
  have hc : ∀ P, ∑ P' ∈ fibre (F' := X0C N) P, (Place.relativeDegree ℂ (RatFunc ℂ) P' : ℤ) = geomCountC N P :=
    fun P => by rw [geomCountC, Nat.cast_sum]
  simp only [hc] at h
  have h0 : (3 : ℤ) * geomCountC N placeJ0C = (CongruenceSubgroup.Gamma0 N).index + 2 * nu3 N := by
    exact_mod_cast three_mul_geomCountC_placeJ0C N
  have h1728 : (2 : ℤ) * geomCountC N placeJ1728C = (CongruenceSubgroup.Gamma0 N).index + nu2 N := by
    exact_mod_cast two_mul_geomCountC_placeJ1728C N
  rw [geomCountC_infty_eq] at h
  push_cast at h ⊢
  linear_combination 6 * h - 2 * h0 - 3 * h1728

/-- **$g(\mathbb C(X_0(N))) = g(\mathbb Q(X_0(N)))$**: the genus of $X_0(N)$ does not change under the constant field
extension $\mathbb Q \to \mathbb C$. -/
@[kb "milne2006ec" "Ch. V, §3, the genus of X_0(N) as a curve over C and over Q, pdf p. 199"]
theorem genus_X0C_eq : TauCeti.genus ℂ (X0C N) = TauCeti.genus ℚ (X0 N) := by
  have hC := genus_formula_X0C N
  have hQ := genus_formula_X0 N
  rw [genus_X0_eq] at hQ
  have : (TauCeti.genus ℂ (X0C N) : ℤ) = TauCeti.genus ℚ (X0 N) := by linarith
  exact_mod_cast this

end NumberFieldKB.ModularCurves
