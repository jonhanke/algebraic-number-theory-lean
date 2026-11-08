import NumberFieldKB.ModularCurves.RiemannHurwitz

/-!
# The genus formula for $X_0(N)$ from the fibres of $j$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196), and Shimura, *Introduction to the Arithmetic
Theory of Automorphic Functions*, Proposition 1.40: with $\mu = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$,
$\nu_2, \nu_3$ the numbers of elliptic points of order $2$, $3$ and $\nu_\infty$ the number of cusps,
$$g = 1 + \frac{\mu}{12} - \frac{\nu_2}{4} - \frac{\nu_3}{3} - \frac{\nu_\infty}{2}.$$

Here the formula is derived from Riemann–Hurwitz for $j$ (`riemannHurwitz_X0_fibres`) and the four fibre counts
$r(P) = \sum_{P' \mid P} f(P')$ (`geomCount`; $r(P) \deg P$ is the number of geometric points of $X_0(N)$ over $P$):

* $j$ is unramified over every place of $\mathbb Q(j)$ other than $j = 0$, $j = 1728$, $j = \infty$;
* $r(\infty) = \nu_\infty$ (the cusps);
* $3\,r(0) = \mu + 2\nu_3$ (over $j = 0$: $\nu_3$ unramified points, the others with $e = 3$);
* $2\,r(1728) = \mu + \nu_2$ (over $j = 1728$: $\nu_2$ unramified points, the others with $e = 2$).

`genus_formula_of_fibres` is the arithmetic: $12 g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$.
-/

open TauCeti Polynomial

noncomputable section

namespace NumberFieldKB.ModularCurves

variable (N : ℕ) [NeZero N]

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRat' : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The place $j = 0$ of $\mathbb Q(j)$. -/
def placeJ0 : Place ℚ (RatFunc ℚ) := Place.adicOfIrreducible (k := ℚ) irreducible_X

theorem irreducible_X_sub_1728 : Irreducible (X - C (1728 : ℚ)) := irreducible_X_sub_C _

/-- The place $j = 1728$ of $\mathbb Q(j)$. -/
def placeJ1728 : Place ℚ (RatFunc ℚ) := Place.adicOfIrreducible (k := ℚ) irreducible_X_sub_1728

theorem placeJ0_ne_placeJ1728 : placeJ0 ≠ placeJ1728 := by
  rw [placeJ0, placeJ1728, Ne, Place.adicOfIrreducible_eq_adicOfIrreducible_iff]
  rintro ⟨u, hu⟩
  have hc := congrArg (Polynomial.eval 0) hu
  norm_num at hc

theorem placeJ0_ne_infty : placeJ0 ≠ Place.infty ℚ := Place.adicOfIrreducible_ne_infty _

theorem placeJ1728_ne_infty : placeJ1728 ≠ Place.infty ℚ := Place.adicOfIrreducible_ne_infty _

theorem degree_placeJ0 : placeJ0.degree = 1 := by
  rw [placeJ0, Place.degree_adicOfIrreducible, natDegree_X]

theorem degree_placeJ1728 : placeJ1728.degree = 1 := by
  rw [placeJ1728, Place.degree_adicOfIrreducible, natDegree_X_sub_C]

/-- The geometric count of a fibre of $j$: $r(P) = \sum_{P' \mid P} f(P')$. -/
def geomCount (P : Place ℚ (RatFunc ℚ)) : ℕ :=
  ∑ P' ∈ fibre (F' := X0 N) P, Place.relativeDegree ℚ (RatFunc ℚ) P'

open scoped Classical in
/-- **The genus formula from the fibres of $j$** (Milne, Ch. V, §2, pdf p. 196; Shimura, Proposition 1.40):
if $j$ is unramified away from $0, 1728, \infty$, $r(\infty) = \nu_\infty$, $3 r(0) = \mu + 2\nu_3$ and
$2 r(1728) = \mu + \nu_2$, then $12 g = 12 + \mu - 3\nu_2 - 4\nu_3 - 6\nu_\infty$. -/
@[kb "milne2006ec" "Ch. V, §2, the genus formula for X_0(N), pdf p. 196"]
theorem genus_formula_of_fibres (ν₂ ν₃ νinf : ℕ)
    (hunr : ∀ P' : Place ℚ (X0 N), 1 < Place.ramificationIdx (RatFunc ℚ) P' →
      P'.restrict ℚ (RatFunc ℚ) ∈ ({placeJ0, placeJ1728, Place.infty ℚ} : Finset (Place ℚ (RatFunc ℚ))))
    (hinf : geomCount N (Place.infty ℚ) = νinf)
    (h0 : 3 * geomCount N placeJ0 = (CongruenceSubgroup.Gamma0 N).index + 2 * ν₃)
    (h1728 : 2 * geomCount N placeJ1728 = (CongruenceSubgroup.Gamma0 N).index + ν₂) :
    12 * MilneEC.genus ℚ (X0 N) = 12 + (CongruenceSubgroup.Gamma0 N).index - 3 * ν₂ - 4 * ν₃ - 6 * νinf := by
  have h := riemannHurwitz_X0_fibres N _ hunr
  rw [Finset.sum_insert (by simp [placeJ0_ne_placeJ1728, placeJ0_ne_infty]),
    Finset.sum_insert (by simp [placeJ1728_ne_infty]), Finset.sum_singleton,
    degree_placeJ0, degree_placeJ1728, Place.degree_infty] at h
  have hc : ∀ P, ∑ P' ∈ fibre (F' := X0 N) P, (Place.relativeDegree ℚ (RatFunc ℚ) P' : ℤ) = geomCount N P :=
    fun P => by rw [geomCount, Nat.cast_sum]
  simp only [hc] at h
  rw [genus_X0_eq]
  have h0' : (3 : ℤ) * geomCount N placeJ0 = (CongruenceSubgroup.Gamma0 N).index + 2 * ν₃ := by exact_mod_cast h0
  have h1728' : (2 : ℤ) * geomCount N placeJ1728 = (CongruenceSubgroup.Gamma0 N).index + ν₂ := by
    exact_mod_cast h1728
  rw [hinf] at h
  push_cast at h
  linear_combination 6 * h - 2 * h0' - 3 * h1728'

end NumberFieldKB.ModularCurves
