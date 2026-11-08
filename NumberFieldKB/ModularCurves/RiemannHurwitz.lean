import NumberFieldKB.ModularCurves.GenusX0
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.Different.Hurwitz

/-!
# The Riemann–Hurwitz formula for $j : X_0(N) \to X_0(1)$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (the genus of $X_0(N)$, pdf p. 196), and
H. Stichtenoth, *Algebraic Function Fields and Codes*, Theorem 3.4.13 and Corollary 3.5.6.

Over a constant field of characteristic $0$ every place is tame, so the Hurwitz genus formula of Tau Ceti
(`TauCeti.two_mul_genus_sub_two_eq_iff_forall_isTame`, ported in `NumberFieldKB/TauCetiPort/`) reads, for a finite
extension $F'$ of the rational function field $k(t)$ with exact constant field $k$:
$$2g(F') - 2 = -2\,[F' : k(t)] + \sum_{P'} (e(P') - 1) \deg P'$$
(`two_mul_genus_sub_two_eq_of_charZero`). Grouping the places $P'$ by the place $P$ of $k(t)$ below them and using the
fundamental identity $\sum_{P' \mid P} e(P') f(P') = [F' : F]$, the ramification term is
$$\sum_P \deg P \Bigl([F' : F] - \sum_{P' \mid P} f(P')\Bigr)$$
(`degree_tameDifferent_eq_sum_fibres`); $\sum_{P' \mid P} f(P') \deg P$ is the number of geometric points over $P$.

For $X_0(N)$, with $F = \mathbb Q(j)$ and $[F' : F] = \mu = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$:
`riemannHurwitz_X0`.
-/

open TauCeti

noncomputable section

namespace NumberFieldKB.ModularCurves

section General

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [Algebra F F']
  [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- The fibre of a place $P$ of $F$: the places of $F'$ over $P$, a finite set. -/
def fibre (P : Place k F) : Finset (Place k F') :=
  (Place.finite_setOf_restrict_eq (k' := k) (F' := F') k F P).toFinset

theorem mem_fibre {P : Place k F} {P' : Place k F'} : P' ∈ fibre (F' := F') P ↔ P'.restrict k F = P := by
  simp [fibre]

/-- **The ramification term of Riemann–Hurwitz, fibre by fibre.** For a finite set `T` of places of `F` containing
the places below all ramified places of `F'`,
$\deg \sum_{P'} (e(P') - 1) P' = \sum_{P \in T} \deg P\,([F' : F] - \sum_{P' \mid P} f(P'))$. -/
theorem degree_tameDifferent_eq_sum_fibres (hF : IsFunctionField k F) (T : Finset (Place k F))
    (hT : ∀ P' : Place k F', 1 < Place.ramificationIdx F P' → P'.restrict k F ∈ T) :
    Divisor.degree (Divisor.tameDifferent k F' hF) =
      ∑ P ∈ T, (P.degree : ℤ) * ((Module.finrank F F' : ℤ) -
        ∑ P' ∈ fibre (F' := F') P, (Place.relativeDegree k F P' : ℤ)) := by
  classical
  set D := Divisor.tameDifferent k F' hF
  have hsupp : D.support ⊆ T.biUnion fun P => fibre (F' := F') P := by
    intro P' hP'
    rw [Finsupp.mem_support_iff] at hP'
    have hD : D P' = (Place.ramificationIdx F P' : ℤ) - 1 := Divisor.coeff_tameDifferent k F' hF P'
    have he : 1 < Place.ramificationIdx F P' := by
      have := Place.ramificationIdx_pos F P'
      omega
    exact Finset.mem_biUnion.2 ⟨_, hT P' he, mem_fibre.2 rfl⟩
  rw [Divisor.degree_eq_sum_support, Finset.sum_subset hsupp (fun P' _ hP' => by
      rw [Finsupp.notMem_support_iff.1 hP', zero_mul]),
    Finset.sum_biUnion (fun P _ Q _ hPQ => Finset.disjoint_left.2 fun P' h1 h2 =>
      hPQ ((mem_fibre.1 h1).symm.trans (mem_fibre.1 h2)))]
  refine Finset.sum_congr rfl fun P _ => ?_
  have hfund := Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField
    (k' := k) (F' := F') k F hF P (s := fibre P) fun _ => mem_fibre
  have hfund' : ∑ P' ∈ fibre (F' := F') P,
      ((Place.ramificationIdx F P' : ℤ) * Place.relativeDegree k F P') = Module.finrank F F' := by
    exact_mod_cast hfund
  rw [← hfund', mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun P' hP' => ?_
  have hD : D P' = (Place.ramificationIdx F P' : ℤ) - 1 := Divisor.coeff_tameDifferent k F' hF P'
  rw [hD, Place.degree_eq_degree_restrict_mul_relativeDegree k F P', mem_fibre.1 hP']
  push_cast
  ring

end General

section RatFunc

variable {k F' : Type*} [Field k] [CharZero k] [Field F'] [Algebra k F'] [Algebra (RatFunc k) F']
  [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F']

/-- **Riemann–Hurwitz over a constant field of characteristic 0** (Stichtenoth, Corollary 3.5.6 (b); Milne uses it
in Ch. V, §2 for $j : X_0(N) \to \mathbb P^1$): for a finite extension $F'$ of $k(t)$ with exact constant field $k$,
$2g(F') - 2 = -2\,[F' : k(t)] + \sum_{P'} (e(P') - 1) \deg P'$. -/
theorem two_mul_genus_sub_two_eq_of_charZero (hex : IsIntegrallyClosedIn k F') :
    2 * (TauCeti.genus k F' : ℤ) - 2 = -2 * Module.finrank (RatFunc k) F' +
      Divisor.degree (Divisor.tameDifferent k F' (IsFunctionField.ratFunc k)) := by
  have hF' : IsFunctionField k F' := isFunctionField_iff_functionField.mpr inferInstance
  rw [(two_mul_genus_sub_two_eq_iff_forall_isTame (IsFunctionField.ratFunc k) hF' inferInstance hex).2
    fun P' => Place.isTame_of_charZero k (RatFunc k) P', geometricDegree_eq_finrank, genus_ratFunc]
  ring

/-- **Riemann–Hurwitz over a constant field of characteristic 0, fibre by fibre**: for a finite set `T` of places of
$k(t)$ containing the places below every ramified place,
$2g(F') - 2 = -2n + \sum_{P \in T} \deg P\,(n - \sum_{P' \mid P} f(P'))$, $n = [F' : k(t)]$. -/
theorem two_mul_genus_sub_two_eq_sum_fibres (hex : IsIntegrallyClosedIn k F') (T : Finset (Place k (RatFunc k)))
    (hT : ∀ P' : Place k F', 1 < Place.ramificationIdx (RatFunc k) P' → P'.restrict k (RatFunc k) ∈ T) :
    2 * (TauCeti.genus k F' : ℤ) - 2 = -2 * Module.finrank (RatFunc k) F' +
      ∑ P ∈ T, (P.degree : ℤ) * ((Module.finrank (RatFunc k) F' : ℤ) -
        ∑ P' ∈ fibre (F' := F') P, (Place.relativeDegree k (RatFunc k) P' : ℤ)) := by
  rw [two_mul_genus_sub_two_eq_of_charZero hex,
    degree_tameDifferent_eq_sum_fibres (IsFunctionField.ratFunc k) T hT]

end RatFunc

section X0

variable (N : ℕ) [NeZero N]

/-- The tower $\mathbb Q \subseteq \mathbb Q(j) \subseteq \mathbb Q(X_0(N))$, for the $\mathbb Q$-algebra structure of
$\mathbb Q(t)$ that Tau Ceti's statements over a general constant field specialize to. -/
instance isScalarTower_ratFunc_X0 :
    @IsScalarTower ℚ (RatFunc ℚ) (X0 N) (RatFunc.instAlgebraOfPolynomial ℚ ℚ).toSMul _ _ :=
  @IsScalarTower.of_algebraMap_eq' ℚ (RatFunc ℚ) (X0 N) _ _ _ (RatFunc.instAlgebraOfPolynomial ℚ ℚ) _ _
    (RingHom.ext_rat _ _)

/-- In this section $\mathbb Q(t)$ is a $\mathbb Q$-algebra through $\mathbb Q[t]$, the structure the general
statements (over any constant field $k$) specialize to; it equals `DivisionRing.toRatAlgebra` (`Algebra ℚ` is a
subsingleton), but not by instance unfolding. -/
local instance (priority := high) ratFuncAlgebraRat : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

/-- The trivial tower $\mathbb Q \subseteq \mathbb Q \subseteq \mathbb Q(X_0(N))$ (the constant field of $X_0(N)$ is
$\mathbb Q$), for the $\mathbb Q$-algebra structure `DivisionRing.toRatAlgebra` of $\mathbb Q(X_0(N))$. -/
instance isScalarTower_rat_X0 : @IsScalarTower ℚ ℚ (X0 N) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := ℚ) (A := X0 N) (RingHom.ext_rat _ _)

/-- **Riemann–Hurwitz for $j : X_0(N) \to X_0(1)$** (Milne, Ch. V, §2, pdf p. 196): with
$\mu = (\mathrm{SL}_2(\mathbb Z) : \Gamma_0(N))$ the degree of $j$,
$2g - 2 = -2\mu + \sum_{P'} (e(P') - 1) \deg P'$, the sum over the places $P'$ of $\mathbb Q(X_0(N))$. -/
@[kb "milne2006ec" "Ch. V, §2, the genus of X_0(N) (Riemann–Hurwitz for j), pdf p. 196"]
theorem riemannHurwitz_X0 :
    2 * (TauCeti.genus ℚ (X0 N) : ℤ) - 2 = -2 * (CongruenceSubgroup.Gamma0 N).index +
      Divisor.degree (Divisor.tameDifferent ℚ (X0 N) (IsFunctionField.ratFunc ℚ)) := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  rw [two_mul_genus_sub_two_eq_of_charZero (isIntegrallyClosedIn_X0 N), finrank_X0]

/-- **Riemann–Hurwitz for $j$, fibre by fibre**: for a finite set `T` of places of $\mathbb Q(j)$ containing the
places below every ramified place of $X_0(N)$,
$2g - 2 = -2\mu + \sum_{P \in T} \deg P\,(\mu - \sum_{P' \mid P} f(P'))$. -/
theorem riemannHurwitz_X0_fibres (T : Finset (Place ℚ (RatFunc ℚ)))
    (hT : ∀ P' : Place ℚ (X0 N), 1 < Place.ramificationIdx (RatFunc ℚ) P' → P'.restrict ℚ (RatFunc ℚ) ∈ T) :
    2 * (TauCeti.genus ℚ (X0 N) : ℤ) - 2 = -2 * (CongruenceSubgroup.Gamma0 N).index +
      ∑ P ∈ T, (P.degree : ℤ) * (((CongruenceSubgroup.Gamma0 N).index : ℤ) -
        ∑ P' ∈ fibre (F' := X0 N) P, (Place.relativeDegree ℚ (RatFunc ℚ) P' : ℤ)) := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  rw [two_mul_genus_sub_two_eq_sum_fibres (isIntegrallyClosedIn_X0 N) T hT, finrank_X0]

end X0

end NumberFieldKB.ModularCurves
