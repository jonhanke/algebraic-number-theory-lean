import NumberFieldKB.ModularCurves.ComplexGenus
import NumberFieldKB.TauCetiPort.FieldTheory.FunctionField.Differential.Comparison

/-!
# The divisor of $dj$ on $\mathbb C(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §3 (Corollary 3.4, pdf p. 199). The holomorphic
differentials of $X_0(N)$ are $h\,dj$ with $h \in L(W)$, $W = \operatorname{div}(dj) = -2(j)_\infty +
\mathrm{Diff}(\mathbb C(X_0(N))/\mathbb C(j))$ (Tau Ceti, Stichtenoth Remark 4.3.7(c), ported:
`TauCeti.weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential`). Here:

* `canonicalW N`, and `dim_canonicalW`: $\ell(W) = g(\mathbb C(X_0(N))) = g(\mathbb Q(X_0(N)))$;
* its coefficients: $W_{P'} = e(P') - 1$ at the places over a finite place of $\mathbb C(j)$
  (`coeff_canonicalW_of_ne_infty`) and $W_{P'} = -e(P') - 1$ at the cusps (`coeff_canonicalW_of_infty`).
-/

open TauCeti Polynomial

noncomputable section

namespace NumberFieldKB.ModularCurves

variable (N : ℕ) [NeZero N]

/-- $j$ as a unit of $\mathbb C(X_0(N))$. -/
def jUnitC : (X0C N)ˣ :=
  Units.map (algebraMap (RatFunc ℂ) (X0C N) : RatFunc ℂ →* X0C N) (Units.mk0 RatFunc.X RatFunc.X_ne_zero)

/-- **The divisor of $dj$**: $W = -2(j)_\infty + \mathrm{Diff}(\mathbb C(X_0(N))/\mathbb C(j))$. -/
def canonicalW : Divisor ℂ (X0C N) :=
  (-2 : ℤ) • Divisor.poles (isFunctionField_X0C N) (jUnitC N) +
    Divisor.different ℂ (X0C N) (IsFunctionField.ratFunc ℂ)

/-- **$W$ is the divisor of a nonzero Weil differential**, the cotrace of $dj$. -/
theorem canonicalW_eq :
    canonicalW N = weilDifferentialDivisor (isFunctionField_X0C N) (isIntegrallyClosedIn_X0C N)
        (weilDifferentialCotrace ℂ (X0C N) (IsFunctionField.ratFunc ℂ) (isFunctionField_X0C N)
          ⟨ratFuncWeilDifferential ℂ, ratFuncWeilDifferential_mem ℂ⟩).2
        (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero (isFunctionField_X0C N)) :=
  (weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential _ _).symm

/-- **$\ell(W) = g$.** -/
theorem dim_canonicalW : Divisor.dim (canonicalW N) = TauCeti.genus ℂ (X0C N) := by
  rw [canonicalW_eq]
  exact dim_weilDifferentialDivisor _ _ _ _

/-- **$\ell(W) = g(X_0(N))$**, the genus of $\mathbb Q(X_0(N))$. -/
theorem dim_canonicalW_eq_genus : Divisor.dim (canonicalW N) = TauCeti.genus ℚ (X0 N) := by
  rw [dim_canonicalW, genus_X0C_eq]

theorem coeff_different_X0C (P' : Place ℂ (X0C N)) :
    (Divisor.different ℂ (X0C N) (IsFunctionField.ratFunc ℂ)).coeff P' =
      (Place.ramificationIdx (RatFunc ℂ) P' : ℤ) - 1 := by
  have h := (Divisor.coeff_different_add_one_eq_ramificationIdx_iff (IsFunctionField.ratFunc ℂ) P').2
    (Place.isTame_of_charZero ℂ (RatFunc ℂ) P')
  omega

theorem ord_jUnitC (P' : Place ℂ (X0C N)) :
    P'.ord ((jUnitC N : X0C N)) =
      Place.ramificationIdx (RatFunc ℂ) P' * (P'.restrict ℂ (RatFunc ℂ)).ord RatFunc.X := by
  exact Place.ord_algebraMap_restrict ℂ (RatFunc ℂ) P' RatFunc.X

/-- **$W_{P'} = e(P') - 1$ over a finite place of $\mathbb C(j)$.** -/
theorem coeff_canonicalW_of_ne_infty (P' : Place ℂ (X0C N)) (hP : P'.restrict ℂ (RatFunc ℂ) ≠ Place.infty ℂ) :
    (canonicalW N).coeff P' = (Place.ramificationIdx (RatFunc ℂ) P' : ℤ) - 1 := by
  obtain ⟨q, hq, hP'⟩ := (Place.eq_infty_or_exists_eq_adicOfIrreducible (P'.restrict ℂ (RatFunc ℂ))).resolve_left hP
  have hX : 0 ≤ (P'.restrict ℂ (RatFunc ℂ)).ord RatFunc.X := by
    rw [hP', Place.ord_adicOfIrreducible_X]
    split_ifs <;> norm_num
  have hj : 0 ≤ P'.ord ((jUnitC N : X0C N)) := by
    rw [ord_jUnitC]
    exact mul_nonneg (by positivity) hX
  rw [canonicalW, AlgebraicGeometry.WeilDivisor.coeff_add, AlgebraicGeometry.WeilDivisor.coeff_zsmul, Divisor.coeff_poles, coeff_different_X0C]
  have : -P'.ord ((jUnitC N : X0C N)) ⊔ 0 = 0 := by omega
  rw [this]
  ring

/-- **$W_{P'} = -e(P') - 1$ at a cusp.** -/
theorem coeff_canonicalW_of_infty (P' : Place ℂ (X0C N)) (hP : P'.restrict ℂ (RatFunc ℂ) = Place.infty ℂ) :
    (canonicalW N).coeff P' = -(Place.ramificationIdx (RatFunc ℂ) P' : ℤ) - 1 := by
  have hX : (P'.restrict ℂ (RatFunc ℂ)).ord RatFunc.X = -1 := by
    rw [hP, Place.ord_infty, RatFunc.intDegree_X]
  rw [canonicalW, AlgebraicGeometry.WeilDivisor.coeff_add, AlgebraicGeometry.WeilDivisor.coeff_zsmul, Divisor.coeff_poles, coeff_different_X0C,
    ord_jUnitC, hX]
  have he : (0 : ℤ) ≤ Place.ramificationIdx (RatFunc ℂ) P' := by positivity
  have : -((Place.ramificationIdx (RatFunc ℂ) P' : ℤ) * -1) ⊔ 0 = Place.ramificationIdx (RatFunc ℂ) P' := by
    rw [mul_neg_one, neg_neg]
    exact max_eq_left he
  rw [this]
  ring

end NumberFieldKB.ModularCurves
