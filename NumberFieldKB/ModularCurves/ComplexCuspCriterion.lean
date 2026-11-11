import NumberFieldKB.ModularCurves.ComplexCanonical
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int

/-!
# $h \in L(W)$ at the cusps

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, Proposition 3.3 and Corollary 3.4 (pdf p. 199), at the cusps.
At the place $P'$ of $\sigma_c$ = `cuspEmbC N c` (Laurent series in $q$, $j \mapsto J(q^N)$), with scaling factor
$s$ and $s\,e(P') = N$: for a Laurent series $D$ with a pole of order $N$ (the expansion of $j'$, up to a constant),
$\operatorname{ord}_q(\sigma_c(h) D) = s \operatorname{ord}_{P'} h - N \ge 1$ iff $\operatorname{ord}_{P'} h \ge e + 1 =
-W_{P'}$ (`lVal_mul_le_iff`). Every place over $\infty$ is such a $P'$, so (`forall_infty_iff`)
$\operatorname{ord}_{P'} h \ge -W_{P'}$ at all cusps iff $\operatorname{ord}_q(\sigma_c(h) D) \ge 1$ for every coset $c$.
-/

open Polynomial TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

variable (N : ℕ) [NeZero N]

/-- The place of $\mathbb C(X_0(N))$ of $\sigma_c$ at the cusp. -/
def placeCusp (c : Cosets N) : Place ℂ (X0C N) :=
  placeOf (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)

theorem restrict_placeCusp (c : Cosets N) : (placeCusp N c).restrict ℂ (RatFunc ℂ) = Place.infty ℂ :=
  restrict_placeOf _ _ _ _

variable {D : CuspField N} (hD : lVal N D = WithZero.exp (N : ℤ))

include hD in
/-- **The local criterion at a cusp.** -/
theorem lVal_mul_le_iff (c : Cosets N) {h : X0C N} (hh : h ≠ 0) :
    lVal N (cuspEmbC N c h * D) ≤ WithZero.exp (-1 : ℤ) ↔
      (Place.ramificationIdx (RatFunc ℂ) (placeCusp N c) : ℤ) + 1 ≤ (placeCusp N c).ord h := by
  have hv := valuation_apply_eq_exp (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c)
    (one_le_N N) hh
  have hs := scale_mul_ramificationIdx (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c)
    (one_le_N N)
  have hpos := scale_pos (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)
  rw [map_mul, hv, hD, ← WithZero.exp_add, WithZero.exp_le_exp]
  change _ ↔ (Place.ramificationIdx (RatFunc ℂ) (placeOf _ _ _ _) : ℤ) + 1 ≤ (placeOf _ _ _ _).ord h
  set s := scale (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)
  set e : ℤ := (Place.ramificationIdx (RatFunc ℂ)
    (placeOf (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)) : ℤ)
  set v := (placeOf (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N c) (one_le_N N)).ord h
  constructor
  · intro H
    by_contra hlt
    push_neg at hlt
    have : s * (v - e) ≤ 0 := by nlinarith
    nlinarith
  · intro H
    nlinarith

/-- Every place over $\infty$ is the place of some $\sigma_c$. -/
theorem exists_placeCusp (P' : Place ℂ (X0C N)) (hP : P'.restrict ℂ (RatFunc ℂ) = Place.infty ℂ) :
    ∃ c, placeCusp N c = P' :=
  exists_placeOf_eq (isFunctionField_X0C N) (cuspValC_algebraMap N) (cuspEmbC N) (cuspEmbC_injective N)
    (card_cosets_eq_finrankC N) (one_le_N N) P' hP

include hD in
/-- **The cusp part of $L(W)$**: for $h \ne 0$, $\operatorname{ord}_{P'} h \ge -W_{P'}$ at every place over $\infty$ iff
$\operatorname{ord}_q(\sigma_c(h) D) \ge 1$ for every coset $c$. -/
theorem forall_infty_iff {h : X0C N} (hh : h ≠ 0) :
    (∀ P' : Place ℂ (X0C N), P'.restrict ℂ (RatFunc ℂ) = Place.infty ℂ → -(canonicalW N).coeff P' ≤ P'.ord h) ↔
    ∀ c : Cosets N, lVal N (cuspEmbC N c h * D) ≤ WithZero.exp (-1 : ℤ) := by
  constructor
  · intro H c
    rw [lVal_mul_le_iff N hD c hh]
    have := H (placeCusp N c) (restrict_placeCusp N c)
    rw [coeff_canonicalW_of_infty N _ (restrict_placeCusp N c)] at this
    linarith
  · intro H P' hP
    obtain ⟨c, rfl⟩ := exists_placeCusp N P' hP
    rw [coeff_canonicalW_of_infty N _ hP]
    have := (lVal_mul_le_iff N hD c hh).1 (H c)
    linarith

end NumberFieldKB.ModularCurves
