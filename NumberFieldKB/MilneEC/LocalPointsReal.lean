import NumberFieldKB.MilneEC.LocalPointsQ
import NumberFieldKB.MilneEC.RealApprox

/-!
# Local injectivity at the real place, and the comparison with only the finite places assumed

* `kummerApprox_real_two`: $E(\mathbb R) = 2E(\mathbb R) + \{\text{algebraic points}\}$ for $E/\mathbb Q$:
  given $R$, choose an algebraic $T$ with $x(R - T)$ large (`exists_isAlgPoint_sub_large`), and then $R - T$ is a
  double (`exists_two_nsmul_eq_of_lt`).
* `kummerApprox_completion_two`: the same at the completion of $\mathbb Q$ at its infinite place, transported along
  $\mathbb Q_\infty \cong \mathbb R$.
* `localPointsInjectiveAt_real`: `LocalPointsInjectiveAt` at the real place, unconditionally.
* `localPointsInjective_of_finiteKummerPrime`: `LocalPointsInjective` from the finite-place statement
  `FiniteKummerPrime` alone; and the three Conjecture 10.5 comparisons of `ShaComparison.lean` with
  `LocalPointsInjective` replaced by `FiniteKummerPrime`.
-/

open WeierstrassCurve WeierstrassCurve.Affine NumberField
open scoped Classical

namespace NumberFieldKB.MilneEC

section Real

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] charZero_completion_infinitePlace_rat

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **Kummer approximation over $\mathbb R$ for $n = 2$**: every point of $E(\mathbb R)$ is $2S + T$ with $T$
algebraic. -/
theorem kummerApprox_real_two : KummerApprox E ℝ 2 := by
  rw [kummerApprox_iff]
  intro R
  obtain ⟨N, hN⟩ := exists_two_nsmul_eq_of_lt (E.baseChange ℝ)
  obtain ⟨T, hT, hRT⟩ := RealApprox.exists_isAlgPoint_sub_large E R N
  rcases hRT with h0 | ⟨x, y, h, hxy, hx⟩
  · exact ⟨0, T, hT, by rw [smul_zero, zero_add]; exact sub_eq_zero.1 h0⟩
  · obtain ⟨Q, hQ⟩ := hN x y h hx
    refine ⟨Q, T, hT, ?_⟩
    rw [hQ, ← hxy, sub_add_cancel]

/-- The completion of $\mathbb Q$ at its infinite place is $\mathbb R$, as $\mathbb Q$-algebras. -/
noncomputable def completionAlgEquivReal (w : InfinitePlace ℚ) : w.Completion ≃ₐ[ℚ] ℝ :=
  AlgEquiv.ofRingEquiv (f := InfinitePlace.Completion.ringEquivRealOfIsReal
    (Subsingleton.elim Rat.infinitePlace w ▸ Rat.isReal_infinitePlace)) fun q => by
      rw [eq_ratCast (algebraMap ℚ w.Completion), map_ratCast, eq_ratCast]

theorem kummerApprox_completion_two (w : InfinitePlace ℚ) : KummerApprox E w.Completion 2 :=
  kummerApprox_of_algEquiv E (completionAlgEquivReal w) 2 (kummerApprox_real_two E)

/-- **Local injectivity at the real place of $\mathbb Q$**, unconditionally. -/
theorem localPointsInjectiveAt_real (w : InfinitePlace ℚ) : LocalPointsInjectiveAt E w.Completion :=
  localPointsInjectiveAt_real_of_kummerApprox_two E w (kummerApprox_completion_two E w)

end Real

/-- **`LocalPointsInjective` from the finite places alone.** -/
theorem localPointsInjective_of_finiteKummerPrime (hF : FiniteKummerPrime) : LocalPointsInjective :=
  localPointsInjective_of_kummer (fun E _ w => kummerApprox_completion_two E w) hF

section BSD

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **Conjecture 10.5 (corrected normalization) is Formal Conjectures' `StrongBSD` over $\mathbb Q$** for a minimal
equation; only the finite-place Kummer statement `FiniteKummerPrime` is assumed. -/
theorem conjecture10_5Corrected_iff_strongBSD_of_finiteKummerPrime (hF : FiniteKummerPrime)
    (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    Conjecture10_5Corrected E ↔ FormalConjectures.StrongBSD E.toAffine :=
  conjecture10_5Corrected_iff_strongBSD_of_localPointsInjective E
    (localPointsInjective_of_finiteKummerPrime hF) hmin

/-- In rank $0$, Conjecture 10.5 as printed is `StrongBSD`, assuming only `FiniteKummerPrime`. -/
theorem conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_finiteKummerPrime (hF : FiniteKummerPrime)
    (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    rank E = 0 → (Conjecture10_5 E ↔ FormalConjectures.StrongBSD E.toAffine) :=
  conjecture10_5_iff_strongBSD_of_rank_eq_zero_of_localPointsInjective E
    (localPointsInjective_of_finiteKummerPrime hF) hmin

/-- In positive rank, `StrongBSD` refutes Conjecture 10.5 as printed, assuming only `FiniteKummerPrime`. -/
theorem not_conjecture10_5_of_strongBSD_of_finiteKummerPrime (hF : FiniteKummerPrime)
    (hmin : IsMinimalOverRat E) :
    haveI := mordell_weil_rat E
    0 < rank E → FormalConjectures.StrongBSD E.toAffine → ¬ Conjecture10_5 E :=
  not_conjecture10_5_of_strongBSD_of_localPointsInjective E (localPointsInjective_of_finiteKummerPrime hF) hmin

end BSD

end NumberFieldKB.MilneEC
