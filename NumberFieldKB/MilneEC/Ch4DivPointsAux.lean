import NumberFieldKB.MilneEC.Ch4ValuedShort
import NumberFieldKB.MilneEC.Ch4LocalBridge
import NumberFieldKB.MilneEC.Ch4Lemma21
import NumberFieldKB.TauCetiPort.NumberTheory.RamificationInertia.Unramified

/-!
# Helpers for `exists_unramified_divPoints_short`

* `torsion_finite`: the $n$-torsion of an elliptic curve over a field is finite ($n \ne 0$): the $x$-coordinate of a
  nonzero $n$-torsion point is a root of the nonzero polynomial $\Psi_n^2$, and each $x$ carries at most two points.
* `isUnramifiedOverQp_of_inertia_trivial`: a finite Galois extension $K/\mathbb Q_p$ whose inertia group (at the
  maximal ideal of $\mathcal O_K$) is trivial is unramified (Tau Ceti's
  `Ideal.isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal`, then $e = 1$).
* `Valued.key_fixed`: an automorphism of $K$ acting trivially on the residue field of the valuation ring $R$ fixes
  every $P$ with $nQ = P$, $\sigma P = P$ (reduction of $\sigma Q - Q$ is $O$ and it is $n$-torsion).
-/

namespace NumberFieldKB.MilneEC

section Unram

open IsLocalRing NumberFieldKB.MilneANT

variable (p : ℕ) [Fact p.Prime]

/-- A finite Galois extension of $\mathbb Q_p$ with trivial inertia is unramified. -/
theorem isUnramifiedOverQp_of_inertia_trivial (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (H : ∀ σ : K ≃ₐ[ℚ_[p]] K, (∀ x : integralClosure ℤ_[p] K,
      ∃ y ∈ maximalIdeal (integralClosure ℤ_[p] K), σ (x : K) = x + y) → σ = 1) :
    IsUnramifiedOverQp p K := by
  have hfin : Module.Finite ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  have hDVR := Remark753.isDVR_of_finite ℤ_[p] ℚ_[p] K
  have htf := Remark753.torsionFree_integralClosure ℤ_[p] ℚ_[p] K
  have hloc := isLocalHom_algebraMap_integralClosure ℤ_[p] K
  have hdom : IsDomain (integralClosure ℤ_[p] K) := inferInstance
  have hFR : IsFractionRing (integralClosure ℤ_[p] K) K :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[p] K
  let _ : MulSemiringAction Gal(K/ℚ_[p]) (integralClosure ℤ_[p] K) :=
    IsIntegralClosure.MulSemiringAction ℤ_[p] ℚ_[p] K (integralClosure ℤ_[p] K)
  have hG : IsGaloisGroup Gal(K/ℚ_[p]) ℤ_[p] (integralClosure ℤ_[p] K) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ_[p] K
  have hbot : (maximalIdeal (integralClosure ℤ_[p] K)).inertia Gal(K/ℚ_[p]) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply H
    intro x
    refine ⟨σ • x - x, hσ x, ?_⟩
    have := algebraMap_galRestrict_apply ℤ_[p] σ x
    simp only [Subalgebra.coe_sub]
    change σ (x : K) = _ + _
    have h2 : (((σ • x : integralClosure ℤ_[p] K)) : K) = σ (x : K) := this
    rw [h2]
    ring
  have hunr : Algebra.IsUnramifiedAt ℤ_[p] (maximalIdeal (integralClosure ℤ_[p] K)) :=
    (Ideal.isUnramifiedAt_iff_inertia_eq_bot_of_isMaximal (G := Gal(K/ℚ_[p])) (R := ℤ_[p]) _).2 hbot
  have hess : Algebra.EssFiniteType ℤ_[p] (integralClosure ℤ_[p] K) := inferInstance
  have he : ramIdxMilne ℤ_[p] K = 1 :=
    ((Ideal.isUnramifiedAt_iff_ramificationIdx_eq_one_and_isSeparable_residueField
      (R := ℤ_[p]) (maximalIdeal (integralClosure ℤ_[p] K))).1 hunr).1
  have hef := cor_7_42 ℤ_[p] ℚ_[p] K
  rw [he, one_mul] at hef
  exact isUnramifiedOverQp_of_isUnramifiedMilne p K hef

end Unram

section Finite

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped Classical

variable {k : Type*} [Field k] (W : WeierstrassCurve k)

/-- The coordinates of a point as an `Option`. -/
noncomputable def ptCoord : W.toAffine.Point → Option (k × k)
  | .zero => none
  | .some x y _ => some (x, y)

lemma ptCoord_injective : Function.Injective (ptCoord W) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) e
  · rfl
  · simp [ptCoord] at e
  · simp [ptCoord] at e
  · simp only [ptCoord, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl

lemma finite_fiber (x : k) : {y : k | W.toAffine.Equation x y}.Finite := by
  by_cases hne : ∃ y₀, W.toAffine.Equation x y₀
  · obtain ⟨y₀, h₀⟩ := hne
    refine (Set.toFinite {y₀, W.toAffine.negY x y₀}).subset ?_
    intro y hy
    rcases Affine.Y_eq_of_X_eq hy h₀ rfl with h | h
    · simp [h]
    · simp [h]
  · push Not at hne
    convert Set.finite_empty
    ext y; simp [hne y]

/-- The $n$-torsion of an elliptic curve over a field is finite for $n \ne 0$. -/
lemma torsion_finite (hΔ : W.Δ ≠ 0) {n : ℤ} (hn : n ≠ 0) :
    {Q : W.toAffine.Point | n • Q = 0}.Finite := by
  have hΨ := W.ΨSq_ne_zero_of_Δ_ne_zero hΔ hn
  have hX : {x | IsRoot (W.ΨSq n) x}.Finite := Polynomial.finite_setOfPred_isRoot hΨ
  have hT : (⋃ x ∈ {x | IsRoot (W.ΨSq n) x}, (fun y => (x, y)) '' {y | W.toAffine.Equation x y}).Finite :=
    hX.biUnion fun x _ => (finite_fiber W x).image _
  refine Set.Finite.of_finite_image (f := ptCoord W) ?_ (ptCoord_injective W).injOn
  refine ((hT.image some).union (Set.finite_singleton none)).subset ?_
  rintro _ ⟨Q, hQ, rfl⟩
  rcases Q with _ | ⟨x, y, h⟩
  · right; rfl
  · left
    refine ⟨(x, y), ?_, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    refine ⟨x, ?_, y, h.1, rfl⟩
    show IsRoot _ _
    rw [IsRoot, eval_ΨSq_eq_zero_iff_zsmul_eq_zero W h n]
    exact zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.2 hQ

end Finite

end NumberFieldKB.MilneEC

namespace NumberFieldKB.MilneEC.II.Valued

open WeierstrassCurve Polynomial IsLocalRing

attribute [local instance] Classical.propDecidable

variable {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {a b : R}

section Inertia

variable (σR : R →+* R) (σK : K →+* K)
  (hc : ∀ x, algebraMap R K (σR x) = σK (algebraMap R K x))
  (hin : ∀ x, σR x - x ∈ maximalIdeal R)

include hc hin

lemma not_isInt_map {x : K} (hx : ¬ IsInt R x) : ¬ IsInt R (σK x) := by
  obtain ⟨S, hS, hSx⟩ := exists_small hx
  rintro ⟨X', hX'⟩
  have h1 : algebraMap R K (σR S * X') = 1 := by
    rw [map_mul, hc, hX', ← map_mul, hSx, map_one]
  have h2 : σR S * X' = 1 := ι_eq (K := K) (by rw [h1, map_one])
  have hσS : σR S ∈ maximalIdeal R := by
    have := Ideal.add_mem _ (hin S) hS
    simpa using this
  exact ((mem_maximalIdeal _).1 hσS) (IsUnit.of_mul_eq_one _ h2)

lemma redPt_some_map (h : Good a b) {x y x' y' : K}
    (hxy : (curveK K a b).toAffine.Nonsingular x y)
    (hxy' : (curveK K a b).toAffine.Nonsingular x' y') (hx : x' = σK x) (hy : y' = σK y) :
    redPt h (Affine.Point.some x' y' hxy') = redPt h (Affine.Point.some x y hxy) := by
  by_cases hX : IsInt R x
  · obtain ⟨X, rfl⟩ := hX
    obtain ⟨Y, rfl⟩ := isInt_y hxy.1 ⟨X, rfl⟩
    have hx' : algebraMap R K (σR X) = x' := by rw [hc, hx]
    have hy' : algebraMap R K (σR Y) = y' := by rw [hc, hy]
    obtain ⟨A1, e1⟩ := redPt_some_of_alg h hxy rfl rfl
    obtain ⟨A2, e2⟩ := redPt_some_of_alg h hxy' hx' hy'
    rw [e1, e2]
    have rX : IsLocalRing.residue R (σR X) = IsLocalRing.residue R X := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hin X
    have rY : IsLocalRing.residue R (σR Y) = IsLocalRing.residue R Y := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hin Y
    simp only [Affine.Point.some.injEq]
    exact ⟨rX, rY⟩
  · rw [redPt_some_of_not_isInt h hxy hX,
      redPt_some_of_not_isInt h hxy' (hx ▸ not_isInt_map σR σK hc hin hX)]

/-- If `σ` is trivial modulo the maximal ideal, `nQ = P` and `σP = P`, then `σQ = Q`
(`n` a unit, good reduction). -/
theorem key_fixed (h : Good a b) {W : WeierstrassCurve K} (e : W = curveK K a b)
    (φ : W.toAffine.Point →+ W.toAffine.Point)
    (hφ : ∀ x y (hxy : W.toAffine.Nonsingular x y),
      ∃ hxy' : W.toAffine.Nonsingular (σK x) (σK y), φ (.some x y hxy) = .some (σK x) (σK y) hxy')
    {n : ℤ} (hn : IsUnit (n : R)) (Q P : W.toAffine.Point) (hQ : n • Q = P) (hP : φ P = P) :
    φ Q = Q := by
  subst e
  have h0 : redPt h (φ Q - Q) = 0 := by
    rw [← redHom_apply, map_sub, redHom_apply, redHom_apply, sub_eq_zero]
    cases Q with
    | zero => rw [show (Affine.Point.zero : (curveK K a b).toAffine.Point) = 0 from rfl, map_zero]
    | some x y hxy =>
      obtain ⟨hxy', e⟩ := hφ x y hxy
      rw [e]
      exact redPt_some_map σR σK hc hin h hxy hxy' rfl rfl
  have h1 : n • (φ Q - Q) = 0 := by
    rw [smul_sub, ← map_zsmul, hQ, hP, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_zsmul_eq_zero h hn h0 h1)

end Inertia

end NumberFieldKB.MilneEC.II.Valued
