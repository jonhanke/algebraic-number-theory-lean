import NumberFieldKB.MilneEC.Ch4ValuedGeneral3
import NumberFieldKB.MilneEC.Ch4DivPointsAux2

/-!
# Division points of a point of $E(\mathbb Q_p)$ generate an unramified extension: general models, every $p$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Lemma 3.5 and Proposition 3.6 (pdf p. 120).

This is `Ch4DivPoints.lean` without the restriction to short models (hence without $p \ge 5$): for an integral
Weierstrass model $W_0$ over $\mathbb Z_p$ with unit discriminant, $p \nmid n$ and $P \in E(\mathbb Q_p)$, there is a
finite unramified extension $K \subseteq \bar{\mathbb Q}_p$ containing the coordinates of every $Q$ with
$nQ = P$ (`exists_unramified_divPoints_general`).  The proof is that of `Ch4DivPoints.lean` (an inertia
automorphism fixes the generators, by `II.ValuedGen.key_fixed`, injectivity of $n$ on the kernel of reduction),
over $\mathcal O_K$ the integral closure of $\mathbb Z_p$ in the finite Galois extension, with the model
$W_0 \otimes \mathcal O_K$.
-/

namespace NumberFieldKB.MilneEC

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable {p : ℕ} [Fact p.Prime]

local notation "𝕃" => AlgebraicClosure ℚ_[p]

theorem unram_of_fixed_general (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : (W₀.toAffine⁄ℚ_[p]).Point)
    (Kf : IntermediateField ℚ_[p] 𝕃) [FiniteDimensional ℚ_[p] Kf] [IsGalois ℚ_[p] Kf]
    (S : Set 𝕃) (hKS : Kf = IntermediateField.adjoin ℚ_[p] S)
    (hQ : ∀ x ∈ S, ∃ (Q₀ : (W₀.toAffine⁄Kf).Point),
      n • Q₀ = Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] Kf) P ∧
      ∃ x0 y0 hh, Q₀ = Point.some x0 y0 hh ∧ (x = (x0 : 𝕃) ∨ x = (y0 : 𝕃))) :
    IsUnramifiedOverQp p Kf := by
  refine isUnramifiedOverQp_of_inertia_trivial p Kf ?_
  intro σ hσ
  set R := integralClosure ℤ_[p] Kf with hR
  have hfin : Module.Finite ℤ_[p] (integralClosure ℤ_[p] Kf) :=
    IsIntegralClosure.finite ℤ_[p] ℚ_[p] Kf (integralClosure ℤ_[p] Kf)
  have hDVR := NumberFieldKB.MilneANT.Remark753.isDVR_of_finite ℤ_[p] ℚ_[p] Kf
  have hFR : IsFractionRing (integralClosure ℤ_[p] Kf) Kf :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[p] Kf
  have hdom : IsDomain (integralClosure ℤ_[p] Kf) := inferInstance
  have hval : ValuationRing (integralClosure ℤ_[p] Kf) := inferInstance
  let σR : integralClosure ℤ_[p] Kf →+* integralClosure ℤ_[p] Kf :=
    RingHom.codRestrict ((σ : Kf →+* Kf).comp (integralClosure ℤ_[p] Kf).val.toRingHom)
      (integralClosure ℤ_[p] Kf) (fun x => by
        have := x.2
        rw [mem_integralClosure_iff] at this ⊢
        exact this.map ((σ : Kf →ₐ[ℚ_[p]] Kf).restrictScalars ℤ_[p]))
  have hc : ∀ x, algebraMap (integralClosure ℤ_[p] Kf) Kf (σR x) =
      (σ : Kf →+* Kf) (algebraMap (integralClosure ℤ_[p] Kf) Kf x) := fun x => rfl
  have hin : ∀ x, σR x - x ∈ IsLocalRing.maximalIdeal (integralClosure ℤ_[p] Kf) := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hσ x
    have : σR x - x = y := by
      apply Subtype.ext
      simp only [Subalgebra.coe_sub]
      change σ (x : Kf) - x = y
      rw [hxy]; ring
    rwa [this]
  have hgood : IsUnit (W₀.map (algebraMap ℤ_[p] R)).Δ := by
    rw [WeierstrassCurve.map_Δ]
    exact hΔ.map _
  have hnR : IsUnit (n : R) := by
    have h1 : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      by_contra hlt
      exact hn ((PadicInt.norm_int_lt_one_iff_dvd n).1 (not_le.1 hlt))
    simpa using h1.map (algebraMap ℤ_[p] R)
  have e : W₀.baseChange Kf = II.ValuedGen.curveK Kf (W₀.map (algebraMap ℤ_[p] R)) := by
    show W₀.map (algebraMap ℤ_[p] Kf) = (W₀.map (algebraMap ℤ_[p] R)).map (algebraMap R Kf)
    rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]
  have hfix : ∀ x (hx : x ∈ Kf), x ∈ S → σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro x hx hxS
    obtain ⟨Q₀, hQ₀, x0, y0, hh, rfl, hxx⟩ := hQ x hxS
    let _ : DecidableEq Kf := fun a b => Classical.propDecidable (a = b)
    have hQ₀' : n • Point.some x0 y0 hh =
        Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] Kf) P := by
      convert hQ₀
      rfl
    let φ : (W₀.baseChange Kf).toAffine.Point →+ (W₀.baseChange Kf).toAffine.Point :=
      Point.map (W' := W₀.toAffine) (σ : Kf →ₐ[ℚ_[p]] Kf)
    have hP : φ (Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] Kf) P) =
        Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] Kf) P := by
      show Point.map (W' := W₀.toAffine) (σ : Kf →ₐ[ℚ_[p]] Kf)
        (Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] Kf) P) = _
      rw [Point.map_map]
      rw [show (σ : Kf →ₐ[ℚ_[p]] Kf).comp (Algebra.ofId ℚ_[p] Kf) = Algebra.ofId ℚ_[p] Kf from
        Subsingleton.elim _ _]
    have key := II.ValuedGen.key_fixed (R := R) (K := Kf) σR (σ : Kf →+* Kf) hc hin hgood e φ
      (fun x y hxy => ⟨_, rfl⟩) hnR (Point.some x0 y0 hh)
      (Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] Kf) P) hQ₀' hP
    have key2 : (Point.some (σ x0) (σ y0) _ : (W₀.baseChange Kf).toAffine.Point) =
        Point.some x0 y0 hh := key
    have key2 := Affine.Point.some.inj key2
    rcases hxx with rfl | rfl
    · exact key2.1
    · exact key2.2
  refine AlgEquiv.ext fun z => ?_
  show σ z = z
  obtain ⟨z, hz⟩ := z
  have main : ∀ z, z ∈ IntermediateField.adjoin ℚ_[p] S → ∀ hz : z ∈ Kf, σ ⟨z, hz⟩ = ⟨z, hz⟩ := by
    intro z hz'
    induction hz' using IntermediateField.adjoin_induction with
    | mem x hx => exact fun hz => hfix x hz hx
    | algebraMap c => exact fun hz => σ.commutes c
    | add x y hx hy ihx ihy =>
      intro hz
      have hx' : x ∈ Kf := hKS ▸ hx
      have hy' : y ∈ Kf := hKS ▸ hy
      have e1 : (⟨x + y, hz⟩ : Kf) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
      rw [e1, map_add, ihx hx', ihy hy']
    | inv x hx ihx =>
      intro hz
      have hx' : x ∈ Kf := hKS ▸ hx
      have e1 : (⟨x⁻¹, hz⟩ : Kf) = (⟨x, hx'⟩)⁻¹ := rfl
      rw [e1, map_inv₀, ihx hx']
    | mul x y hx hy ihx ihy =>
      intro hz
      have hx' : x ∈ Kf := hKS ▸ hx
      have hy' : y ∈ Kf := hKS ▸ hy
      have e1 : (⟨x * y, hz⟩ : Kf) = ⟨x, hx'⟩ * ⟨y, hy'⟩ := rfl
      rw [e1, map_mul, ihx hx', ihy hy']
  exact main z (hKS ▸ hz) hz

theorem short_main_general (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : (W₀.toAffine⁄ℚ_[p]).Point) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧
      ∀ Q : (W₀.toAffine⁄(AlgebraicClosure ℚ_[p])).Point,
        n • Q = Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P →
          ∃ Q₀ : (W₀.toAffine⁄K).Point,
            Point.map (W' := W₀.toAffine) K.val Q₀ = Q := by
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero _)
  have hΔ' : (W₀.baseChange 𝕃).Δ ≠ 0 := by
    show (W₀.map (algebraMap ℤ_[p] 𝕃)).Δ ≠ 0
    rw [WeierstrassCurve.map_Δ]
    have hinj : Function.Injective (algebraMap ℤ_[p] 𝕃) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] 𝕃]
      exact (algebraMap ℚ_[p] 𝕃).injective.comp Subtype.val_injective
    intro h0
    exact hΔ.ne_zero (hinj (h0.trans (map_zero _).symm))
  set ιP := Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] 𝕃) P with hιP
  have hDfin := divPts_finite hΔ' hn0 ιP
  set S : Set 𝕃 := ⋃ Q ∈ {Q | n • Q = ιP}, coordSet Q with hS
  have hSfin : S.Finite := by
    refine hDfin.biUnion fun Q _ => ?_
    cases Q with
    | zero => exact Set.finite_empty
    | some x y _ => exact Set.toFinite ({x, y} : Set 𝕃)
  have hst : ∀ σ : 𝕃 →ₐ[ℚ_[p]] 𝕃, ∀ x ∈ S, σ x ∈ S := by
    intro σ x hx
    simp only [hS, Set.mem_iUnion] at hx ⊢
    obtain ⟨Q, hQ, hx⟩ := hx
    refine ⟨Point.map (W' := W₀.toAffine) σ Q, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq] at hQ ⊢
      rw [← map_zsmul, hQ, hιP, Point.map_map]
      rw [show σ.comp (Algebra.ofId ℚ_[p] 𝕃) = Algebra.ofId ℚ_[p] 𝕃 from Subsingleton.elim _ _]
    · cases Q with
      | zero => simp [coordSet] at hx
      | some x0 y0 hh =>
        simp only [coordSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
  obtain ⟨hfd, hgal⟩ := adjoin_finite_galois S hSfin hst
  have hdesc : ∀ Q : (W₀.toAffine⁄𝕃).Point, n • Q = ιP →
      ∃ Q₀ : (W₀.toAffine⁄(IntermediateField.adjoin ℚ_[p] S)).Point,
        Point.map (W' := W₀.toAffine) (IntermediateField.adjoin ℚ_[p] S).val Q₀ = Q := by
    intro Q hQ
    have hQD : Q ∈ {Q | n • Q = ιP} := hQ
    cases Q with
    | zero => exact ⟨0, rfl⟩
    | some x y hh =>
      have hx : x ∈ IntermediateField.adjoin ℚ_[p] S := IntermediateField.subset_adjoin _ _
        (Set.mem_iUnion₂.2 ⟨_, hQD, by simp [coordSet]⟩)
      have hy : y ∈ IntermediateField.adjoin ℚ_[p] S := IntermediateField.subset_adjoin _ _
        (Set.mem_iUnion₂.2 ⟨_, hQD, by simp [coordSet]⟩)
      exact ⟨Point.some ⟨x, hx⟩ ⟨y, hy⟩
        ((W₀.toAffine.baseChange_nonsingular
          (f := (IntermediateField.adjoin ℚ_[p] S).val) (IntermediateField.adjoin ℚ_[p] S).val.injective
          ⟨x, hx⟩ ⟨y, hy⟩).1 hh), rfl⟩
  refine ⟨IntermediateField.adjoin ℚ_[p] S, hfd, ?_, fun Q hQ => hdesc Q hQ⟩
  have := hfd
  have := hgal
  refine unram_of_fixed_general W₀ hΔ hn P (IntermediateField.adjoin ℚ_[p] S) S rfl ?_
  intro x hx
  have hxK : x ∈ IntermediateField.adjoin ℚ_[p] S := IntermediateField.subset_adjoin _ _ hx
  obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨Q₀, hQ₀⟩ := hdesc Q hQ
  have hn' : n • Q₀ = Point.map (W' := W₀.toAffine)
      (Algebra.ofId ℚ_[p] (IntermediateField.adjoin ℚ_[p] S)) P := by
    apply Point.map_injective (W' := W₀.toAffine) (IntermediateField.adjoin ℚ_[p] S).val
    rw [map_zsmul, hQ₀, Point.map_map]
    exact hQ
  refine ⟨Q₀, hn', ?_⟩
  cases Q₀ with
  | zero =>
    rw [← hQ₀] at hxQ
    exact (show x ∈ (∅ : Set 𝕃) from hxQ).elim
  | some x0 y0 hh =>
    refine ⟨x0, y0, hh, rfl, ?_⟩
    rw [← hQ₀] at hxQ
    have h2 : x ∈ ({(x0 : 𝕃), (y0 : 𝕃)} : Set 𝕃) := hxQ
    simpa using h2

/-- All $n$-division points over $\bar{\mathbb Q}_p$ of a point of $E(\mathbb Q_p)$ lie in one finite
unramified extension of $\mathbb Q_p$ (general integral model with unit discriminant, every prime $p$,
$p \nmid n$). -/
theorem exists_unramified_divPoints_general (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : (W₀.toAffine⁄ℚ_[p]).Point) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧
      ∀ Q : (W₀.toAffine⁄(AlgebraicClosure ℚ_[p])).Point,
        n • Q = Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P →
          ∃ Q₀ : (W₀.toAffine⁄K).Point, Point.map (W' := W₀.toAffine) K.val Q₀ = Q :=
  short_main_general W₀ hΔ hn P

end NumberFieldKB.MilneEC
