import NumberFieldKB.MilneEC.Ch4DivPointsAux
import NumberFieldKB.MilneEC.Ch4Local
import NumberFieldKB.MilneEC.Ch2Corollary42

namespace NumberFieldKB.MilneEC

variable {p : ℕ} [Fact p.Prime]

theorem adjoin_finite_galois (S : Set (AlgebraicClosure ℚ_[p])) (hS : S.Finite)
    (hst : ∀ σ : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p], ∀ x ∈ S, σ x ∈ S) :
    FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] S) ∧
      IsGalois ℚ_[p] (IntermediateField.adjoin ℚ_[p] S) := by
  have hfd : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] S) := by
    have := hS.to_subtype
    exact IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsIntegral.isIntegral x)
  refine ⟨hfd, ?_⟩
  have : Normal ℚ_[p] (IntermediateField.adjoin ℚ_[p] S) := by
    rw [IntermediateField.normal_iff_forall_map_le]
    intro σ
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin_le_iff.2 fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact IntermediateField.subset_adjoin _ _ (hst σ y hy)
  exact ⟨⟩


section Div

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

local notation "𝕃" => AlgebraicClosure ℚ_[p]

/-- Coordinates of a point. -/
def coordSet {W : WeierstrassCurve 𝕃} : W.toAffine.Point → Set 𝕃
  | .zero => ∅
  | .some x y _ => {x, y}

theorem divPts_finite {W : WeierstrassCurve 𝕃} (hΔ : W.Δ ≠ 0) {n : ℤ} (hn : n ≠ 0)
    (P0 : W.toAffine.Point) : {Q : W.toAffine.Point | n • Q = P0}.Finite := by
  classical
  by_cases hne : ∃ Q₀ : W.toAffine.Point, n • Q₀ = P0
  · obtain ⟨Q₀, hQ₀⟩ := hne
    refine ((torsion_finite W hΔ hn).image (fun T => T + Q₀)).subset ?_
    intro Q hQ
    refine ⟨Q - Q₀, ?_, by simp⟩
    simp only [Set.mem_ofPred_eq] at hQ ⊢
    rw [smul_sub, hQ, hQ₀, sub_self]
  · convert Set.finite_empty
    ext Q
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hne ⟨Q, h⟩


theorem unram_of_fixed (a b : ℤ_[p]) (h : II.Valued.Good a b) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : ((II.shortZp a b).toAffine⁄ℚ_[p]).Point)
    (Kf : IntermediateField ℚ_[p] 𝕃) [FiniteDimensional ℚ_[p] Kf] [IsGalois ℚ_[p] Kf]
    (S : Set 𝕃) (hKS : Kf = IntermediateField.adjoin ℚ_[p] S)
    (hQ : ∀ x ∈ S, ∃ (Q₀ : ((II.shortZp a b).toAffine⁄Kf).Point),
      n • Q₀ = Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] Kf) P ∧
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
  have hgood : II.Valued.Good (algebraMap ℤ_[p] R a) (algebraMap ℤ_[p] R b) := by
    refine ⟨?_, ?_⟩
    · have := h.two.map (algebraMap ℤ_[p] R)
      rwa [map_ofNat] at this
    · have := h.disc.map (algebraMap ℤ_[p] R)
      simp only [map_add, map_mul, map_pow, map_ofNat] at this
      exact this
  have hnR : IsUnit (n : R) := by
    have h1 : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) ?_
      by_contra hlt
      exact hn ((PadicInt.norm_int_lt_one_iff_dvd n).1 (not_le.1 hlt))
    simpa using h1.map (algebraMap ℤ_[p] R)
  have e : (II.shortZp a b).baseChange Kf =
      II.Valued.curveK Kf (algebraMap ℤ_[p] R a) (algebraMap ℤ_[p] R b) := by
    ext <;> simp [II.shortZp, II.shortCurve, ← IsScalarTower.algebraMap_apply]
  have hfix : ∀ x (hx : x ∈ Kf), x ∈ S → σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro x hx hxS
    obtain ⟨Q₀, hQ₀, x0, y0, hh, rfl, hxx⟩ := hQ x hxS
    let _ : DecidableEq Kf := fun a b => Classical.propDecidable (a = b)
    have hQ₀' : n • Point.some x0 y0 hh =
        Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] Kf) P := by
      convert hQ₀
      rfl
    let φ : ((II.shortZp a b).baseChange Kf).toAffine.Point →+
        ((II.shortZp a b).baseChange Kf).toAffine.Point :=
      Point.map (W' := (II.shortZp a b).toAffine) (σ : Kf →ₐ[ℚ_[p]] Kf)
    have hP : φ (Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] Kf) P) =
        Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] Kf) P := by
      show Point.map (W' := (II.shortZp a b).toAffine) (σ : Kf →ₐ[ℚ_[p]] Kf)
        (Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] Kf) P) = _
      rw [Point.map_map]
      rw [show (σ : Kf →ₐ[ℚ_[p]] Kf).comp (Algebra.ofId ℚ_[p] Kf) = Algebra.ofId ℚ_[p] Kf from
        Subsingleton.elim _ _]
    have key := II.Valued.key_fixed (R := R) (K := Kf) σR (σ : Kf →+* Kf) hc hin hgood e φ
      (fun x y hxy => ⟨_, rfl⟩) hnR (Point.some x0 y0 hh)
      (Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] Kf) P) hQ₀' hP
    have key2 : (Point.some (σ x0) (σ y0) _ : ((II.shortZp a b).baseChange Kf).toAffine.Point) =
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

theorem short_main (a b : ℤ_[p]) (h : II.Valued.Good a b) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : ((II.shortZp a b).toAffine⁄ℚ_[p]).Point) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧
      ∀ Q : ((II.shortZp a b).toAffine⁄(AlgebraicClosure ℚ_[p])).Point,
        n • Q = Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P →
          ∃ Q₀ : ((II.shortZp a b).toAffine⁄K).Point,
            Point.map (W' := (II.shortZp a b).toAffine) K.val Q₀ = Q := by
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero _)
  have hΔ : ((II.shortZp a b).baseChange 𝕃).Δ ≠ 0 := by
    have h16 : IsUnit (16 : ℤ_[p]) := by
      have := h.two.pow 4
      norm_num at this
      exact this
    have hu : IsUnit (II.shortZp a b).Δ := by
      have e : (II.shortZp a b).Δ = -16 * (4 * a ^ 3 + 27 * b ^ 2) := by
        simp only [II.shortZp, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆, WeierstrassCurve.b₈]
        ring
      rw [e]
      exact h16.neg.mul h.disc
    show ((II.shortZp a b).map (algebraMap ℤ_[p] 𝕃)).Δ ≠ 0
    rw [WeierstrassCurve.map_Δ]
    have hinj : Function.Injective (algebraMap ℤ_[p] 𝕃) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] 𝕃]
      exact (algebraMap ℚ_[p] 𝕃).injective.comp Subtype.val_injective
    intro h0
    exact hu.ne_zero (hinj (h0.trans (map_zero _).symm))
  set ιP := Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] 𝕃) P with hιP
  have hDfin := divPts_finite hΔ hn0 ιP
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
    refine ⟨Point.map (W' := (II.shortZp a b).toAffine) σ Q, ?_, ?_⟩
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
  have hdesc : ∀ Q : ((II.shortZp a b).toAffine⁄𝕃).Point, n • Q = ιP →
      ∃ Q₀ : ((II.shortZp a b).toAffine⁄(IntermediateField.adjoin ℚ_[p] S)).Point,
        Point.map (W' := (II.shortZp a b).toAffine) (IntermediateField.adjoin ℚ_[p] S).val Q₀ = Q := by
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
        (((II.shortZp a b).toAffine.baseChange_nonsingular
          (f := (IntermediateField.adjoin ℚ_[p] S).val) (IntermediateField.adjoin ℚ_[p] S).val.injective
          ⟨x, hx⟩ ⟨y, hy⟩).1 hh), rfl⟩
  refine ⟨IntermediateField.adjoin ℚ_[p] S, hfd, ?_, fun Q hQ => hdesc Q hQ⟩
  have := hfd
  have := hgal
  refine unram_of_fixed a b h hn P (IntermediateField.adjoin ℚ_[p] S) S rfl ?_
  intro x hx
  have hxK : x ∈ IntermediateField.adjoin ℚ_[p] S := IntermediateField.subset_adjoin _ _ hx
  obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨Q₀, hQ₀⟩ := hdesc Q hQ
  have hn' : n • Q₀ = Point.map (W' := (II.shortZp a b).toAffine) (Algebra.ofId ℚ_[p] (IntermediateField.adjoin ℚ_[p] S)) P := by
    apply Point.map_injective (W' := (II.shortZp a b).toAffine) (IntermediateField.adjoin ℚ_[p] S).val
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

end Div

end NumberFieldKB.MilneEC
