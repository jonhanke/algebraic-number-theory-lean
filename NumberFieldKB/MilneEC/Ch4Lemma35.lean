import NumberFieldKB.MilneEC.Ch4DivPoints
import NumberFieldKB.MilneEC.Ch4Lemma32
import NumberFieldKB.MilneEC.Ch2Iso
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Milne, *Elliptic Curves*, Chapter IV, Lemmas 3.2 and 3.5 for general models, $p \ge 5$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Lemma 3.2 (pdf p. 119) and Lemma 3.5
(pdf p. 120).

For $p \ge 5$ the numbers $2$ and $3$ are units of $\mathbb Z_p$, so an integral Weierstrass model $W_0$ with
unit discriminant becomes a short model $Y^2 = X^3 + aX + b$ by a change of variables over $\mathbb Z_p$ with
$u = 1$ (Mathlib `WeierstrassCurve.toShortNF`); the change of variables preserves the discriminant, integrality of
coordinates and reduction, and commutes with base change.  The short case is `II.lemma_3_2_short` (over
$\mathbb Z_p$) and `exists_unramified_divPoints_short` (over $\bar{\mathbb Q}_p$).

* `exists_unramified_divPoints`: all $n$-division points of a point of $E(\mathbb Q_p)$ lie in one finite
  unramified extension (general model, $p \ge 5$).
* `lemma_3_2_of_five_le`: the statement of the named `Lemma3_2` for $p \ge 5$.
* `lemma_3_5_of_five_le`: the statement of the named `Lemma3_5` for $p \ge 5$.

The restriction $p \ge 5$ is harmless: Milne's route needs these lemmas only for
$p \nmid 2n\Delta$, and $p = 3$ can be put in the finite exceptional set.
-/

namespace NumberFieldKB.MilneEC

open WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

section Transport

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

/-- Transport of points along an equality of Weierstrass curves. -/
noncomputable def ptCast {X Y : WeierstrassCurve F} (h : X = Y) :
    X.toAffine.Point ≃+ Y.toAffine.Point := by
  subst h; exact AddEquiv.refl _

theorem ptCast_zero {X Y : WeierstrassCurve F} (h : X = Y) : ptCast h 0 = 0 := map_zero _

theorem ptCast_some {X Y : WeierstrassCurve F} (h : X = Y) {x y : F}
    (hxy : X.toAffine.Nonsingular x y) :
    ∃ hxy' : Y.toAffine.Nonsingular x y, ptCast h (Point.some x y hxy) = Point.some x y hxy' := by
  subst h; exact ⟨hxy, rfl⟩

variable {p} (W₀ : WeierstrassCurve ℤ_[p]) (C : VariableChange ℤ_[p])

/-- The change of variables `C` as an isomorphism of the groups of points over `F`
(the formula is `(x, y) ↦ (u²x + r, u³y + su²x + t)`). -/
noncomputable def vc (φ : ℤ_[p] →+* F) :
    ((C • W₀).map φ).toAffine.Point ≃+ (W₀.map φ).toAffine.Point :=
  (ptCast (map_variableChange W₀ C φ).symm).trans (II.variableChangePointEquiv (W₀.map φ) (C.map φ))

theorem vc_some (φ : ℤ_[p] →+* F) {x y : F} (h : ((C • W₀).map φ).toAffine.Nonsingular x y) :
    ∃ h' : (W₀.map φ).toAffine.Nonsingular (φ (C.u : ℤ_[p]) ^ 2 * x + φ C.r)
        (φ (C.u : ℤ_[p]) ^ 3 * y + φ C.s * φ (C.u : ℤ_[p]) ^ 2 * x + φ C.t),
      vc W₀ C φ (Point.some x y h) = Point.some _ _ h' := by
  obtain ⟨h1, e1⟩ := ptCast_some (map_variableChange W₀ C φ).symm h
  refine ⟨II.variableChange_nonsingular (W₀.map φ) (C.map φ) h1, ?_⟩
  simp only [vc, AddEquiv.trans_apply]
  rw [e1]
  rfl

theorem vc_zero (φ : ℤ_[p] →+* F) : vc W₀ C φ 0 = 0 := map_zero _

theorem vc_natural {G : Type*} [Field G] [DecidableEq G] [Algebra ℚ_[p] F] [Algebra ℚ_[p] G]
    [Algebra ℤ_[p] F] [Algebra ℤ_[p] G] [IsScalarTower ℤ_[p] ℚ_[p] F] [IsScalarTower ℤ_[p] ℚ_[p] G]
    (f : F →ₐ[ℚ_[p]] G) (Q : (((C • W₀).map (algebraMap ℤ_[p] F)).toAffine).Point) :
    Point.map (W' := W₀.toAffine) f (by exact vc W₀ C (algebraMap ℤ_[p] F) Q) =
      vc W₀ C (algebraMap ℤ_[p] G) (by exact Point.map (W' := (C • W₀).toAffine) f (by exact Q)) := by
  have hφ : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] F z) = algebraMap ℤ_[p] G z := fun z => by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] F, f.commutes,
      ← IsScalarTower.algebraMap_apply]
  rcases Q with _ | ⟨x, y, h⟩
  · exact (congrArg (Point.map (W' := W₀.toAffine) f) (vc_zero W₀ C _)).trans
      ((map_zero _).trans (vc_zero W₀ C _).symm)
  · obtain ⟨h', e⟩ := vc_some W₀ C (algebraMap ℤ_[p] F) h
    obtain ⟨hf, hm⟩ : ∃ hf, Point.map (W' := (C • W₀).toAffine) f (Point.some x y h) =
      Point.some (f x) (f y) hf := ⟨_, rfl⟩
    erw [e, hm]
    obtain ⟨h2, e2⟩ := vc_some W₀ C (algebraMap ℤ_[p] G) hf
    erw [e2, Point.map_some]
    simp only [Point.some.injEq, map_add, map_mul, map_pow, hφ]
    rfl

theorem unit_int_of_not_dvd {k : ℤ} (hk : ¬ (p : ℤ) ∣ k) : IsUnit (k : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) ?_
  by_contra hlt
  exact hk ((PadicInt.norm_int_lt_one_iff_dvd k).1 (not_le.1 hlt))

theorem short_setup (hp : 5 ≤ p) (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) :
    ∃ (C : VariableChange ℤ_[p]) (a b : ℤ_[p]), C • W₀ = II.shortZp a b ∧ (C.u : ℤ_[p]) = 1 ∧
      II.Valued.Good a b := by
  have h2 : IsUnit (2 : ℤ_[p]) := by
    have := unit_int_of_not_dvd (p := p) (k := 2) (fun h => by
      have := Int.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have h3 : IsUnit (3 : ℤ_[p]) := by
    have := unit_int_of_not_dvd (p := p) (k := 3) (fun h => by
      have := Int.le_of_dvd (by norm_num) h; omega)
    simpa using this
  have _i2 : Invertible (2 : ℤ_[p]) := Classical.choice h2.nonempty_invertible
  have _i3 : Invertible (3 : ℤ_[p]) := Classical.choice h3.nonempty_invertible
  set C := W₀.toShortNF with hC
  have hu : C.u = 1 := by
    simp [hC, WeierstrassCurve.toShortNF, WeierstrassCurve.toCharNeTwoNF, VariableChange.mul_def]
  have hshort : (C • W₀).IsShortNF := W₀.toShortNF_spec
  refine ⟨C, (C • W₀).a₄, (C • W₀).a₆, ?_, by rw [hu]; rfl, ?_⟩
  · ext
    · simpa [II.shortZp] using WeierstrassCurve.a₁_of_isShortNF (C • W₀)
    · simpa [II.shortZp] using WeierstrassCurve.a₂_of_isShortNF (C • W₀)
    · simpa [II.shortZp] using WeierstrassCurve.a₃_of_isShortNF (C • W₀)
    · rfl
    · rfl
  · refine ⟨h2, ?_⟩
    have hD : (C • W₀).Δ = -16 * (4 * (C • W₀).a₄ ^ 3 + 27 * (C • W₀).a₆ ^ 2) :=
      WeierstrassCurve.Δ_of_isShortNF (C • W₀)
    have hD2 : (C • W₀).Δ = W₀.Δ := by
      rw [WeierstrassCurve.variableChange_Δ, hu]; simp
    have : IsUnit (-16 * (4 * (C • W₀).a₄ ^ 3 + 27 * (C • W₀).a₆ ^ 2)) := by
      rw [← hD, hD2]; exact hΔ
    exact isUnit_of_mul_isUnit_right this

theorem baseChange_baseChange_eq (W₀ : WeierstrassCurve ℤ_[p]) (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    (W₀.baseChange ℚ_[p]).baseChange K = W₀.baseChange K := by
  show (W₀.map (algebraMap ℤ_[p] ℚ_[p])).map (algebraMap ℚ_[p] K) = W₀.map (algebraMap ℤ_[p] K)
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

theorem ptCast_map_comm (W₀ : WeierstrassCurve ℤ_[p]) (K : Type*) [Field K] [DecidableEq K]
    [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (P : ((W₀.baseChange ℚ_[p]).toAffine).Point) :
    ptCast (baseChange_baseChange_eq W₀ K)
      (by exact Point.map (W' := (W₀.baseChange ℚ_[p]).toAffine) (Algebra.ofId ℚ_[p] K) P) =
      Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] K) (by exact P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact (ptCast_zero _).trans rfl
  · obtain ⟨h1, e1⟩ := ptCast_some (baseChange_baseChange_eq W₀ K)
      (x := algebraMap ℚ_[p] K x) (y := algebraMap ℚ_[p] K y)
      ((W₀.baseChange ℚ_[p]).toAffine.baseChange_nonsingular (f := Algebra.ofId ℚ_[p] K)
        (Algebra.ofId ℚ_[p] K).injective x y |>.2 h)
    erw [e1]
    rfl

theorem ptCast_symm {X Y : WeierstrassCurve F} (h : X = Y) : (ptCast h).symm = ptCast h.symm := by
  subst h; rfl

theorem vc_symm_some (φ : ℤ_[p] →+* F) (hu : φ (C.u : ℤ_[p]) = 1) {x y : F}
    (h : (W₀.map φ).toAffine.Nonsingular x y) :
    ∃ h' : ((C • W₀).map φ).toAffine.Nonsingular (x - φ C.r) (y - φ C.s * (x - φ C.r) - φ C.t),
      (vc W₀ C φ).symm (Point.some x y h) = Point.some _ _ h' := by
  rcases hQ : (vc W₀ C φ).symm (Point.some x y h) with _ | ⟨x', y', h1⟩
  · exfalso
    have h0 := congrArg (vc W₀ C φ) hQ
    rw [AddEquiv.apply_symm_apply] at h0
    have h00 : (Point.zero : ((C • W₀).map φ).toAffine.Point) = 0 := rfl
    rw [h00, map_zero] at h0
    cases h0
  · obtain ⟨h2, e2⟩ := vc_some W₀ C φ h1
    have h0 := congrArg (vc W₀ C φ) hQ
    rw [AddEquiv.apply_symm_apply, e2] at h0
    have h3 := Affine.Point.some.inj h0
    obtain ⟨h4, h5⟩ := h3
    rw [hu] at h4 h5
    have hx' : x' = x - φ C.r := by linear_combination -h4
    subst hx'
    have hy' : y' = y - φ C.s * (x - φ C.r) - φ C.t := by linear_combination -h5
    subst hy'
    exact ⟨h1, rfl⟩

/-- The identification of the points of a model `X = C • W₀` (over `F`) with those of `W₀`. -/
noncomputable def vcS (φ : ℤ_[p] →+* F) {X : WeierstrassCurve F} (hX : X = (C • W₀).map φ) :
    X.toAffine.Point ≃+ (W₀.map φ).toAffine.Point :=
  (ptCast hX).trans (vc W₀ C φ)

theorem vcS_symm_zero (φ : ℤ_[p] →+* F) {X : WeierstrassCurve F} (hX : X = (C • W₀).map φ) :
    (vcS W₀ C φ hX).symm 0 = 0 := map_zero _

theorem vcS_symm_some (φ : ℤ_[p] →+* F) (hu : φ (C.u : ℤ_[p]) = 1) {X : WeierstrassCurve F}
    (hX : X = (C • W₀).map φ) {x y : F} (h : (W₀.map φ).toAffine.Nonsingular x y) :
    ∃ h' : X.toAffine.Nonsingular (x - φ C.r) (y - φ C.s * (x - φ C.r) - φ C.t),
      (vcS W₀ C φ hX).symm (Point.some x y h) = Point.some _ _ h' := by
  obtain ⟨h1, e1⟩ := vc_symm_some W₀ C φ hu h
  obtain ⟨h2, e2⟩ := ptCast_some hX.symm h1
  refine ⟨h2, ?_⟩
  simp only [vcS, AddEquiv.symm_trans_apply]
  rw [e1, ptCast_symm, e2]

theorem reduces_compat {a b : ℤ_[p]} (hu : (C.u : ℤ_[p]) = 1)
    (hX1 : II.curveQp a b = (C • W₀).map (algebraMap ℤ_[p] ℚ_[p]))
    (hX2 : II.curveFp a b = (C • W₀).map PadicInt.toZMod)
    (P : (W₀.baseChange ℚ_[p]).toAffine.Point) (P' : (W₀.map PadicInt.toZMod).toAffine.Point)
    (hR : ReducesTo W₀ P P') :
    II.toProjCoords ((vcS W₀ C PadicInt.toZMod hX2).symm P') =
      II.reducePoint ((vcS W₀ C (algebraMap ℤ_[p] ℚ_[p]) hX1).symm P) := by
  have hu1 : (algebraMap ℤ_[p] ℚ_[p]) (C.u : ℤ_[p]) = 1 := by rw [hu, map_one]
  have hu2 : PadicInt.toZMod (C.u : ℤ_[p]) = 1 := by rw [hu, map_one]
  rcases hR with ⟨rfl, rfl⟩ | ⟨x, y, h, rfl, hx, rfl⟩ | ⟨x, y, h, h', rfl, rfl⟩
  · erw [vcS_symm_zero, vcS_symm_zero, II.reducePoint_zero, II.toProjCoords_zero]
  · obtain ⟨h1, e1⟩ := vcS_symm_some W₀ C _ hu1 hX1 h
    erw [e1, vcS_symm_zero, II.toProjCoords_zero]
    rw [II.reducePoint_some_of_gt]
    by_contra hle
    rw [not_lt] at hle
    have hr : ‖(algebraMap ℤ_[p] ℚ_[p]) C.r‖ ≤ 1 := PadicInt.norm_le_one _
    have := IsUltrametricDist.norm_add_le_max (x - (algebraMap ℤ_[p] ℚ_[p]) C.r)
      ((algebraMap ℤ_[p] ℚ_[p]) C.r)
    rw [sub_add_cancel] at this
    exact absurd (this.trans (max_le hle hr)) (not_le.2 hx)
  · obtain ⟨h1, e1⟩ := vcS_symm_some W₀ C _ hu1 hX1 h
    obtain ⟨h2, e2⟩ := vcS_symm_some W₀ C _ hu2 hX2 h'
    erw [e1, e2]
    have ex : (x : ℚ_[p]) - (algebraMap ℤ_[p] ℚ_[p]) C.r = ((x - C.r : ℤ_[p]) : ℚ_[p]) := by
      simp
    have ey : (y : ℚ_[p]) - (algebraMap ℤ_[p] ℚ_[p]) C.s * ((x : ℚ_[p]) - (algebraMap ℤ_[p] ℚ_[p]) C.r) -
        (algebraMap ℤ_[p] ℚ_[p]) C.t = ((y - C.s * (x - C.r) - C.t : ℤ_[p]) : ℚ_[p]) := by
      simp
    have hx1 : ‖(x : ℚ_[p]) - (algebraMap ℤ_[p] ℚ_[p]) C.r‖ ≤ 1 := by
      rw [ex]; exact PadicInt.norm_le_one _
    rw [II.reducePoint_some_of_le hx1, ey, ex, II.residue_coe, II.residue_coe]
    show ![_, _, _] = _
    simp

end Transport

/-- All $n$-division points over $\bar{\mathbb Q}_p$ of a point of $E(\mathbb Q_p)$ lie in one finite unramified
extension of $\mathbb Q_p$ ($p \ge 5$, integral model with unit discriminant, $p \nmid n$). -/
theorem exists_unramified_divPoints (hp : 5 ≤ p) (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) (P : (W₀.toAffine⁄ℚ_[p]).Point) :
    ∃ K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]), FiniteDimensional ℚ_[p] K ∧
      IsUnramifiedOverQp p K ∧
      ∀ Q : (W₀.toAffine⁄(AlgebraicClosure ℚ_[p])).Point,
        n • Q = Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P →
          ∃ Q₀ : (W₀.toAffine⁄K).Point, Point.map (W' := W₀.toAffine) K.val Q₀ = Q := by
  obtain ⟨C, a, b, hC, hu, hg⟩ := short_setup hp W₀ hΔ
  have short := exists_unramified_divPoints_short a b hg hn
  rw [← hC] at short
  set P₁ : (((C • W₀).toAffine)⁄ℚ_[p]).Point := (vc W₀ C (algebraMap ℤ_[p] ℚ_[p])).symm P with hP₁
  obtain ⟨K, hfd, hun, hK⟩ := short P₁
  refine ⟨K, hfd, hun, fun Q hQ => ?_⟩
  set Q₁ : (((C • W₀).toAffine)⁄(AlgebraicClosure ℚ_[p])).Point :=
    (vc W₀ C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]))).symm Q with hQ₁
  have hnat := vc_natural W₀ C (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P₁
  have hQ₁' : n • Q₁ = Point.map (W' := (C • W₀).toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P₁ := by
    apply (vc W₀ C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]))).injective
    have h1 := map_zsmul (vc W₀ C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]))) n Q₁
    have h2 : vc W₀ C (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) Q₁ = Q :=
      AddEquiv.apply_symm_apply _ _
    have h3 : vc W₀ C (algebraMap ℤ_[p] ℚ_[p]) P₁ = P := AddEquiv.apply_symm_apply _ _
    rw [h3] at hnat
    refine h1.trans ?_
    erw [h2, hQ]
    exact hnat
  obtain ⟨Q₀, hQ₀⟩ := hK Q₁ hQ₁'
  refine ⟨vc W₀ C (algebraMap ℤ_[p] K) Q₀, ?_⟩
  have := vc_natural W₀ C (K.val) Q₀
  refine this.trans ?_
  erw [hQ₀]
  rw [hQ₁]
  exact AddEquiv.apply_symm_apply _ _

/-- **Lemma 3.2** (Milne, pdf p. 119) for $p \ge 5$: the statement of the named `Lemma3_2`. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.2, pdf p. 119"]
theorem lemma_3_2_of_five_le (hp : 5 ≤ p) (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) (n : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) (P : (W₀.baseChange ℚ_[p]).toAffine.Point)
    (P' : (W₀.map PadicInt.toZMod).toAffine.Point) (hPP' : ReducesTo W₀ P P') :
    (∃ Q, n • Q = P) ↔ ∃ Q', n • Q' = P' := by
  obtain ⟨C, a, b, hC, hu, hg⟩ := short_setup hp W₀ hΔ
  have hX1 : II.curveQp a b = (C • W₀).map (algebraMap ℤ_[p] ℚ_[p]) := by
    rw [hC, II.curveQp_eq_map]
  have hX2 : II.curveFp a b = (C • W₀).map PadicInt.toZMod := by
    rw [hC]; ext <;> simp [II.curveFp, II.shortCurve, II.shortZp]
  have hcompat := reduces_compat W₀ C hu hX1 hX2 P P' hPP'
  have hp2 : p ≠ 2 := by omega
  have key := II.lemma_3_2_short hp2 a b hg.disc hn ((vcS W₀ C _ hX1).symm P)
    ((vcS W₀ C _ hX2).symm P') hcompat
  constructor
  · rintro ⟨Q, hQ⟩
    obtain ⟨Q', hQ'⟩ := key.1 ⟨(vcS W₀ C _ hX1).symm Q, by
      rw [← hQ]; exact (map_zsmul _ n Q).symm⟩
    refine ⟨vcS W₀ C _ hX2 Q', ?_⟩
    exact (map_zsmul _ n Q').symm.trans ((congrArg _ hQ').trans (AddEquiv.apply_symm_apply _ _))
  · rintro ⟨Q', hQ'⟩
    obtain ⟨Q, hQ⟩ := key.2 ⟨(vcS W₀ C _ hX2).symm Q', by
      rw [← hQ']; exact (map_zsmul _ n Q').symm⟩
    refine ⟨vcS W₀ C _ hX1 Q, ?_⟩
    exact (map_zsmul _ n Q).symm.trans ((congrArg _ hQ).trans (AddEquiv.apply_symm_apply _ _))

/-- **Lemma 3.5** (Milne, pdf p. 120) for $p \ge 5$: the statement of the named `Lemma3_5`. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.5, pdf p. 120"]
theorem lemma_3_5_of_five_le (hp : 5 ≤ p) (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ) (n : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) (P : (W₀.baseChange ℚ_[p]).toAffine.Point) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[p] K) (_ : Algebra ℤ_[p] K) (_ : IsScalarTower ℤ_[p] ℚ_[p] K),
      FiniteDimensional ℚ_[p] K ∧ IsUnramifiedOverQp p K ∧
        ∃ Q : ((W₀.baseChange ℚ_[p]).toAffine⁄K).Point,
          n • Q = Point.map (W' := (W₀.baseChange ℚ_[p]).toAffine) (Algebra.ofId ℚ_[p] K) P := by
  have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero _)
  obtain ⟨K, hfd, hun, hK⟩ := exists_unramified_divPoints p hp W₀ hΔ hn P
  have hell : (W₀.baseChange (AlgebraicClosure ℚ_[p])).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    show IsUnit (W₀.map (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]))).Δ
    rw [WeierstrassCurve.map_Δ]
    exact hΔ.map _
  obtain ⟨QL, hQL⟩ := lemma2_1.surjective (AlgebraicClosure ℚ_[p]) (W₀.baseChange (AlgebraicClosure ℚ_[p])) n hn0
    (Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p])) P)
  obtain ⟨Q₀, hQ₀⟩ := hK QL hQL
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, hfd, hun, ?_⟩
  have hn' : n • Q₀ = Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] K) (by exact P) := by
    apply Point.map_injective (W' := W₀.toAffine) K.val
    rw [map_zsmul, hQ₀, Point.map_map]
    refine hQL.trans ?_
    rw [show K.val.comp (Algebra.ofId ℚ_[p] K) = Algebra.ofId ℚ_[p] (AlgebraicClosure ℚ_[p]) from
      Subsingleton.elim _ _]
  let _ : DecidableEq K := fun a b => Classical.propDecidable (a = b)
  have hn'A : n • Q₀ = Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] K) (by exact P) := by
    convert hn'
    rfl
  let T := ptCast (baseChange_baseChange_eq W₀ K)
  refine ⟨T.symm Q₀, ?_⟩
  have hsymm : T.symm (Point.map (W' := W₀.toAffine) (Algebra.ofId ℚ_[p] K) (by exact P)) =
      Point.map (W' := (W₀.baseChange ℚ_[p]).toAffine) (Algebra.ofId ℚ_[p] K) P :=
    (T.symm_apply_eq).2 (ptCast_map_comm W₀ K P).symm
  have h1 : n • T.symm Q₀ = T.symm (n • Q₀) := (map_zsmul T.symm n Q₀).symm
  exact h1.trans ((congrArg T.symm hn'A).trans hsymm)

end NumberFieldKB.MilneEC
