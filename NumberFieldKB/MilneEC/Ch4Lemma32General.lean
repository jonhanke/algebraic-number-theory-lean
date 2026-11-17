import NumberFieldKB.MilneEC.Ch4DivPointsGeneral
import NumberFieldKB.MilneEC.Ch4Lemma35
import NumberFieldKB.MilneEC.Ch4Prop36Proof

/-!
# Milne, *Elliptic Curves*, Chapter IV, Lemmas 3.2 and 3.5 for general models and every prime $p$

Source: J. S. Milne, *Elliptic Curves* (`milne2006ec`), Chapter IV, Lemma 3.2 (pdf p. 119) and Lemma 3.5
(pdf p. 120).

* `lemma3_5`: the named `Lemma3_5`, for every prime $p$ (no short model, so no $p \ge 5$): this is
  `lemma_3_5_of_five_le` with `exists_unramified_divPoints_general` in place of the $p \ge 5$ division-point
  theorem.
* `lemma3_2`: the named `Lemma3_2` for every prime $p$, from `II.ValuedGen.lemma_3_2_valued` with
  $R = \mathbb Z_p$, $K = \mathbb Q_p$ ($\mathbb Z_p$ is a Henselian discrete valuation ring).  The bridge: the relation
  `ReducesTo` of `Ch4Local.lean` is the graph of `II.ValuedGen.redPt` followed by the transport of points along
  the $\mathbb Z_p$-algebra isomorphism $\mathrm{ResidueField}\,\mathbb Z_p \cong \mathbb Z/p\mathbb Z$
  (`PadicInt.residueField`), `resMap`.
-/

namespace NumberFieldKB.MilneEC

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped Classical

noncomputable section Bridge

variable {p : ℕ} [Fact p.Prime]

lemma some_congr {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {a b x y : F}
    (ha : a = x) (hb : b = y) (h1 : W.toAffine.Nonsingular a b) (h2 : W.toAffine.Nonsingular x y) :
    Point.some a b h1 = Point.some x y h2 := by
  subst ha hb; rfl

local instance zmodAlgebra : Algebra ℤ_[p] (ZMod p) := PadicInt.toZMod.toAlgebra

/-- The isomorphism of the residue field of $\mathbb Z_p$ with $\mathbb Z/p\mathbb Z$ as $\mathbb Z_p$-algebras
($\mathbb Z/p\mathbb Z$ a $\mathbb Z_p$-algebra via `PadicInt.toZMod`). -/
noncomputable def resAlgEquiv : ResidueField ℤ_[p] ≃ₐ[ℤ_[p]] ZMod p :=
  { PadicInt.residueField with
    commutes' := fun x => by
      show PadicInt.residueField (residue ℤ_[p] x) = PadicInt.toZMod x
      rfl }

/-- Transport of points of the reduced curve to the curve over $\mathbb F_p = \mathbb Z/p\mathbb Z$. -/
noncomputable def resMap (W₀ : WeierstrassCurve ℤ_[p]) :
    ((W₀.map (residue ℤ_[p])).toAffine).Point →+ ((W₀.map PadicInt.toZMod).toAffine).Point :=
  Point.map (W' := W₀.toAffine) (resAlgEquiv (p := p) : ResidueField ℤ_[p] →ₐ[ℤ_[p]] ZMod p)

lemma resMap_injective (W₀ : WeierstrassCurve ℤ_[p]) : Function.Injective (resMap W₀) :=
  Point.map_injective (W' := W₀.toAffine) _

lemma resMap_surjective (W₀ : WeierstrassCurve ℤ_[p]) : Function.Surjective (resMap W₀) := by
  rintro (_ | ⟨x, y, h⟩)
  · exact ⟨0, map_zero _⟩
  · let e : ResidueField ℤ_[p] ≃ₐ[ℤ_[p]] ZMod p := resAlgEquiv
    have hx : (e : ResidueField ℤ_[p] →ₐ[ℤ_[p]] ZMod p) (e.symm x) = x := e.apply_symm_apply x
    have hy : (e : ResidueField ℤ_[p] →ₐ[ℤ_[p]] ZMod p) (e.symm y) = y := e.apply_symm_apply y
    have h' : (W₀.toAffine⁄(ResidueField ℤ_[p])).Nonsingular (e.symm x) (e.symm y) :=
      (W₀.toAffine.baseChange_nonsingular (f := (e : ResidueField ℤ_[p] →ₐ[ℤ_[p]] ZMod p))
        e.injective (e.symm x) (e.symm y)).1 (by rw [hx, hy]; exact h)
    refine ⟨Point.some _ _ h', ?_⟩
    exact some_congr hx hy _ _

lemma resMap_some (W₀ : WeierstrassCurve ℤ_[p]) {x y : ResidueField ℤ_[p]}
    (h : (W₀.map (residue ℤ_[p])).toAffine.Nonsingular x y) :
    ∃ h', resMap W₀ (Point.some x y h) = Point.some (PadicInt.residueField x) (PadicInt.residueField y) h' :=
  ⟨_, rfl⟩

lemma not_isInt_of_one_lt {x : ℚ_[p]} (hx : 1 < ‖x‖) : ¬ II.Valued.IsInt ℤ_[p] x := by
  rintro ⟨X, rfl⟩
  have : ‖algebraMap ℤ_[p] ℚ_[p] X‖ ≤ 1 := PadicInt.norm_le_one X
  exact absurd this (not_le.2 hx)

/-- `ReducesTo` is the graph of `redPt` followed by `resMap`. -/
theorem reducesTo_eq (W₀ : WeierstrassCurve ℤ_[p]) (hΔ : IsUnit W₀.Δ)
    (P : (II.ValuedGen.curveK ℚ_[p] W₀).toAffine.Point) (P' : (W₀.map PadicInt.toZMod).toAffine.Point)
    (hPP' : ReducesTo W₀ P P') : resMap W₀ (II.ValuedGen.redPt W₀ hΔ P) = P' := by
  rcases hPP' with ⟨rfl, rfl⟩ | ⟨x, y, h, rfl, hx, rfl⟩ | ⟨x, y, h, h', rfl, rfl⟩
  · exact (congrArg (resMap W₀) (II.ValuedGen.redPt_zero hΔ)).trans (map_zero _)
  · exact (congrArg (resMap W₀)
      (II.ValuedGen.redPt_some_of_not_isInt hΔ h (not_isInt_of_one_lt hx))).trans (map_zero _)
  · obtain ⟨hA, e⟩ := II.ValuedGen.redPt_some_of_alg (K := ℚ_[p]) hΔ h (X := x) (Y := y) rfl rfl
    exact (congrArg (resMap W₀) e).trans rfl

end Bridge

/-- **Lemma 3.2** (Milne, pdf p. 119), for every prime $p$ and every integral Weierstrass model with unit
discriminant. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.2, pdf p. 119"]
theorem lemma3_2 : Lemma3_2 where
  mem_multiples_iff p _ W₀ hΔ n hn P P' hPP' := by
    have hnR : IsUnit (n : ℤ_[p]) := unit_int_of_not_dvd hn
    have hred : resMap W₀ (II.ValuedGen.redPt W₀ hΔ (K := ℚ_[p]) P) = P' :=
      reducesTo_eq W₀ hΔ P P' hPP'
    have key := II.ValuedGen.lemma_3_2_valued (K := ℚ_[p]) hΔ hnR P
    refine key.trans ?_
    constructor
    · rintro ⟨Q', hQ'⟩
      exact ⟨resMap W₀ Q', by rw [← map_zsmul, hQ', hred]⟩
    · rintro ⟨Q'', hQ''⟩
      obtain ⟨Q', rfl⟩ := resMap_surjective W₀ Q''
      refine ⟨Q', resMap_injective W₀ ?_⟩
      rw [map_zsmul, hQ'', hred]

/-- **Lemma 3.5** (Milne, pdf p. 120), for every prime $p$ and every integral Weierstrass model with unit
discriminant. -/
@[kb "milne2006ec" "Ch. IV, Lemma 3.5, pdf p. 120"]
theorem lemma3_5 : Lemma3_5 where
  exists_unramified p _ W₀ hΔ n hn P := by
    have hn0 : n ≠ 0 := fun h0 => hn (h0 ▸ dvd_zero _)
    obtain ⟨K, hfd, hun, hK⟩ := exists_unramified_divPoints_general W₀ hΔ hn P
    have hell : (W₀.baseChange (AlgebraicClosure ℚ_[p])).IsElliptic := by
      rw [WeierstrassCurve.isElliptic_iff]
      show IsUnit (W₀.map (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]))).Δ
      rw [WeierstrassCurve.map_Δ]
      exact hΔ.map _
    obtain ⟨QL, hQL⟩ := lemma2_1.surjective (AlgebraicClosure ℚ_[p])
      (W₀.baseChange (AlgebraicClosure ℚ_[p])) n hn0
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

/-- **Proposition 3.6** (Milne, pdf p. 120), for every prime $p$: `prop_3_6_general` (the cocycle-level
argument of `exists_unramified_cocycle_eq_zero` with `exists_unramified_divPoints_general`). -/
@[kb "milne2006ec" "Ch. IV, Prop. 3.6, pdf p. 120"]
theorem prop3_6 : Prop3_6 where
  exists_unramified W₀ _ n hn γ hγ p _ hpΔ := prop_3_6_general W₀ n hn γ hγ p hpΔ

end NumberFieldKB.MilneEC
