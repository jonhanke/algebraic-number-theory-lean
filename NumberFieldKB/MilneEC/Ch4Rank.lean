import NumberFieldKB.MilneEC.Ch4Selmer
import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Cases
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Milne, Elliptic Curves, Chapter IV §5: the problem of computing the rank of $E(\mathbb{Q})$

J. S. Milne, *Elliptic Curves* (2006; bibliography key `milne2006ec`), Chapter IV, Section 5.  Locators give the
pdf page of the text `ectext6` (printed page = pdf page − 8).

Conventions and deviations.
* The **rank** of $E(K)$ is `Module.finrank ℤ E(K)`; `rank_spec` shows $E(K) \cong E(K)_{\mathrm{tors}} \oplus \mathbb{Z}^r$
  with $r$ the rank, when $E(K)$ is finitely generated.
* Milne's $S^{(2,n)}(E/\mathbb{Q})$, the image of $S^{(2^n)}$ in $S^{(2)}$ ($n \ge 1$), is `selmerImage K W m` with
  $n = m + 1$: the image of $S^{(2^{m+1})}$ under the map induced by $2^m : E_{2^{m+1}} \to E_2$.
* Proposition 5.1 is corrected: Milne's condition "no nonzero element of $Ш$ divisible by all powers of 2" must be
  restricted to elements of 2-power order, since elements of odd order are always divisible by every power of 2.
* For Propositions 5.5 and 5.6 the curve is $Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ with integers $\alpha, \beta,
  \gamma$ (`cubicCurve`); it is an elliptic curve exactly when the roots are distinct (`cubicCurve_isElliptic_iff`).
-/

open CategoryTheory groupCohomology WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace NumberFieldKB.MilneEC

/-! ## The rank -/

section Rank

variable {K : Type} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- The **rank** of $E(K)$ (pdf p. 134): the rank of the finitely generated abelian group $E(K)$. -/
@[kb "milne2006ec" "Ch. IV, §5, definition of the rank of E(Q), pdf p. 134"]
noncomputable def rank : ℕ := Module.finrank ℤ W.toAffine.Point

/-- Structure of a finitely generated abelian group: the torsion subgroup times a free group of rank
`Module.finrank ℤ`. -/
theorem addEquiv_torsion_prod_free (M : Type*) [AddCommGroup M] [AddGroup.FG M] :
    Nonempty (M ≃+ AddCommGroup.torsion M × (Fin (Module.finrank ℤ M) → ℤ)) := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr ‹_›
  have hfr : Module.finrank ℤ (M ⧸ Submodule.torsion ℤ M) = Module.finrank ℤ M := by
    have := finrank_quotient_torsion_eq (M := M)
    rwa [← Submodule.torsion_int, Submodule.toAddSubgroup_toIntSubmodule] at this
  have : Module.Free ℤ (M ⧸ Submodule.torsion ℤ M) := inferInstance
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Submodule.torsion ℤ M).mkQ
    LinearMap.id (Submodule.torsion ℤ M).mkQ_surjective
  have e1 := lequivProdOfRightSplitExact (j := (Submodule.torsion ℤ M).subtype)
    (g := (Submodule.torsion ℤ M).mkQ) (f := f) (Submodule.torsion ℤ M).injective_subtype
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf
  let b := Module.finBasis ℤ (M ⧸ Submodule.torsion ℤ M)
  let e2 : (M ⧸ Submodule.torsion ℤ M) ≃ₗ[ℤ] (Fin (Module.finrank ℤ M) → ℤ) :=
    (b.equivFun).trans (LinearEquiv.funCongrLeft ℤ ℤ (finCongr hfr)).symm
  have h : (Submodule.torsion ℤ M).toAddSubgroup = AddCommGroup.torsion M := by
    rw [← Submodule.torsion_int]
  let e3 : (Submodule.torsion ℤ M) ≃+ AddCommGroup.torsion M := AddEquiv.addSubgroupCongr h
  exact ⟨e1.symm.toAddEquiv.trans (e3.prodCongr e2.toAddEquiv)⟩

/-- Milne (pdf p. 134): if $E(K)$ is finitely generated, then $E(K) \cong E(K)_{\mathrm{tors}} \oplus \mathbb{Z}^r$
with $r$ the rank. -/
@[kb "milne2006ec" "Ch. IV, §5, E(Q) ≅ E(Q)_tors ⊕ Z^r, pdf p. 134"]
theorem rank_spec [AddGroup.FG W.toAffine.Point] :
    Nonempty (W.toAffine.Point ≃+ AddCommGroup.torsion W.toAffine.Point × (Fin (rank W) → ℤ)) :=
  addEquiv_torsion_prod_free W.toAffine.Point

end Rank

/-! ## Counting $M/2M$ -/

/-- The torsion subgroup of a finitely generated abelian group is finite. -/
theorem finite_torsion_of_fg (M : Type*) [AddCommGroup M] [AddGroup.FG M] :
    Finite (AddCommGroup.torsion M) := by
  have : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr ‹_›
  have : Module.Finite ℤ (AddCommGroup.torsion M) :=
    inferInstanceAs (Module.Finite ℤ (AddCommGroup.torsion M).toIntSubmodule)
  refine Module.finite_of_fg_torsion _ ?_
  rw [← isAddTorsion_iff_isTorsion_int]
  intro x
  have := x.2
  rw [AddCommGroup.mem_torsion, isOfFinAddOrder_iff_nsmul_eq_zero] at this
  obtain ⟨n, hn, h⟩ := this
  exact (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨n, hn, Subtype.ext h⟩

/-- For a finite abelian group, the index of $2G$ equals the number of elements killed by $2$. -/
theorem card_quot_two_eq {G : Type*} [AddCommGroup G] [Finite G] :
    Nat.card (G ⧸ multiples G 2) = Nat.card (zsmulAddGroupHom (α := G) 2).ker := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (zsmulAddGroupHom (α := G) 2).ker
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (multiples G 2)
  have h3 : Nat.card (G ⧸ (zsmulAddGroupHom (α := G) 2).ker) = Nat.card (multiples G 2) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange _).toEquiv
  have hpos : 0 < Nat.card (multiples G 2) := Nat.card_pos
  rw [h3] at h1
  have : Nat.card (G ⧸ multiples G 2) * Nat.card (multiples G 2) =
      Nat.card (zsmulAddGroupHom (α := G) 2).ker * Nat.card (multiples G 2) := by
    rw [← h2, h1, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right hpos this

/-- If a finitely generated abelian group $M$ has four distinct elements killed by $2$, then
$\#(M/2M) \ge 2^{r+2}$, where $r$ is the rank of $M$. -/
theorem two_pow_le_card_quot_two {M : Type*} [AddCommGroup M] [AddGroup.FG M]
    (f : Fin 4 → M) (hf : Function.Injective f) (h2 : ∀ i, (2 : ℤ) • f i = 0) :
    2 ^ (Module.finrank ℤ M + 2) ≤ Nat.card (M ⧸ multiples M 2) := by
  obtain ⟨e⟩ := addEquiv_torsion_prod_free M
  have hTfin := finite_torsion_of_fg M
  have hMfin := finite_quotient_multiples_of_fg (M := M) (two_ne_zero)
  set T := AddCommGroup.torsion M with hT
  set r := Module.finrank ℤ M with hr
  -- the surjection onto T/2T × (Z/2)^r
  let σ : M →+ (T ⧸ multiples T 2) × (Fin r → ZMod 2) :=
    ((((QuotientAddGroup.mk' (multiples T 2)).comp (AddMonoidHom.fst T (Fin r → ℤ))).prod
      ((AddMonoidHom.compLeft (Int.castAddHom (ZMod 2)) (Fin r)).comp (AddMonoidHom.snd T (Fin r → ℤ)))).comp
      e.toAddMonoidHom)
  have hσsurj : Function.Surjective σ := by
    rintro ⟨q, g⟩
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨e.symm (t, fun i => ((g i).val : ℤ)), ?_⟩
    simp only [σ, AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply]
    refine Prod.ext rfl ?_
    funext i
    simp
  have hσ2 : ∀ x : M, σ ((2 : ℤ) • x) = 0 := by
    intro x
    rw [map_zsmul]
    generalize σ x = y
    obtain ⟨q, g⟩ := y
    refine Prod.ext ?_ ?_
    · obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
      show (2 : ℤ) • (QuotientAddGroup.mk t : T ⧸ multiples T 2) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact ⟨t, rfl⟩
    · funext i
      show (2 : ℤ) • g i = 0
      have : (2 : ZMod 2) = 0 := rfl
      rw [zsmul_eq_mul]
      simp [this]
  have hlift : Function.Surjective (QuotientAddGroup.lift (multiples M 2) σ (by
      rintro _ ⟨x, rfl⟩
      exact hσ2 x)) := by
    intro y
    obtain ⟨x, rfl⟩ := hσsurj y
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hcard := Nat.card_le_card_of_surjective _ hlift
  have hT2 : 4 ≤ Nat.card (T ⧸ multiples T 2) := by
    rw [card_quot_two_eq]
    let g : Fin 4 → (zsmulAddGroupHom (α := T) 2).ker := fun i =>
      ⟨(e (f i)).1, by
        show (2 : ℤ) • (e (f i)).1 = 0
        have h := congrArg Prod.fst (show (2 : ℤ) • e (f i) = 0 by rw [← map_zsmul, h2, map_zero])
        simpa using h⟩
    have hginj : Function.Injective g := by
      intro i j hij
      have h1 : (e (f i)).1 = (e (f j)).1 := congrArg Subtype.val hij
      have hs : ∀ k, (e (f k)).2 = 0 := by
        intro k
        have h := congrArg Prod.snd (show (2 : ℤ) • e (f k) = 0 by rw [← map_zsmul, h2, map_zero])
        funext l
        have := congrFun h l
        simp at this
        simpa using this
      apply hf
      apply e.injective
      exact Prod.ext h1 (by rw [hs i, hs j])
    have := Nat.card_le_card_of_injective g hginj
    simpa using this
  have hprod : Nat.card ((T ⧸ multiples T 2) × (Fin r → ZMod 2)) =
      Nat.card (T ⧸ multiples T 2) * 2 ^ r := by
    rw [Nat.card_prod]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
    simp
  calc 2 ^ (r + 2) = 2 ^ r * 4 := by ring
    _ ≤ 2 ^ r * Nat.card (T ⧸ multiples T 2) := Nat.mul_le_mul_left _ hT2
    _ = Nat.card ((T ⧸ multiples T 2) × (Fin r → ZMod 2)) := by rw [hprod, mul_comm]
    _ ≤ _ := hcard

/-- If a function `g` from `M` to a finite set separates the cosets of $2M$ (equal values force a difference in
$2M$), then $\#(M/2M) \le \#F$. -/
theorem card_quot_two_le {M : Type*} [AddCommGroup M] {F : Type*} [Finite F] (g : M → F)
    (hg : ∀ P Q, g P = g Q → P - Q ∈ multiples M 2) : Nat.card (M ⧸ multiples M 2) ≤ Nat.card F := by
  refine Nat.card_le_card_of_injective (fun c : M ⧸ multiples M 2 => g c.out) ?_
  intro c d hcd
  have h := hg _ _ hcd
  rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d]
  exact (QuotientAddGroup.eq_iff_sub_mem).2 h

/-- If a map to a finite set has fibres inside the cosets of $2M$, then $M/2M$ is finite. -/
theorem finite_quot_two_of {M : Type*} [AddCommGroup M] {F : Type*} [Finite F] (g : M → F)
    (hg : ∀ P Q, g P = g Q → P - Q ∈ multiples M 2) : Finite (M ⧸ multiples M 2) := by
  refine Finite.of_injective (fun c : M ⧸ multiples M 2 => g c.out) ?_
  intro c d hcd
  have h := hg _ _ hcd
  rw [← QuotientAddGroup.out_eq' c, ← QuotientAddGroup.out_eq' d]
  exact (QuotientAddGroup.eq_iff_sub_mem).2 h

/-! ## Proposition 5.1 and Remark 5.2 -/

section Selmer

variable {K : Type} [Field K] [DecidableEq K] [NumberField K] (W : WeierstrassCurve K)

/-- Multiplication by $2^m$, a map of Galois modules $E_{2^{m+1}} \to E_2$. -/
noncomputable def torsionTwoPowDown (L : Type) [Field L] [Algebra K L] (m : ℕ) :
    torsionRep W L ((2 : ℤ) ^ (m + 1)) ⟶ torsionRep W L 2 :=
  Rep.ofHom ⟨((zsmulAddGroupHom (α := (W.toAffine⁄L).Point) ((2 : ℤ) ^ m)).comp
      (torsionPoints W L ((2 : ℤ) ^ (m + 1))).subtype |>.codRestrict (torsionPoints W L 2) (fun P => by
        have hP : ((2 : ℤ) ^ (m + 1)) • (P : (W.toAffine⁄L).Point) = 0 := P.2
        show (2 : ℤ) • (((2 : ℤ) ^ m) • (P : (W.toAffine⁄L).Point)) = 0
        rw [← mul_smul, ← pow_succ']
        exact hP)).toIntLinearMap, fun σ => by
    ext P
    exact (map_zsmul (Point.map (W' := W.toAffine) (σ : L →ₐ[K] L)) ((2 : ℤ) ^ m)
      (P : (W.toAffine⁄L).Point)).symm⟩

/-- Milne's $S^{(2,m+1)}(E/K)$ (pdf p. 135): the image of $S^{(2^{m+1})}(E/K)$ in $H^1(K, E_2)$ under the map induced
by $2^m : E_{2^{m+1}} \to E_2$. -/
@[kb "milne2006ec" "Ch. IV, §5, definition of S^(2,n)(E/Q), pdf p. 135"]
noncomputable def selmerImage (m : ℕ) : AddSubgroup (H1 (torsionRep W (AlgebraicClosure K) 2)) :=
  (selmerGroup K W ((2 : ℤ) ^ (m + 1))).map
    (map (MonoidHom.id _) (torsionTwoPowDown W (AlgebraicClosure K) m) 1).hom.toAddMonoidHom

omit [DecidableEq K] [NumberField K] in
/-- Multiplication by an integer on the points induces the scalar multiplication on $H^1$. -/
theorem rank_map_pointsMul_H1 (L : Type) [Field L] [Algebra K L] (n : ℤ) (x : H1 (pointsRep W L)) :
    map (MonoidHom.id _) (pointsMul W L n) 1 x = n • x := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (H1π (pointsRep W L))).1 inferInstance x
  have h : map (MonoidHom.id _) (pointsMul W L n) 1 (H1π (pointsRep W L) c) =
      H1π (pointsRep W L) (n • c) := by
    rw [H1π_comp_map_apply]
    congr 1
  rw [h, map_zsmul]

omit [DecidableEq K] [NumberField K] in
/-- The two inclusions of torsion into the points are compatible with multiplication by $2^m$. -/
theorem torsionTwoPowDown_incl (L : Type) [Field L] [Algebra K L] (m : ℕ) :
    torsionTwoPowDown W L m ≫ torsionIncl W L 2 =
      torsionIncl W L ((2 : ℤ) ^ (m + 1)) ≫ pointsMul W L ((2 : ℤ) ^ m) := by
  ext P
  rfl

/-- The map of short exact sequences from $0 \to E_{2^{m+1}} \to E \to E \to 0$ (multiplication by $2^{m+1}$) to
$0 \to E_2 \to E \to E \to 0$ (multiplication by $2$), given by $2^m$ on $E_{2^{m+1}}$ and on the middle term and
the identity on the last term. -/
noncomputable def kummerComplexDown (L : Type) [Field L] [Algebra K L] (m : ℕ) :
    kummerComplex W L ((2 : ℤ) ^ (m + 1)) ⟶ kummerComplex W L 2 where
  τ₁ := torsionTwoPowDown W L m
  τ₂ := pointsMul W L ((2 : ℤ) ^ m)
  τ₃ := 𝟙 _
  comm₁₂ := torsionTwoPowDown_incl W L m
  comm₂₃ := by
    ext P
    show (2 : ℤ) • ((2 : ℤ) ^ m • P) = ((2 : ℤ) ^ (m + 1)) • P
    rw [← mul_smul, ← pow_succ']

/-- The Kummer maps are compatible with multiplication by $2^m$. -/
theorem kummerMap_twoPowDown (h21 : Lemma2_1) [W.IsElliptic] (m : ℕ) (P : W.toAffine.Point) :
    map (MonoidHom.id _) (torsionTwoPowDown W (AlgebraicClosure K) m) 1
        (kummerMap W h21 ((2 : ℤ) ^ (m + 1)) (pow_ne_zero _ two_ne_zero) P) =
      kummerMap W h21 2 two_ne_zero P := by
  have h := δ_naturality (kummerComplex_shortExact W h21 (AlgebraicClosure K)
    ((2 : ℤ) ^ (m + 1)) (pow_ne_zero _ two_ne_zero))
    (kummerComplex_shortExact W h21 (AlgebraicClosure K) 2 two_ne_zero)
    (kummerComplexDown W (AlgebraicClosure K) m) 0 1 rfl
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) (pointsToH0 W (AlgebraicClosure K) P)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (kummerComplexDown W (AlgebraicClosure K) m).τ₃ = 𝟙 _ := rfl
  rw [h3, groupCohomology.map_id] at h2
  exact h2

/-- Compatibility of $H^1(K, E_{2^{m+1}}) \to H^1(K, E_2) \to H^1(K, E)$ with multiplication by $2^m$. -/
theorem torsionToPointsH1_twoPowDown (m : ℕ) (s : H1 (torsionRep W (AlgebraicClosure K) ((2 : ℤ) ^ (m + 1)))) :
    torsionToPointsH1 W (AlgebraicClosure K) 2
        (map (MonoidHom.id _) (torsionTwoPowDown W (AlgebraicClosure K) m) 1 s) =
      (2 : ℤ) ^ m • torsionToPointsH1 W (AlgebraicClosure K) ((2 : ℤ) ^ (m + 1)) s := by
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (groupCohomology.map_id_comp (torsionTwoPowDown W (AlgebraicClosure K) m)
      (torsionIncl W (AlgebraicClosure K) 2) 1)) s
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (groupCohomology.map_id_comp (torsionIncl W (AlgebraicClosure K) ((2 : ℤ) ^ (m + 1)))
      (pointsMul W (AlgebraicClosure K) ((2 : ℤ) ^ m)) 1)) s
  rw [torsionTwoPowDown_incl] at e1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e2, rank_map_pointsMul_H1] at e1
  exact e1.symm

/-- A class of $H^1(K, E_2)$ lies in $S^{(2,m+1)}(E/K)$ exactly when its image in $H^1(K, E)$ is $2^m y$ with
$y \in Ш(E/K)$ killed by $2^{m+1}$. -/
theorem mem_selmerImage_iff (h21 : Lemma2_1) [W.IsElliptic] (m : ℕ)
    (x : H1 (torsionRep W (AlgebraicClosure K) 2)) :
    x ∈ selmerImage W m ↔ ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ (m + 1) • y = 0 ∧
      torsionToPointsH1 W (AlgebraicClosure K) 2 x = (2 : ℤ) ^ m • y := by
  have hn : ((2 : ℤ) ^ (m + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  obtain ⟨hA, hB, -⟩ := exact_23 K W h21 ((2 : ℤ) ^ (m + 1)) hn
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hy : torsionToPointsH1 W (AlgebraicClosure K) ((2 : ℤ) ^ (m + 1)) s ∈
        tateShafarevich K W ⊓ (zsmulAddGroupHom (α := H1 (pointsRep W (AlgebraicClosure K)))
          ((2 : ℤ) ^ (m + 1))).ker := hB ▸ AddSubgroup.mem_map_of_mem _ hs
    refine ⟨_, hy.1, hy.2, ?_⟩
    exact torsionToPointsH1_twoPowDown W m s
  · rintro ⟨y, hyS, hy0, hxy⟩
    have hy : y ∈ (selmerGroup K W ((2 : ℤ) ^ (m + 1))).map
        (torsionToPointsH1 W (AlgebraicClosure K) ((2 : ℤ) ^ (m + 1))) := by
      rw [hB]
      exact ⟨hyS, hy0⟩
    obtain ⟨s, hs, rfl⟩ := hy
    have h0 : torsionToPointsH1 W (AlgebraicClosure K) 2
        (x - map (MonoidHom.id _) (torsionTwoPowDown W (AlgebraicClosure K) m) 1 s) = 0 := by
      rw [map_sub, hxy, torsionToPointsH1_twoPowDown W m s, sub_self]
    have hker : x - map (MonoidHom.id _) (torsionTwoPowDown W (AlgebraicClosure K) m) 1 s ∈
        (kummerMap W h21 2 two_ne_zero).range := by
      rw [(exact_22 W h21 2 two_ne_zero).2.1]
      exact h0
    obtain ⟨P, hP⟩ := hker
    refine ⟨s + kummerMap W h21 ((2 : ℤ) ^ (m + 1)) hn P, add_mem hs (hA ⟨P, rfl⟩), ?_⟩
    show map (MonoidHom.id _) (torsionTwoPowDown W (AlgebraicClosure K) m) 1
      (s + kummerMap W h21 ((2 : ℤ) ^ (m + 1)) hn P) = x
    rw [map_add, kummerMap_twoPowDown, hP]
    abel

/-- A nonzero element killed by a power of 2 has a multiple (by a power of 2) of order exactly 2. -/
theorem exists_pred_order_two {X : Type*} [AddCommGroup X] (z : X) (hz : z ≠ 0) (k : ℕ)
    (hk : (2 : ℤ) ^ k • z = 0) : ∃ j : ℕ, (2 : ℤ) ^ j • z ≠ 0 ∧ (2 : ℤ) ^ (j + 1) • z = 0 := by
  induction k with
  | zero => exact absurd (by simpa using hk) hz
  | succ k ih =>
    by_cases h : (2 : ℤ) ^ k • z = 0
    · exact ih h
    · exact ⟨k, h, hk⟩

/-- If the elements of a subgroup killed by $2$ form a finite set, then so do those killed by $2^k$. -/
theorem finite_twoPow_torsion {X : Type*} [AddCommGroup X] (S : AddSubgroup X)
    (h1 : {z | z ∈ S ∧ (2 : ℤ) • z = 0}.Finite) (k : ℕ) :
    {z | z ∈ S ∧ (2 : ℤ) ^ k • z = 0}.Finite := by
  induction k with
  | zero =>
    refine (Set.finite_singleton (0 : X)).subset ?_
    rintro z ⟨-, hz⟩
    simpa using hz
  | succ k ih =>
    have hU : {z | z ∈ S ∧ (2 : ℤ) ^ (k + 1) • z = 0} ⊆
        ⋃ w ∈ {z | z ∈ S ∧ (2 : ℤ) ^ k • z = 0},
          {z | z ∈ S ∧ (2 : ℤ) ^ (k + 1) • z = 0 ∧ (2 : ℤ) • z = w} := by
      rintro z ⟨hzS, hz⟩
      refine Set.mem_biUnion (x := (2 : ℤ) • z) ⟨zsmul_mem hzS _, ?_⟩ ⟨hzS, hz, rfl⟩
      rw [← mul_smul, ← pow_succ]
      exact hz
    refine Set.Finite.subset (ih.biUnion fun w _ => ?_) hU
    by_cases hne : ∃ z0, z0 ∈ S ∧ (2 : ℤ) ^ (k + 1) • z0 = 0 ∧ (2 : ℤ) • z0 = w
    · obtain ⟨z0, hz0S, hz0, hz0w⟩ := hne
      refine (h1.image (fun t => z0 + t)).subset ?_
      rintro z ⟨hzS, hz, hzw⟩
      refine ⟨z - z0, ⟨sub_mem hzS hz0S, ?_⟩, by simp⟩
      rw [smul_sub, hzw, hz0w, sub_self]
    · refine Set.Finite.subset (Set.finite_empty) ?_
      rintro z ⟨hzS, hz, hzw⟩
      exact absurd ⟨z, hzS, hz, hzw⟩ hne

/-- **Proposition 5.1** (pdf p. 135), corrected.  (a) The image of $E(K)/2E(K)$ in $S^{(2)}(E/K)$ lies in every
$S^{(2,n)}(E/K)$.  (b) It equals $\bigcap_n S^{(2,n)}(E/K)$ if and only if no nonzero element of $Ш(E/K)$ of
2-power order is divisible in $Ш(E/K)$ by all powers of 2.  (Milne omits "of 2-power order"; without it the "only if"
fails as soon as $Ш(E/K)$ has a nonzero element of odd order.) -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.1, pdf p. 135"]
theorem prop_5_1 (h21 : Lemma2_1) [W.IsElliptic] :
    (∀ m : ℕ, (kummerMap W h21 2 two_ne_zero).range ≤ selmerImage W m) ∧
      ((⨅ m : ℕ, selmerImage W m) = (kummerMap W h21 2 two_ne_zero).range ↔
        ∀ z ∈ tateShafarevich K W, (∃ k : ℕ, (2 : ℤ) ^ k • z = 0) →
          (∀ n : ℕ, ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z) → z = 0) := by
  have hR : ∀ x, x ∈ (kummerMap W h21 2 two_ne_zero).range ↔
      torsionToPointsH1 W (AlgebraicClosure K) 2 x = 0 := by
    intro x
    rw [(exact_22 W h21 2 two_ne_zero).2.1]
    rfl
  have ha : ∀ m : ℕ, (kummerMap W h21 2 two_ne_zero).range ≤ selmerImage W m := by
    intro m x hx
    rw [mem_selmerImage_iff W h21]
    exact ⟨0, zero_mem _, zsmul_zero _, by rw [(hR x).1 hx]; exact (zsmul_zero _).symm⟩
  refine ⟨ha, ?_⟩
  constructor
  · intro heq z hz ⟨k, hk⟩ hdiv
    by_contra hz0
    obtain ⟨j, hj1, hj2⟩ := exists_pred_order_two z hz0 k hk
    have hz'S : (2 : ℤ) ^ j • z ∈ tateShafarevich K W := zsmul_mem hz _
    have hz'2 : (2 : ℤ) • ((2 : ℤ) ^ j • z) = 0 := by rw [← mul_smul, ← pow_succ']; exact hj2
    obtain ⟨-, hB, -⟩ := exact_23 K W h21 2 two_ne_zero
    have hz'mem : (2 : ℤ) ^ j • z ∈ (selmerGroup K W 2).map
        (torsionToPointsH1 W (AlgebraicClosure K) 2) := by
      rw [hB]
      exact ⟨hz'S, hz'2⟩
    obtain ⟨x, -, hx⟩ := hz'mem
    have hxI : x ∈ ⨅ m : ℕ, selmerImage W m := by
      rw [AddSubgroup.mem_iInf]
      intro m
      rw [mem_selmerImage_iff W h21]
      obtain ⟨w, hwS, hw⟩ := hdiv m
      refine ⟨(2 : ℤ) ^ j • w, zsmul_mem hwS _, ?_, ?_⟩
      · calc (2 : ℤ) ^ (m + 1) • (2 : ℤ) ^ j • w = (2 : ℤ) • ((2 : ℤ) ^ j • (2 : ℤ) ^ m • w) := by
              rw [← mul_smul, ← mul_smul, ← mul_smul]
              congr 1
              ring
          _ = 0 := by rw [hw]; exact hz'2
      · rw [hx, smul_comm ((2 : ℤ) ^ m) ((2 : ℤ) ^ j) w, hw]
    rw [heq] at hxI
    exact hj1 (by rw [← hx]; exact (hR x).1 hxI)
  · intro hcond
    refine le_antisymm (fun x hx => ?_) (le_iInf ha)
    rw [AddSubgroup.mem_iInf] at hx
    rw [hR]
    have h0 := (mem_selmerImage_iff W h21 0 x).1 (hx 0)
    obtain ⟨y0, hy0S, hy0, hxy0⟩ := h0
    refine hcond _ ?_ ⟨1, ?_⟩ ?_
    · rw [hxy0, pow_zero, one_smul]; exact hy0S
    · rw [hxy0, pow_zero, one_smul]; simpa using hy0
    · intro n
      obtain ⟨y, hyS, -, hxy⟩ := (mem_selmerImage_iff W h21 n x).1 (hx n)
      exact ⟨y, hyS, hxy.symm⟩

/-- Remark 5.2 given only the finiteness of $S^{(2)}(E/K)$ (the only use of Theorem 3.1 in its proof). -/
theorem remark_5_2_of_finite (h21 : Lemma2_1) [W.IsElliptic] (hfin : Finite (selmerGroup K W 2))
    (hdiv : ∀ z ∈ tateShafarevich K W, (∃ k : ℕ, (2 : ℤ) ^ k • z = 0) →
      (∀ n : ℕ, ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z) → z = 0) :
    {z | z ∈ tateShafarevich K W ∧ ∃ k : ℕ, (2 : ℤ) ^ k • z = 0}.Finite ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀, selmerImage W m = (kummerMap W h21 2 two_ne_zero).range := by
  have hR : ∀ x, x ∈ (kummerMap W h21 2 two_ne_zero).range ↔
      torsionToPointsH1 W (AlgebraicClosure K) 2 x = 0 := by
    intro x
    rw [(exact_22 W h21 2 two_ne_zero).2.1]
    rfl
  -- the 2-torsion of the Tate-Shafarevich group is finite
  have hF2 : {z | z ∈ tateShafarevich K W ∧ (2 : ℤ) • z = 0}.Finite := by
    obtain ⟨-, hB, -⟩ := exact_23 K W h21 2 two_ne_zero
    have : Finite (selmerGroup K W 2) := hfin
    refine ((Set.toFinite (selmerGroup K W 2 : Set _)).image
      (torsionToPointsH1 W (AlgebraicClosure K) 2)).subset ?_
    intro z hz
    have hz' : z ∈ (selmerGroup K W 2).map (torsionToPointsH1 W (AlgebraicClosure K) 2) := by
      rw [hB]
      exact ⟨hz.1, hz.2⟩
    obtain ⟨x, hx, rfl⟩ := hz'
    exact ⟨x, hx, rfl⟩
  -- no nonzero 2-torsion element is divisible by all large powers of 2
  set nz : H1 (pointsRep W (AlgebraicClosure K)) → ℕ := fun z =>
    if h : ∃ n : ℕ, ¬ ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z then Classical.choose h else 0 with hnz
  set N : ℕ := hF2.toFinset.sup nz with hN
  have hN2 : ∀ z ∈ tateShafarevich K W, (2 : ℤ) • z = 0 → ∀ n ≥ N,
      (∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z) → z = 0 := by
    intro z hzS hz2 n hn ⟨y, hyS, hy⟩
    by_contra hz0
    have hex : ∃ n : ℕ, ¬ ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z := by
      by_contra hne
      push_neg at hne
      exact hz0 (hdiv z hzS ⟨1, by simpa using hz2⟩ hne)
    have hle : nz z ≤ N := Finset.le_sup (f := nz) (by simpa using ⟨hzS, hz2⟩)
    have hnzz : nz z = Classical.choose hex := by simp only [hnz, dif_pos hex]
    obtain ⟨n0, hn0, hspec⟩ : ∃ n0, nz z = n0 ∧ ¬ ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n0 • y = z :=
      ⟨_, hnzz, Classical.choose_spec hex⟩
    apply hspec
    refine ⟨(2 : ℤ) ^ (n - n0) • y, zsmul_mem hyS _, ?_⟩
    have hsum : n0 + (n - n0) = n := by omega
    rw [← mul_smul, ← pow_add, hsum]
    exact hy
  have hT : ∀ z ∈ tateShafarevich K W, (∃ k : ℕ, (2 : ℤ) ^ k • z = 0) → (2 : ℤ) ^ N • z = 0 := by
    rintro z hzS ⟨k, hk⟩
    by_contra hw0
    have hwk : (2 : ℤ) ^ k • ((2 : ℤ) ^ N • z) = 0 := by
      rw [smul_comm, hk, zsmul_zero]
    obtain ⟨j, hj1, hj2⟩ := exists_pred_order_two _ hw0 k hwk
    refine hj1 (hN2 _ (zsmul_mem (zsmul_mem hzS _) _) ?_ N le_rfl
      ⟨(2 : ℤ) ^ j • z, zsmul_mem hzS _, ?_⟩)
    · rw [← mul_smul, ← pow_succ']
      exact hj2
    · exact smul_comm _ _ _
  refine ⟨(finite_twoPow_torsion (tateShafarevich K W) hF2 N).subset ?_, N, fun m hm => ?_⟩
  · rintro z ⟨hzS, hz⟩
    exact ⟨hzS, hT z hzS hz⟩
  · refine le_antisymm (fun x hx => ?_) ((prop_5_1 W h21).1 m)
    obtain ⟨y, hyS, hy0, hxy⟩ := (mem_selmerImage_iff W h21 m x).1 hx
    rw [hR, hxy]
    have := hT y hyS ⟨m + 1, hy0⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, mul_comm, mul_smul, this, zsmul_zero]

/-- **Remark 5.2** (pdf p. 135).  If no nonzero element of $Ш(E/K)$ of 2-power order is divisible in $Ш(E/K)$ by
all powers of 2, then the 2-primary component of $Ш(E/K)$ is finite, and $S^{(2,n)}(E/K)$ equals the image of
$E(K)/2E(K)$ for all large $n$. -/
@[kb "milne2006ec" "Ch. IV, Remark 5.2, pdf p. 135"]
theorem remark_5_2 (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) [W.IsElliptic]
    (hdiv : ∀ z ∈ tateShafarevich K W, (∃ k : ℕ, (2 : ℤ) ^ k • z = 0) →
      (∀ n : ℕ, ∃ y ∈ tateShafarevich K W, (2 : ℤ) ^ n • y = z) → z = 0) :
    {z | z ∈ tateShafarevich K W ∧ ∃ k : ℕ, (2 : ℤ) ^ k • z = 0}.Finite ∧
      ∃ m₀ : ℕ, ∀ m ≥ m₀, selmerImage W m = (kummerMap W h21 2 two_ne_zero).range :=
  remark_5_2_of_finite W h21 (h31.finite K W 2 two_ne_zero) hdiv

end Selmer

/-- **Conjecture 5.3** (pdf p. 135): the Tate–Shafarevich group of an elliptic curve over a number field is finite.
(Recorded as a proposition; it is not assumed anywhere.) -/
@[kb "milne2006ec" "Ch. IV, Conjecture 5.3, pdf p. 135"]
def Conjecture5_3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    Finite (tateShafarevich K W)

/-- $\mathbb{Q}/\mathbb{Z}$. -/
abbrev RatModInt : Type := ℚ ⧸ (Int.castAddHom ℚ).range

/-- **Remark 5.4 (a)** (pdf p. 136), a named statement (Cassels 1962): if $Ш(E/K)$ is finite, it carries a
nondegenerate alternating pairing $Ш \times Ш \to \mathbb{Q}/\mathbb{Z}$.  (Milne states it over $\mathbb{Q}$; Cassels's
theorem holds over every number field.) -/
@[kb "milne2006ec" "Ch. IV, Remark 5.4 (a), pdf p. 136"]
structure Remark5_4a : Prop where
  pairing : ∀ (K : Type) [Field K] [NumberField K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic],
    Finite (tateShafarevich K W) →
      ∃ ψ : tateShafarevich K W →+ tateShafarevich K W →+ RatModInt,
        (∀ x, ψ x x = 0) ∧ Function.Injective ψ

/-- The class of $1/n$ in $\mathbb{Q}/\mathbb{Z}$. -/
noncomputable def ratModIntGen (n : ℕ) : RatModInt := QuotientAddGroup.mk ((n : ℚ)⁻¹)

theorem ratModInt_mk_eq_zero (q : ℚ) :
    (QuotientAddGroup.mk q : RatModInt) = 0 ↔ ∃ m : ℤ, (m : ℚ) = q := by
  rw [QuotientAddGroup.eq_zero_iff]
  simp [AddSubgroup.mem_zmultiples_iff]

/-- The class of $1/n$ has order exactly $n$ in $\mathbb{Q}/\mathbb{Z}$. -/
theorem addOrderOf_ratModIntGen (n : ℕ) (hn : 0 < n) : addOrderOf (ratModIntGen n) = n := by
  rw [addOrderOf_eq_iff hn]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨?_, fun m hm hm0 => ?_⟩
  · unfold ratModIntGen
    rw [← QuotientAddGroup.mk_nsmul, ratModInt_mk_eq_zero]
    exact ⟨1, by simp [hn']⟩
  · unfold ratModIntGen
    rw [← QuotientAddGroup.mk_nsmul]
    intro h
    rw [ratModInt_mk_eq_zero] at h
    obtain ⟨k, hk⟩ := h
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm0
    have hmn : (m : ℚ) < n := by exact_mod_cast hm
    have h1 : (0 : ℚ) < k := by
      rw [hk, nsmul_eq_mul]; positivity
    have h2 : (k : ℚ) < 1 := by
      rw [hk, nsmul_eq_mul, mul_inv_lt_iff₀ (by exact_mod_cast hn)]; simpa using hmn
    have h1' : 0 < k := by exact_mod_cast h1
    have h2' : k < 1 := by exact_mod_cast h2
    omega

/-- The elements of $\mathbb{Q}/\mathbb{Z}$ killed by $n$ are the multiples of the class of $1/n$. -/
theorem mem_zmultiples_ratModIntGen (n : ℕ) (hn : 0 < n) (v : RatModInt) (hv : n • v = 0) :
    v ∈ AddSubgroup.zmultiples (ratModIntGen n) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  induction v using QuotientAddGroup.induction_on with
  | H q =>
    rw [← QuotientAddGroup.mk_nsmul, ratModInt_mk_eq_zero] at hv
    obtain ⟨m, hm⟩ := hv
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨m, ?_⟩
    unfold ratModIntGen
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    rw [nsmul_eq_mul] at hm
    rw [zsmul_eq_mul]
    field_simp
    linarith

/-- An element of order exactly $n$ in $\mathbb{Q}/\mathbb{Z}$ generates the elements killed by $n$. -/
theorem mem_zmultiples_of_addOrderOf (n : ℕ) (hn : 0 < n) (u v : RatModInt) (hu : addOrderOf u = n)
    (hv : n • v = 0) : v ∈ AddSubgroup.zmultiples u := by
  have hu0 : n • u = 0 := hu ▸ addOrderOf_nsmul_eq_zero u
  have hle : AddSubgroup.zmultiples u ≤ AddSubgroup.zmultiples (ratModIntGen n) :=
    (AddSubgroup.zmultiples_le).2 (mem_zmultiples_ratModIntGen n hn u hu0)
  have hfin : Finite (AddSubgroup.zmultiples (ratModIntGen n)) := by
    have := addOrderOf_ratModIntGen n hn
    exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, this]; omega)
  have heq : AddSubgroup.zmultiples u = AddSubgroup.zmultiples (ratModIntGen n) := by
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zmultiples, Nat.card_zmultiples, hu, addOrderOf_ratModIntGen n hn]
  rw [heq]
  exact mem_zmultiples_ratModIntGen n hn v hv

/-- The splitting step in the proof of footnote 8: a finite nontrivial abelian group with a nondegenerate
alternating pairing has a subgroup $B$, with a nondegenerate restriction, of index $n^2$ for some $n > 1$. -/
theorem alt_step {A : Type*} [AddCommGroup A] [Finite A]
    (ψ : A →+ A →+ RatModInt) (halt : ∀ x, ψ x x = 0) (hnd : Function.Injective ψ)
    (hA : 1 < Nat.card A) :
    ∃ (B : AddSubgroup A) (n : ℕ), 1 < n ∧ Nat.card A = n ^ 2 * Nat.card B ∧
      ∀ z ∈ B, (∀ w ∈ B, ψ z w = 0) → z = 0 := by
  have hanti : ∀ a b, ψ a b = - ψ b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, AddMonoidHom.add_apply, halt] at h
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h)
  have : Nontrivial A := by
    rw [← Finite.one_lt_card_iff_nontrivial]; exact hA
  obtain ⟨x, hx⟩ := AddMonoid.exists_addOrderOf_eq_exponent (G := A) AddMonoid.ExponentExists.of_finite
  have hnpos : 0 < AddMonoid.exponent A := Nat.pos_of_ne_zero AddMonoid.exponent_ne_zero_of_finite
  have hn1 : 1 < AddMonoid.exponent A := AddMonoid.one_lt_exponent
  have hnA : ∀ a : A, AddMonoid.exponent A • a = 0 := fun a => AddMonoid.exponent_nsmul_eq_zero a
  generalize AddMonoid.exponent A = n at hx hnpos hn1 hnA
  set S : AddSubgroup RatModInt := (ψ x).range with hS
  have : Finite S :=
    Finite.of_surjective (fun a => (⟨ψ x a, a, rfl⟩ : S)) (fun ⟨_, a, h⟩ => ⟨a, Subtype.ext h⟩)
  obtain ⟨s, hs⟩ := AddMonoid.exists_addOrderOf_eq_exponent (G := S) AddMonoid.ExponentExists.of_finite
  obtain ⟨y, hy⟩ : ∃ y, ψ x y = (s : RatModInt) := s.2
  have hSe : ∀ y' : A, AddMonoid.exponent S • ψ x y' = 0 := by
    intro y'
    have := AddMonoid.exponent_nsmul_eq_zero (G := S) (g := ⟨ψ x y', y', rfl⟩)
    simpa using congrArg Subtype.val this
  have hen : AddMonoid.exponent S = n := by
    apply Nat.dvd_antisymm
    · rw [← hs]
      apply addOrderOf_dvd_of_nsmul_eq_zero
      apply Subtype.ext
      show n • (s : RatModInt) = 0
      rw [← hy, ← map_nsmul, hnA, map_zero]
    · rw [← hx]
      apply addOrderOf_dvd_of_nsmul_eq_zero
      apply hnd
      ext y'
      simp [map_nsmul, hSe]
  set u : RatModInt := ψ x y with hu
  have hordu : addOrderOf u = n := by
    rw [hy, AddSubgroup.addOrderOf_coe, hs, hen]
  have hyx : ψ y x = -u := hanti y x
  have hyy : ψ y y = 0 := halt y
  have hxx : ψ x x = 0 := halt x
  let Φ : A →+ RatModInt × RatModInt := (ψ x).prod (ψ y)
  have hF : ∀ a : A, ψ x a ∈ AddSubgroup.zmultiples u ∧ ψ y a ∈ AddSubgroup.zmultiples u := by
    intro a
    exact ⟨mem_zmultiples_of_addOrderOf n hnpos u _ hordu (by rw [← map_nsmul, hnA, map_zero]),
      mem_zmultiples_of_addOrderOf n hnpos u _ hordu (by rw [← map_nsmul, hnA, map_zero])⟩
  have hrange : Φ.range = (AddSubgroup.zmultiples u).prod (AddSubgroup.zmultiples u) := by
    ext ⟨v, w⟩
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod]
    constructor
    · rintro ⟨a, ha⟩
      have h1 : ψ x a = v := congrArg Prod.fst ha
      have h2 : ψ y a = w := congrArg Prod.snd ha
      rw [← h1, ← h2]
      exact hF a
    · rintro ⟨h1, h2⟩
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
      obtain ⟨r, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
      refine ⟨k • y - r • x, Prod.ext ?_ ?_⟩
      · simp [Φ, map_sub, hxx, hu]
      · simp [Φ, map_sub, hyx, hyy]
  refine ⟨Φ.ker, n, hn1, ?_, ?_⟩
  · have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ.ker
    have h2 : Nat.card (A ⧸ Φ.ker) = Nat.card Φ.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Φ).toEquiv
    have h3 : Nat.card Φ.range = n * n := by
      rw [hrange, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
        Nat.card_zmultiples, hordu]
    rw [h1, h2, h3]; ring
  · intro z hz hw
    rw [AddMonoidHom.mem_ker] at hz
    have hzx : ψ x z = 0 := congrArg Prod.fst hz
    have hzy : ψ y z = 0 := congrArg Prod.snd hz
    have hzx' : ψ z x = 0 := by rw [hanti, hzx, neg_zero]
    have hzy' : ψ z y = 0 := by rw [hanti, hzy, neg_zero]
    have hz' : ∀ a, ψ z a = 0 := by
      intro a
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 (hF a).1
      obtain ⟨r, hr⟩ := AddSubgroup.mem_zmultiples_iff.1 (hF a).2
      have hb : a - (k • y - r • x) ∈ Φ.ker := by
        rw [AddMonoidHom.mem_ker]
        refine Prod.ext ?_ ?_
        · simp [Φ, map_sub, hxx, ← hu, hk]
        · simp [Φ, map_sub, hyx, hyy, hr]
      have hba := hw _ hb
      simpa [map_sub, hzx', hzy'] using hba
    exact hnd (AddMonoidHom.ext fun a => by rw [hz' a]; simp)

/-- Footnote 8 to Remark 5.4 (pdf p. 136): a finite abelian group admitting a nondegenerate alternating pairing
with values in $\mathbb{Q}/\mathbb{Z}$ has square order. -/
@[kb "milne2006ec" "Ch. IV, Remark 5.4, footnote 8, pdf p. 136"]
theorem card_isSquare_of_alternating {A : Type*} [AddCommGroup A] [Finite A]
    (ψ : A →+ A →+ RatModInt) (halt : ∀ x, ψ x x = 0) (hnd : Function.Injective ψ) :
    IsSquare (Nat.card A) := by
  induction' hN : Nat.card A using Nat.strong_induction_on with N ih generalizing A
  by_cases hA : 1 < Nat.card A
  · obtain ⟨B, n, hn, hcard, hB⟩ := alt_step ψ halt hnd hA
    let ψ' : B →+ B →+ RatModInt :=
      AddMonoidHom.mk' (fun z => (ψ z.1).comp B.subtype) (by intro a b; ext c; simp)
    have halt' : ∀ x, ψ' x x = 0 := fun x => halt x.1
    have hnd' : Function.Injective ψ' := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      apply Subtype.ext
      refine hB z.1 z.2 (fun w hw => ?_)
      exact DFunLike.congr_fun hz ⟨w, hw⟩
    have hBpos : 0 < Nat.card B := Nat.card_pos
    have hlt : Nat.card B < N := by
      rw [← hN, hcard]
      have h4 : 4 ≤ n ^ 2 := by nlinarith
      nlinarith
    obtain ⟨c, hc⟩ := ih _ hlt ψ' halt' hnd' rfl
    exact ⟨n * c, by rw [← hN, hcard, hc]; ring⟩
  · have : Nonempty A := ⟨0⟩
    have : Nat.card A = 1 := by have := Nat.card_pos (α := A); omega
    exact ⟨1, by rw [← hN, this]⟩

/-- **Remark 5.4 (a)** (pdf p. 136): if $Ш(E/K)$ is finite, its order is a square (from Cassels's pairing, a named
statement). -/
@[kb "milne2006ec" "Ch. IV, Remark 5.4 (a), pdf p. 136"]
theorem remark_5_4a_square (h : Remark5_4a) {K : Type} [Field K] [NumberField K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (hfin : Finite (tateShafarevich K W)) :
    IsSquare (Nat.card (tateShafarevich K W)) := by
  obtain ⟨ψ, halt, hnd⟩ := h.pairing K W hfin
  exact card_isSquare_of_alternating ψ halt hnd

/-! ## Explicit calculations (Propositions 5.5, 5.6, Example 5.7) -/

section Explicit

/-- The curve $Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ over $\mathbb{Q}$ (pdf p. 136). -/
def cubicCurve (α β γ : ℤ) : WeierstrassCurve ℚ :=
  ⟨0, -((α : ℚ) + β + γ), 0, (α : ℚ) * β + β * γ + γ * α, -((α : ℚ) * β * γ)⟩

/-- The discriminant $\Delta = (\alpha - \beta)^2(\beta - \gamma)^2(\gamma - \alpha)^2$ of the cubic (pdf p. 137). -/
@[kb "milne2006ec" "Ch. IV, §5, the discriminant of (X-α)(X-β)(X-γ), pdf p. 137"]
def cubicDisc (α β γ : ℤ) : ℤ := ((α - β) * (β - γ) * (γ - α)) ^ 2

/-- The Weierstrass discriminant of `cubicCurve` is $16\Delta$. -/
theorem cubicCurve_Δ (α β γ : ℤ) : (cubicCurve α β γ).Δ = 16 * (cubicDisc α β γ : ℚ) := by
  simp only [cubicCurve, cubicDisc, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  ring

/-- `cubicCurve α β γ` is an elliptic curve if and only if $\alpha, \beta, \gamma$ are distinct. -/
theorem cubicCurve_isElliptic_iff (α β γ : ℤ) :
    (cubicCurve α β γ).IsElliptic ↔ α ≠ β ∧ β ≠ γ ∧ γ ≠ α := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero, cubicCurve_Δ]
  have h16 : (16 : ℚ) ≠ 0 := by norm_num
  simp only [cubicDisc, mul_eq_zero, h16, false_or, Int.cast_pow, pow_eq_zero_iff, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, Int.cast_mul, Int.cast_sub, not_or]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun h => h1 ?_, fun h => h2 ?_, fun h => h3 ?_⟩ <;> subst h <;> simp
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact sub_ne_zero.2 (by exact_mod_cast h1)
    · exact sub_ne_zero.2 (by exact_mod_cast h2)
    · exact sub_ne_zero.2 (by exact_mod_cast h3)

/-- $\mathbb{Q}^\times/\mathbb{Q}^{\times 2}$. -/
abbrev RatModSquares : Type := ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range

/-- The representative in $\mathbb{Q}^\times$ of Milne's map $\varphi_r$ (Remark 3.7, pdf p. 121), for a root $r$ of
the cubic and $c = $ the product of the differences of $r$ with the other two roots:
$(x : y : 1) \mapsto x - r$ if $x \ne r$, $\mapsto c$ if $x = r$, and $O \mapsto 1$. -/
noncomputable def descentRep {α β γ : ℤ} (r c : ℚ) : (cubicCurve α β γ).toAffine.Point → ℚ
  | 0 => 1
  | .some x _ _ => if x = r then c else x - r

/-- Milne's map $\varphi_r : E(\mathbb{Q}) \to \mathbb{Q}^\times/\mathbb{Q}^{\times 2}$ (Remark 3.7, pdf p. 121): the class
of `descentRep r c` (when it is nonzero, which holds for distinct roots). -/
@[kb "milne2006ec" "Ch. IV, Remark 3.7, the maps φ_α, φ_β, pdf p. 121"]
noncomputable def descentMap {α β γ : ℤ} (r c : ℚ) (P : (cubicCurve α β γ).toAffine.Point) : RatModSquares :=
  if h : descentRep r c P = 0 then 1 else QuotientGroup.mk (Units.mk0 _ h)

/-- Milne's $\varphi_\alpha$. -/
noncomputable abbrev phiAlpha (α β γ : ℤ) : (cubicCurve α β γ).toAffine.Point → RatModSquares :=
  descentMap (α : ℚ) ((α - β) * (α - γ))

/-- Milne's $\varphi_\beta$. -/
noncomputable abbrev phiBeta (α β γ : ℤ) : (cubicCurve α β γ).toAffine.Point → RatModSquares :=
  descentMap (β : ℚ) ((β - α) * (β - γ))

/-- **Remark 3.7** (pdf p. 121), a named statement (Milne: "one can prove directly", citing Cassels 1991,
Chap. 15).  For distinct integers $\alpha, \beta, \gamma$: (i) $\varphi_\alpha$ and $\varphi_\beta$ are homomorphisms;
(ii) the kernel of $(\varphi_\alpha, \varphi_\beta) : E(\mathbb{Q}) \to (\mathbb{Q}^\times/\mathbb{Q}^{\times 2})^2$ is
$2E(\mathbb{Q})$; (iii) $\varphi_\alpha(P)$ and $\varphi_\beta(P)$ are represented by $\pm$ a product of primes dividing
$2\Delta$, i.e. their representatives have even valuation at every prime not dividing $2\Delta$. -/
@[kb "milne2006ec" "Ch. IV, Remark 3.7, pdf p. 121"]
structure Remark3_7 : Prop where
  hom_alpha : ∀ α β γ : ℤ, α ≠ β → β ≠ γ → γ ≠ α → ∀ P Q,
    phiAlpha α β γ (P + Q) = phiAlpha α β γ P * phiAlpha α β γ Q
  hom_beta : ∀ α β γ : ℤ, α ≠ β → β ≠ γ → γ ≠ α → ∀ P Q,
    phiBeta α β γ (P + Q) = phiBeta α β γ P * phiBeta α β γ Q
  ker : ∀ α β γ : ℤ, α ≠ β → β ≠ γ → γ ≠ α → ∀ P,
    (phiAlpha α β γ P = 1 ∧ phiBeta α β γ P = 1) ↔ P ∈ multiples (cubicCurve α β γ).toAffine.Point 2
  support : ∀ α β γ : ℤ, α ≠ β → β ≠ γ → γ ≠ α → ∀ (P : (cubicCurve α β γ).toAffine.Point) (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ 2 * cubicDisc α β γ →
    Even (padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) P)) ∧
      Even (padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) P))

/-- Two integers have even sum exactly when their classes modulo $2$ agree. -/
theorem even_add_iff_cast_eq (a b : ℤ) : Even (a + b) ↔ ((a : ZMod 2) = (b : ZMod 2)) := by
  rw [← ZMod.intCast_eq_zero_iff_even, Int.cast_add]
  constructor
  · intro h
    have : (a : ZMod 2) = -b := eq_neg_of_add_eq_zero_left h
    rwa [ZMod.neg_eq_self_mod_two] at this
  · intro h
    rw [h]
    exact CharTwo.add_self_eq_zero _

/-- A product of two nonzero rationals of the same sign is a square if the $p$-adic valuations have the same
parity for $p$ in a finite set $S$ and are both even for the primes outside $S$. -/
theorem isSquare_mul_of_parity (S : Finset ℕ) {q q' : ℚ} (hq : q ≠ 0) (hq' : q' ≠ 0)
    (hsgn : q < 0 ↔ q' < 0)
    (hpar : ∀ p ∈ S, ((padicValRat p q : ℤ) : ZMod 2) = ((padicValRat p q' : ℤ) : ZMod 2))
    (hev : ∀ p : ℕ, p.Prime → p ∉ S → Even (padicValRat p q) ∧ Even (padicValRat p q')) :
    IsSquare (q * q') := by
  rw [Rat.isSquare_iff_even_factorization]
  refine ⟨?_, fun p hp => ?_⟩
  · rcases lt_or_gt_of_ne hq with h | h
    · exact (mul_pos_of_neg_of_neg h (hsgn.1 h)).le
    · exact mul_nonneg h.le (not_lt.1 (fun h' => by linarith [hsgn.2 h']))
  · haveI := Fact.mk hp
    rw [padicValRat.mul hq hq']
    by_cases hpS : p ∈ S
    · exact (even_add_iff_cast_eq _ _).2 (hpar p hpS)
    · exact (hev p hp hpS).1.add (hev p hp hpS).2

/-- The classes of two points whose representatives multiply to a square agree. -/
theorem descentMap_eq_of_isSquare {α β γ : ℤ} (r c : ℚ) (P Q : (cubicCurve α β γ).toAffine.Point)
    (hP : descentRep r c P ≠ 0) (hQ : descentRep r c Q ≠ 0)
    (hsq : IsSquare (descentRep r c P * descentRep r c Q)) : descentMap r c P = descentMap r c Q := by
  unfold descentMap
  rw [dif_neg hP, dif_neg hQ]
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hP hQ (by simpa using hs)
  apply QuotientGroup.eq.2
  refine ⟨Units.mk0 (s / descentRep r c P) (div_ne_zero hs0 hP), ?_⟩
  apply Units.ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
  linarith [hs]

/-- The representative `descentRep` is nonzero when the constant is. -/
theorem descentRep_ne_zero {α β γ : ℤ} (r c : ℚ) (hc : c ≠ 0) (P : (cubicCurve α β γ).toAffine.Point) :
    descentRep r c P ≠ 0 := by
  cases P with
  | zero => simp [descentRep]
  | some x y h =>
    by_cases hx : x = r
    · simp [descentRep, hx, hc]
    · simp [descentRep, hx, sub_ne_zero]

/-- Points with equal images under $\varphi_\alpha$ and $\varphi_\beta$ differ by an element of $2E(\mathbb{Q})$. -/
theorem sub_mem_multiples_of_phi_eq (h37 : Remark3_7) {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ)
    (hγα : γ ≠ α) (P Q : (cubicCurve α β γ).toAffine.Point)
    (h1 : phiAlpha α β γ P = phiAlpha α β γ Q) (h2 : phiBeta α β γ P = phiBeta α β γ Q) :
    P - Q ∈ multiples (cubicCurve α β γ).toAffine.Point 2 := by
  rw [← h37.ker α β γ hαβ hβγ hγα (P - Q)]
  have ha := h37.hom_alpha α β γ hαβ hβγ hγα (P - Q) Q
  have hb := h37.hom_beta α β γ hαβ hβγ hγα (P - Q) Q
  rw [sub_add_cancel] at ha hb
  refine ⟨mul_right_cancel (b := phiAlpha α β γ Q) ?_, mul_right_cancel (b := phiBeta α β γ Q) ?_⟩
  · rw [← ha, one_mul, h1]
  · rw [← hb, one_mul, h2]

/-- The points $(r, 0)$ for the roots $r$ are nonsingular. -/
theorem cubicCurve_nonsingular_root {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) (x : ℚ)
    (hx : x = α ∨ x = β ∨ x = γ) : (cubicCurve α β γ).toAffine.Nonsingular x 0 := by
  haveI : (cubicCurve α β γ).IsElliptic := (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ, hβγ, hγα⟩
  rw [← WeierstrassCurve.Affine.equation_iff_nonsingular, WeierstrassCurve.Affine.equation_iff]
  rcases hx with rfl | rfl | rfl <;> simp [cubicCurve] <;> ring

/-- The points $(r, 0)$ are killed by $2$. -/
theorem cubicCurve_two_smul_root {α β γ : ℤ} (x : ℚ) (h : (cubicCurve α β γ).toAffine.Nonsingular x 0) :
    (2 : ℤ) • (Point.some x 0 h : (cubicCurve α β γ).toAffine.Point) = 0 := by
  rw [two_zsmul]
  exact Point.add_self_of_Y_eq (by simp [WeierstrassCurve.Affine.negY, cubicCurve])

/-- $\#(E(\mathbb{Q})/2E(\mathbb{Q})) \ge 2^{r+2}$ for $E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$. -/
theorem two_pow_le_card_cubic_of_fg {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α)
    [AddGroup.FG (cubicCurve α β γ).toAffine.Point] :
    2 ^ (rank (cubicCurve α β γ) + 2) ≤
      Nat.card ((cubicCurve α β γ).toAffine.Point ⧸ multiples (cubicCurve α β γ).toAffine.Point 2) := by
  have hA := cubicCurve_nonsingular_root hαβ hβγ hγα (α : ℚ) (Or.inl rfl)
  have hB := cubicCurve_nonsingular_root hαβ hβγ hγα (β : ℚ) (Or.inr (Or.inl rfl))
  have hC := cubicCurve_nonsingular_root hαβ hβγ hγα (γ : ℚ) (Or.inr (Or.inr rfl))
  refine two_pow_le_card_quot_two
    ![0, Point.some _ _ hA, Point.some _ _ hB, Point.some _ _ hC] ?_ ?_
  · intro i j hij
    have h1 : (α : ℚ) ≠ β := by exact_mod_cast hαβ
    have h2 : (β : ℚ) ≠ γ := by exact_mod_cast hβγ
    have h3 : (γ : ℚ) ≠ α := by exact_mod_cast hγα
    fin_cases i <;> fin_cases j <;> simp [Point.some.injEq] at hij ⊢ <;> tauto
  · intro i
    fin_cases i
    · simp
    · exact cubicCurve_two_smul_root _ hA
    · exact cubicCurve_two_smul_root _ hB
    · exact cubicCurve_two_smul_root _ hC

/-- $\#(E(\mathbb{Q})/2E(\mathbb{Q})) \ge 2^{r+2}$, given Lemma 2.1 and Theorem 3.1 (for finite generation). -/
theorem two_pow_le_card_cubic (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ)
    (hγα : γ ≠ α) :
    2 ^ (rank (cubicCurve α β γ) + 2) ≤
      Nat.card ((cubicCurve α β γ).toAffine.Point ⧸ multiples (cubicCurve α β γ).toAffine.Point 2) := by
  haveI : (cubicCurve α β γ).IsElliptic := (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ, hβγ, hγα⟩
  haveI := finite_basis ℚ (cubicCurve α β γ) h21 h31
  exact two_pow_le_card_cubic_of_fg hαβ hβγ hγα

/-- The discriminant of distinct roots is nonzero. -/
theorem cubicDisc_ne_zero {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    cubicDisc α β γ ≠ 0 := by
  unfold cubicDisc
  exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (sub_ne_zero.2 hαβ) (sub_ne_zero.2 hβγ)) (sub_ne_zero.2 hγα))

/-- The sign (as an element of $\mathbb{Z}/2$, $1$ for negative) and the parities of the $p$-adic valuations at the
primes of a finite set $S$. -/
noncomputable def encRat (S : Finset ℕ) (q : ℚ) : ZMod 2 × (S → ZMod 2) :=
  ((if q < 0 then 1 else 0), fun p => ((padicValRat p q : ℤ) : ZMod 2))

theorem lt_zero_iff_of_encRat {S : Finset ℕ} {q q' : ℚ} (h : encRat S q = encRat S q') : q < 0 ↔ q' < 0 := by
  have := (Prod.ext_iff.1 h).1
  simp only [encRat] at this
  by_cases h1 : q < 0 <;> by_cases h2 : q' < 0 <;> simp [h1, h2] at this ⊢

theorem parity_of_encRat {S : Finset ℕ} {q q' : ℚ} (h : encRat S q = encRat S q') (p : ℕ) (hp : p ∈ S) :
    ((padicValRat p q : ℤ) : ZMod 2) = ((padicValRat p q' : ℤ) : ZMod 2) :=
  congrFun (Prod.ext_iff.1 h).2 ⟨p, hp⟩

theorem card_encRat (S : Finset ℕ) : Nat.card (ZMod 2 × (S → ZMod 2)) = 2 * 2 ^ S.card := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_prod, Fintype.card_fun, ZMod.card]

/-- The encoding used for Proposition 5.5: the signs and the parities of the valuations at the primes dividing
$2\Delta$ of the representatives of $\varphi_\alpha(P)$ and $\varphi_\beta(P)$. -/
noncomputable def encodeCubic (α β γ : ℤ) (X : (cubicCurve α β γ).toAffine.Point) :
    (ZMod 2 × ((2 * cubicDisc α β γ).natAbs.primeFactors → ZMod 2)) ×
      (ZMod 2 × ((2 * cubicDisc α β γ).natAbs.primeFactors → ZMod 2)) :=
  (encRat (2 * cubicDisc α β γ).natAbs.primeFactors (descentRep (α : ℚ) ((α - β) * (α - γ)) X),
    encRat (2 * cubicDisc α β γ).natAbs.primeFactors (descentRep (β : ℚ) ((β - α) * (β - γ)) X))

/-- Points with the same encoding differ by an element of $2E(\mathbb{Q})$ (from Remark 3.7). -/
theorem encodeCubic_spec (h37 : Remark3_7) {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α)
    (X Y : (cubicCurve α β γ).toAffine.Point) (hXY : encodeCubic α β γ X = encodeCubic α β γ Y) :
    X - Y ∈ multiples (cubicCurve α β γ).toAffine.Point 2 := by
  set S : Finset ℕ := (2 * cubicDisc α β γ).natAbs.primeFactors with hS
  have hΔ := cubicDisc_ne_zero hαβ hβγ hγα
  have hc1 : ((α : ℚ) - β) * (α - γ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ)) (sub_ne_zero.2 (by exact_mod_cast hγα.symm))
  have hc2 : ((β : ℚ) - α) * (β - γ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ.symm)) (sub_ne_zero.2 (by exact_mod_cast hβγ))
  have hev : ∀ (X : (cubicCurve α β γ).toAffine.Point) (p : ℕ), p.Prime → p ∉ S →
      Even (padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) X)) ∧
        Even (padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) X)) := by
    intro X p hp hpS
    refine h37.support α β γ hαβ hβγ hγα X p hp fun hdvd => hpS ?_
    exact Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 hdvd, by simpa using hΔ⟩
  obtain ⟨hα, hβ⟩ := Prod.ext_iff.1 hXY
  refine sub_mem_multiples_of_phi_eq h37 hαβ hβγ hγα X Y ?_ ?_
  · refine descentMap_eq_of_isSquare _ _ X Y (descentRep_ne_zero _ _ hc1 X) (descentRep_ne_zero _ _ hc1 Y) ?_
    refine isSquare_mul_of_parity S (descentRep_ne_zero _ _ hc1 X) (descentRep_ne_zero _ _ hc1 Y)
      (lt_zero_iff_of_encRat hα) (fun p hp => parity_of_encRat hα p hp) fun p hp hpS =>
      ⟨(hev X p hp hpS).1, (hev Y p hp hpS).1⟩
  · refine descentMap_eq_of_isSquare _ _ X Y (descentRep_ne_zero _ _ hc2 X) (descentRep_ne_zero _ _ hc2 Y) ?_
    refine isSquare_mul_of_parity S (descentRep_ne_zero _ _ hc2 X) (descentRep_ne_zero _ _ hc2 Y)
      (lt_zero_iff_of_encRat hβ) (fun p hp => parity_of_encRat hβ p hp) fun p hp hpS =>
      ⟨(hev X p hp hpS).2, (hev Y p hp hpS).2⟩

/-- **Remark 3.7, finiteness** (pdf p. 121): $E(\mathbb{Q})/2E(\mathbb{Q})$ is finite for
$E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$ with distinct integers, given Remark 3.7. -/
theorem finite_quot_two_cubic (h37 : Remark3_7) {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α) :
    Finite ((cubicCurve α β γ).toAffine.Point ⧸ multiples (cubicCurve α β γ).toAffine.Point 2) :=
  finite_quot_two_of (encodeCubic α β γ) (encodeCubic_spec h37 hαβ hβγ hγα)

/-- Proposition 5.5 for a curve whose group of rational points is finitely generated, from Remark 3.7. -/
theorem prop_5_5_rank_of_fg (h37 : Remark3_7) {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ) (hγα : γ ≠ α)
    [AddGroup.FG (cubicCurve α β γ).toAffine.Point] :
    rank (cubicCurve α β γ) ≤ 2 * (2 * cubicDisc α β γ).natAbs.primeFactors.card := by
  set S : Finset ℕ := (2 * cubicDisc α β γ).natAbs.primeFactors with hS
  have hle := card_quot_two_le (encodeCubic α β γ) (encodeCubic_spec h37 hαβ hβγ hγα)
  have hcard := two_pow_le_card_cubic_of_fg hαβ hβγ hγα
  rw [Nat.card_prod, card_encRat] at hle
  have h2 : 2 ^ (rank (cubicCurve α β γ) + 2) ≤ 2 ^ (2 * S.card + 2) := by
    refine hcard.trans (hle.trans (le_of_eq ?_))
    ring
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2
  omega

/-- **Proposition 5.5** (pdf p. 137).  For distinct integers $\alpha, \beta, \gamma$ the rank $r$ of $E(\mathbb{Q})$,
$E : Y^2 = (X - \alpha)(X - \beta)(X - \gamma)$, satisfies $r \le 2\cdot\#\{p \mid p \text{ divides } 2\Delta\}$.
Proved from Remark 3.7 and the finite basis theorem (named statements); the unconditional form is
`prop_5_5_rank_unconditional` (`Ch4TwoDescent.lean`). -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.5, pdf p. 137"]
theorem prop_5_5_rank (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) (h37 : Remark3_7) {α β γ : ℤ} (hαβ : α ≠ β) (hβγ : β ≠ γ)
    (hγα : γ ≠ α) :
    rank (cubicCurve α β γ) ≤ 2 * (2 * cubicDisc α β γ).natAbs.primeFactors.card := by
  haveI : (cubicCurve α β γ).IsElliptic := (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ, hβγ, hγα⟩
  haveI := finite_basis ℚ (cubicCurve α β γ) h21 h31
  exact prop_5_5_rank_of_fg h37 hαβ hβγ hγα

/-- The primes of nodal reduction for `cubicCurve` (pdf p. 137): exactly two of the roots coincide modulo $p$. -/
def nodalPrimes (α β γ : ℤ) : Finset ℕ :=
  (cubicDisc α β γ).natAbs.primeFactors.filter fun p => ¬ ((p : ℤ) ∣ α - β ∧ (p : ℤ) ∣ β - γ)

/-- The primes of cuspidal reduction for `cubicCurve` (pdf p. 137): all three roots coincide modulo $p$. -/
def cuspidalPrimes (α β γ : ℤ) : Finset ℕ :=
  (cubicDisc α β γ).natAbs.primeFactors.filter fun p => (p : ℤ) ∣ α - β ∧ (p : ℤ) ∣ β - γ

/-- The three local statements (a), (b), (c) in the proof of **Proposition 5.6** (pdf pp. 137–138), a named
statement (Milne proves (b) in one case and says the others are similar).  For distinct integers
$\alpha < \beta < \gamma$ and $P \in E(\mathbb{Q})$, with $\varphi_\alpha(P), \varphi_\beta(P)$ represented by
`descentRep`:
(a) if $p \nmid \Delta$, both representatives have even $p$-adic valuation;
(b) if exactly two roots coincide modulo $p$, the pair of valuations modulo 2 lies on a line: on the diagonal if
$\alpha \equiv \beta$, with second coordinate even if $\alpha \equiv \gamma$, with first coordinate even if
$\beta \equiv \gamma$;
(c) the representative of $\varphi_\alpha(P)$ is positive (so the signs are $(+,+)$ or $(+,-)$). -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.6, statements (a), (b), (c) of the proof, pdf pp. 137-138"]
structure Prop5_6Local : Prop where
  away : ∀ α β γ : ℤ, α < β → β < γ → ∀ P (p : ℕ), p.Prime → ¬ (p : ℤ) ∣ cubicDisc α β γ →
    Even (padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) (P : (cubicCurve α β γ).toAffine.Point))) ∧
      Even (padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) P))
  nodal : ∀ α β γ : ℤ, α < β → β < γ → ∀ P (p : ℕ), p ∈ nodalPrimes α β γ →
    let a := padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) (P : (cubicCurve α β γ).toAffine.Point))
    let b := padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) P)
    ((p : ℤ) ∣ α - β → Even (a + b)) ∧ ((p : ℤ) ∣ γ - α → Even b) ∧ ((p : ℤ) ∣ β - γ → Even a)
  sign : ∀ α β γ : ℤ, α < β → β < γ → ∀ P,
    0 < descentRep (α : ℚ) ((α - β) * (α - γ)) (P : (cubicCurve α β γ).toAffine.Point)

/-- A rational with the same sign indicator as another has the same sign. -/
theorem lt_zero_iff_of_ite_eq {q q' : ℚ}
    (h : (if q < 0 then (1 : ZMod 2) else 0) = if q' < 0 then 1 else 0) : q < 0 ↔ q' < 0 := by
  by_cases h1 : q < 0 <;> by_cases h2 : q' < 0 <;> simp [h1, h2] at h ⊢

/-- The algebra behind the nodal case of Proposition 5.6. -/
theorem nodal_parity {D1 D2 D3 : Prop} [Decidable D3] {a b a' b' : ℤ}
    (hD : ¬ D3 → D1 ∨ D2)
    (hX : (D1 → Even (a + b)) ∧ (D2 → Even b) ∧ (D3 → Even a))
    (hY : (D1 → Even (a' + b')) ∧ (D2 → Even b') ∧ (D3 → Even a'))
    (hc : (if D3 then (b : ZMod 2) else (a : ZMod 2)) = (if D3 then (b' : ZMod 2) else (a' : ZMod 2))) :
    (a : ZMod 2) = a' ∧ (b : ZMod 2) = b' := by
  by_cases h3 : D3
  · rw [if_pos h3, if_pos h3] at hc
    refine ⟨?_, hc⟩
    rw [ZMod.intCast_eq_zero_iff_even.2 (hX.2.2 h3), ZMod.intCast_eq_zero_iff_even.2 (hY.2.2 h3)]
  · rw [if_neg h3, if_neg h3] at hc
    refine ⟨hc, ?_⟩
    rcases hD h3 with h1 | h2
    · have e1 := (even_add_iff_cast_eq _ _).1 (hX.1 h1)
      have e2 := (even_add_iff_cast_eq _ _).1 (hY.1 h1)
      rw [← e1, ← e2]
      exact hc
    · rw [ZMod.intCast_eq_zero_iff_even.2 (hX.2.1 h2), ZMod.intCast_eq_zero_iff_even.2 (hY.2.1 h2)]

/-- A prime dividing the discriminant divides one of the differences of the roots. -/
theorem dvd_cubicDisc_cases {α β γ : ℤ} {p : ℕ} (hp : p.Prime) (h : (p : ℤ) ∣ cubicDisc α β γ) :
    (p : ℤ) ∣ α - β ∨ (p : ℤ) ∣ β - γ ∨ (p : ℤ) ∣ γ - α := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  unfold cubicDisc at h
  have h' := hpr.dvd_of_dvd_pow h
  rcases hpr.dvd_or_dvd h' with h1 | h1
  · rcases hpr.dvd_or_dvd h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h1)

/-- Proposition 5.6 for a curve whose group of rational points is finitely generated, from Remark 3.7 and the
local statements (a)–(c). -/
theorem prop_5_6_of_fg (h37 : Remark3_7) (h56 : Prop5_6Local) {α β γ : ℤ}
    (hαβ : α < β) (hβγ : β < γ) [AddGroup.FG (cubicCurve α β γ).toAffine.Point] :
    rank (cubicCurve α β γ) + 1 ≤ (nodalPrimes α β γ).card + 2 * (cuspidalPrimes α β γ).card := by
  have hαβ' : α ≠ β := hαβ.ne
  have hβγ' : β ≠ γ := hβγ.ne
  have hγα' : γ ≠ α := (lt_trans hαβ hβγ).ne'
  set S : Finset ℕ := (cubicDisc α β γ).natAbs.primeFactors with hS
  have hΔ := cubicDisc_ne_zero hαβ' hβγ' hγα'
  have hc1 : ((α : ℚ) - β) * (α - γ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ')) (sub_ne_zero.2 (by exact_mod_cast hγα'.symm))
  have hc2 : ((β : ℚ) - α) * (β - γ) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.2 (by exact_mod_cast hαβ'.symm)) (sub_ne_zero.2 (by exact_mod_cast hβγ'))
  have hSdvd : ∀ p ∈ S, (p : ℤ) ∣ cubicDisc α β γ := fun p hp =>
    Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hp)
  let g : (cubicCurve α β γ).toAffine.Point → ZMod 2 × ((nodalPrimes α β γ) → ZMod 2) ×
      ((cuspidalPrimes α β γ) → ZMod 2 × ZMod 2) := fun X =>
    ((if descentRep (β : ℚ) ((β - α) * (β - γ)) X < 0 then 1 else 0),
      fun p => if ((p : ℕ) : ℤ) ∣ β - γ then
          ((padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) X) : ℤ) : ZMod 2)
        else ((padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) X) : ℤ) : ZMod 2),
      fun p => (((padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) X) : ℤ) : ZMod 2),
        ((padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) X) : ℤ) : ZMod 2)))
  have hle : Nat.card ((cubicCurve α β γ).toAffine.Point ⧸ multiples (cubicCurve α β γ).toAffine.Point 2) ≤
      Nat.card (ZMod 2 × ((nodalPrimes α β γ) → ZMod 2) × ((cuspidalPrimes α β γ) → ZMod 2 × ZMod 2)) := by
    refine card_quot_two_le g fun X Y hXY => ?_
    obtain ⟨e0, e12⟩ := Prod.ext_iff.1 hXY
    obtain ⟨e1, e2⟩ := Prod.ext_iff.1 e12
    have hpar : ∀ p ∈ S,
        ((padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) X) : ℤ) : ZMod 2) =
          ((padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) Y) : ℤ) : ZMod 2) ∧
        ((padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) X) : ℤ) : ZMod 2) =
          ((padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) Y) : ℤ) : ZMod 2) := by
      intro p hpS
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpS
      by_cases hcusp : (p : ℤ) ∣ α - β ∧ (p : ℤ) ∣ β - γ
      · have hmem : p ∈ cuspidalPrimes α β γ := Finset.mem_filter.2 ⟨hpS, hcusp⟩
        have h := Prod.ext_iff.1 (congrFun e2 ⟨p, hmem⟩)
        exact h
      · have hmem : p ∈ nodalPrimes α β γ := Finset.mem_filter.2 ⟨hpS, hcusp⟩
        have hc : (if ((p : ℕ) : ℤ) ∣ β - γ then
            ((padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) X) : ℤ) : ZMod 2)
          else ((padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) X) : ℤ) : ZMod 2)) =
            (if ((p : ℕ) : ℤ) ∣ β - γ then
            ((padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) Y) : ℤ) : ZMod 2)
          else ((padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) Y) : ℤ) : ZMod 2)) :=
          congrFun e1 ⟨p, hmem⟩
        have hD : ¬ ((p : ℤ) ∣ β - γ) → (p : ℤ) ∣ α - β ∨ (p : ℤ) ∣ γ - α := by
          intro h3
          rcases dvd_cubicDisc_cases hp (hSdvd p hpS) with h | h | h
          · exact Or.inl h
          · exact absurd h h3
          · exact Or.inr h
        obtain ⟨nX1, nX2, nX3⟩ := h56.nodal α β γ hαβ hβγ X p hmem
        obtain ⟨nY1, nY2, nY3⟩ := h56.nodal α β γ hαβ hβγ Y p hmem
        exact nodal_parity hD ⟨nX1, nX2, nX3⟩ ⟨nY1, nY2, nY3⟩ hc
    have hev : ∀ (Z : (cubicCurve α β γ).toAffine.Point) (p : ℕ), p.Prime → p ∉ S →
        Even (padicValRat p (descentRep (α : ℚ) ((α - β) * (α - γ)) Z)) ∧
          Even (padicValRat p (descentRep (β : ℚ) ((β - α) * (β - γ)) Z)) := by
      intro Z p hp hpS
      refine h56.away α β γ hαβ hβγ Z p hp fun hdvd => hpS ?_
      exact Nat.mem_primeFactors.2 ⟨hp, Int.natCast_dvd.1 hdvd, by simpa using hΔ⟩
    refine sub_mem_multiples_of_phi_eq h37 hαβ' hβγ' hγα' X Y ?_ ?_
    · refine descentMap_eq_of_isSquare _ _ X Y (descentRep_ne_zero _ _ hc1 X) (descentRep_ne_zero _ _ hc1 Y) ?_
      refine isSquare_mul_of_parity S (descentRep_ne_zero _ _ hc1 X) (descentRep_ne_zero _ _ hc1 Y)
        ?_ (fun p hp => (hpar p hp).1) fun p hp hpS => ⟨(hev X p hp hpS).1, (hev Y p hp hpS).1⟩
      exact iff_of_false (not_lt.2 (h56.sign α β γ hαβ hβγ X).le) (not_lt.2 (h56.sign α β γ hαβ hβγ Y).le)
    · refine descentMap_eq_of_isSquare _ _ X Y (descentRep_ne_zero _ _ hc2 X) (descentRep_ne_zero _ _ hc2 Y) ?_
      refine isSquare_mul_of_parity S (descentRep_ne_zero _ _ hc2 X) (descentRep_ne_zero _ _ hc2 Y)
        (lt_zero_iff_of_ite_eq e0) (fun p hp => (hpar p hp).2) fun p hp hpS =>
        ⟨(hev X p hp hpS).2, (hev Y p hp hpS).2⟩
  have hcard := two_pow_le_card_cubic_of_fg hαβ' hβγ' hγα'
  have hF : Nat.card (ZMod 2 × ((nodalPrimes α β γ) → ZMod 2) × ((cuspidalPrimes α β γ) → ZMod 2 × ZMod 2)) =
      2 ^ ((nodalPrimes α β γ).card + 2 * (cuspidalPrimes α β γ).card + 1) := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_prod, Fintype.card_fun, ZMod.card]
    rw [pow_succ, pow_add, pow_mul]
    norm_num
    ring
  rw [hF] at hle
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (hcard.trans hle)
  omega

/-- **Proposition 5.6** (pdf p. 137).  For integers $\alpha < \beta < \gamma$, the rank $r$ of $E(\mathbb{Q})$ satisfies
$r \le t_1 + 2t_2 - 1$, where $t_1$ and $t_2$ are the numbers of primes of nodal and cuspidal reduction (stated as
$r + 1 \le t_1 + 2t_2$).  Proved from Remark 3.7, the statements (a)–(c) of the proof, and the finite basis theorem
(named statements); the unconditional form is `prop_5_6_unconditional` (`Ch4TwoDescent.lean`).  (Ordering the
roots loses no generality.) -/
@[kb "milne2006ec" "Ch. IV, Prop. 5.6, pdf p. 137"]
theorem prop_5_6 (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) (h37 : Remark3_7) (h56 : Prop5_6Local) {α β γ : ℤ}
    (hαβ : α < β) (hβγ : β < γ) :
    rank (cubicCurve α β γ) + 1 ≤ (nodalPrimes α β γ).card + 2 * (cuspidalPrimes α β γ).card := by
  haveI : (cubicCurve α β γ).IsElliptic :=
    (cubicCurve_isElliptic_iff α β γ).2 ⟨hαβ.ne, hβγ.ne, (lt_trans hαβ hβγ).ne'⟩
  haveI := finite_basis ℚ (cubicCurve α β γ) h21 h31
  exact prop_5_6_of_fg h37 h56 hαβ hβγ

/-- Example 5.7 for $Y^2 = X^3 - X$, given finite generation: the rank is $0$ and $E(\mathbb{Q})$ is finite. -/
theorem example_5_7_of_fg (h37 : Remark3_7) (h56 : Prop5_6Local) [AddGroup.FG (cubicCurve (-1) 0 1).toAffine.Point] :
    rank (cubicCurve (-1) 0 1) = 0 ∧ Finite (cubicCurve (-1) 0 1).toAffine.Point := by
  have h4 : (cubicDisc (-1) 0 1).natAbs = 2 ^ 2 := by
    norm_num [cubicDisc]
  have hpf : (cubicDisc (-1) 0 1).natAbs.primeFactors = {2} := by
    rw [h4, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  have hne : nodalPrimes (-1) 0 1 = {2} := by
    simp only [nodalPrimes, hpf, Finset.filter_singleton]
    rw [if_pos]
    decide
  have hcu : cuspidalPrimes (-1) 0 1 = ∅ := by
    simp only [cuspidalPrimes, hpf, Finset.filter_singleton]
    rw [if_neg]
    decide
  have h := prop_5_6_of_fg h37 h56 (α := -1) (β := 0) (γ := 1) (by norm_num) (by norm_num)
  rw [hne, hcu] at h
  have h0 : rank (cubicCurve (-1) 0 1) = 0 := by
    simp at h
    omega
  refine ⟨h0, ?_⟩
  obtain ⟨e⟩ := rank_spec (cubicCurve (-1) 0 1)
  haveI := finite_torsion_of_fg (cubicCurve (-1) 0 1).toAffine.Point
  have : Finite (Fin (rank (cubicCurve (-1) 0 1)) → ℤ) := by
    rw [h0]
    infer_instance
  exact Finite.of_equiv _ e.symm.toEquiv

/-- **Example 5.7** (pdf p. 138), the rank: for $E : Y^2 = X^3 - X$, i.e. $(\alpha, \beta, \gamma) = (-1, 0, 1)$, the rank
of $E(\mathbb{Q})$ is $0$, so $E(\mathbb{Q})$ is finite.  The unconditional form, with $E(\mathbb{Q}) \cong
(\mathbb{Z}/2)^2$, is `example_5_7_unconditional` (`Ch4TwoDescent.lean`). -/
@[kb "milne2006ec" "Ch. IV, Example 5.7, pdf p. 138"]
theorem example_5_7 (h21 : Lemma2_1) (h31 : Thm3_1_Selmer) (h37 : Remark3_7) (h56 : Prop5_6Local) :
    rank (cubicCurve (-1) 0 1) = 0 ∧ Finite (cubicCurve (-1) 0 1).toAffine.Point := by
  haveI : (cubicCurve (-1) 0 1).IsElliptic :=
    (cubicCurve_isElliptic_iff (-1) 0 1).2 ⟨by norm_num, by norm_num, by norm_num⟩
  haveI := finite_basis ℚ (cubicCurve (-1) 0 1) h21 h31
  exact example_5_7_of_fg h37 h56

end Explicit

end NumberFieldKB.MilneEC
