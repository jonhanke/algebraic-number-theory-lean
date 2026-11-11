import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import QuadFormsKB.Citation
import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Milne, *Class Field Theory*, Chapter II §1: restriction, corestriction, inflation

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Milne's maps on cohomology defined by a compatible pair $(\alpha : G' \to G, \beta : M \to M')$ (p. 68) are
Mathlib's `groupCohomology.map α β` (for `β : res α M ⟶ M'`). Restriction and inflation (Example 1.27 (b), (c))
are Mathlib's `groupCohomology.map H.subtype (𝟙 _)` and `groupCohomology.infNatTrans`.

Milne gives a second construction of restriction (Example 1.27 (b)): the map induced by
$M \to \operatorname{Ind}_H^G(M)$, $m \mapsto (g \mapsto gm)$, followed by Shapiro's isomorphism. We define
`resShapiro` this way, and the corestriction `cor` (Example 1.29) as Milne does: the inverse of Shapiro's
isomorphism followed by the map induced by $\operatorname{Ind}_H^G(M) \to M$, $\varphi \mapsto \sum_{s} s\varphi(s^{-1})$
($s$ running over left coset representatives). With these definitions Proposition 1.30 ($\mathrm{Cor} \circ
\mathrm{Res} = (G:H)$) and its corollaries are proved; the agreement of `resShapiro` with Mathlib's restriction is
Example 1.27 (b).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory Rep groupCohomology

variable {G : Type} [Group G]

/-- The $G$-homomorphism $M \to \operatorname{Ind}_H^G(M)$, $m \mapsto (g \mapsto gm)$ (Example 1.27 (b)); it is the
unit of Mathlib's adjunction `Rep.resCoindAdjunction`. -/
noncomputable abbrev toCoind (H : Subgroup G) (M : Rep ℤ G) : M ⟶ coind H.subtype (res H.subtype M) :=
  (resCoindAdjunction ℤ H.subtype).unit.app M

theorem toCoind_apply (H : Subgroup G) (M : Rep ℤ G) (m : M) (g : G) :
    ((toCoind H M).hom m).1 g = M.ρ g m := by
  rfl

/-- **Restriction, Milne's second construction** (Example 1.27 (b), p. 69): the map
$H^r(G, M) \to H^r(G, \operatorname{Ind}_H^G M) \simeq H^r(H, M)$ induced by $M \to \operatorname{Ind}_H^G M$
followed by Shapiro's isomorphism (Mathlib's `groupCohomology.coindIso`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (b), restriction via Shapiro's lemma, p. 69"]
noncomputable def resShapiro (H : Subgroup G) (M : Rep ℤ G) (r : ℕ) :
    groupCohomology M r ⟶ groupCohomology (res H.subtype M) r :=
  (functor ℤ G r).map (toCoind H M) ≫ (coindIso (res H.subtype M) r).hom

/-- **Example 1.27 (a)** (p. 68–69), as a named statement. For a subgroup $H$ of a group $G$ and an $H$-module
$M$, the map $\operatorname{Ind}_H^G(M) \to M$, $\varphi \mapsto \varphi(1_G)$ (the counit of Mathlib's adjunction
`Rep.resCoindAdjunction`), is compatible with $H \hookrightarrow G$, and the induced map
$H^r(G, \operatorname{Ind}_H^G M) \to H^r(H, M)$ is the isomorphism of Shapiro's lemma (Mathlib's
`groupCohomology.coindIso`). Milne checks $r = 0$ and dimension-shifts; in Mathlib, `coindIso` is built from Ext
groups and a comparison of projective resolutions, and identifying it with a map of inhomogeneous cochains is not
available, so the statement is recorded as a named input. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (a), p. 68–69"]
structure Example1_27a : Prop where
  map_counit_eq : ∀ (G : Type) [Group G] (H : Subgroup G) (M : Rep ℤ H) (r : ℕ),
    map H.subtype ((resCoindAdjunction ℤ H.subtype).counit.app M) r = (coindIso M r).hom

/-- **Example 1.27 (b)** (p. 69). Milne's two constructions of the restriction map agree: the map defined by the
compatible pair $(H \hookrightarrow G, \mathrm{id}_M)$ (Mathlib's restriction) equals `resShapiro`. Proved from
Example 1.27 (a) (named statement) and the triangle identity of the adjunction. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (b), p. 69"]
theorem example_1_27b (h127a : Example1_27a) (H : Subgroup G) (M : Rep ℤ G) (r : ℕ) :
    map H.subtype (𝟙 (res H.subtype M)) r = resShapiro H M r := by
  rw [resShapiro, ← h127a.map_counit_eq G H (res H.subtype M) r]
  have key := map_comp (MonoidHom.id G) H.subtype (A := M) (B := coind H.subtype (res H.subtype M))
    (C := res H.subtype M) (toCoind H M)
    ((resCoindAdjunction ℤ H.subtype).counit.app (res H.subtype M)) r
  have tri := (resCoindAdjunction ℤ H.subtype).left_triangle_components M
  exact (map_congr (by simp) (by rw [tri]) r).trans key

/-- The $G$-homomorphism $\beta : M \to M$, $m \mapsto g_0^{-1}m$, compatible with the inner automorphism
$\alpha : \sigma \mapsto g_0\sigma g_0^{-1}$ (Example 1.27 (d)). -/
noncomputable def conjCompat (g₀ : G) (M : Rep ℤ G) : res (MulAut.conj g₀).toMonoidHom M ⟶ M :=
  Rep.ofHom ⟨M.ρ g₀⁻¹, fun σ => by
    ext m
    change M.ρ g₀⁻¹ (M.ρ (g₀ * σ * g₀⁻¹) m) = M.ρ σ (M.ρ g₀⁻¹ m)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group⟩

theorem conjCompat_apply (g₀ : G) (M : Rep ℤ G) (m : M) : (conjCompat g₀ M).hom m = M.ρ g₀⁻¹ m := by
  rfl

/-- **Example 1.27 (d)** (p. 69), as a named statement: for every group $G$, every $g_0 \in G$ and every $G$-module
$M$, the map $H^r(G, M) \to H^r(G, M)$ defined by the compatible pair
($\sigma \mapsto g_0\sigma g_0^{-1}$, $m \mapsto g_0^{-1}m$) is the identity. Milne proves it by dimension shifting
from the case $r = 0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (d), p. 69"]
structure Example1_27d : Prop where
  map_conj_eq_id : ∀ (G : Type) [Group G] (g₀ : G) (M : Rep ℤ G) (r : ℕ),
    map (MulAut.conj g₀).toMonoidHom (conjCompat g₀ M) r = 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- Degree $0$ of Example 1.27 (d): the map is $m \mapsto g_0^{-1}m$ on $M^G$, the identity. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.27 (d), case r = 0, p. 69"]
theorem example_1_27d_zero (g₀ : G) (M : Rep ℤ G) :
    map (MulAut.conj g₀).toMonoidHom (conjCompat g₀ M) 0 = 𝟙 _ := by
  have : Mono (shortComplexH0 M).f := inferInstance
  have : Mono ((H0Iso M).hom ≫ (shortComplexH0 M).f) := mono_comp _ _
  apply (cancel_mono ((H0Iso M).hom ≫ (shortComplexH0 M).f)).1
  rw [map_H0Iso_hom_f, Category.id_comp]
  congr 1
  have key : ∀ x : M.ρ.invariants, M.ρ g₀⁻¹ x.1 = x.1 := fun x => x.2 g₀⁻¹
  exact ModuleCat.hom_ext (DFunLike.ext _ _ fun x => key x)

/-! ## Remark 1.28 (b): the action of $G/H$ on $H^r(H, M)$ -/

/-- The inner automorphism $h \mapsto g_0 h g_0^{-1}$ of a normal subgroup $H$. -/
def conjNormal (H : Subgroup G) [H.Normal] (g₀ : G) : H →* H where
  toFun h := ⟨g₀ * h * g₀⁻¹, Subgroup.Normal.conj_mem ‹_› _ h.2 g₀⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjNormal_apply (H : Subgroup G) [H.Normal] (g₀ : G) (h : H) :
    (conjNormal H g₀ h : G) = g₀ * h * g₀⁻¹ := by
  rfl

/-- The $H$-homomorphism $m \mapsto g_0^{-1}m$ compatible with `conjNormal H g₀`. -/
noncomputable def conjNormalCompat (H : Subgroup G) [H.Normal] (g₀ : G) (M : Rep ℤ G) :
    res (conjNormal H g₀) (res H.subtype M) ⟶ res H.subtype M :=
  Rep.ofHom ⟨M.ρ g₀⁻¹, fun σ => by
    ext m
    change M.ρ g₀⁻¹ (M.ρ ((conjNormal H g₀ σ : H) : G) m) = M.ρ (σ : G) (M.ρ g₀⁻¹ m)
    rw [conjNormal_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group⟩

theorem conjNormalCompat_apply (H : Subgroup G) [H.Normal] (g₀ : G) (M : Rep ℤ G) (m : M) :
    (conjNormalCompat H g₀ M).hom m = M.ρ g₀⁻¹ m := by
  rfl

/-- **Remark 1.28 (b)** (p. 69): for a normal subgroup $H$ of $G$ and $g_0 \in G$, the recipe of Example 1.27 (d)
gives the endomorphism of $H^r(H, M)$ defined by the pair ($h \mapsto g_0hg_0^{-1}$, $m \mapsto g_0^{-1}m$). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.28 (b), the action of G on H^r(H, M), p. 69"]
noncomputable def conjAction (H : Subgroup G) [H.Normal] (M : Rep ℤ G) (r : ℕ) (g₀ : G) :
    groupCohomology (res H.subtype M) r ⟶ groupCohomology (res H.subtype M) r :=
  map (conjNormal H g₀) (conjNormalCompat H g₀ M) r

/-- **Remark 1.28 (b)**, the action property: $1$ acts trivially and the endomorphism for $g_1g_2$ is the one for
$g_1$ followed by the one for $g_2$ (so, written as maps, it is a right action; $g \mapsto$ the endomorphism for
$g^{-1}$ is a left action). -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.28 (b), p. 69"]
theorem conjAction_one_mul (H : Subgroup G) [H.Normal] (M : Rep ℤ G) (r : ℕ) :
    conjAction H M r 1 = 𝟙 _ ∧
      ∀ g₁ g₂ : G, conjAction H M r (g₁ * g₂) = conjAction H M r g₁ ≫ conjAction H M r g₂ := by
  constructor
  · rw [conjAction, ← map_id (B := res H.subtype M) (n := r)]
    exact map_congr (by ext; simp [conjNormal_apply])
      (by ext m; show M.ρ (1 : G)⁻¹ m = m; simp) r
  · intro g₁ g₂
    rw [conjAction, conjAction, conjAction,
      ← map_comp (conjNormal H g₁) (conjNormal H g₂) (conjNormalCompat H g₁ M)
        (conjNormalCompat H g₂ M) r]
    refine map_congr (by ext; simp [conjNormal_apply, mul_assoc]) ?_ r
    ext m
    show M.ρ (g₁ * g₂)⁻¹ m = M.ρ g₂⁻¹ (M.ρ g₁⁻¹ m)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev]

/-- **Remark 1.28 (b)**: the action of $G$ on $H^r(H, M)$ factors through $G/H$ (elements of $H$ act trivially).
This is Example 1.27 (d) for the group $H$, so it is proved from the named statement `Example1_27d`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 1.28 (b), p. 69"]
theorem remark_1_28b (h127d : Example1_27d) (H : Subgroup G) [H.Normal] (M : Rep ℤ G) (r : ℕ)
    (g : G) (hg : g ∈ H) : conjAction H M r g = 𝟙 _ := by
  have := h127d.map_conj_eq_id H ⟨g, hg⟩ (res H.subtype M) r
  rw [conjAction, ← this]
  refine map_congr (by ext; simp [conjNormal_apply]) ?_ r
  ext m
  rfl

/-! ## Example 1.29: corestriction -/

section Cor

variable (H : Subgroup G) [Fintype (G ⧸ H)]

omit [Fintype (G ⧸ H)] in
private lemma coindTerm_eq (M : Rep ℤ G) (φ : coind H.subtype (res H.subtype M)) (x y : G)
    (hxy : (x : G ⧸ H) = y) :
    M.ρ x (φ.1 x⁻¹) = M.ρ y (φ.1 y⁻¹) := by
  have hh : y⁻¹ * x ∈ H := QuotientGroup.eq.1 hxy.symm
  have key := φ.2 ⟨y⁻¹ * x, hh⟩ x⁻¹
  have e : ((⟨y⁻¹ * x, hh⟩ : H) : G) * x⁻¹ = y⁻¹ := by
    show y⁻¹ * x * x⁻¹ = y⁻¹
    group
  change φ.1 (((⟨y⁻¹ * x, hh⟩ : H) : G) * x⁻¹) = M.ρ (y⁻¹ * x) (φ.1 x⁻¹) at key
  rw [e] at key
  rw [key, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

omit [Fintype (G ⧸ H)] in
private lemma coindSum_indep (M : Rep ℤ G) (φ : coind H.subtype (res H.subtype M)) (s : G ⧸ H → G)
    (hs : ∀ q, (s q : G ⧸ H) = q) [Fintype (G ⧸ H)] :
    ∑ q : G ⧸ H, M.ρ (s q) (φ.1 (s q)⁻¹) = ∑ q : G ⧸ H, M.ρ q.out (φ.1 q.out⁻¹) :=
  Finset.sum_congr rfl fun q _ => coindTerm_eq H M φ _ _ ((hs q).trans (QuotientGroup.out_eq' q).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The $G$-homomorphism $\operatorname{Ind}_H^G(M) \to M$, $\varphi \mapsto \sum_{s \in S} s\varphi(s^{-1})$, $S$ a set
of left coset representatives (Example 1.29, p. 70); here $S$ is given by `Quotient.out`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.29, the map Ind_H^G M → M, p. 70"]
noncomputable def coindToSelf (M : Rep ℤ G) : coind H.subtype (res H.subtype M) ⟶ M :=
  letI : Module ℤ (Representation.coindV H.subtype (res H.subtype M).ρ) := Submodule.module _
  Rep.ofHom ⟨∑ q : G ⧸ H, (M.ρ q.out).comp
      ((LinearMap.proj q.out⁻¹).comp (Representation.coindV H.subtype (res H.subtype M).ρ).subtype),
    fun g => by
      refine LinearMap.ext fun φ => ?_
      have hs : ∀ q : G ⧸ H, (((g * (g⁻¹ • q).out : G)) : G ⧸ H) = q := by
        intro q
        have := MulAction.Quotient.mk_smul_out (H := H) g (g⁻¹ • q)
        simpa [smul_inv_smul] using this
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        Submodule.subtype_apply]
      change ∑ q : G ⧸ H, M.ρ q.out (((coind H.subtype (res H.subtype M)).ρ g φ).1 q.out⁻¹) =
        M.ρ g (∑ q : G ⧸ H, M.ρ q.out (φ.1 q.out⁻¹))
      rw [← coindSum_indep H M _ (fun q => g * (g⁻¹ • q).out) hs, map_sum]
      rw [← Equiv.sum_comp (MulAction.toPerm g⁻¹)
        (fun q : G ⧸ H => M.ρ g (M.ρ q.out (φ.1 q.out⁻¹)))]
      refine Finset.sum_congr rfl fun q _ => ?_
      show M.ρ (g * (g⁻¹ • q).out) (φ.1 ((g * (g⁻¹ • q).out)⁻¹ * g)) =
        M.ρ g (M.ρ (g⁻¹ • q).out (φ.1 (g⁻¹ • q).out⁻¹))
      rw [mul_inv_rev, inv_mul_cancel_right, map_mul, Module.End.mul_apply]⟩

theorem coindToSelf_apply (M : Rep ℤ G) (φ : coind H.subtype (res H.subtype M)) :
    (coindToSelf H M).hom φ = ∑ q : G ⧸ H, M.ρ q.out (φ.1 q.out⁻¹) := by
  simp [coindToSelf]

/-- The value $\sum_{s \in S} s\varphi(s^{-1})$ does not depend on the set $S$ of left coset representatives
(Example 1.29). -/
theorem coindToSelf_indep (M : Rep ℤ G) (φ : coind H.subtype (res H.subtype M)) (s : G ⧸ H → G)
    (hs : ∀ q, (s q : G ⧸ H) = q) :
    (coindToSelf H M).hom φ = ∑ q : G ⧸ H, M.ρ (s q) (φ.1 (s q)⁻¹) :=
  (coindToSelf_apply H M φ).trans (coindSum_indep H M φ s hs).symm

/-- **Corestriction** (Example 1.29, p. 70): $\mathrm{Cor} : H^r(H, M) \to H^r(G, M)$ for $H$ of finite index, the
inverse of Shapiro's isomorphism followed by the map induced by `coindToSelf`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.29, corestriction, p. 70"]
noncomputable def cor (M : Rep ℤ G) (r : ℕ) :
    groupCohomology (res H.subtype M) r ⟶ groupCohomology M r :=
  (coindIso (res H.subtype M) r).inv ≫ (functor ℤ G r).map (coindToSelf H M)

omit [Fintype (G ⧸ H)] in
private lemma functor_map_zsmul {A B : Rep ℤ G} (n : ℤ) (f : A ⟶ B) (r : ℕ) :
    (functor ℤ G r).map (n • f) = n • (functor ℤ G r).map f := by
  change (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r).map
      ((cochainsFunctor ℤ G).map (n • f)) =
    n • (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) r).map
      ((cochainsFunctor ℤ G).map f)
  rw [Functor.map_zsmul, Functor.map_zsmul]

private lemma toCoind_comp_coindToSelf (M : Rep ℤ G) :
    toCoind H M ≫ coindToSelf H M = (H.index : ℤ) • 𝟙 M := by
  apply Rep.hom_ext
  ext m
  change (coindToSelf H M).hom ((toCoind H M).hom m) = (H.index : ℤ) • m
  rw [coindToSelf_apply]
  have : ∀ q : G ⧸ H, M.ρ q.out (((toCoind H M).hom m).1 q.out⁻¹) = m := by
    intro q
    rw [toCoind_apply, ← Module.End.mul_apply, ← map_mul]
    simp
  simp only [this, Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]
  simp

/-- **Example 1.29**, degree $0$: on $H^0 = $ invariants, corestriction is the norm
$\mathrm{Nm}_{G/H} : M^H \to M^G$, $m \mapsto \sum_{s \in S} sm$. Shapiro's isomorphism enters the definition of
`cor`, and its value in degree $0$ is supplied by Example 1.27 (a) (named statement). -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.29, p. 70"]
theorem example_1_29_zero (h127a : Example1_27a) (M : Rep ℤ G) (x : (res H.subtype M).ρ.invariants) :
    ((H0Iso M).hom ((cor H M 0) ((H0Iso (res H.subtype M)).inv x)) : M) =
      ∑ q : G ⧸ H, M.ρ q.out (x : M) := by
  set z : groupCohomology (coind H.subtype (res H.subtype M)) 0 :=
    (coindIso (res H.subtype M) 0).inv ((H0Iso (res H.subtype M)).inv x) with hz
  have hmap : map H.subtype ((resCoindAdjunction ℤ H.subtype).counit.app (res H.subtype M)) 0 z =
      (H0Iso (res H.subtype M)).inv x := by
    rw [h127a.map_counit_eq G H (res H.subtype M) 0, hz]
    simp
  have h1 := map_id_comp_H0Iso_hom_apply (coindToSelf H M) z
  have h2 := map_H0Iso_hom_f_apply (f := H.subtype)
    ((resCoindAdjunction ℤ H.subtype).counit.app (res H.subtype M)) z
  set w := (H0Iso (coind H.subtype (res H.subtype M))).hom z with hw
  have hxw : (w.1 : coind H.subtype (res H.subtype M)).1 1 = (x : M) := by
    rw [hmap] at h2
    have hx : (ConcreteCategory.hom (H0Iso (res H.subtype M)).hom)
        ((ConcreteCategory.hom (H0Iso (res H.subtype M)).inv) x) = x :=
      Iso.inv_hom_id_apply _ _
    erw [hx] at h2
    exact h2.symm
  have hconst : ∀ g : G, (w.1 : coind H.subtype (res H.subtype M)).1 g = (x : M) := by
    intro g
    have hg : (w.1 : coind H.subtype (res H.subtype M)).1 (1 * g) =
        (w.1 : coind H.subtype (res H.subtype M)).1 1 :=
      congrArg (fun φ : coind H.subtype (res H.subtype M) => φ.1 1) (w.2 g)
    rw [one_mul] at hg
    rw [hg]
    exact hxw
  have h0 : (ConcreteCategory.hom (cor H M 0)) ((H0Iso (res H.subtype M)).inv x) =
      (map (MonoidHom.id G) (coindToSelf H M) 0) z := rfl
  rw [h0, h1]
  change (coindToSelf H M).hom w.1 = _
  rw [coindToSelf_apply]
  exact Finset.sum_congr rfl fun q _ => by rw [hconst]

set_option backward.isDefEq.respectTransparency false in
/-- **Proposition 1.30** (p. 70). For $H$ of finite index, $\mathrm{Cor} \circ \mathrm{Res} : H^r(G, M) \to H^r(G, M)$
is multiplication by $(G : H)$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.30, p. 70"]
theorem prop_1_30 (M : Rep ℤ G) (r : ℕ) :
    resShapiro H M r ≫ cor H M r = (H.index : ℤ) • 𝟙 (groupCohomology M r) := by
  have h1 : resShapiro H M r ≫ cor H M r =
      (functor ℤ G r).map (toCoind H M ≫ coindToSelf H M) := by
    simp only [resShapiro, cor, Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  rw [h1, toCoind_comp_coindToSelf, functor_map_zsmul, CategoryTheory.Functor.map_id]
  rfl

/-- Proposition 1.30 with Mathlib's restriction map (via Example 1.27 (b)). -/
theorem prop_1_30_map (h127a : Example1_27a) (M : Rep ℤ G) (r : ℕ) :
    map H.subtype (𝟙 (res H.subtype M)) r ≫ cor H M r = (H.index : ℤ) • 𝟙 (groupCohomology M r) := by
  rw [example_1_27b h127a]; exact prop_1_30 H M r

end Cor

/-- **Corollary 1.31** (p. 70). If $(G : 1) = m$ is finite, then $mH^r(G, M) = 0$ for $r > 0$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 1.31, p. 70"]
theorem cor_1_31 [Finite G] (M : Rep ℤ G) (r : ℕ) (hr : 0 < r) (x : groupCohomology M r) :
    (Nat.card G : ℤ) • x = 0 := by
  classical
  have : Fintype (G ⧸ (⊥ : Subgroup G)) := Fintype.ofFinite _
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hz := isZero_groupCohomology_succ_of_subsingleton
    (res (⊥ : Subgroup G).subtype M) r'
  have h0 : resShapiro (⊥ : Subgroup G) M (r' + 1) ≫ cor (⊥ : Subgroup G) M (r' + 1) = 0 := by
    rw [hz.eq_of_tgt (resShapiro (⊥ : Subgroup G) M (r' + 1)) 0, Limits.zero_comp]
  rw [prop_1_30, Subgroup.index_bot] at h0
  have := congrArg (fun f => (ConcreteCategory.hom f) x) h0
  simpa using this

private lemma fg_of_module_finite {A : Type*} [AddCommGroup A] (h : Module ℤ A)
    [@Module.Finite ℤ A _ _ h] : AddGroup.FG A := by
  have e : h = AddCommGroup.toIntModule A := Subsingleton.elim _ _
  subst e
  exact Module.Finite.iff_addGroup_fg.1 ‹_›

private lemma fg_pi_aux {A ι : Type*} [AddCommGroup A] [Finite ι] (h : AddGroup.FG A) :
    AddGroup.FG (ι → A) := by
  have := Module.Finite.iff_addGroup_fg.2 h
  exact fg_of_module_finite (Pi.module ι (fun _ => A) ℤ)

private lemma fg_quot_aux {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (hC : AddGroup.FG C) (i : B →+ C) (hi : Function.Injective i) (π : B →+ A)
    (hπ : Function.Surjective π) : AddGroup.FG A := by
  have := Module.Finite.iff_addGroup_fg.2 hC
  have := isNoetherian_of_isNoetherianRing_of_finite ℤ C
  have : Module.Finite ℤ B := Module.Finite.of_injective i.toIntLinearMap hi
  have : Module.Finite ℤ A := Module.Finite.of_surjective π.toIntLinearMap hπ
  exact Module.Finite.iff_addGroup_fg.1 this

private lemma finite_of_fg_bounded {A : Type*} [AddCommGroup A] (hfg : AddGroup.FG A) (n : ℕ)
    (hn : n ≠ 0) (h : ∀ x : A, n • x = 0) : Finite A := by
  have := Module.Finite.iff_addGroup_fg.2 hfg
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
  rw [Submonoid.smul_def]
  simpa using h x

set_option backward.isDefEq.respectTransparency false in
/-- **Corollary 1.32** (p. 70). If $G$ is finite and $M$ is finitely generated as an abelian group, then
$H^r(G, M)$ is finite for $r > 0$. (Milne writes "$H^r(G, M)$ is finite" without $r > 0$; for $r = 0$ it fails:
$H^0(G, \mathbb Z) = \mathbb Z$.) -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 1.32, p. 70"]
theorem cor_1_32 [Finite G] (M : Rep ℤ G) [Module.Finite ℤ M] (r : ℕ) (hr : 0 < r) :
    Finite (groupCohomology M r) := by
  have hM : AddGroup.FG M.V := fg_of_module_finite _
  have hC : AddGroup.FG ((inhomogeneousCochains M).X r) :=
    fg_pi_aux (ι := Fin r → G) hM
  have hinj : Function.Injective ((iCocycles M r).hom) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hsurj : Function.Surjective ((π M r).hom) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hH : AddGroup.FG (groupCohomology M r) :=
    fg_quot_aux hC (iCocycles M r).hom.toAddMonoidHom hinj (π M r).hom.toAddMonoidHom hsurj
  exact finite_of_fg_bounded hH (Nat.card G) Nat.card_pos.ne' (fun x => by
    have := cor_1_31 M r hr x
    simpa using this)

private lemma bezout_aux {A : Type*} [AddCommGroup A] (x : A) (n m a b : ℤ)
    (hab : a * n + b * m = 1) (h1 : n • x = 0) (h2 : m • x = 0) : x = 0 := by
  calc x = (a * n + b * m) • x := by rw [hab, one_smul]
    _ = 0 := by rw [add_zsmul, mul_zsmul, mul_zsmul, h1, h2, zsmul_zero, zsmul_zero, add_zero]

/-- **Corollary 1.33** (p. 71), with Milne's second construction of restriction (`resShapiro`, Example 1.27 (b)).
Let $G$ be finite and $G_p$ a Sylow $p$-subgroup. For every $G$-module $M$, restriction
$H^r(G, M) \to H^r(G_p, M)$ is injective on the $p$-primary component of $H^r(G, M)$. -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 1.33, p. 71"]
theorem cor_1_33_resShapiro [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M : Rep ℤ G) (r : ℕ)
    (x : groupCohomology M r) (hx : ∃ k : ℕ, (p ^ k : ℤ) • x = 0)
    (h : resShapiro (P : Subgroup G) M r x = 0) : x = 0 := by
  classical
  have : Fintype (G ⧸ (P : Subgroup G)) := Fintype.ofFinite _
  obtain ⟨k, hk⟩ := hx
  have hidx : ((P : Subgroup G).index : ℤ) • x = 0 := by
    have := congrArg (fun f => (ConcreteCategory.hom f) x) (prop_1_30 (P : Subgroup G) M r)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, h, map_zero] at this
    simpa using this.symm
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) ((P : Subgroup G).index : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 P.not_dvd_index)
  obtain ⟨a, b, hab⟩ := hcop
  push_cast at hab
  exact bezout_aux x _ _ a b hab hk hidx

/-- **Corollary 1.33** (p. 71), with restriction defined by the compatible pair (Mathlib's
`groupCohomology.map`), from Example 1.27 (a) (named statement). -/
@[kb "milne2020cft" "v4.03, Ch. II, Cor. 1.33, p. 71"]
theorem cor_1_33 (h127a : Example1_27a) [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M : Rep ℤ G)
    (r : ℕ) (x : groupCohomology M r) (hx : ∃ k : ℕ, (p ^ k : ℤ) • x = 0)
    (h : map (P : Subgroup G).subtype (𝟙 _) r x = 0) : x = 0 := by
  rw [example_1_27b h127a] at h
  exact cor_1_33_resShapiro p P M r x hx h

/-! ## Proposition 1.34: inflation-restriction -/

/-- **Proposition 1.34** (p. 71), as a named statement. Let $H$ be a normal subgroup of $G$, $M$ a $G$-module and
$r > 0$. If $H^j(H, M) = 0$ for $0 < j < r$, then
$0 \to H^r(G/H, M^H) \xrightarrow{\mathrm{Inf}} H^r(G, M) \xrightarrow{\mathrm{Res}} H^r(H, M)$ is exact
(Mathlib's short complex `groupCohomology.HInfRes`; Mathlib proves the case $r = 1$, `H1InfRes_exact`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.34, p. 71"]
structure Prop1_34 : Prop where
  exact : ∀ (G : Type) [Group G] (H : Subgroup G) [H.Normal] (M : Rep ℤ G) (r : ℕ) [NeZero r],
    (∀ j : ℕ, 0 < j → j < r → Limits.IsZero (groupCohomology (res H.subtype M) j)) →
      Mono (HInfRes M H r).f ∧ (HInfRes M H r).Exact

/-- **Proposition 1.34** for $r = 1$ (no hypothesis), from Mathlib. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 1.34, case r = 1, p. 71"]
theorem prop_1_34_one (H : Subgroup G) [H.Normal] (M : Rep ℤ G) :
    Mono (HInfRes M H 1).f ∧ (HInfRes M H 1).Exact :=
  ⟨inferInstanceAs (Mono (H1InfRes M H).f), H1InfRes_exact M H⟩

set_option backward.isDefEq.respectTransparency false in
/-- Hilbert's Theorem 90 for $\Omega/L$, transported to the subgroup $\operatorname{Gal}(\Omega/L) \subseteq
\operatorname{Gal}(\Omega/K)$: $H^1(\operatorname{Gal}(\Omega/L), \Omega^\times) = 0$. -/
lemma isZero_h1_fixingSubgroup (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] (L : IntermediateField K Ω) :
    Limits.IsZero (groupCohomology (res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K Ω)) 1) := by
  have hz : ∀ a : groupCohomology (res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K Ω)) 1,
      a = 0 := by
    intro a
    refine H1_induction_on a fun x => (H1π_eq_zero_iff x).2 ?_
    have hx := (mem_cocycles₁_iff x.1).1 x.2
    let e := IntermediateField.fixingSubgroupEquiv L
    let xa : L.fixingSubgroup → Additive Ωˣ := fun g => x g
    let f' : (Ω ≃ₐ[L] Ω) → Ωˣ := fun σ => Additive.toMul (xa (e.symm σ))
    have hf' : IsMulCocycle₁ f' := by
      intro σ τ
      have := hx (e.symm σ) (e.symm τ)
      have hact : ∀ u : Ωˣ, ((e.symm σ).1 : Ω ≃ₐ[K] Ω) • u = σ • u := by
        intro u; ext; simp [AlgEquiv.smul_units_def, e]
      have this' : xa (e.symm σ * e.symm τ) =
          Additive.ofMul (((e.symm σ).1 : Ω ≃ₐ[K] Ω) • (xa (e.symm τ)).toMul) + xa (e.symm σ) :=
        this
      change Additive.toMul (xa (e.symm (σ * τ))) =
        σ • Additive.toMul (xa (e.symm τ)) * Additive.toMul (xa (e.symm σ))
      rw [map_mul, this', toMul_add, toMul_ofMul, hact]
    obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f' hf'
    refine ⟨Additive.ofMul β, funext fun g => ?_⟩
    have := hβ (e g)
    have h2 : e g • β = (g : Ω ≃ₐ[K] Ω) • β := by
      ext; simp [AlgEquiv.smul_units_def, e]
    rw [h2] at this
    apply Additive.toMul.injective
    refine this.trans ?_
    simp [f', e]
    rfl
  have : Subsingleton (groupCohomology (res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K Ω)) 1) :=
    ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- **Example 1.36** (p. 72). Let $\Omega \supseteq L \supseteq K$ with $\Omega/K$ and $L/K$ finite Galois,
$G = \operatorname{Gal}(\Omega/K)$, $H = \operatorname{Gal}(\Omega/L)$ (normal, since $L/K$ is Galois:
`InfiniteGalois.normal_iff_isGalois`). Then $0 \to H^2(G/H, (\Omega^\times)^H) \to H^2(G, \Omega^\times) \to
H^2(H, \Omega^\times)$ is exact; $(\Omega^\times)^H = L^\times$. Proved from Proposition 1.34 (named statement) and
Hilbert's Theorem 90 for $\Omega/L$. Milne allows infinite Galois extensions; here they are finite (§1 has no
topology on $G$). -/
@[kb "milne2020cft" "v4.03, Ch. II, Example 1.36, p. 72"]
theorem example_1_36 (h134 : Prop1_34) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω] (L : IntermediateField K Ω) [L.fixingSubgroup.Normal] :
    Mono (HInfRes (Rep.ofAlgebraAutOnUnits K Ω) L.fixingSubgroup 2).f ∧
      (HInfRes (Rep.ofAlgebraAutOnUnits K Ω) L.fixingSubgroup 2).Exact := by
  refine h134.exact _ L.fixingSubgroup (Rep.ofAlgebraAutOnUnits K Ω) 2 ?_
  intro j hj0 hj2
  obtain rfl : j = 1 := by omega
  exact isZero_h1_fixingSubgroup K Ω L

end NumberFieldKB.MilneCFT
