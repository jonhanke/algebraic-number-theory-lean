import Mathlib.RepresentationTheory.Homological.ContCohomology.Sha
import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
import NumberFieldKB.MilneEC.Ch4Cohomology

/-!
# Degree-one continuous cohomology of a discrete module

Mathlib defines continuous cohomology (`continuousCohomology n A`, `ContCohomology/Basic.lean`) as the cohomology
of the homogeneous cochains: in degree one these are the continuous maps $F : G \to C(G, A)$ with
$F(gx)(gy) = g\,F(x)(y)$, with differential $(dF)(x)(y)(z) = F(y)(z) - F(x)(z) + F(x)(y)$. At the pinned Mathlib only
degree zero is identified (`ContinuousCohomology.zeroIso`).

This file identifies degree one with Milne's $H^1$ (*Elliptic Curves*, IV, §1, pdf p. 114; `H1cont`): continuous
crossed homomorphisms modulo principal ones, for a discrete module ($A$ discrete and every stabilizer open). The map
sends a homogeneous cocycle $F$ to the crossed homomorphism $g \mapsto F(1)(g)$; its inverse sends $c$ to
$x \mapsto (y \mapsto x\,c(x^{-1}y))$.

## Main results
* `ContH1.equiv`: `continuousCohomology 1 A ≃+ H1cont B` for a discrete module `A` and a `G`-module `B` with an
  equivariant additive isomorphism `A ≃+ B`.
* `ContH1.equiv_π`: the isomorphism on the class of a cocycle.
* `ContH1.equiv_map`: compatibility with the maps induced by a continuous group homomorphism and a morphism of
  modules (restriction to a subgroup, in particular).
-/

open CategoryTheory groupCohomology TopRep ContRepresentation

namespace NumberFieldKB.MilneEC.ContH1

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.Functor.mapHomologicalComplex

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Cochains

variable (A : TopRep ℤ G)

/-- The zeroth differential: $(df)(x)(y) = f(y) - f(x)$. -/
theorem d01_apply (f : (homogeneousCochains A).X 0) (x y : G) :
    (((homogeneousCochains A).d 0 1).hom f).1 x y = f.1 y - f.1 x := by
  rw [homogeneousCochains.d_apply]
  rfl

/-- The first differential: $(dF)(x)(y)(z) = F(y)(z) - (F(x)(z) - F(x)(y))$. -/
theorem d12_apply (F : (homogeneousCochains A).X 1) (x y z : G) :
    (((homogeneousCochains A).d 1 2).hom F).1 x y z = F.1 y z - (F.1 x z - F.1 x y) := by
  rw [homogeneousCochains.d_apply]
  rfl

/-- A homogeneous $0$-cochain is equivariant: $f(gx) = g f(x)$. -/
theorem inv0 (f : (homogeneousCochains A).X 0) (g x : G) : f.1 (g * x) = A.ρ g (f.1 x) := by
  have h := congrArg (fun f : C(G, A) => f (g * x)) (f.2 g)
  simpa using h.symm

/-- A homogeneous $1$-cochain is equivariant: $F(gx)(gy) = g F(x)(y)$. -/
theorem inv1 (F : (homogeneousCochains A).X 1) (g x y : G) : F.1 (g * x) (g * y) = A.ρ g (F.1 x y) := by
  have h := congrArg (fun F : C(G, C(G, A)) => F (g * x) (g * y)) (F.2 g)
  simpa using h.symm

/-- The second map of the short complex at degree one is the first differential. -/
theorem sc1_g_eq_zero_iff (F : (homogeneousCochains A).X 1) :
    ((homogeneousCochains A).sc 1).g.hom F = 0 ↔ ((homogeneousCochains A).d 1 2).hom F = 0 := by
  have key : ∀ j (_ : j = 2), ((homogeneousCochains A).d 1 j).hom F = 0 ↔
      ((homogeneousCochains A).d 1 2).hom F = 0 := by
    rintro _ rfl; rfl
  exact key _ (CochainComplex.next ℕ 1)

/-- The first map of the short complex at degree one is the zeroth differential. -/
theorem sc1_f_apply_iff (F : (homogeneousCochains A).X 1) :
    (∃ f, ((homogeneousCochains A).sc 1).f.hom f = F) ↔ ∃ f, ((homogeneousCochains A).d 0 1).hom f = F := by
  have key : ∀ j (_ : j = 0), (∃ f : (homogeneousCochains A).X j, ((homogeneousCochains A).d j 1).hom f = F) ↔
      ∃ f, ((homogeneousCochains A).d 0 1).hom f = F := by
    rintro _ rfl; rfl
  exact key _ (CochainComplex.prev_nat_succ 0)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit left homology data at degree one: kernel of the first differential modulo the image of the
zeroth (`TopModuleCat.ker`, `TopModuleCat.coker`). -/
noncomputable def D : ((homogeneousCochains A).sc 1).LeftHomologyData :=
  ⟨_, _, _, _, _, TopModuleCat.isLimitKer _, by simp, TopModuleCat.isColimitCoker _⟩

end Cochains

/-! ## Discrete modules -/

section Discrete

variable (A : TopRep ℤ G) [DiscreteTopology A] (B : Rep.{0} ℤ G) (e : A ≃+ B)
  (he : ∀ (g : G) (a : A), e (A.ρ g a) = B.ρ g (e a))

omit [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology A] in
include he in
theorem he_symm (g : G) (b : B) : e.symm (B.ρ g b) = A.ρ g (e.symm b) := by
  apply e.injective
  rw [he]
  simp

theorem ρ_mul_apply (g h : G) (a : A) : A.ρ (g * h) a = A.ρ g (A.ρ h a) := by
  rw [map_mul]
  rfl

/-- The action $G \times A \to A$ is continuous when every stabilizer is open ($A$ discrete). -/
theorem continuous_act (hA : ∀ a : A, IsOpen {g : G | A.ρ g a = a}) :
    Continuous (fun p : G × A => A.ρ p.1 p.2) := by
  rw [continuous_discrete_rng]
  intro b
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨g0, a0⟩ hb
  refine ⟨((fun g => g0⁻¹ * g) ⁻¹' {g | A.ρ g a0 = a0}) ×ˢ {a0}, ?_, ?_, ?_⟩
  · rintro ⟨g, a⟩ ⟨hg, ha⟩
    have ha' : a = a0 := ha
    subst ha'
    have hg' : A.ρ (g0⁻¹ * g) a = a := hg
    show A.ρ g a = b
    have : A.ρ g a = A.ρ g0 (A.ρ (g0⁻¹ * g) a) := by rw [← ρ_mul_apply, mul_inv_cancel_left]
    rw [this, hg']
    exact hb
  · exact ((hA a0).preimage (continuous_const.mul continuous_id)).prod (isOpen_discrete _)
  · refine ⟨?_, rfl⟩
    show A.ρ (g0⁻¹ * g0) a0 = a0
    rw [inv_mul_cancel, map_one]
    rfl

/-- The inhomogeneous cochain $g \mapsto F(1)(g)$ of a homogeneous $1$-cochain $F$. -/
def toFun (F : (homogeneousCochains A).X 1) : G → B := fun g => e (F.1 1 g)

include he in
theorem toFun_mem (F : (homogeneousCochains A).X 1) (hF : ((homogeneousCochains A).d 1 2).hom F = 0) :
    toFun A B e F ∈ cocycles₁ B := by
  rw [mem_cocycles₁_iff]
  intro g h
  have h1 : F.1 g (g * h) - (F.1 1 (g * h) - F.1 1 g) = 0 := by
    rw [← d12_apply, hF]
    rfl
  have h2 := inv1 A F g 1 h
  rw [mul_one] at h2
  have h3 : F.1 1 (g * h) = A.ρ g (F.1 1 h) + F.1 1 g := by
    rw [← h2]
    rw [sub_eq_zero] at h1
    rw [h1]; abel
  simp only [toFun, h3, map_add, he]

theorem toFun_continuous (F : (homogeneousCochains A).X 1) : @Continuous G B _ ⊥ (toFun A B e F) := by
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  exact (continuous_of_discreteTopology (f := e)).comp (F.1 1).continuous

theorem i_mem (z : (D A).K) : ((homogeneousCochains A).d 1 2).hom ((D A).i.hom z) = 0 :=
  (sc1_g_eq_zero_iff A _).1 (by rw [← ConcreteCategory.comp_apply, (D A).wi]; rfl)

/-- The crossed homomorphism of a homogeneous $1$-cocycle in the kernel of the first differential. -/
noncomputable def toCoc (z : (D A).K) : cocycles₁ B :=
  ⟨toFun A B e ((D A).i.hom z), toFun_mem A B e he _ (i_mem A z)⟩

theorem toCoc_apply (z : (D A).K) (g : G) : toCoc A B e he z g = e (((D A).i.hom z).1 1 g) := rfl

/-- The class of the crossed homomorphism of a homogeneous $1$-cocycle. -/
noncomputable def Φ : (D A).K →+ H1 B where
  toFun z := H1π B (toCoc A B e he z)
  map_zero' := by
    have : toCoc A B e he 0 = 0 := by
      ext g
      rw [toCoc_apply, map_zero]
      exact map_zero e
    rw [this, map_zero]
  map_add' x y := by
    have : toCoc A B e he (x + y) = toCoc A B e he x + toCoc A B e he y := by
      ext g
      have key : ((D A).i.hom (x + y)).1 1 g = ((D A).i.hom x).1 1 g + ((D A).i.hom y).1 1 g := by
        rw [map_add]; rfl
      show e (((D A).i.hom (x + y)).1 1 g) = e (((D A).i.hom x).1 1 g) + e (((D A).i.hom y).1 1 g)
      rw [key, map_add]
    rw [this, map_add]

variable (hA : ∀ a : A, IsOpen {g : G | A.ρ g a = a})

/-- The homogeneous $0$-cochain $x \mapsto x\,m$. -/
noncomputable def orbit0 (m : A) : (homogeneousCochains A).X 0 :=
  ⟨⟨fun x => A.ρ x m, (continuous_act A hA).comp (continuous_id.prodMk continuous_const)⟩, fun g => by
    ext x
    show A.ρ g (A.ρ (g⁻¹ * x) m) = A.ρ x m
    rw [← ρ_mul_apply, mul_inv_cancel_left]⟩

theorem orbit0_apply (m : A) (x : G) : (orbit0 A hA m).1 x = A.ρ x m := rfl

/-- A homogeneous $1$-cochain is determined by $F(1)$: $F(x)(y) = x\,F(1)(x^{-1}y)$. -/
theorem homog_eq (F : (homogeneousCochains A).X 1) (x y : G) : F.1 x y = A.ρ x (F.1 1 (x⁻¹ * y)) := by
  have := inv1 A F x 1 (x⁻¹ * y)
  rwa [mul_one, mul_inv_cancel_left] at this

include he hA in
/-- The kernel of `Φ` is the image of the zeroth differential. -/
theorem mem_ker_Φ_iff (z : (D A).K) : Φ A B e he z = 0 ↔ ∃ w, (D A).f'.hom w = z := by
  have hi : Function.Injective (D A).i.hom := Subtype.val_injective
  have hfi : ∀ w, (D A).i.hom ((D A).f'.hom w) = ((homogeneousCochains A).sc 1).f.hom w := fun w => by
    rw [← ConcreteCategory.comp_apply, (D A).f'_i]
  constructor
  · intro hz
    obtain ⟨m, hm⟩ := (H1π_eq_zero_iff (toCoc A B e he z)).1 hz
    have hm' : ∀ g, e (((D A).i.hom z).1 1 g) = B.ρ g m - m := fun g => by
      rw [← toCoc_apply A B e he]
      exact (congrFun hm g).symm
    have hd : ((homogeneousCochains A).d 0 1).hom (orbit0 A hA (e.symm m)) = (D A).i.hom z := by
      apply Subtype.ext
      ext x y
      rw [d01_apply, orbit0_apply, orbit0_apply, homog_eq A ((D A).i.hom z) x y]
      have : ((D A).i.hom z).1 1 (x⁻¹ * y) = A.ρ (x⁻¹ * y) (e.symm m) - e.symm m := by
        apply e.injective
        rw [hm', map_sub, he, AddEquiv.apply_symm_apply]
      rw [this, map_sub, ← ρ_mul_apply, mul_inv_cancel_left]
    obtain ⟨w, hw⟩ := (sc1_f_apply_iff A _).2 ⟨_, hd⟩
    exact ⟨w, hi (by rw [hfi, hw])⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨u, hu⟩ := (sc1_f_apply_iff A _).1 ⟨w, rfl⟩
    refine (H1π_eq_zero_iff _).2 ⟨e (u.1 1), funext fun g => ?_⟩
    show B.ρ g (e (u.1 1)) - e (u.1 1) = e (((D A).i.hom ((D A).f'.hom w)).1 1 g)
    rw [hfi, ← hu, d01_apply, ← he, ← map_sub]
    have := inv0 A u g 1
    rw [mul_one] at this
    rw [this]

/-- The homogeneous $1$-cochain $x \mapsto (y \mapsto x\,c(x^{-1}y))$ of a continuous crossed homomorphism. -/
noncomputable def homog (c : cocycles₁ B) (hc : @Continuous G B _ ⊥ c) : (homogeneousCochains A).X 1 :=
  ⟨ContinuousMap.curry ⟨fun p : G × G => A.ρ p.1 (e.symm (c (p.1⁻¹ * p.2))), by
    letI : TopologicalSpace B := ⊥
    haveI : DiscreteTopology B := ⟨rfl⟩
    have hc' : Continuous (fun g => e.symm (c g)) := continuous_of_discreteTopology.comp hc
    exact (continuous_act A hA).comp (continuous_fst.prodMk
      (hc'.comp (continuous_fst.inv.mul continuous_snd)))⟩, fun g => by
    ext x y
    show A.ρ g (A.ρ (g⁻¹ * x) (e.symm (c ((g⁻¹ * x)⁻¹ * (g⁻¹ * y))))) = A.ρ x (e.symm (c (x⁻¹ * y)))
    rw [← ρ_mul_apply, mul_inv_cancel_left]
    congr 3
    group⟩

theorem homog_apply (c : cocycles₁ B) (hc : @Continuous G B _ ⊥ c) (x y : G) :
    (homog A B e hA c hc).1 x y = A.ρ x (e.symm (c (x⁻¹ * y))) := rfl

include he in
theorem homog_mem (c : cocycles₁ B) (hc : @Continuous G B _ ⊥ c) :
    ((homogeneousCochains A).d 1 2).hom (homog A B e hA c hc) = 0 := by
  have hcoc : ∀ a b : G, e.symm (c (a * b)) = A.ρ a (e.symm (c b)) + e.symm (c a) := fun a b => by
    rw [(mem_cocycles₁_iff (c : G → B)).1 c.2 a b, map_add, he_symm A B e he]
  apply Subtype.ext
  ext x y z
  rw [d12_apply, homog_apply, homog_apply, homog_apply]
  have : x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) := by group
  rw [this, hcoc (x⁻¹ * y) (y⁻¹ * z), map_add, ← ρ_mul_apply, mul_inv_cancel_left]
  show _ = (0 : A)
  abel

include he hA in
/-- The image of `Φ` is Milne's $H^1$: the classes of continuous crossed homomorphisms. -/
theorem mem_range_Φ_iff (x : H1 B) : (∃ z, Φ A B e he z = x) ↔ x ∈ H1cont B := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨toCoc A B e he z, toFun_continuous A B e _, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    let z : (D A).K := ⟨homog A B e hA c hc, (sc1_g_eq_zero_iff A _).2 (homog_mem A B e he hA c hc)⟩
    refine ⟨z, ?_⟩
    show H1π B (toCoc A B e he z) = H1π B c
    congr 1
    ext g
    rw [toCoc_apply]
    show e (A.ρ 1 (e.symm (c (1⁻¹ * g)))) = c g
    rw [inv_one, one_mul, map_one]
    exact e.apply_symm_apply _

/-- `Φ` on the homology of `D A`, the quotient of the cocycles by the coboundaries. -/
noncomputable def Ψ : (D A).H →+ H1 B :=
  QuotientAddGroup.lift (LinearMap.range (D A).f'.hom.toLinearMap).toAddSubgroup (Φ A B e he) (by
    rintro _ ⟨w, rfl⟩
    exact (mem_ker_Φ_iff A B e he hA _).2 ⟨w, rfl⟩)

theorem Ψ_π (z : (D A).K) : Ψ A B e he hA ((D A).π.hom z) = Φ A B e he z := rfl

theorem Ψ_injective : Function.Injective (Ψ A B e he hA) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := (LinearMap.range (D A).f'.hom.toLinearMap).toAddSubgroup) x
  obtain ⟨u, hu⟩ := (mem_ker_Φ_iff A B e he hA w).1 hx
  exact (QuotientAddGroup.eq_zero_iff _).2 ⟨u, hu⟩

theorem range_Ψ : (Ψ A B e he hA).range = H1cont B := by
  ext x
  rw [AddMonoidHom.mem_range, ← mem_range_Φ_iff A B e he hA]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective
      (s := (LinearMap.range (D A).f'.hom.toLinearMap).toAddSubgroup) y
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(D A).π.hom w, rfl⟩

/-- The homology of `D A` is Milne's $H^1$. -/
noncomputable def equivH : (D A).H ≃+ H1cont B :=
  (AddMonoidHom.ofInjective (Ψ_injective A B e he hA)).trans (AddEquiv.addSubgroupCongr (range_Ψ A B e he hA))

omit [DiscreteTopology A] in
/-- Degree-one continuous cohomology is the homology of the explicit left homology data `D A`. -/
noncomputable def isoH : continuousCohomology 1 A ≃+ (D A).H where
  toFun x := (D A).homologyIso.hom.hom x
  invFun y := (D A).homologyIso.inv.hom y
  left_inv x := by
    change ((D A).homologyIso.hom ≫ (D A).homologyIso.inv).hom x = x
    rw [Iso.hom_inv_id]
    rfl
  right_inv y := by
    change ((D A).homologyIso.inv ≫ (D A).homologyIso.hom).hom y = y
    rw [Iso.inv_hom_id]
    rfl
  map_add' x y := map_add _ x y

/-- **Degree-one continuous cohomology of a discrete module is Milne's $H^1$**: `continuousCohomology 1 A`
(homogeneous cochains) is isomorphic to `H1cont B` (continuous crossed homomorphisms modulo principal ones). -/
noncomputable def equiv : continuousCohomology 1 A ≃+ H1cont B :=
  (isoH A).trans (equivH A B e he hA)

omit [DiscreteTopology A] in
theorem isoH_π (z : ContinuousCohomology.cocycles A 1) :
    isoH A (((homogeneousCochains A).homologyπ 1).hom z) = (D A).π.hom ((D A).cyclesIso.hom.hom z) := by
  change (((homogeneousCochains A).sc 1).homologyπ ≫ (D A).homologyIso.hom).hom z = _
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rfl

/-- The isomorphism on the class of a homogeneous cocycle $F$: the class of $g \mapsto F(1)(g)$. -/
theorem equiv_π (z : ContinuousCohomology.cocycles A 1) :
    (equiv A B e he hA (((homogeneousCochains A).homologyπ 1).hom z) : H1 B) =
      H1π B ⟨toFun A B e (((homogeneousCochains A).iCycles 1).hom z),
        toFun_mem A B e he _ (by
          change ((homogeneousCochains A).d 1 2).hom ((((homogeneousCochains A).sc 1).iCycles).hom z) = 0
          rw [← (D A).cyclesIso_hom_comp_i]
          exact i_mem A _)⟩ := by
  change Ψ A B e he hA (isoH A _) = _
  rw [isoH_π, Ψ_π]
  change H1π B (toCoc A B e he _) = _
  congr 2

/-- `equiv_π` for any crossed homomorphism equal to $g \mapsto F(1)(g)$. -/
theorem equiv_π_eq (z : ContinuousCohomology.cocycles A 1) (c : cocycles₁ B)
    (hc : ∀ g, (c : G → B) g = e ((((homogeneousCochains A).iCycles 1).hom z).1 1 g)) :
    (equiv A B e he hA (((homogeneousCochains A).homologyπ 1).hom z) : H1 B) = H1π B c := by
  rw [equiv_π]
  congr 1
  ext g
  exact (hc g).symm

end Discrete

/-! ## Naturality -/

section Naturality

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (φ : H →ₜ* G)
  {A : TopRep ℤ G} {A' : TopRep ℤ H} (f : res φ A ⟶ A')

/-- The cochain map induced by `φ` and `f` in degree one: $F \mapsto ((x, y) \mapsto f(F(\varphi x)(\varphi y)))$. -/
theorem cochainsMap_one_apply (F : (homogeneousCochains A).X 1) (x y : H) :
    (((ContinuousCohomology.cochainsMap φ f).f 1).hom F).1 x y = f.hom (F.1 (φ x) (φ y)) := rfl

omit φ f in
/-- Every degree-one continuous cohomology class is the class of a homogeneous cocycle. -/
theorem homologyπ_surjective (x : continuousCohomology 1 A) :
    ∃ z, ((homogeneousCochains A).homologyπ 1).hom z = x := by
  obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective
    (s := (LinearMap.range (D A).f'.hom.toLinearMap).toAddSubgroup) (isoH A x)
  refine ⟨(D A).cyclesIso.inv.hom w, (isoH A).injective ((isoH_π A _).trans ?_)⟩
  rw [← hw]
  change (D A).π.hom (((D A).cyclesIso.inv ≫ (D A).cyclesIso.hom).hom w) = _
  rw [Iso.inv_hom_id]
  rfl

variable [DiscreteTopology A] [DiscreteTopology A'] (hA : ∀ a : A, IsOpen {g : G | A.ρ g a = a})
  (hA' : ∀ a : A', IsOpen {g : H | A'.ρ g a = a})
  {B : Rep.{0} ℤ G} {B' : Rep.{0} ℤ H} (e : A ≃+ B) (he : ∀ (g : G) (a : A), e (A.ρ g a) = B.ρ g (e a))
  (e' : A' ≃+ B') (he' : ∀ (g : H) (a : A'), e' (A'.ρ g a) = B'.ρ g (e' a))
  (k : Rep.res (φ : H →* G) B ⟶ B') (hk : ∀ a : A, e' (f.hom a) = k.hom (e a))

include hk in
/-- **Naturality**: the isomorphism `equiv` carries the map on continuous cohomology induced by `φ` and `f` to
the map on $H^1$ induced by `φ` and `k` (for compatible `f` and `k`). -/
theorem equiv_map (x : continuousCohomology 1 A) :
    (equiv A' B' e' he' hA' ((ContinuousCohomology.map φ f 1).hom x) : H1 B') =
      (groupCohomology.map (φ : H →* G) k 1).hom (equiv A B e he hA x : H1 B) := by
  obtain ⟨z, rfl⟩ := homologyπ_surjective x
  have h1 : (ContinuousCohomology.map φ f 1).hom (((homogeneousCochains A).homologyπ 1).hom z) =
      ((homogeneousCochains A').homologyπ 1).hom ((ContinuousCohomology.cocyclesMap φ f 1).hom z) := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
    exact congrArg (fun m => m.hom z) (ContinuousCohomology.π_map φ f 1)
  rw [h1, equiv_π A B e he hA z]
  have h3 (c : cocycles₁ B) : (groupCohomology.map (φ : H →* G) k 1).hom (H1π B c) =
      H1π B' (mapCocycles₁ (φ : H →* G) k c) :=
    congrArg (fun m => m.hom c) (groupCohomology.H1π_comp_map (φ : H →* G) k)
  rw [h3]
  apply equiv_π_eq
  intro h
  symm
  have h2 : ((homogeneousCochains A').iCycles 1).hom ((ContinuousCohomology.cocyclesMap φ f 1).hom z) =
      ((ContinuousCohomology.cochainsMap φ f).f 1).hom (((homogeneousCochains A).iCycles 1).hom z) := by
    have := HomologicalComplex.cyclesMap_i (ContinuousCohomology.cochainsMap φ f) 1
    exact congrArg (fun m : (homogeneousCochains A).cycles 1 ⟶ (homogeneousCochains A').X 1 => m.hom z) this
  change e' ((((homogeneousCochains A').iCycles 1).hom ((ContinuousCohomology.cocyclesMap φ f 1).hom z)).1 1 h) =
    k.hom (e ((((homogeneousCochains A).iCycles 1).hom z).1 1 (φ h)))
  rw [h2, cochainsMap_one_apply, map_one, hk]

end Naturality

end NumberFieldKB.MilneEC.ContH1
