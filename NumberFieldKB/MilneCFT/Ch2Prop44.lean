import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2Profinite

/-!
# Milne, *Class Field Theory*, Chapter II §4: Proposition 4.4

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

Continuous cohomology is Mathlib's `continuousCohomology` (continuous homogeneous cochains), with its functoriality
`ContinuousCohomology.map`. A Mathlib `ContRepresentation` only asks each $g \in G$ to act continuously, so a
discrete $G$-module is a topological representation with the discrete topology satisfying `IsDiscreteModule`.

The proof follows Milne: the cochains of a compact group with values in a discrete module have finite image
(`exists_lift`, by induction on the nested `C(G, C(G, …))` structure, using that evaluation is continuous and
`C(G, -)` preserves inducing maps), so they lift to some $M_i$, and then a concrete description of homology classes
in `TopModuleCat` (`cls`, `cls_surj`, `cls_eq_zero_iff`, `homologyMap_cls`) gives the two halves of exactness of
direct limits (`colim_surj`, `colim_zero`).
-/

namespace NumberFieldKB.MilneCFT

open CategoryTheory

/-! ### Homology classes in `TopModuleCat` -/

section Generic

open Limits ShortComplex

universe v

variable {R : Type v} [Ring R] [TopologicalSpace R]

set_option backward.isDefEq.respectTransparency false in
/-- Left homology data of a short complex of topological modules (kernel with the subspace topology, cokernel
with the quotient topology). -/
noncomputable def LH (S : ShortComplex (TopModuleCat.{v} R)) : S.LeftHomologyData :=
  ⟨_, _, _, _, _, TopModuleCat.isLimitKer S.g, by simp, TopModuleCat.isColimitCoker _⟩

/-- A cycle as an element of the kernel. -/
def kel (S : ShortComplex (TopModuleCat.{v} R)) (z : S.X₂) (hz : S.g z = 0) : (LH S).K :=
  (⟨z, by simpa using hz⟩ : S.g.hom.ker)

/-- The homology class of a cycle. -/
noncomputable def cls (S : ShortComplex (TopModuleCat.{v} R)) (z : S.X₂) (hz : S.g z = 0) :
    S.homology :=
  S.homologyπ.hom ((LH S).cyclesIso.inv.hom (kel S z hz))

lemma homologyIso_cls (S : ShortComplex (TopModuleCat.{v} R)) (z : S.X₂) (hz : S.g z = 0) :
    (LH S).homologyIso.hom.hom (cls S z hz) = (LH S).π.hom (kel S z hz) := by
  have h := congr(($((LH S).homologyπ_comp_homologyIso_hom)).hom
    ((LH S).cyclesIso.inv.hom (kel S z hz)))
  rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at h
  have h2 : (LH S).cyclesIso.hom.hom ((LH S).cyclesIso.inv.hom (kel S z hz)) =
      kel S z hz := by
    have := congr(($((LH S).cyclesIso.inv_hom_id)).hom (kel S z hz))
    rw [TopModuleCat.hom_comp] at this
    exact this
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h2] at h
  exact h

lemma iso_hom_injective {A B : TopModuleCat.{v} R} (e : A ≅ B) {a b : A}
    (h : e.hom.hom a = e.hom.hom b) : a = b := by
  have h2 := congrArg e.inv.hom h
  have h3 : ∀ c : A, e.inv.hom (e.hom.hom c) = c := fun c => by
    have := congr(($(e.hom_inv_id)).hom c)
    rw [TopModuleCat.hom_comp] at this
    exact this
  rwa [h3, h3] at h2

lemma cls_surj (S : ShortComplex (TopModuleCat.{v} R)) (x : S.homology) :
    ∃ (z : S.X₂) (hz : S.g z = 0), cls S z hz = x := by
  obtain ⟨k, hk⟩ := TopModuleCat.cokerπ_surjective _ ((LH S).homologyIso.hom.hom x)
  have hk' : S.g k.1 = 0 := by simp
  refine ⟨k.1, hk', iso_hom_injective (LH S).homologyIso ?_⟩
  rw [homologyIso_cls]
  exact hk

lemma cls_eq_zero_iff (S : ShortComplex (TopModuleCat.{v} R)) (z : S.X₂) (hz : S.g z = 0) :
    cls S z hz = 0 ↔ ∃ w : S.X₁, S.f w = z := by
  have h0 : cls S z hz = 0 ↔ (LH S).π.hom (kel S z hz) = 0 := by
    rw [← homologyIso_cls]
    constructor
    · intro h; rw [h]; exact map_zero _
    · intro h
      apply iso_hom_injective (LH S).homologyIso
      rw [h]; exact (map_zero _).symm
  rw [h0]
  have hf : ∀ w : S.X₁, (LH S).i.hom ((LH S).f'.hom w) = S.f w := fun w => by
    have := congr(($((LH S).f'_i)).hom w)
    rw [TopModuleCat.hom_comp] at this
    exact this
  have hk : (LH S).i.hom (kel S z hz) = z := rfl
  change Submodule.Quotient.mk (p := LinearMap.range (LH S).f'.hom.toLinearMap) (kel S z hz) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [← hf]
    exact (congrArg (LH S).i.hom hw).trans hk
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    exact (hf w).trans hw

lemma iCycles_cyclesIso_inv (S : ShortComplex (TopModuleCat.{v} R)) (k : (LH S).K) :
    S.iCycles.hom ((LH S).cyclesIso.inv.hom k) = (LH S).i.hom k := by
  have := congr(($((LH S).cyclesIso_inv_comp_iCycles)).hom k)
  rw [TopModuleCat.hom_comp] at this
  exact this

lemma iCycles_injective (S : ShortComplex (TopModuleCat.{v} R)) :
    Function.Injective S.iCycles.hom := by
  intro a b h
  have e : ∀ c, S.iCycles.hom c = (LH S).i.hom ((LH S).cyclesIso.hom.hom c) := fun c => by
    have := congr(($((LH S).cyclesIso_hom_comp_i)).hom c)
    rw [TopModuleCat.hom_comp] at this
    exact this.symm
  rw [e, e] at h
  have h' : (LH S).cyclesIso.hom.hom a = (LH S).cyclesIso.hom.hom b := Subtype.ext h
  exact iso_hom_injective _ h'

lemma homologyMap_cls {S T : ShortComplex (TopModuleCat.{v} R)} (φ : S ⟶ T) (z : S.X₂)
    (hz : S.g z = 0) (hz' : T.g (φ.τ₂ z) = 0) :
    (homologyMap φ).hom (cls S z hz) = cls T (φ.τ₂ z) hz' := by
  have h1 : (homologyMap φ).hom (S.homologyπ.hom ((LH S).cyclesIso.inv.hom (kel S z hz))) =
      T.homologyπ.hom ((cyclesMap φ).hom ((LH S).cyclesIso.inv.hom (kel S z hz))) := by
    have := congr(($(homologyπ_naturality φ)).hom ((LH S).cyclesIso.inv.hom (kel S z hz)))
    rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at this
    exact this
  unfold cls
  rw [h1]
  congr 1
  apply iCycles_injective T
  have h2 := congr(($(cyclesMap_i φ)).hom ((LH S).cyclesIso.inv.hom (kel S z hz)))
  rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at h2
  refine h2.trans ?_
  show φ.τ₂ (S.iCycles.hom ((LH S).cyclesIso.inv.hom (kel S z hz))) = _
  rw [iCycles_cyclesIso_inv, iCycles_cyclesIso_inv]
  rfl

section cx

variable {ι : Type} (C : ι → CochainComplex (TopModuleCat.{v} R) ℕ)
  (D : CochainComplex (TopModuleCat.{v} R) ℕ) (F : ∀ i, C i ⟶ D)

/-- Surjectivity half of "homology commutes with directed unions", for chain maps that are injective in each
degree and such that every element of `D` lies in the image of some `C i`. -/
theorem colim_surj
    (hinj : ∀ i m, Function.Injective ((F i).f m).hom)
    (H2 : ∀ m (w : D.X m) (_ : ι), ∃ i, w ∈ Set.range ((F i).f m).hom)
    (i0 : ι) (r : ℕ) (x : D.homology r) :
    ∃ (i : ι) (y : (C i).homology r), (HomologicalComplex.homologyMap (F i) r).hom y = x := by
  obtain ⟨z, hz, rfl⟩ := cls_surj (D.sc r) x
  obtain ⟨i, z', hz'⟩ := H2 r z i0
  let φ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) r).map (F i)
  have key : ((F i).f ((ComplexShape.up ℕ).next r)).hom (((C i).sc r).g.hom z') =
      ((D.sc r).g.hom) (((F i).f r).hom z') := by
    have := congr(($((F i).comm r ((ComplexShape.up ℕ).next r))).hom z')
    rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at this
    exact this.symm
  have hz0 : ((C i).sc r).g z' = 0 := by
    apply hinj i ((ComplexShape.up ℕ).next r)
    refine key.trans ?_
    rw [hz']
    exact hz.trans (map_zero _).symm
  refine ⟨i, cls ((C i).sc r) z' hz0, ?_⟩
  have := homologyMap_cls φ z' hz0 (by
    show ((D.sc r).g) (((F i).f r).hom z') = 0
    rw [hz']; exact hz)
  refine this.trans ?_
  congr 1

/-- Injectivity half of "homology commutes with directed unions". -/
theorem colim_zero (P : ∀ i j : ι, (C i ⟶ C j) → Prop)
    (hinj : ∀ i m, Function.Injective ((F i).f m).hom)
    (H2 : ∀ m (w : D.X m) (i0 : ι), ∃ i, ∃ G : C i0 ⟶ C i, P i0 i G ∧ G ≫ F i = F i0 ∧
      w ∈ Set.range ((F i).f m).hom)
    (i0 : ι) (r : ℕ) (y : (C i0).homology r)
    (hy : (HomologicalComplex.homologyMap (F i0) r).hom y = 0) :
    ∃ (j : ι) (G : C i0 ⟶ C j), P i0 j G ∧ G ≫ F j = F i0 ∧
      (HomologicalComplex.homologyMap G r).hom y = 0 := by
  obtain ⟨z, hz, rfl⟩ := cls_surj ((C i0).sc r) y
  let φ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) r).map (F i0)
  have hz' : (D.sc r).g (((F i0).f r).hom z) = 0 := by
    have key : ((F i0).f ((ComplexShape.up ℕ).next r)).hom (((C i0).sc r).g.hom z) =
        ((D.sc r).g.hom) (((F i0).f r).hom z) := by
      have := congr(($((F i0).comm r ((ComplexShape.up ℕ).next r))).hom z)
      rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at this
      exact this.symm
    rw [← key, hz]; exact map_zero _
  have h1 := homologyMap_cls φ z hz hz'
  have h2 : (HomologicalComplex.homologyMap (F i0) r).hom (cls ((C i0).sc r) z hz) =
      cls (D.sc r) (((F i0).f r).hom z) hz' := h1
  rw [h2] at hy
  obtain ⟨w, hw⟩ := (cls_eq_zero_iff _ _ hz').1 hy
  obtain ⟨j, G, hP, hG, w', hw'⟩ := H2 _ w i0
  refine ⟨j, G, hP, hG, ?_⟩
  have hf : G.f r ≫ (F j).f r = (F i0).f r := by rw [← HomologicalComplex.comp_f, hG]
  have e : ((F j).f r).hom ((G.f r).hom z) = ((F i0).f r).hom z := by
    have := congr(($hf).hom z)
    rw [TopModuleCat.hom_comp] at this
    exact this
  have hGz : ((C j).sc r).g (((G.f r)).hom z) = 0 := by
    apply hinj j ((ComplexShape.up ℕ).next r)
    have key : ((F j).f ((ComplexShape.up ℕ).next r)).hom (((C j).sc r).g.hom ((G.f r).hom z)) =
        ((D.sc r).g.hom) (((F j).f r).hom ((G.f r).hom z)) := by
      have := congr(($((F j).comm r ((ComplexShape.up ℕ).next r))).hom ((G.f r).hom z))
      rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at this
      exact this.symm
    refine key.trans ?_
    rw [e]
    exact hz'.trans (map_zero _).symm
  have := homologyMap_cls ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) r).map G)
    z hz hGz
  refine this.trans ?_
  refine (cls_eq_zero_iff _ _ _).2 ⟨w', ?_⟩
  apply hinj j r
  have c1 := congr(($((F j).comm ((ComplexShape.up ℕ).prev r) r)).hom w')
  rw [TopModuleCat.hom_comp, TopModuleCat.hom_comp] at c1
  refine Eq.trans ?_ e.symm
  refine Eq.trans c1.symm ?_
  exact (congrArg (D.d _ r).hom hw').trans hw

end cx

end Generic

/-! ### Finite image of continuous cochains -/

section Cochains

open _root_.TopRep _root_.ContinuousCohomology

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The level-`n` map `C(G, … C(G, X)) → C(G, … C(G, Y))` induced by `f : X ⟶ Y` (postcomposition). -/
noncomputable def Φ {X Y : TopRep.{0} ℤ G} (f : X ⟶ Y) (n : ℕ) :
    resolutionX X n → resolutionX Y n :=
  fun v => (resolutionMap (ContinuousMonoidHom.id G) f n).hom v

section Phi

variable {X Y : TopRep.{0} ℤ G} (f : X ⟶ Y)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma hom_cont {A B : TopRep.{0} ℤ G} (h : A ⟶ B) : Continuous (h : A → B) := by
  exact map_continuous h.hom

lemma Φ_cont (n : ℕ) : Continuous (Φ f n) :=
  hom_cont (resolutionMap (ContinuousMonoidHom.id G) f n)

/-- `Φ f n` as a continuous map. -/
noncomputable def Φc (n : ℕ) : C(resolutionX X n, resolutionX Y n) := ⟨Φ f n, Φ_cont f n⟩

lemma Φ_zero (v : X) : Φ f 0 v = f v := rfl

lemma Φ_succ (n : ℕ) (F : resolutionX X (n + 1)) (x : G) :
    Φ f (n + 1) F x = Φ f n (F x) := rfl

lemma Φ_succ' (n : ℕ) : Φ f (n + 1) =
    fun F : C(G, resolutionX X n) => (Φc f n).comp F := rfl

lemma Φ_inducing_inj (h1 : Topology.IsInducing (f : X → Y)) (h2 : Function.Injective (f : X → Y))
    (n : ℕ) :
    Topology.IsInducing (Φ f n) ∧ Function.Injective (Φ f n) := by
  induction n with
  | zero => exact ⟨h1, h2⟩
  | succ n ih =>
    rw [Φ_succ']
    exact ⟨ContinuousMap.isInducing_postcomp (Φc f n) ih.1,
      ContinuousMap.postcomp_injective (Φc f n) ih.2⟩

lemma Φ_smul (n : ℕ) (g : G) (v : resolutionX X n) :
    Φ f n ((resolutionX X n).ρ g v) = (resolutionX Y n).ρ g (Φ f n v) :=
  TopRep.hom_comm_apply (resolutionMap (ContinuousMonoidHom.id G) f n) g v

lemma Φ_comp {A B M : TopRep.{0} ℤ G} (g : A ⟶ B) (f1 : A ⟶ M) (f2 : B ⟶ M) (h : g ≫ f2 = f1)
    (n : ℕ) (v : resolutionX A n) : Φ f2 n (Φ g n v) = Φ f1 n v := by
  induction n with
  | zero =>
    show f2 (g v) = f1 v
    rw [← h]; rfl
  | succ n ih =>
    ext x
    exact ih _

end Phi

omit [IsTopologicalGroup G] in
lemma inducing_of_discrete {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [DiscreteTopology A] [DiscreteTopology B] (f : A → B) (hf : Function.Injective f) :
    Topology.IsInducing f :=
  ⟨le_antisymm (fun s _ => isOpen_discrete s)
    (fun s _ => ⟨f '' s, isOpen_discrete _, hf.preimage_image s⟩)⟩

section lift

variable [CompactSpace G]
variable (M : TopRep.{0} ℤ G) {ι : Type} (Mi : ι → TopRep.{0} ℤ G) (f : ∀ i, Mi i ⟶ M)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
lemma exists_fin
    (hdir : ∀ i j, ∃ k, Set.range (f i) ⊆ Set.range (f k) ∧ Set.range (f j) ⊆ Set.range (f k))
    (hcover : ∀ m : M, ∃ i, m ∈ Set.range (f i)) (i0 : ι) (K : Set M) (hK : K.Finite) :
    ∃ i : ι, Set.range (f i0) ⊆ Set.range (f i) ∧ K ⊆ Set.range (f i) := by
  induction K, hK using Set.Finite.induction_on with
  | empty => exact ⟨i0, subset_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨i1, h1, h2⟩ := ih
    obtain ⟨j, hj⟩ := hcover a
    obtain ⟨k, hk1, hk2⟩ := hdir i1 j
    refine ⟨k, h1.trans hk1, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · exact hk2 hj
    · exact hk1 (h2 hx)

/-- A compact set of (nested continuous) cochains with values in a directed union of discrete modules
lies in the image of a single member of the union. -/
lemma exists_lift [DiscreteTopology M] [∀ i, DiscreteTopology (Mi i)]
    (hinj : ∀ i, Function.Injective (f i))
    (hdir : ∀ i j, ∃ k, Set.range (f i) ⊆ Set.range (f k) ∧ Set.range (f j) ⊆ Set.range (f k))
    (hcover : ∀ m : M, ∃ i, m ∈ Set.range (f i)) (n : ℕ) :
    ∀ (K : Set (resolutionX M n)), IsCompact K → ∀ i0 : ι, ∃ i : ι,
      Set.range (f i0) ⊆ Set.range (f i) ∧ K ⊆ Set.range (Φ (f i) n) := by
  induction n with
  | zero =>
    intro K hK i0
    exact exists_fin M Mi f hdir hcover i0 K hK.finite_of_discrete
  | succ n ih =>
    intro K hK i0
    have hK' : IsCompact ((fun p : C(G, resolutionX M n) × G => p.1 p.2) '' (K ×ˢ Set.univ)) :=
      (hK.prod isCompact_univ).image (by fun_prop)
    obtain ⟨i, hi0, hi⟩ := ih _ hK' i0
    refine ⟨i, hi0, ?_⟩
    intro k hk
    have hx : ∀ x : G, ∃ y, Φ (f i) n y = k x := fun x =>
      hi ⟨(k, x), ⟨hk, Set.mem_univ _⟩, rfl⟩
    choose k' hk' using hx
    obtain ⟨hind, hinj'⟩ := Φ_inducing_inj (f i) (inducing_of_discrete _ (hinj i)) (hinj i) n
    have hcont : Continuous k' := by
      rw [hind.continuous_iff]
      have : Φ (f i) n ∘ k' = k := funext hk'
      rw [this]; exact k.continuous
    refine ⟨⟨k', hcont⟩, ?_⟩
    ext x
    exact hk' x

end lift

/-- The underlying function of `liftHom`. -/
noncomputable def liftFun {A B M : TopRep.{0} ℤ G} (f1 : A ⟶ M) (f2 : B ⟶ M)
    (hr : Set.range f1 ⊆ Set.range f2) (a : A) : B := (hr ⟨a, rfl⟩).choose

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma liftFun_spec {A B M : TopRep.{0} ℤ G} (f1 : A ⟶ M) (f2 : B ⟶ M)
    (hr : Set.range f1 ⊆ Set.range f2) (a : A) : f2 (liftFun f1 f2 hr a) = f1 a :=
  (hr ⟨a, rfl⟩).choose_spec

/-- Given discrete `A` and injective `f2 : B ⟶ M` whose range contains that of `f1 : A ⟶ M`, the factorization
`A ⟶ B` of `f1` through `f2`. -/
noncomputable def liftHom {A B M : TopRep.{0} ℤ G} [DiscreteTopology A] (f1 : A ⟶ M) (f2 : B ⟶ M)
    (hinj : Function.Injective f2) (hr : Set.range f1 ⊆ Set.range f2) : A ⟶ B :=
  letI : Module ℤ A := A.hV2
  letI : Module ℤ B := B.hV2
  letI : Module ℤ M := M.hV2
  TopRep.ofHom (ρ := A.ρ) (σ := B.ρ)
    ⟨⟨⟨⟨liftFun f1 f2 hr, fun a b => by
        apply hinj
        have h1 := liftFun_spec f1 f2 hr (a + b)
        have h2 := liftFun_spec f1 f2 hr a
        have h3 := liftFun_spec f1 f2 hr b
        rw [map_add (ConcreteCategory.hom f2), h1, h2, h3]
        exact map_add (ConcreteCategory.hom f1) a b⟩, by
          intro r a
          apply hinj
          dsimp only [RingHom.id_apply]
          have e2 := liftFun_spec f1 f2 hr a
          have m1 := map_intCast_smul (ConcreteCategory.hom f1) ℤ ℤ r a
          have m2 := map_intCast_smul (ConcreteCategory.hom f2) ℤ ℤ r (liftFun f1 f2 hr a)
          simp only [Int.cast_id] at m1 m2
          refine (liftFun_spec f1 f2 hr _).trans (m1.trans (Eq.trans ?_ m2.symm))
          rw [e2]⟩, continuous_of_discreteTopology⟩, by
          intro g
          refine ContinuousLinearMap.ext fun a => ?_
          show liftFun f1 f2 hr (A.ρ g a) = B.ρ g (liftFun f1 f2 hr a)
          apply hinj
          have e1 := liftFun_spec f1 f2 hr (A.ρ g a)
          have e2 := liftFun_spec f1 f2 hr a
          rw [e1, TopRep.hom_comm_apply f2, e2, TopRep.hom_comm_apply f1]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma liftHom_spec {A B M : TopRep.{0} ℤ G} [DiscreteTopology A] (f1 : A ⟶ M) (f2 : B ⟶ M)
    (hinj : Function.Injective f2) (hr : Set.range f1 ⊆ Set.range f2) :
    liftHom f1 f2 hinj hr ≫ f2 = f1 := by
  let _ : Module ℤ A := A.hV2
  let _ : Module ℤ M := M.hV2
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  refine ContinuousLinearMap.ext fun a => ?_
  exact liftFun_spec f1 f2 hr a

lemma cochainsMap_apply {X Y : TopRep.{0} ℤ G} (f : X ⟶ Y) (m : ℕ) (w : (homogeneousCochains X).X m) :
    (((cochainsMap (ContinuousMonoidHom.id G) f).f m).hom w).1 = Φ f (m + 1) w.1 := rfl

end Cochains

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open _root_.TopRep _root_.ContinuousCohomology in
/-- **Proposition 4.4** (p. 88). Let $G$ be a profinite group and $M$ a discrete $G$-module. If
$M = \varinjlim M_i$ with $M_i \subseteq M$ (a directed family of submodules with union $M$), then
$H^r(G, M) = \varinjlim H^r(G, M_i)$.

The submodules are given as injective morphisms `f i : Mi i ⟶ M` of discrete topological representations whose
images are directed and cover $M$. The equality with the direct limit is stated by its two defining properties:
every class in $H^r(G, M)$ comes from some $H^r(G, M_i)$, and a class in $H^r(G, M_i)$ that dies in $H^r(G, M)$
already dies in some $H^r(G, M_j)$ with $M_i \subseteq M_j$.

Proved following Milne: continuous cochains on the compact group $G$ with values in the discrete module $M$ have
finite image (`exists_lift`), hence come from a single $M_i$; exactness of direct limits is then checked on
homology classes (`colim_surj`, `colim_zero`). -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 4.4, p. 88"]
theorem prop_4_4 [CompactSpace G] [TotallyDisconnectedSpace G] (M : TopRep.{0} ℤ G) [DiscreteTopology M]
    (_hM : IsDiscreteModule (TopRep.toRep M)) {ι : Type} (Mi : ι → TopRep.{0} ℤ G)
    [∀ i, DiscreteTopology (Mi i)] (f : ∀ i, Mi i ⟶ M) (hinj : ∀ i, Function.Injective (f i))
    (hdir : ∀ i j, ∃ k, Set.range (f i) ⊆ Set.range (f k) ∧ Set.range (f j) ⊆ Set.range (f k))
    (hcover : ∀ m : M, ∃ i, m ∈ Set.range (f i)) (r : ℕ) :
    (∀ x : continuousCohomology r M,
      ∃ (i : ι) (y : continuousCohomology r (Mi i)),
        ContinuousCohomology.map (ContinuousMonoidHom.id G) (f i) r y = x) ∧
    (∀ (i : ι) (y : continuousCohomology r (Mi i)),
      ContinuousCohomology.map (ContinuousMonoidHom.id G) (f i) r y = 0 →
      ∃ (j : ι) (g : Mi i ⟶ Mi j), g ≫ f j = f i ∧
        ContinuousCohomology.map (ContinuousMonoidHom.id G) g r y = 0) := by
  have hinj' : ∀ i m, Function.Injective
      ((cochainsMap (ContinuousMonoidHom.id G) (f i)).f m).hom := by
    intro i m a b h
    apply Subtype.ext
    exact (Φ_inducing_inj (f i) (inducing_of_discrete _ (hinj i)) (hinj i) (m + 1)).2
      (congrArg Subtype.val h)
  have H2 : ∀ m (w : (homogeneousCochains M).X m) (i0 : ι), ∃ i,
      ∃ Gm : homogeneousCochains (Mi i0) ⟶ homogeneousCochains (Mi i),
        (∃ g : Mi i0 ⟶ Mi i, g ≫ f i = f i0 ∧ Gm = cochainsMap (ContinuousMonoidHom.id G) g) ∧
        Gm ≫ cochainsMap (ContinuousMonoidHom.id G) (f i) =
          cochainsMap (ContinuousMonoidHom.id G) (f i0) ∧
        w ∈ Set.range ((cochainsMap (ContinuousMonoidHom.id G) (f i)).f m).hom := by
    intro m w i0
    obtain ⟨i, hi0, hi⟩ := exists_lift M Mi f hinj hdir hcover (m + 1) ({w.1} : Set (resolutionX M (m + 1))) isCompact_singleton i0
    obtain ⟨v, hv⟩ := hi (Set.mem_singleton w.1)
    have hind := (Φ_inducing_inj (f i) (inducing_of_discrete _ (hinj i)) (hinj i) (m + 1))
    have hinv : ∀ g : G, (resolutionX (Mi i) (m + 1)).ρ g v = v := by
      intro g
      apply hind.2
      rw [Φ_smul, hv]
      exact w.2 g
    set g := liftHom (f i0) (f i) (hinj i) hi0 with hg
    have hgf : g ≫ f i = f i0 := liftHom_spec _ _ _ _
    refine ⟨i, cochainsMap (ContinuousMonoidHom.id G) g, ⟨g, hgf, rfl⟩, ?_, ⟨⟨v, hinv⟩, Subtype.ext hv⟩⟩
    ext n x
    apply Subtype.ext
    exact Φ_comp g (f i0) (f i) hgf (n + 1) x.1
  obtain ⟨i0, -⟩ := hcover 0
  refine ⟨fun x => colim_surj (fun i => homogeneousCochains (Mi i)) (homogeneousCochains M)
    (fun i => cochainsMap (ContinuousMonoidHom.id G) (f i)) hinj'
    (fun m w i0 => by obtain ⟨i, -, -, -, h⟩ := H2 m w i0; exact ⟨i, h⟩) i0 r x, ?_⟩
  intro i y hy
  obtain ⟨j, Gm, ⟨g, hg, rfl⟩, -, hGy⟩ := colim_zero (fun i => homogeneousCochains (Mi i))
    (homogeneousCochains M) (fun i => cochainsMap (ContinuousMonoidHom.id G) (f i))
    (fun i j Gm => ∃ g : Mi i ⟶ Mi j, g ≫ f j = f i ∧ Gm = cochainsMap (ContinuousMonoidHom.id G) g)
    hinj' H2 i r y hy
  exact ⟨j, g, hg, hGy⟩

end NumberFieldKB.MilneCFT

