import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch2DerivedDelta

/-!
# Milne, *Class Field Theory*, Proposition A.11: right derived functors form a cohomological delta functor

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`,
Chapter II, Appendix A, Proposition A.11, printed pages 94 to 95.

Mathlib has the right derived functor `Functor.rightDerived` (through injective resolutions indexed by the
natural numbers) but no connecting morphism and no horseshoe lemma. We obtain the connecting morphisms
from the derived category. For an additive functor `F` out of a category with enough injectives, Mathlib
constructs the triangulated functor `F.rightDerivedFunctorPlus` on the bounded below derived categories.
Evaluating it at a single object in degree zero and taking homology in degree `n` gives functors
`Gfun F n`. A short exact sequence gives a distinguished triangle of single objects; its image under the
triangulated functor is distinguished, and the long exact homology sequence of this triangle provides the
connecting morphisms `Gδ` and the exactness; the naturality of the triangle gives the naturality of the
connecting morphisms (`derivedDelta`).

The comparison `rightDerivedIso : F.rightDerived n ≅ Gfun F n` is proved by choosing injective resolutions: the
resolution, extended by zero to a complex indexed by the integers, is quasi-isomorphic to the single
object, and the derived functor is computed termwise on complexes of injective objects. Naturality in the
object is proved by lifting morphisms to morphisms of resolutions. The headline is `propA_11`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

universe w w'

namespace NumberFieldKB.MilneCFT

open CategoryTheory Limits Pretriangulated

namespace PropA11Aux

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open DerivedCategory

/-- The triangle in the bounded below derived category attached to a short exact sequence in the
abelian category: the images of the three single objects, with the connecting morphism of Mathlib's
triangle in the full derived category. -/
noncomputable def sesTriangle {S : ShortComplex C} (hS : S.ShortExact) :
    Triangle (DerivedCategory.Plus C) :=
  Triangle.mk ((Plus.singleFunctor C 0).map S.f) ((Plus.singleFunctor C 0).map S.g)
    (Plus.ι.preimage (hS.singleδ ≫ (Plus.ι.commShiftIso (1 : ℤ)).inv.app ((Plus.singleFunctor C 0).obj S.X₁)))

set_option backward.isDefEq.respectTransparency false in
lemma sesTriangle_distinguished {S : ShortComplex C} (hS : S.ShortExact) :
    sesTriangle hS ∈ distTriang (DerivedCategory.Plus C) := by
  show Plus.ι.mapTriangle.obj (sesTriangle hS) ∈ distTriang (DerivedCategory C)
  refine isomorphic_distinguished _ (hS.singleTriangle_distinguished) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [sesTriangle]; rfl
  · simp [sesTriangle]; rfl
  · simp [sesTriangle]
    change Plus.ι.map _ ≫ _ = _
    rw [Plus.ι.map_preimage]
    simp
    exact Category.comp_id _


variable {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency false in
noncomputable def sesTriangleMap : sesTriangle h₁ ⟶ sesTriangle h₂ where
  hom₁ := (Plus.singleFunctor C 0).map φ.τ₁
  hom₂ := (Plus.singleFunctor C 0).map φ.τ₂
  hom₃ := (Plus.singleFunctor C 0).map φ.τ₃
  comm₁ := by simp [sesTriangle, ← Functor.map_comp, φ.comm₁₂]
  comm₂ := by simp [sesTriangle, ← Functor.map_comp, φ.comm₂₃]
  comm₃ := by
    apply Plus.ι.map_injective
    have this : h₁.singleδ ≫ (shiftFunctor (DerivedCategory C) (1 : ℤ)).map
        ((singleFunctor C 0).map φ.τ₁) = (singleFunctor C 0).map φ.τ₃ ≫ h₂.singleδ :=
      (ShortComplex.ShortExact.singleTriangle.map h₁ h₂ φ).comm₃
    simp only [sesTriangle, Triangle.mk_mor₃, Functor.map_comp]
    erw [Plus.ι.map_preimage, Plus.ι.map_preimage]
    rw [Category.assoc]
    erw [← Functor.commShiftIso_inv_naturality]
    rw [← Category.assoc]
    erw [this]
    simp
    rfl


/-- The right derived functor of `F` on the bounded below derived categories, evaluated at the single
object in degree zero, followed by taking homology in degree `n`. These are the candidates for the
right derived functors of `F`. -/
noncomputable def Gfun (n : ℤ) : C ⥤ D :=
  Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus ⋙ Plus.ι ⋙ DerivedCategory.homologyFunctor D n

/-- The image in the derived category of the target of the triangle of a short exact sequence. -/
noncomputable def GTri {S : ShortComplex C} (hS : S.ShortExact) : Triangle (DerivedCategory D) :=
  (F.rightDerivedFunctorPlus ⋙ Plus.ι).mapTriangle.obj (sesTriangle hS)

/-- The triangle `GTri` is distinguished, since the right derived functor is triangulated. -/
lemma GTri_dist {S : ShortComplex C} (hS : S.ShortExact) : GTri F hS ∈ distTriang (DerivedCategory D) :=
  Functor.map_distinguished _ _ (sesTriangle_distinguished hS)

/-- The connecting morphism of the long exact sequence of homology of the distinguished triangle. -/
noncomputable def Gδ {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (Gfun F n₀).obj S.X₃ ⟶ (Gfun F n₁).obj S.X₁ :=
  DerivedCategory.HomologySequence.δ (GTri F hS) n₀ n₁ h

/-- The connecting morphisms are natural in morphisms of short exact sequences. -/
lemma Gδ_naturality (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Gδ F h₁ n₀ n₁ h ≫ (Gfun F n₁).map φ.τ₁ = (Gfun F n₀).map φ.τ₃ ≫ Gδ F h₂ n₀ n₁ h := by
  have := (DerivedCategory.homologyFunctor D 0).homologySequenceδ_naturality
    ((F.rightDerivedFunctorPlus ⋙ Plus.ι).mapTriangle.map (sesTriangleMap h₁ h₂ φ)) n₀ n₁ h
  exact this.symm

/-- The functors `Gfun F n` are additive. -/
instance Gfun_additive (n : ℤ) : (Gfun F n).Additive := by
  unfold Gfun; infer_instance


end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex

open Classical in
/-- The component, in one degree, of the isomorphism between applying an additive functor to the
extension by zero of a complex of natural number degrees, and extending the functor applied to it by
zero. -/
noncomputable def extFX (K : CochainComplex C ℕ) (n : ℤ) :
    F.obj ((K.extend embeddingUpNat).X n) ≅
      (((F.mapHomologicalComplex (up ℕ)).obj K).extend embeddingUpNat).X n :=
    if h : ∃ i : ℕ, embeddingUpNat.f i = n then
      F.mapIso (K.extendXIso embeddingUpNat h.choose_spec) ≪≫
        (((F.mapHomologicalComplex (up ℕ)).obj K).extendXIso embeddingUpNat h.choose_spec).symm
    else
      IsZero.iso (F.map_isZero (K.isZero_extend_X _ _ (fun i hi => h ⟨i, hi⟩)))
        (((F.mapHomologicalComplex (up ℕ)).obj K).isZero_extend_X _ _ (fun i hi => h ⟨i, hi⟩))

/-- The component of the comparison in a degree in the image of the embedding. -/
lemma extFX_eq (K : CochainComplex C ℕ) (a : ℕ) (n : ℤ) (h : embeddingUpNat.f a = n) :
    extFX F K n = F.mapIso (K.extendXIso embeddingUpNat h) ≪≫
        (((F.mapHomologicalComplex (up ℕ)).obj K).extendXIso embeddingUpNat h).symm := by
  subst h
  have hex : ∃ i : ℕ, embeddingUpNat.f i = embeddingUpNat.f a := ⟨a, rfl⟩
  rw [extFX, dif_pos hex]
  have key : ∀ (c : ℕ) (hc : embeddingUpNat.f c = embeddingUpNat.f a),
      (F.mapIso (K.extendXIso embeddingUpNat hc) ≪≫
        (((F.mapHomologicalComplex (up ℕ)).obj K).extendXIso embeddingUpNat hc).symm) =
      (F.mapIso (K.extendXIso embeddingUpNat rfl) ≪≫
        (((F.mapHomologicalComplex (up ℕ)).obj K).extendXIso embeddingUpNat rfl).symm) := by
    intro c hc
    obtain rfl := embeddingUpNat.injective_f hc
    rfl
  exact key _ _

/-- The extension by zero is a zero object outside the image of the embedding. -/
lemma extFX_zero (K : CochainComplex C ℕ) (n : ℤ) (h : ∀ i : ℕ, embeddingUpNat.f i ≠ n) :
    IsZero ((((F.mapHomologicalComplex (up ℕ)).obj K).extend embeddingUpNat).X n) :=
  ((F.mapHomologicalComplex (up ℕ)).obj K).isZero_extend_X _ _ h

/-- Comparing application of an additive functor with extension by zero. -/
noncomputable def extF (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (up ℤ)).obj (K.extend embeddingUpNat) ≅
      ((F.mapHomologicalComplex (up ℕ)).obj K).extend embeddingUpNat :=
  Hom.isoOfComponents (extFX F K)
    (by
      intro i j _
      by_cases hi : ∃ a : ℕ, embeddingUpNat.f a = i
      · by_cases hj : ∃ b : ℕ, embeddingUpNat.f b = j
        · obtain ⟨a, ha⟩ := hi
          obtain ⟨b, hb⟩ := hj
          rw [extFX_eq F K a i ha, extFX_eq F K b j hb]
          simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
            Functor.mapHomologicalComplex_obj_d]
          rw [HomologicalComplex.extend_d_eq _ _ ha hb, HomologicalComplex.extend_d_eq _ _ ha hb]
          simp only [Functor.mapHomologicalComplex_obj_d, Category.assoc, Iso.inv_hom_id_assoc,
            Functor.map_comp]
          simp
        · exact (extFX_zero F K j (fun b hb => hj ⟨b, hb⟩)).eq_of_tgt _ _
      · exact ((F.map_isZero (K.isZero_extend_X _ _ (fun a ha => hi ⟨a, ha⟩)))).eq_of_src _ _)


/-- Naturality of the comparison between applying a functor and extending by zero. -/
lemma extF_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (up ℤ)).map (extendMap φ embeddingUpNat) ≫ (extF F L).hom =
      (extF F K).hom ≫ extendMap ((F.mapHomologicalComplex (up ℕ)).map φ) embeddingUpNat := by
  ext n
  by_cases hn : ∃ a : ℕ, embeddingUpNat.f a = n
  · obtain ⟨a, ha⟩ := hn
    simp only [comp_f, extF, Hom.isoOfComponents_hom_f, Functor.mapHomologicalComplex_map_f]
    rw [extFX_eq F L a n ha, extFX_eq F K a n ha, extendMap_f _ _ ha, extendMap_f _ _ ha]
    simp
  · exact (extFX_zero F L n (fun b hb => hn ⟨b, hb⟩)).eq_of_tgt _ _

/-- The homology of the extension by zero of a complex, in a degree in the image of the embedding. -/
noncomputable def extHI (K : CochainComplex D ℕ) (n : ℕ) :
    (K.extend embeddingUpNat).homology (n : ℤ) ≅ K.homology n :=
  K.extendHomologyIso embeddingUpNat (j := n) (j' := (n : ℤ)) rfl

/-- The homology of `F` applied to a complex of non-negative degrees agrees with the homology of
`F` applied to its extension by zero. -/
noncomputable def epsIso (K : CochainComplex C ℕ) (n : ℕ) :
    ((F.mapHomologicalComplex (up ℕ)).obj K).homology n ≅
      ((F.mapHomologicalComplex (up ℤ)).obj (K.extend embeddingUpNat)).homology (n : ℤ) :=
  (extHI ((F.mapHomologicalComplex (up ℕ)).obj K) n).symm ≪≫
    homologyMapIso (extF F K).symm (n : ℤ)

/-- Naturality of the comparison of homology with the homology of the extension by zero. -/
lemma epsIso_naturality {K L : CochainComplex C ℕ} (φ : K ⟶ L) (n : ℕ) :
    homologyMap ((F.mapHomologicalComplex (up ℕ)).map φ) n ≫ (epsIso F L n).hom =
      (epsIso F K n).hom ≫
        homologyMap ((F.mapHomologicalComplex (up ℤ)).map (extendMap φ embeddingUpNat)) (n : ℤ) := by
  have h1 : homologyMap (extendMap ((F.mapHomologicalComplex (up ℕ)).map φ) embeddingUpNat) ↑n ≫
      (extHI ((F.mapHomologicalComplex (up ℕ)).obj L) n).hom =
      (extHI ((F.mapHomologicalComplex (up ℕ)).obj K) n).hom ≫
      homologyMap ((F.mapHomologicalComplex (up ℕ)).map φ) n :=
    extendHomologyIso_hom_naturality ((F.mapHomologicalComplex (up ℕ)).map φ)
    embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have h2 : (extF F K).inv ≫ (F.mapHomologicalComplex (up ℤ)).map (extendMap φ embeddingUpNat) =
      extendMap ((F.mapHomologicalComplex (up ℕ)).map φ) embeddingUpNat ≫ (extF F L).inv := by
    rw [← cancel_epi (extF F K).hom, Iso.hom_inv_id_assoc, ← Category.assoc, ← extF_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h3 : homologyMap ((F.mapHomologicalComplex (up ℕ)).map φ) n ≫
      (extHI ((F.mapHomologicalComplex (up ℕ)).obj L) n).inv =
      (extHI ((F.mapHomologicalComplex (up ℕ)).obj K) n).inv ≫
      homologyMap (extendMap ((F.mapHomologicalComplex (up ℕ)).map φ) embeddingUpNat) ↑n := by
    rw [← cancel_epi (extHI ((F.mapHomologicalComplex (up ℕ)).obj K) n).hom, Iso.hom_inv_id_assoc,
      ← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [epsIso, Iso.trans_hom, Iso.symm_hom, homologyMapIso_hom]
  rw [← Category.assoc, h3, Category.assoc, Category.assoc, ← homologyMap_comp, ← homologyMap_comp, h2]


end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex DerivedCategory

/-- The unit of the right derived functor is an isomorphism on complexes of injective objects. -/
instance isIso_unit_app (K : CochainComplex.Plus C) [∀ n, Injective (K.obj.X n)] :
    IsIso (F.rightDerivedFunctorPlusUnit.app K) := by
  simp only [Functor.rightDerivedFunctorPlusUnit_app]
  infer_instance

/-- For a bounded below complex of injective objects, the homology of the right derived functor
evaluated at its image in the derived category is the homology of `F` applied termwise. -/
noncomputable def thetaIso (K : CochainComplex.Plus C) [∀ n, Injective (K.obj.X n)] (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).obj (Plus.ι.obj (F.rightDerivedFunctorPlus.obj (Plus.Q.obj K))) ≅
      (HomologicalComplex.homologyFunctor D (up ℤ) n).obj
        ((F.mapHomologicalComplex (up ℤ)).obj K.obj) :=
  (DerivedCategory.homologyFunctor D n).mapIso
    (Plus.ι.mapIso (asIso (F.rightDerivedFunctorPlusUnit.app K)).symm) ≪≫
  (DerivedCategory.homologyFunctor D n).mapIso ((Plus.QCompιIso D).app (F.mapCochainComplexPlus.obj K)) ≪≫
  (DerivedCategory.homologyFunctorFactors D n).app _


/-- Naturality of `thetaIso` in the complex of injective objects. -/
lemma thetaIso_naturality {K L : CochainComplex.Plus C} [∀ n, Injective (K.obj.X n)]
    [∀ n, Injective (L.obj.X n)] (g : K ⟶ L) (n : ℤ) :
    (DerivedCategory.homologyFunctor D n).map (Plus.ι.map (F.rightDerivedFunctorPlus.map (Plus.Q.map g))) ≫
      (thetaIso F L n).hom =
    (thetaIso F K n).hom ≫
      (HomologicalComplex.homologyFunctor D (up ℤ) n).map ((F.mapHomologicalComplex (up ℤ)).map g.hom) := by
  have h := F.rightDerivedFunctorPlusUnit.naturality g
  have e1 : F.rightDerivedFunctorPlus.map (Plus.Q.map g) ≫ inv (F.rightDerivedFunctorPlusUnit.app L) =
      inv (F.rightDerivedFunctorPlusUnit.app K) ≫ Plus.Q.map (F.mapCochainComplexPlus.map g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact h.symm
  have e2 := (Plus.QCompιIso D).hom.naturality (F.mapCochainComplexPlus.map g)
  have e3 := homologyFunctorFactors_hom_naturality (F.mapHomologicalComplex (up ℤ) |>.map g.hom) n
  simp only [thetaIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, asIso_inv]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp, e1, Functor.map_comp, Functor.map_comp,
    Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have e2' : Plus.ι.map (Plus.Q.map (F.mapCochainComplexPlus.map g)) ≫
      (Plus.QCompιIso D).hom.app (F.mapCochainComplexPlus.obj L) =
      (Plus.QCompιIso D).hom.app (F.mapCochainComplexPlus.obj K) ≫
        Q.map ((F.mapHomologicalComplex (up ℤ)).map g.hom) := e2
  rw [Category.assoc, e2', Functor.map_comp, Category.assoc, Category.assoc, Functor.map_comp,
    Category.assoc, Category.assoc]
  erw [e3]
  rfl


end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex DerivedCategory

/-- The single complex as a bounded below complex. -/
noncomputable def singlePlus (X : C) : CochainComplex.Plus C :=
  ⟨(CochainComplex.singleFunctor C 0).obj X, 0, inferInstance⟩

/-- An injective resolution as a bounded below complex indexed by the integers. -/
noncomputable def resPlus {X : C} (I : InjectiveResolution X) : CochainComplex.Plus C :=
  ⟨I.cochainComplex, 0, inferInstance⟩

instance {X : C} (I : InjectiveResolution X) (n : ℤ) : Injective ((resPlus I).obj.X n) :=
  inferInstanceAs (Injective (I.cochainComplex.X n))

/-- The quasi-isomorphism from the single complex to the resolution. -/
noncomputable def resMap {X : C} (I : InjectiveResolution X) : singlePlus X ⟶ resPlus I :=
  ObjectProperty.homMk I.ι'

instance {X : C} (I : InjectiveResolution X) : IsIso (Plus.Q.map (resMap I)) :=
  Localization.inverts Plus.Q (CochainComplex.Plus.quasiIso C) _
    ((CochainComplex.Plus.quasiIso_iff _ _).2 (inferInstanceAs (QuasiIso I.ι')))

/-- The identification of the single object in the derived category with the localization of the
single complex. -/
noncomputable def sigmaIso (X : C) : (Plus.singleFunctor C 0).obj X ≅ Plus.Q.obj (singlePlus X) :=
  Iso.refl _


end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex DerivedCategory

/-- The map of single complexes. -/
noncomputable def singlePlusMap {X Y : C} (f : X ⟶ Y) : singlePlus X ⟶ singlePlus Y :=
  ObjectProperty.homMk ((CochainComplex.singleFunctor C 0).map f)

/-- The map of resolutions. -/
noncomputable def resPlusMap {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X}
    {J : InjectiveResolution Y} (φ : InjectiveResolution.Hom I J f) : resPlus I ⟶ resPlus J :=
  ObjectProperty.homMk φ.hom'

/-- Naturality of the identification of single objects. -/
lemma sigmaIso_naturality {X Y : C} (f : X ⟶ Y) :
    (Plus.singleFunctor C 0).map f ≫ (sigmaIso Y).hom =
      (sigmaIso X).hom ≫ Plus.Q.map (singlePlusMap f) := by
  apply ObjectProperty.hom_ext
  simp only [sigmaIso, Iso.refl_hom]
  erw [Category.comp_id, Category.id_comp]
  rfl

/-- Compatibility of the resolution maps with a morphism of resolutions. -/
lemma resMap_naturality {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X}
    {J : InjectiveResolution Y} (φ : InjectiveResolution.Hom I J f) :
    resMap I ≫ resPlusMap φ = singlePlusMap f ≫ resMap J := by
  apply ObjectProperty.hom_ext
  exact φ.ι'_comp_hom'


end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex DerivedCategory

/-- Inverting the isomorphisms in a commuting square. -/
lemma iso_inv_naturality {E : Type*} [Category* E] {a b a' b' : E} (e : a ≅ b) (e' : a' ≅ b')
    (u : a ⟶ a') (v : b ⟶ b') (h : u ≫ e'.hom = e.hom ≫ v) : v ≫ e'.inv = e.inv ≫ u := by
  rw [← cancel_mono e'.hom, Category.assoc, e'.inv_hom_id, Category.comp_id, Category.assoc, h,
    e.inv_hom_id_assoc]

/-- The functor `H^n ∘ ι ∘ R` on the bounded below derived category. -/
noncomputable abbrev omegaFun (n : ℤ) : DerivedCategory.Plus C ⥤ D :=
  F.rightDerivedFunctorPlus ⋙ Plus.ι ⋙ DerivedCategory.homologyFunctor D n

/-- The identification of `H^n` of the right derived functor applied to a single object with
the homology of `F` applied to an injective resolution. -/
noncomputable def thetaRes {X : C} (I : InjectiveResolution X) (n : ℕ) :
    ((F.mapHomologicalComplex (up ℕ)).obj I.cocomplex).homology n ≅
      (Gfun F (n : ℤ)).obj X :=
  epsIso F I.cocomplex n ≪≫ (thetaIso F (resPlus I) (n : ℤ)).symm ≪≫
    ((omegaFun F (n : ℤ)).mapIso (sigmaIso X ≪≫ asIso (Plus.Q.map (resMap I)))).symm

/-- Naturality of `thetaRes` with respect to a morphism of resolutions. -/
lemma thetaRes_naturality {X Y : C} (f : X ⟶ Y) {I : InjectiveResolution X}
    {J : InjectiveResolution Y} (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    homologyMap ((F.mapHomologicalComplex (up ℕ)).map φ.hom) n ≫ (thetaRes F J n).hom =
      (thetaRes F I n).hom ≫ (Gfun F (n : ℤ)).map f := by
  have hA := epsIso_naturality F φ.hom n
  have hB := thetaIso_naturality F (resPlusMap φ) (n : ℤ)
  have hC : (Plus.singleFunctor C 0).map f ≫ (sigmaIso Y ≪≫ asIso (Plus.Q.map (resMap J))).hom =
      (sigmaIso X ≪≫ asIso (Plus.Q.map (resMap I))).hom ≫ Plus.Q.map (resPlusMap φ) := by
    simp only [Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, sigmaIso_naturality, Category.assoc, ← Plus.Q.map_comp,
      ← resMap_naturality φ, Plus.Q.map_comp, Category.assoc]
  have hC' := iso_inv_naturality ((omegaFun F (n : ℤ)).mapIso (sigmaIso X ≪≫ asIso (Plus.Q.map (resMap I))))
    ((omegaFun F (n : ℤ)).mapIso (sigmaIso Y ≪≫ asIso (Plus.Q.map (resMap J))))
    ((omegaFun F (n : ℤ)).map ((Plus.singleFunctor C 0).map f))
    ((omegaFun F (n : ℤ)).map (Plus.Q.map (resPlusMap φ)))
    (by simp only [Functor.mapIso_hom]; rw [← Functor.map_comp, ← Functor.map_comp, hC])
  have hB' := iso_inv_naturality (thetaIso F (resPlus I) (n : ℤ)) (thetaIso F (resPlus J) (n : ℤ))
    ((omegaFun F (n : ℤ)).map (Plus.Q.map (resPlusMap φ))) _ hB
  show homologyMap _ n ≫ (epsIso F J.cocomplex n).hom ≫ (thetaIso F (resPlus J) (n : ℤ)).inv ≫
      ((omegaFun F (n : ℤ)).mapIso (sigmaIso Y ≪≫ asIso (Plus.Q.map (resMap J)))).inv =
    ((epsIso F I.cocomplex n).hom ≫ (thetaIso F (resPlus I) (n : ℤ)).inv ≫
      ((omegaFun F (n : ℤ)).mapIso (sigmaIso X ≪≫ asIso (Plus.Q.map (resMap I)))).inv) ≫
        (Gfun F (n : ℤ)).map f
  have key : homologyMap ((F.mapHomologicalComplex (up ℤ)).map (extendMap φ.hom embeddingUpNat)) ↑n ≫
      (thetaIso F (resPlus J) (n : ℤ)).inv ≫
      ((omegaFun F (n : ℤ)).mapIso (sigmaIso Y ≪≫ asIso (Plus.Q.map (resMap J)))).inv =
      (thetaIso F (resPlus I) (n : ℤ)).inv ≫
      ((omegaFun F (n : ℤ)).mapIso (sigmaIso X ≪≫ asIso (Plus.Q.map (resMap I)))).inv ≫
        (Gfun F (n : ℤ)).map f := by
    erw [← Category.assoc, hB', Category.assoc, hC']
    rfl
  rw [← Category.assoc _ (epsIso F J.cocomplex n).hom, hA]
  exact (Category.assoc _ _ _).trans ((congrArg ((epsIso F I.cocomplex n).hom ≫ ·) key).trans
    ((congrArg ((epsIso F I.cocomplex n).hom ≫ ·) (Category.assoc _ _ _).symm).trans
      (Category.assoc _ _ _).symm))


end

section
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex DerivedCategory

/-- The homomorphism of resolutions induced by a morphism. -/
noncomputable def resHom [HasInjectiveResolutions C] {X Y : C} (f : X ⟶ Y)
    (I : InjectiveResolution X) (J : InjectiveResolution Y) : InjectiveResolution.Hom I J f :=
  ⟨InjectiveResolution.desc f J I, by
    simpa using InjectiveResolution.desc_commutes_zero f J I⟩

/-- The right derived functors of `F` are naturally isomorphic to the homology of `F` applied to
the right derived functor on the bounded below derived category, evaluated on single objects. -/
noncomputable def rightDerivedIso [HasInjectiveResolutions C] (n : ℕ) :
    F.rightDerived n ≅ Gfun F (n : ℤ) :=
  NatIso.ofComponents
    (fun X => (InjectiveResolution.of X).isoRightDerivedObj F n ≪≫
      thetaRes F (InjectiveResolution.of X) n)
    (fun {X Y} f => by
      have h1 := InjectiveResolution.isoRightDerivedObj_hom_naturality f (InjectiveResolution.of X)
        (InjectiveResolution.of Y) (resHom f (InjectiveResolution.of X) (InjectiveResolution.of Y)).hom
        (by simpa using (resHom f (InjectiveResolution.of X) (InjectiveResolution.of Y)).ι_f_zero_comp_hom_f_zero) F n
      have h2 := thetaRes_naturality F f (resHom f (InjectiveResolution.of X) (InjectiveResolution.of Y)) n
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (thetaRes F (InjectiveResolution.of Y) n).hom) h1).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (((InjectiveResolution.of X).isoRightDerivedObj F n).hom ≫ ·) h2).trans
              (Category.assoc _ _ _).symm))))


end

section
variable {C : Type 1} [Category.{0} C] {D : Type 1} [Category.{0} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

open ComplexShape HomologicalComplex DerivedCategory

/-- The functor `Gfun F 0` takes monomorphisms to monomorphisms, by comparison with the right derived
functor in degree zero. -/
lemma Gfun_zero_map_mono [HasInjectiveResolutions C] [PreservesFiniteLimits F] {X Y : C} (f : X ⟶ Y)
    [Mono f] : Mono ((Gfun F ((0 : ℕ) : ℤ)).map f) := by
  have := rightDerived_zero_map_mono F f
  have h := (rightDerivedIso F 0).hom.naturality f
  have h2 : (Gfun F ((0 : ℕ) : ℤ)).map f =
      inv ((rightDerivedIso F 0).hom.app X) ≫ (F.rightDerived 0).map f ≫
        (rightDerivedIso F 0).hom.app Y := by
    rw [IsIso.eq_inv_comp, h]
  rw [h2]
  infer_instance

/-- The cohomological delta functor built from the right derived functor on the bounded below derived
category: in degree `n` the homology in degree `n` of the derived functor evaluated at the single
object, with connecting maps from the long exact homology sequence of the distinguished triangle of a
short exact sequence. -/
noncomputable def derivedDelta [HasInjectiveResolutions C] [PreservesFiniteLimits F] :
    CohomDeltaFunctor C D where
  T n := Gfun F (n : ℤ)
  additive n := inferInstance
  δ S hS n := Gδ F hS (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; rfl)
  comp_δ S hS n :=
    DerivedCategory.HomologySequence.comp_δ (GTri F hS) (GTri_dist F hS) (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (by push_cast; rfl)
  δ_comp S hS n :=
    DerivedCategory.HomologySequence.δ_comp (GTri F hS) (GTri_dist F hS) (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (by push_cast; rfl)
  mono₀ S hS := by
    have := hS.mono_f
    exact Gfun_zero_map_mono F S.f
  exact₂ S hS n := DerivedCategory.HomologySequence.exact₂ (GTri F hS) (GTri_dist F hS) (n : ℤ)
  exact₃ S hS n := DerivedCategory.HomologySequence.exact₃ (GTri F hS) (GTri_dist F hS) (n : ℤ)
    ((n + 1 : ℕ) : ℤ) (by push_cast; rfl)
  exact₁ S hS n := DerivedCategory.HomologySequence.exact₁ (GTri F hS) (GTri_dist F hS) (n : ℤ)
    ((n + 1 : ℕ) : ℤ) (by push_cast; rfl)
  naturality S₁ S₂ h₁ h₂ φ n := Gδ_naturality F h₁ h₂ φ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; rfl)


end

end PropA11Aux

open PropA11Aux in
/-- **Proposition A.11** (Milne, *Class Field Theory*, Ch. II, App. A, p. 94 to 95), unconditionally. For an
abelian category `C` with injective resolutions and a left exact additive functor `F : C ⥤ D`, there is a
cohomological delta functor whose functors are naturally isomorphic to the right derived functors
`F.rightDerived n`. The connecting morphisms come from the derived category (see `derivedDelta`). -/
@[kb "milne2020cft" "v4.03, Ch. II, App. A, Prop. A.11, p. 94–95"]
theorem propA_11 : PropA_11 := by
  refine ⟨fun C _ _ _ D _ _ F _ _ => ?_⟩
  let _ : HasDerivedCategory.{1} C := HasDerivedCategory.standard C
  let _ : HasDerivedCategory.{1} D := HasDerivedCategory.standard D
  have : EnoughInjectives C :=
    ⟨fun X => by
      obtain ⟨I⟩ := (HasInjectiveResolution.out : Nonempty (InjectiveResolution X))
      exact ⟨{ J := I.cocomplex.X 0
               injective := I.injective 0
               f := I.ι.f 0
               mono := (inferInstance : Mono (I.ι.f 0)) }⟩⟩
  exact ⟨derivedDelta F, ⟨fun n => (rightDerivedIso F n).symm⟩⟩

end NumberFieldKB.MilneCFT
