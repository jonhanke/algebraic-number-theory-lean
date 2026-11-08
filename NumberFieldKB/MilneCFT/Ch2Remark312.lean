import NumberFieldKB.MilneCFT.Ch2Tate
import NumberFieldKB.MilneCFT.Ch2Remark313
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.Cup.TateTheorem
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.TateCohomology.IsoCriterion

/-!
# Milne, *Class Field Theory*, Chapter II, Remark 3.12: reduction to a Kuenneth-type lemma

`Remark3_12` (in `Ch2Tate.lean`) asks, under the hypotheses of Tate's theorem and `Tor_1^ℤ(M, C) = 0`, for
isomorphisms `Ĥ^r(G, M) ≅ Ĥ^{r+2}(G, M ⊗ C)`.

**Status: conditional.** We prove `remark3_12_of_lemma : TensorCohomTrivialLemma → Remark3_12`. The only input not
proved is `TensorCohomTrivialLemma`: if `W` has trivial Tate cohomology on every subgroup and `Tor_1^ℤ(M, W) = 0`,
then `M ⊗ W` has trivial Tate cohomology (the textbook consequence of a cohomologically trivial module having
projective dimension at most one over `ℤ[G]`; Milne uses it on p. 85 for `C(φ) ⊗ M`; source not yet checked,
`[unverified]`). No such statement is in Tau Ceti's Tate cohomology development or in this repository.

Route (this differs from Milne's splitting module `C(φ)`, using Tau Ceti's Tate theorem instead):
1. `exists_tate_map`: Tate's theorem gives `f : ℤ ⟶ N₂ = dimensionShiftUp (dimensionShiftUp C)` bijective on `Ĥ^n(S, -)`
   for every subgroup `S` and every `n` (same proof as `cup_bijective_of_forall_isPGroup`, with the criterion on
   all subgroups).
2. `padCokernelSeq f`: `0 ⟶ ℤ ⟶ N₂ ⊞ Coind_⊥^G ℤ ⟶ W ⟶ 0`, which is split over `ℤ` so stays exact after `M ⊗ -`
   (`padCokernelSeq_tensorLeft_shortExact`), with `W` cohomologically trivial (`isZero_res_padCokernelSeq_X₃`).
3. `Tor_1(M, W) = 0` (`isZero_tor_padCokernelSeq_X₃`): `W` is a `ℤ`-retract of `N₂ ⊞ Coind_⊥^G ℤ`, and `N₂` is a
   retract of `Coind_⊥^G (Coind_⊥^G C)`, using additivity of `Tor_1(M, -)` (proved here, `torOneAdditive`).
4. With the lemma, `M ⊗ W` is cohomologically trivial, so `M ◁ f` is bijective on `Ĥ^n(G, -)`
   (`tateCohomology_map_whiskerLeft_bijective`); compose with `ρ_ M` and the two tensored dimension shifts.
-/

open CategoryTheory Rep Limits MonoidalCategory
open TauCeti TauCeti.TateCohomology

namespace NumberFieldKB.MilneCFT

section TateMap

attribute [local instance] Subgroup.fintypeOfFinite

/-- The map `f : ℤ ⟶ N₂` of Tate's theorem is bijective on Tate cohomology of every subgroup in every degree. -/
theorem exists_tate_map {G : Type} [Group G] [Fintype G] (N : Rep ℤ G) (u : tateCohomology N 2)
    (hgen : ∀ y : tateCohomology N 2, ∃ m : ℤ, m • u = y)
    (hcardG : Nat.card (tateCohomology N 2) = Nat.card G)
    (h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (Rep.res S.subtype N) 1))
    (hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Nat.card (tateCohomology (Rep.res S.subtype N) 2) = Nat.card S) :
    ∃ f : Rep.trivial ℤ G ℤ ⟶ dimensionShiftUp (dimensionShiftUp N),
      ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
        Function.Bijective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map f)) := by
  have hinj₀ : Function.Injective (cupTrivialInt N u) :=
    (cupTrivialInt_bijective N u hgen (hcardG.trans Nat.card_eq_fintype_card)).injective
  obtain ⟨a, ha⟩ := H0_induction_on
    (C := fun z ↦ ∃ a, H0π (dimensionShiftUp (dimensionShiftUp N)) a = z)
    ((dimensionShiftUpTwoIso N).inv u) fun y ↦ ⟨y, rfl⟩
  have hu : u = (dimensionShiftUpTwoIso N).hom (H0π _ a) := by
    rw [ha, Iso.inv_hom_id_apply]
  set f := Rep.tensorInvariant (Rep.trivial ℤ G ℤ) a with hf
  have hcup : ∀ p : ℤ,
      (fun x : tateCohomology (Rep.trivial ℤ G ℤ) p ↦
        cup (Rep.trivial ℤ G ℤ) N p 2 (p + 2) rfl x u) =
      ⇑(tensorDimensionShiftUpIso N (Rep.trivial ℤ G ℤ) (p + 1) (p + 2) (by omega)).hom ∘
        ⇑(tensorDimensionShiftUpIso (dimensionShiftUp N) (Rep.trivial ℤ G ℤ) p (p + 1) rfl).hom ∘
        ⇑((tateCohomologyFunctor p).map f) := fun p ↦ funext fun x ↦ by
    rw [hu, cup_dimensionShiftUpTwoIso_hom, cupH0_H0π]
    rfl
  have hinj : Function.Injective ((tateCohomologyFunctor 0).map f) := by
    have : ⇑(cupTrivialInt N u) = ⇑((tateCohomologyFunctor 2).map (λ_ N).hom) ∘
        fun x : tateCohomology (Rep.trivial ℤ G ℤ) 0 ↦
          cup (Rep.trivial ℤ G ℤ) N 0 2 (0 + 2) rfl x u :=
      funext fun x ↦ cupTrivialInt_apply N u x
    rw [this, hcup 0] at hinj₀
    exact hinj₀.of_comp.of_comp.of_comp
  refine ⟨f ≫ (λ_ _).hom, fun S _ n => ?_⟩
  rw [Functor.map_comp, Functor.map_comp, ConcreteCategory.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso (((tateCohomologyFunctor n).mapIso
    ((resFunctor S.subtype).mapIso (λ_ (dimensionShiftUp (dimensionShiftUp N))))).hom)).comp ?_
  refine map_res_bijective_of_forall_isPGroup f (q := 0) ?_ ?_ ?_ S n
  · intro p _ S inst hS
    obtain rfl : inst = Subgroup.fintypeOfFinite S := Subsingleton.elim _ _
    have : Subsingleton (tateCohomology
        (Rep.res S.subtype (Rep.trivial ℤ G ℤ ⊗ dimensionShiftUp (dimensionShiftUp N))) (0 - 1)) :=
      ModuleCat.subsingleton_of_isZero ((h1 p S hS).of_iso
        ((tateCohomologyFunctor (0 - 1)).mapIso
          ((resFunctor S.subtype).mapIso (λ_ (dimensionShiftUp (dimensionShiftUp N)))) ≪≫
        dimensionShiftUpTwoResIso N S (0 - 1)))
    exact Function.surjective_to_subsingleton _
  · intro p _ S inst hS
    obtain rfl : inst = Subgroup.fintypeOfFinite S := Subsingleton.elim _ _
    exact map_res_zero_bijective_of_injective f hinj S
      ((Nat.card_congr ((tateCohomologyFunctor 0).mapIso
          ((resFunctor S.subtype).mapIso (λ_ (dimensionShiftUp (dimensionShiftUp N)))) ≪≫
        dimensionShiftUpTwoResIso N S 0).toLinearEquiv.toEquiv).trans (hcard p S hS))
  · intro p _ S inst _
    obtain rfl : inst = Subgroup.fintypeOfFinite S := Subsingleton.elim _ _
    have : Subsingleton (tateCohomology (Rep.res S.subtype (Rep.trivial ℤ G ℤ)) (0 + 1)) :=
      ModuleCat.subsingleton_of_isZero (isZero_tateCohomology_one_res_trivial_int S)
    exact Function.injective_of_subsingleton _


end TateMap

section Pad

variable {G : Type} [Group G] [Fintype G]

/-- The cokernel of the monomorphism `A ⟶ B ⊞ Coind A` with components `f` and the coinduction unit. -/
noncomputable abbrev padCokernelSeq {A B : Rep ℤ G} (f : A ⟶ B) : ShortComplex (Rep ℤ G) :=
  ShortComplex.cokernelSequence (biprod.lift f (coindBotUnit A))

theorem padCokernelSeq_shortExact {A B : Rep ℤ G} (f : A ⟶ B) : (padCokernelSeq f).ShortExact := by
  haveI : Mono (biprod.lift f (coindBotUnit A)) := mono_of_mono_fac (biprod.lift_snd f (coindBotUnit A))
  exact TauCeti.cokernelSequence_shortExact _

/-- Tensoring the padded cokernel sequence with `M` on the left stays short exact (the first map has a
`ℤ`-linear retraction). -/
theorem padCokernelSeq_tensorLeft_shortExact {A B : Rep ℤ G} (f : A ⟶ B) (M : Rep ℤ G) :
    ((padCokernelSeq f).map (tensorLeft M)).ShortExact := by
  haveI : Epi (padCokernelSeq f).g := (padCokernelSeq_shortExact f).epi_g
  have hU : Mono (M ◁ coindBotUnit A) :=
    (Rep.mono_iff_injective _).2
      (leftInverse_whiskerLeft M (coindBotUnit A) (leftInverse_coindBotUnit A)).injective
  have hw : (M ◁ biprod.lift f (coindBotUnit A)) ≫ (M ◁ (biprod.snd : B ⊞ coindBot ℤ G A.V ⟶ _)) =
      M ◁ coindBotUnit A := by
    rw [← whiskerLeft_comp, biprod.lift_snd]
  have hL : Mono (M ◁ (padCokernelSeq f).f) := by
    exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hU hw
  have hf : Function.Injective (LinearMap.lTensor M.V (padCokernelSeq f).f.hom.toLinearMap) :=
    (Rep.mono_iff_injective _).1 hL
  exact shortExact_map_tensorLeft_of_injective (padCokernelSeq_shortExact f).exact M hf

/-- If `M ⊗ W` has no Tate cohomology, then `M ◁ f` is bijective on Tate cohomology in every degree. -/
theorem tateCohomology_map_whiskerLeft_bijective {A B : Rep ℤ G} (f : A ⟶ B) (M : Rep ℤ G)
    (hW : ∀ n, IsZero (tateCohomology (M ⊗ (padCokernelSeq f).X₃) n)) (n : ℤ) :
    Function.Bijective ((tateCohomologyFunctor n).map (M ◁ f)) := by
  have hS := padCokernelSeq_tensorLeft_shortExact f M
  have hlift : Function.Bijective ((tateCohomologyFunctor n).map (M ◁ biprod.lift f (coindBotUnit A))) :=
    ⟨map_f_injective_of_isZero_X₃ hS (n - 1) n (sub_add_cancel n 1) (hW (n - 1)),
      map_f_surjective_of_isZero_X₃ hS n (hW n)⟩
  haveI : IsIso ((tensorLeft M ⋙ tateCohomologyFunctor n).map
      (biprod.fst : B ⊞ coindBot ℤ G A.V ⟶ B)) :=
    (tensorLeft M ⋙ tateCohomologyFunctor n).isIso_map_biprod_fst_of_isZero B (coindBot ℤ G A.V)
      (isZero_tensor_coindBot A.V M n)
  have hfst := ConcreteCategory.bijective_of_isIso
    ((tensorLeft M ⋙ tateCohomologyFunctor n).map (biprod.fst : B ⊞ coindBot ℤ G A.V ⟶ B))
  have : M ◁ f = (M ◁ biprod.lift f (coindBotUnit A)) ≫ (M ◁ (biprod.fst : B ⊞ coindBot ℤ G A.V ⟶ B)) := by
    rw [← whiskerLeft_comp, biprod.lift_fst]
  rw [this, Functor.map_comp, ConcreteCategory.coe_comp]
  exact hfst.comp hlift

/-- If `f` is bijective on the Tate cohomology of every subgroup in every degree, the padded cokernel `W` has no
Tate cohomology on any subgroup. -/
theorem isZero_res_padCokernelSeq_X₃ {A B : Rep ℤ G} (f : A ⟶ B)
    (hf : ∀ (S : Subgroup G) [Fintype S] (n : ℤ),
      Function.Bijective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map f)))
    (S : Subgroup G) [Fintype S] (m : ℤ) :
    IsZero (tateCohomology (res S.subtype (padCokernelSeq f).X₃) m) := by
  haveI : Mono (biprod.lift f (coindBotUnit A)) := mono_of_mono_fac (biprod.lift_snd f (coindBotUnit A))
  have hT : ((padCokernelSeq f).map (resFunctor S.subtype)).ShortExact :=
    (shortExact_res S.subtype).2 (padCokernelSeq_shortExact f)
  have hfst : ∀ n, Function.Bijective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map
      (biprod.fst : B ⊞ coindBot ℤ G A.V ⟶ B))) := fun n =>
    haveI := (resFunctor S.subtype ⋙ tateCohomologyFunctor n).isIso_map_biprod_fst_of_isZero
      B (coindBot ℤ G A.V) (isZero_res_coindBot S A.V n)
    ConcreteCategory.bijective_of_isIso
      ((resFunctor S.subtype ⋙ tateCohomologyFunctor n).map (biprod.fst : B ⊞ coindBot ℤ G A.V ⟶ B))
  have hlift : ∀ n, Function.Bijective ((tateCohomologyFunctor n).map ((resFunctor S.subtype).map
      (biprod.lift f (coindBotUnit A)))) := fun n => by
    have h := hf S n
    rw [← biprod.lift_fst f (coindBotUnit A), Functor.map_comp, Functor.map_comp,
      ConcreteCategory.coe_comp] at h
    exact (Function.Bijective.of_comp_iff' (hfst n) _).1 h
  exact isZero_X₃_of_surjective_of_injective hT m (m + 1) rfl (hlift m).2 (hlift (m + 1)).1


end Pad

section Split

theorem exists_section_cokernelSequence {k G : Type} [CommRing k] [Group G] {A B : Rep k G} (f : A ⟶ B)
    (hS : (ShortComplex.cokernelSequence (biprod.lift f (coindBotUnit A))).ShortExact) :
    ∃ s : (ShortComplex.cokernelSequence (biprod.lift f (coindBotUnit A))).X₃.V →ₗ[k]
        (ShortComplex.cokernelSequence (biprod.lift f (coindBotUnit A))).X₂.V,
      Function.RightInverse s (ShortComplex.cokernelSequence (biprod.lift f (coindBotUnit A))).g.hom := by
  obtain ⟨r0, hr0⟩ : ∃ r : (coindBot k G A.V).V →ₗ[k] A.V, Function.LeftInverse r (coindBotUnit A).hom :=
    ⟨_, leftInverse_coindBotUnit A⟩
  haveI := hS.epi_g
  refine exists_rightInverse_of_leftInverse hS.exact
    (r := r0 ∘ₗ (biprod.snd : B ⊞ coindBot k G A.V ⟶ _).hom.toLinearMap) ?_
  intro a
  have h2 : (biprod.snd : B ⊞ coindBot k G A.V ⟶ _).hom ((biprod.lift f (coindBotUnit A)).hom a) =
      (coindBotUnit A).hom a := by
    conv_rhs => rw [← biprod.lift_snd f (coindBotUnit A)]
    rfl
  change r0 ((biprod.snd : B ⊞ coindBot k G A.V ⟶ _).hom ((biprod.lift f (coindBotUnit A)).hom a)) = a
  rw [h2]
  exact hr0 a


end Split

section Tor

variable {k : Type} [CommRing k]

/-- A retract of an object killed by a functor is killed by it. -/
theorem isZero_obj_of_retract {C D : Type*} [Category C] [Category D] [Preadditive D]
    (F : C ⥤ D) {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X) (h : i ≫ p = 𝟙 X) (hY : IsZero (F.obj Y)) :
    IsZero (F.obj X) := by
  rw [IsZero.iff_id_eq_zero]
  rw [← F.map_id, ← h, F.map_comp]
  rw [hY.eq_of_tgt (F.map i) 0, zero_comp]

/-- An additive functor killing both summands kills the biproduct. -/
theorem isZero_obj_biprod {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] (F : C ⥤ D) [F.Additive] {X Y : C} (hX : IsZero (F.obj X))
    (hY : IsZero (F.obj Y)) : IsZero (F.obj (X ⊞ Y)) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← biprod.total, F.map_add, F.map_comp, F.map_comp,
    hX.eq_of_tgt (F.map biprod.fst) 0, hY.eq_of_tgt (F.map biprod.snd) 0]
  simp

/-- An additive functor killing every summand kills a finite biproduct. -/
theorem isZero_obj_biproduct {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → C) [HasBiproduct f] (F : C ⥤ D) [F.Additive]
    (h : ∀ i, IsZero (F.obj (f i))) : IsZero (F.obj (⨁ f)) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← biproduct.total, F.map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [F.map_comp, (h i).eq_of_tgt (F.map (biproduct.π f i)) 0, zero_comp]

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- An additive functor killing `A` kills `Coind_⊥^G A` (as a `k`-module, a finite product of copies of `A`). -/
theorem isZero_obj_coindBot (F : ModuleCat k ⥤ ModuleCat k) [F.Additive] (A : Rep k G)
    (h : IsZero (F.obj (ModuleCat.of k A.V))) :
    IsZero (F.obj (ModuleCat.of k (coindBot k G A.V))) := by
  have e : ModuleCat.of k (coindBot k G A.V) ≅ ModuleCat.of k (G → A.V) :=
    (coindBotEquivPi k G A.V).toModuleIso
  refine IsZero.of_iso ?_ (F.mapIso e)
  refine IsZero.of_iso ?_ (F.mapIso (ModuleCat.biproductIsoPi (fun _ : G => ModuleCat.of k A.V)).symm)
  exact isZero_obj_biproduct (fun _ : G => ModuleCat.of k A.V) F fun _ => h

/-- An additive functor killing `A` kills the dimension shift `dimensionShiftUp A`, a retract of
`Coind_⊥^G A`. -/
theorem isZero_obj_dimensionShiftUp (F : ModuleCat k ⥤ ModuleCat k) [F.Additive] (A : Rep k G)
    (h : IsZero (F.obj (ModuleCat.of k A.V))) :
    IsZero (F.obj (ModuleCat.of k (dimensionShiftUp A).V)) := by
  obtain ⟨r0, hr0⟩ : ∃ r : (coindBot k G A.V).V →ₗ[k] A.V,
      Function.LeftInverse r (coindBotUnit A).hom := ⟨_, leftInverse_coindBotUnit A⟩
  haveI := (dimensionShiftUpSES_shortExact A).epi_g
  obtain ⟨s, hs⟩ := exists_rightInverse_of_leftInverse (dimensionShiftUpSES_shortExact A).exact hr0
  refine isZero_obj_of_retract F (ModuleCat.ofHom s)
    (ModuleCat.ofHom (dimensionShiftUpSES A).g.hom.toLinearMap) ?_ (isZero_obj_coindBot F A h)
  exact ModuleCat.hom_ext (LinearMap.ext fun x => hs x)

end Tor


section Main

variable {G : Type} [Group G] [Fintype G]

/-- Taking projective resolutions is additive (lifts of sums are homotopic to sums of lifts). -/
instance projectiveResolutions_additive (C : Type*) [Category C] [Abelian C] [HasProjectiveResolutions C] :
    (projectiveResolutions C).Additive where
  map_add {X Y f g} := by
    have key : (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift (f + g) (projectiveResolution X) (projectiveResolution Y)) =
        (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
          (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
           ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y)) := by
      apply HomotopyCategory.eq_of_homotopy
      exact ProjectiveResolution.liftHomotopy (f + g) _ _ (by simp) (by simp)
    exact key.trans (Functor.map_add _)

open MonoidalCategory in
/-- `Tor_1(M, -)` is an additive functor. -/
instance torOneAdditive (X : ModuleCat ℤ) : ((Tor (ModuleCat ℤ) 1).obj X).Additive := by
  show (Functor.leftDerived ((tensoringLeft (ModuleCat ℤ)).obj X) 1).Additive
  unfold Functor.leftDerived Functor.leftDerivedToHomotopyCategory
  infer_instance

/-- The `Tor_1`-vanishing of the padded cokernel: if `Tor_1(M, A) = Tor_1(M, B) = 0` then `Tor_1(M, W) = 0` for
the cokernel `W` of `A ⟶ B ⊞ Coind_⊥^G A` (`W` is a `ℤ`-retract of `B ⊞ Coind_⊥^G A`). -/
theorem isZero_tor_padCokernelSeq_X₃ {A B : Rep ℤ G} (f : A ⟶ B) (M : Rep ℤ G)
    (hA : IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ A)))
    (hB : IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ B))) :
    IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj
      (ModuleCat.of ℤ (padCokernelSeq f).X₃)) := by
  classical
  obtain ⟨s, hs⟩ := exists_section_cokernelSequence f (padCokernelSeq_shortExact f)
  refine isZero_obj_of_retract ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)) (ModuleCat.ofHom s)
    (ModuleCat.ofHom (padCokernelSeq f).g.hom.toLinearMap) (ModuleCat.hom_ext (LinearMap.ext fun x => hs x)) ?_
  have hC := isZero_obj_coindBot ((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)) A hA
  exact isZero_obj_biprod (forget₂ (Rep ℤ G) (ModuleCat ℤ) ⋙ (Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M))
    (X := B) (Y := coindBot ℤ G A.V) hB hC

/-- **The missing lemma** (Kuenneth-type, Atiyah-Wall; Milne uses it for `C(φ) ⊗ M` on p. 85): if `W` has trivial Tate
cohomology on every subgroup and `Tor_1^ℤ(M, W) = 0`, then `M ⊗ W` has trivial Tate cohomology. -/
@[kb "milne2020cft" "v4.03, Ch. II, Remark 3.12, p. 85, C(φ) ⊗ M cohomologically trivial (input)"]
structure TensorCohomTrivialLemma : Prop where
  isZero : ∀ (G : Type) [Group G] [Fintype G] (W M : Rep ℤ G),
    (∀ (S : Subgroup G) [Fintype S] (n : ℤ), IsZero (tateCohomology (res S.subtype W) n)) →
    IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj (ModuleCat.of ℤ W)) →
    ∀ n : ℤ, IsZero (tateCohomology (M ⊗ W) n)

/-- **Remark 3.12 from the lemma `TensorCohomTrivialLemma`.** -/
theorem remark3_12_of_lemma (hK : TensorCohomTrivialLemma) : Remark3_12 := by
  refine ⟨fun G _ _ C M hC hTor γ hγ r => ?_⟩
  let e2 : tateCohomology C ((2 : ℕ) : ℤ) ≅ groupCohomology C 2 :=
    (TateCohomology.isoGroupCohomology (R := ℤ) (G := G) 2).app C
  let u : tateCohomology C 2 := (Rep.fromGroupCohomology C 2).hom γ
  have hu : u = e2.inv.hom γ := by
    change (Rep.fromGroupCohomology C (1 + 1)).hom γ = _
    rw [Rep.fromGroupCohomology_succ]
  have hgen : ∀ y : tateCohomology C 2, ∃ m : ℤ, m • u = y := by
    intro y
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 (hγ (e2.hom.hom y))
    refine ⟨m, ?_⟩
    have : e2.inv.hom (e2.hom.hom y) = y := by
      rw [← ModuleCat.comp_apply, Iso.hom_inv_id]; rfl
    rw [hu, ← this, ← hm, map_zsmul]
  have hcardG : Nat.card (tateCohomology C 2) = Nat.card G := by
    refine (Nat.card_congr e2.toLinearEquiv.toEquiv).trans ?_
    rw [← Nat.card_congr (groupCohomologyResTopIso C 2).toLinearEquiv.toEquiv, (hC ⊤).2.2]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have h1 : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      IsZero (tateCohomology (res S.subtype C) 1) := fun _ _ S _ _ =>
    ((TateCohomology.isoGroupCohomology (R := ℤ) 1).app (res S.subtype C)).isZero_iff.2 (hC S).1
  have hcard : ∀ (p : ℕ) [Fact p.Prime] (S : Subgroup G) [Fintype S], IsPGroup p S →
      Nat.card (tateCohomology (res S.subtype C) 2) = Nat.card S := fun _ _ S _ _ => by
    exact (Nat.card_congr ((TateCohomology.isoGroupCohomology (R := ℤ) 2).app
      (res S.subtype C)).toLinearEquiv.toEquiv).trans (hC S).2.2
  obtain ⟨f, hf⟩ := exists_tate_map C u hgen hcardG h1 hcard
  classical
  have hA : IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj
      (ModuleCat.of ℤ (Rep.trivial ℤ G ℤ))) :=
    isZero_Tor_succ_of_projective (ModuleCat ℤ) (ModuleCat.of ℤ M) (ModuleCat.of ℤ ℤ) 0
  have hB : IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ M)).obj
      (ModuleCat.of ℤ (dimensionShiftUp (dimensionShiftUp C)))) :=
    isZero_obj_dimensionShiftUp _ _ (isZero_obj_dimensionShiftUp _ C hTor)
  have hW := hK.isZero G (padCokernelSeq f).X₃ M (isZero_res_padCokernelSeq_X₃ f hf)
    (isZero_tor_padCokernelSeq_X₃ f M hA hB)
  haveI : IsIso ((tateCohomologyFunctor r).map (M ◁ f)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (tateCohomology_map_whiskerLeft_bijective f M hW r)
  exact ⟨(tateCohomologyFunctor r).mapIso (ρ_ M).symm ≪≫ asIso ((tateCohomologyFunctor r).map (M ◁ f)) ≪≫
    tensorDimensionShiftUpIso (dimensionShiftUp C) M r (r + 1) rfl ≪≫
    tensorDimensionShiftUpIso C M (r + 1) (r + 2) (by ring)⟩

end Main

end NumberFieldKB.MilneCFT
