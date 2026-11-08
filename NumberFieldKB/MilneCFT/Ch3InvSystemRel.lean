import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3InvSystemTop
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.FiniteExtension.IntermediateField
import NumberFieldKB.MilneCFT.Ch4SplitDegree

/-!
# Milne, *Class Field Theory*, Chapter III §2: the relative invariant maps $\mathrm{inv}_{M/M^H}$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

For a finite Galois $M/K$ inside $\Omega$ and a subgroup $H$ of $\operatorname{Gal}(M/K)$, put $F = M^H$
(`IntermediateField.fixedField H`, a subfield of $M$, with Tau Ceti's local-field structure). The relative invariant
`tcInvRel M H : H^2(M/F) → ℚ/ℤ` is Tau Ceti's local invariant $\mathrm{inv}_F$ of the class inflated into
$\mathrm{Br}(F)$, after $H \simeq \operatorname{Gal}(M/F)$ (`relIso`).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory IntermediateField

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Local

variable {M : IntermediateField K Ω} [FiniteDimensional K M]

/-- Tau Ceti's local-field structure (spectral norm) on a subfield of $M$ containing $K$. -/
noncomputable local instance subVR (F : IntermediateField K M) : ValuativeRel F :=
  TauCeti.algebraicExtensionValuativeRel K F

noncomputable local instance subTop (F : IntermediateField K M) : TopologicalSpace F :=
  TauCeti.algebraicExtensionNormedFieldTopology K F

local instance subLocal (F : IntermediateField K M) : IsNonarchimedeanLocalField F :=
  TauCeti.finiteExtension_isNonarchimedeanLocalField K F

local instance subExt (F : IntermediateField K M) : ValuativeExtension K F :=
  TauCeti.algebraicExtension_valuativeExtension K F

variable (M)

/-- $H \simeq \operatorname{Gal}(M/M^H)$. -/
noncomputable def galFixEquiv (H : Subgroup Gal(M/K)) : H ≃* (M ≃ₐ[fixedField H] M) :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField H).symm).trans (fixingSubgroupEquiv (fixedField H))

/-- $H^2(M/M^H)$ computed with the subgroup $H$ is $H^2(\operatorname{Gal}(M/M^H), M^\times)$. -/
noncomputable def relIso (H : Subgroup Gal(M/K)) :
    H2rel M H ≅ groupCohomology (Rep.ofAlgebraAutOnUnits (fixedField H) M) 2 :=
  groupCohomology.mapIso (A := Rep.ofAlgebraAutOnUnits (fixedField H) M)
    (B := res H.subtype (Rep.ofAlgebraAutOnUnits K M)) (galFixEquiv M H) (LinearEquiv.refl ℤ _)
    (fun _ => LinearMap.ext fun _ => rfl) 2

/-- The embedding of $M$ into $(M^H)^{\mathrm{sep}}$. -/
noncomputable def embFix (H : Subgroup Gal(M/K)) : M →ₐ[fixedField H] SeparableClosure (fixedField H) :=
  IsSepClosed.lift

/-- $H^2(M/M^H) \to \mathrm{Br}(M^H)$. -/
noncomputable def toBrRel (H : Subgroup Gal(M/K)) : H2rel M H →+ Br (fixedField H) :=
  (relBrInfl (fixedField H) M (embFix M H)).comp (relIso M H).hom.hom.toAddMonoidHom

/-- **The relative invariant map** $\mathrm{inv}_{M/M^H}$ (Milne, p. 103–105), with Tau Ceti's
$\mathrm{inv}_{M^H} : \mathrm{Br}(M^H) \simeq \mathbb Q/\mathbb Z$. -/
noncomputable def tcInvRel (H : Subgroup Gal(M/K)) : H2rel M H →+ QZ :=
  (Ch4.addCircleEquivQZ.toAddMonoidHom.comp (invMap (fixedField H)).toAddMonoidHom).comp (toBrRel M H)

theorem tcInvRel_apply (H : Subgroup Gal(M/K)) (x : H2rel M H) :
    tcInvRel M H x = Ch4.addCircleEquivQZ (invMap (fixedField H) (toBrRel M H x)) := rfl

theorem relIso_bijective (H : Subgroup Gal(M/K)) : Function.Bijective (relIso M H).hom.hom :=
  ConcreteCategory.bijective_of_isIso (relIso M H).hom

theorem tcInvRel_injective (H : Subgroup Gal(M/K)) : Function.Injective (tcInvRel M H) :=
  ((Ch4.addCircleEquivQZ.injective.comp (invMap _).injective).comp
    (relBrInfl_injective _ M (embFix M H))).comp (relIso_bijective M H).1

theorem range_tcInvRel (H : Subgroup Gal(M/K)) : (tcInvRel M H).range = qzOver (Nat.card H) := by
  set F := fixedField H
  let _ := TauCeti.algebraicExtensionValuativeRel F M
  let _ := TauCeti.algebraicExtensionNormedFieldTopology F M
  have := TauCeti.finiteExtension_isNonarchimedeanLocalField F M
  have := TauCeti.algebraicExtension_valuativeExtension F M
  have hFM : Module.finrank F M = Nat.card H := finrank_fixedField_eq_card H
  have hn : 0 < Nat.card H := Nat.card_pos
  have h := range_invMap_comp_relBrInfl F M (embFix M H)
  rw [hFM] at h
  ext y
  rw [mem_qzOver_iff _ hn, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    have hx : invMap F (toBrRel M H x) ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) (Nat.card H) := by
      have : (invMap F ∘ relBrInfl F M (embFix M H)) ((relIso M H).hom.hom x) ∈ Set.range
          (invMap F ∘ relBrInfl F M (embFix M H)) := ⟨_, rfl⟩
      rw [h] at this
      exact this
    rw [AddSubgroup.torsionBy.nsmul_iff] at hx
    rw [tcInvRel_apply, ← map_nsmul, hx, map_zero]
  · intro hy
    have ht : Ch4.addCircleEquivQZ.symm y ∈ Set.range (invMap F ∘ relBrInfl F M (embFix M H)) := by
      rw [h]
      exact AddSubgroup.torsionBy.nsmul_iff.2 (by rw [← map_nsmul, hy, map_zero])
    obtain ⟨z, hz⟩ := ht
    obtain ⟨x, rfl⟩ := (relIso_bijective M H).2 z
    have hz' : invMap F (toBrRel M H x) = Ch4.addCircleEquivQZ.symm y := hz
    exact ⟨x, show Ch4.addCircleEquivQZ (invMap F (toBrRel M H x)) = y by
      rw [hz', AddEquiv.apply_symm_apply]⟩

/-! ### Restriction from $K$ to $M^H$ -/

theorem restrictNormalHom_self_apply {F : Type} [Field F] [Algebra F M] [Normal F M] (g : M ≃ₐ[F] M) (y : M) :
    (AlgEquiv.restrictNormalHom M g) y = g y := by
  have := AlgEquiv.restrictNormal_commutes g M y
  simp at this
  exact this

theorem relIso_resK [IsGalois K M] (H : Subgroup Gal(M/K)) (x : H2 M) :
    (relIso M H).hom.hom ((resK M H).hom x) =
      (groupCohomology.map ((AlgEquiv.restrictNormalHom M).comp (AlgEquiv.restrictScalarsHom K))
        (TauCeti.unitsBaseChangeHom K M (fixedField H) M) 2).hom x := by
  rw [relIso]
  erw [groupCohomology.mapIso_hom]
  rw [resK, ← ModuleCat.comp_apply, ← groupCohomology.map_comp]
  congr 2
  apply groupCohomology.map_congr
  · refine MonoidHom.ext fun g => AlgEquiv.ext fun y => ?_
    change g y = _
    rw [MonoidHom.comp_apply, restrictNormalHom_self_apply]
    rfl
  · rfl

/-- **Restriction to $M^H$ is base change of Brauer classes** (Milne, II, 1.27 (b) and p. 105). -/
theorem toBrRel_resK [IsGalois K M] (H : Subgroup Gal(M/K)) (x : H2 M) :
    toBrRel M H ((resK M H).hom x) = brBaseChange K (fixedField H) (toBr M x) := by
  have e := brBaseChange_relBrInfl K (fixedField H) M M ((sepEquiv K Ω).toAlgHom.comp M.val) (embFix M H) x
  rw [toBr]
  erw [e]
  exact congrArg (relBrInfl (fixedField H) M (embFix M H)) (relIso_resK M H x)

theorem finrank_fixedField_eq_index [IsGalois K M] (H : Subgroup Gal(M/K)) :
    Module.finrank K (fixedField H) = H.index := by
  have h1 := Module.finrank_mul_finrank K (fixedField H) M
  rw [finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank K M] at h1
  have h2 := H.card_mul_index
  have hpos : 0 < Nat.card H := Nat.card_pos
  rw [← h2, mul_comm (Nat.card H)] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

/-- **(29) for $M^H/K$**: $\mathrm{inv}_{M/M^H} \circ \mathrm{Res} = (G : H)\,\mathrm{inv}_{M/K}$. -/
theorem tcInvRel_resK [IsGalois K M] (H : Subgroup Gal(M/K)) (x : H2 M) :
    tcInvRel M H ((resK M H).hom x) = H.index • tcInvK M x := by
  rw [tcInvRel_apply, toBrRel_resK, Ch4.invMap_brBaseChange, finrank_fixedField_eq_index, map_nsmul,
    tcInvK_apply]

/-! ### Composition of two group-cohomology maps -/

/-- Applying `groupCohomology.map g ψ` after `groupCohomology.map f φ` is `map (f.comp g) _`
(elementwise form of `groupCohomology.map_comp`). -/
theorem map_map_apply {G H K : Type} [Group G] [Group H] [Group K] {A : Rep ℤ K} {B : Rep ℤ H}
    {C : Rep ℤ G} (f : H →* K) (g : G →* H) (φ : res f A ⟶ B) (ψ : res g B ⟶ C) (n : ℕ)
    (y : groupCohomology A n) :
    (groupCohomology.map g ψ n).hom ((groupCohomology.map f φ n).hom y) =
      (groupCohomology.map (f.comp g) ((resFunctor g).map φ ≫ ψ) n).hom y := by
  rw [groupCohomology.map_comp]; rfl

/-! ### Restriction from $M^H$ to $M^{H'}$, $H' \subseteq H$ -/

section ResRel

variable {H' H : Subgroup Gal(M/K)} (h : H' ≤ H)
include h

/-- The inclusion $M^H \subseteq M^{H'}$ as an algebra. -/
noncomputable abbrev fixAlg : Algebra (fixedField H) (fixedField H') :=
  (IntermediateField.inclusion (fixedField_le h)).toAlgebra

/-- $\mathrm{inv}$-compatibility at the level of cohomology: restriction $H^2(M/M^H) \to H^2(M/M^{H'})$ is
the map induced by the base change $M^H \subseteq M^{H'}$. -/
theorem relIso_resRel [Algebra (fixedField H) (fixedField H')]
    [IsScalarTower (fixedField H) (fixedField H') M] (x : H2rel M H) :
    (relIso M H').hom.hom ((resRel M h).hom x) =
      (groupCohomology.map ((AlgEquiv.restrictNormalHom M).comp
          (AlgEquiv.restrictScalarsHom (fixedField H)))
        (TauCeti.unitsBaseChangeHom (fixedField H) M (fixedField H') M) 2).hom
        ((relIso M H).hom.hom x) := by
  rw [relIso, relIso]
  erw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
  rw [resRel]
  erw [map_map_apply, map_map_apply]
  congr 2
  apply groupCohomology.map_congr
  · refine MonoidHom.ext fun g => ?_
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    show g y = (AlgEquiv.restrictNormalHom M (AlgEquiv.restrictScalarsHom (fixedField H) g)) y
    rw [restrictNormalHom_self_apply]
    rfl
  · ext a
    rfl

theorem toBrRel_resRel [Algebra (fixedField H) (fixedField H')]
    [IsScalarTower (fixedField H) (fixedField H') M] (x : H2rel M H) :
    toBrRel M H' ((resRel M h).hom x) = brBaseChange (fixedField H) (fixedField H') (toBrRel M H x) := by
  have e := brBaseChange_relBrInfl (fixedField H) (fixedField H') M M (embFix M H) (embFix M H')
    ((relIso M H).hom.hom x)
  have e2 := congrArg (relBrInfl (fixedField H') M (embFix M H')) (relIso_resRel M h x)
  have key : toBrRel M H' ((resRel M h).hom x) =
      relBrInfl (fixedField H') M (embFix M H') ((relIso M H').hom.hom ((resRel M h).hom x)) := rfl
  have key2 : toBrRel M H x = relBrInfl (fixedField H) M (embFix M H) ((relIso M H).hom.hom x) := rfl
  rw [key, key2]
  exact e2.trans e.symm

theorem finrank_fixedField_fixedField [Algebra (fixedField H) (fixedField H')]
    [IsScalarTower (fixedField H) (fixedField H') M] :
    Module.finrank (fixedField H) (fixedField H') = H'.relIndex H := by
  have h1 := Module.finrank_mul_finrank (fixedField H) (fixedField H') M
  rw [finrank_fixedField_eq_card, finrank_fixedField_eq_card] at h1
  have h2 := H'.relIndex_mul_card H
  rw [inf_of_le_left h] at h2
  have hpos : 0 < Nat.card H' := Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem tcInvRel_resRel_aux [Algebra (fixedField H) (fixedField H')]
    [IsScalarTower (fixedField H) (fixedField H') M] [IsScalarTower K (fixedField H) (fixedField H')]
    (x : H2rel M H) :
    tcInvRel M H' ((resRel M h).hom x) = H'.relIndex H • tcInvRel M H x := by
  have : ValuativeExtension (fixedField H) (fixedField H') :=
    TauCeti.algebraicExtension_valuativeExtension_tower K (fixedField H) (fixedField H')
  have : FiniteDimensional (fixedField H) (fixedField H') :=
    FiniteDimensional.right K (fixedField H) (fixedField H')
  rw [tcInvRel_apply, toBrRel_resRel M h, Ch4.invMap_brBaseChange, finrank_fixedField_fixedField M h,
    map_nsmul, tcInvRel_apply]

/-- **(29) for $M^{H'}/M^H$**: $\mathrm{inv}_{M/M^{H'}} \circ \mathrm{Res} = (H : H')\,\mathrm{inv}_{M/M^H}$. -/
theorem tcInvRel_resRel (x : H2rel M H) :
    tcInvRel M H' ((resRel M h).hom x) = H'.relIndex H • tcInvRel M H x := by
  letI := fixAlg M h
  have : IsScalarTower (fixedField H) (fixedField H') M := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K (fixedField H) (fixedField H') := .of_algebraMap_eq fun _ => rfl
  exact tcInvRel_resRel_aux M h x

end ResRel

/-! ### Inflation from $M$ to $E \supseteq M$

The `IsScalarTower` hypotheses below are written with the `Algebra.toSMul` scalar actions made explicit:
for the concrete subfields `fixedField (H.comap (galRestrict hME))` of `E`, instance search elaborates the
plain `IsScalarTower` binder with a different (defeq but not reducibly so) `SMul` instance and then fails to
find the hypothesis. -/

section Infl

variable {E : IntermediateField K Ω} [FiniteDimensional K E] [IsGalois K E] [IsGalois K M] (hME : M ≤ E)
  (H : Subgroup Gal(M/K))

theorem inclusion_mem_fixedField (x : fixedField H) :
    IntermediateField.inclusion hME (x : M) ∈ fixedField (H.comap (galRestrict hME)) := by
  rw [mem_fixedField_iff]
  intro g hg
  apply Subtype.ext
  have h1 := galRestrict_apply hME g (x : M)
  have h2 : galRestrict hME g (x : M) = x := (mem_fixedField_iff H _).1 x.2 _ hg
  rw [h2] at h1
  exact h1.symm

/-- $M^H \to E^{H'}$, $H' = \{\tau : \tau|_M \in H\}$ (an isomorphism). -/
noncomputable def fixMap : fixedField H →ₐ[K] fixedField (H.comap (galRestrict hME)) :=
  ((IntermediateField.inclusion hME).comp (fixedField H).val).codRestrict
    (fixedField (H.comap (galRestrict hME))).toSubalgebra (inclusion_mem_fixedField M hME H)

/-- The algebra structures of the base change $(M/M^H) \to (E/E^{H'})$. -/
noncomputable abbrev fixAlgE : Algebra (fixedField H) (fixedField (H.comap (galRestrict hME))) :=
  (fixMap M hME H).toRingHom.toAlgebra

/-- $M^H \to E^{H'} \to E$. -/
noncomputable abbrev algFE : Algebra (fixedField H) E :=
  ((algebraMap (fixedField (H.comap (galRestrict hME))) E).comp
    (fixMap M hME H).toRingHom).toAlgebra

/-- $M \to E$, the inclusion. -/
noncomputable abbrev algME : Algebra M E := (IntermediateField.inclusion hME).toAlgebra

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem relIso_inflRel [Algebra (fixedField H) (fixedField (H.comap (galRestrict hME)))]
    [Algebra (fixedField H) E] [Algebra M E]
    [@IsScalarTower (fixedField H) (fixedField (H.comap (galRestrict hME))) E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower (fixedField H) M E Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (hM : ∀ m : M, algebraMap M E m = IntermediateField.inclusion hME m) (x : H2rel M H) :
    (relIso E (H.comap (galRestrict hME))).hom.hom ((inflRel hME H).hom x) =
      (groupCohomology.map ((AlgEquiv.restrictNormalHom M).comp
          (AlgEquiv.restrictScalarsHom (fixedField H)))
        (TauCeti.unitsBaseChangeHom (fixedField H) M (fixedField (H.comap (galRestrict hME))) E) 2).hom
        ((relIso M H).hom.hom x) := by
  rw [relIso, relIso]
  erw [groupCohomology.mapIso_hom, groupCohomology.mapIso_hom]
  rw [inflRel]
  erw [map_map_apply, map_map_apply]
  congr 2
  apply groupCohomology.map_congr
  · refine MonoidHom.ext fun g => ?_
    apply Subtype.ext
    apply AlgEquiv.ext
    intro y
    apply Subtype.ext
    have h1 := galRestrict_apply hME ((galFixEquiv E (H.comap (galRestrict hME))).symm g).1 y
    have h2 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalarsHom (fixedField H) g) M y
    have h3 := congrArg (fun z : E => (z : Ω)) h2
    simp only [hM] at h3
    exact h1.trans h3.symm
  · ext a
    refine Additive.toMul.injective (Units.ext ?_)
    exact (hM _).symm

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem toBrRel_inflRel_aux [Algebra (fixedField H) (fixedField (H.comap (galRestrict hME)))]
    [Algebra (fixedField H) E] [Algebra M E]
    [@IsScalarTower (fixedField H) (fixedField (H.comap (galRestrict hME))) E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower (fixedField H) M E Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (hM : ∀ m : M, algebraMap M E m = IntermediateField.inclusion hME m) (x : H2rel M H) :
    toBrRel E (H.comap (galRestrict hME)) ((inflRel hME H).hom x) =
      brBaseChange (fixedField H) (fixedField (H.comap (galRestrict hME))) (toBrRel M H x) := by
  have e := brBaseChange_relBrInfl (fixedField H) (fixedField (H.comap (galRestrict hME))) M E
    (embFix M H) (embFix E (H.comap (galRestrict hME))) ((relIso M H).hom.hom x)
  have e2 := congrArg (relBrInfl (fixedField (H.comap (galRestrict hME))) E
    (embFix E (H.comap (galRestrict hME)))) (relIso_inflRel M hME H hM x)
  have key : toBrRel E (H.comap (galRestrict hME)) ((inflRel hME H).hom x) =
      relBrInfl (fixedField (H.comap (galRestrict hME))) E (embFix E (H.comap (galRestrict hME)))
        ((relIso E (H.comap (galRestrict hME))).hom.hom ((inflRel hME H).hom x)) := rfl
  have key2 : toBrRel M H x = relBrInfl (fixedField H) M (embFix M H) ((relIso M H).hom.hom x) := rfl
  rw [key, key2]
  exact e2.trans e.symm

theorem finrank_fixedField_comap :
    Module.finrank K (fixedField (H.comap (galRestrict hME))) = Module.finrank K (fixedField H) := by
  rw [finrank_fixedField_eq_index, finrank_fixedField_eq_index]
  letI := algME M hME
  have : @IsScalarTower K M E Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun _ => rfl
  have hs : Function.Surjective (galRestrict hME) :=
    AlgEquiv.restrictNormalHom_surjective E
  exact Subgroup.index_comap_of_surjective H hs

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 4000000 in
theorem tcInvRel_inflRel_aux [Algebra (fixedField H) (fixedField (H.comap (galRestrict hME)))]
    [Algebra (fixedField H) E] [Algebra M E]
    [@IsScalarTower (fixedField H) (fixedField (H.comap (galRestrict hME))) E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower (fixedField H) M E Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    [@IsScalarTower K (fixedField H) (fixedField (H.comap (galRestrict hME)))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul]
    (hM : ∀ m : M, algebraMap M E m = IntermediateField.inclusion hME m) (x : H2rel M H) :
    tcInvRel E (H.comap (galRestrict hME)) ((inflRel hME H).hom x) = tcInvRel M H x := by
  have : ValuativeExtension (fixedField H) (fixedField (H.comap (galRestrict hME))) :=
    TauCeti.algebraicExtension_valuativeExtension_tower K (fixedField H)
      (fixedField (H.comap (galRestrict hME)))
  have : FiniteDimensional (fixedField H) (fixedField (H.comap (galRestrict hME))) :=
    FiniteDimensional.right K (fixedField H) (fixedField (H.comap (galRestrict hME)))
  have h1 := Module.finrank_mul_finrank K (fixedField H) (fixedField (H.comap (galRestrict hME)))
  rw [finrank_fixedField_comap M hME H] at h1
  have hpos : 0 < Module.finrank K (fixedField H) := Module.finrank_pos
  have hdeg : Module.finrank (fixedField H) (fixedField (H.comap (galRestrict hME))) = 1 := by
    have : Module.finrank K (fixedField H) * Module.finrank (fixedField H)
        (fixedField (H.comap (galRestrict hME))) = Module.finrank K (fixedField H) * 1 := by
      rw [h1, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  rw [tcInvRel_apply, toBrRel_inflRel_aux M hME H hM, Ch4.invMap_brBaseChange, hdeg, one_smul,
    ← tcInvRel_apply]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 4000000 in
/-- **Inflation preserves the invariant**: for $M \subseteq E$ and $H' = \{\tau : \tau|_M \in H\}$,
$\mathrm{inv}_{E/E^{H'}} \circ \mathrm{Inf} = \mathrm{inv}_{M/M^H}$. -/
theorem tcInvRel_inflRel (x : H2rel M H) :
    tcInvRel E (H.comap (galRestrict hME)) ((inflRel hME H).hom x) = tcInvRel M H x := by
  letI := fixAlgE M hME H
  letI := algFE M hME H
  letI := algME M hME
  have : @IsScalarTower (fixedField H) (fixedField (H.comap (galRestrict hME))) E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (fixedField H) M E Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower K (fixedField H) (fixedField (H.comap (galRestrict hME)))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun r => ((fixMap M hME H).commutes r).symm
  exact tcInvRel_inflRel_aux M hME H (fun _ => rfl) x

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 4000000 in
/-- **Inflation commutes with base change of Brauer classes** (with the algebra structure `fixAlgE`). -/
theorem toBrRel_inflRel (x : H2rel M H) :
    letI := fixAlgE M hME H
    toBrRel E (H.comap (galRestrict hME)) ((inflRel hME H).hom x) =
      brBaseChange (fixedField H) (fixedField (H.comap (galRestrict hME))) (toBrRel M H x) := by
  letI := fixAlgE M hME H
  letI := algFE M hME H
  letI := algME M hME
  have : @IsScalarTower (fixedField H) (fixedField (H.comap (galRestrict hME))) E
      Algebra.toSMul Algebra.toSMul Algebra.toSMul := .of_algebraMap_eq fun _ => rfl
  have : @IsScalarTower (fixedField H) M E Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    .of_algebraMap_eq fun _ => rfl
  exact toBrRel_inflRel_aux M hME H (fun _ => rfl) x

end Infl

end Local

end NumberFieldKB.MilneCFT.Ch3
