import Mathlib
import NumberFieldKB.MilneCFT.Ch2Prop42Aux3
import NumberFieldKB.MilneCFT.Ch2Profinite
import NumberFieldKB.TauCetiPort.RepresentationTheory.Homological.ContCohomology.Resolution.Basic
import NumberFieldKB.TauCetiPort.Algebra.Homology.ModuleCat.Basic

/-!
# Proposition 4.2, auxiliary file 4: classes of cocycles on both sides

Elementwise descriptions of continuous cohomology (classes of homogeneous cocycles) and of group
cohomology of the finite quotients (classes of inhomogeneous cocycles), and the map between them
induced by `theta`.
-/

open CategoryTheory _root_.TopRep groupCohomology

namespace NumberFieldKB.MilneCFT.Prop42

section Cts

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : TopRep ℤ G)

/-- Two homogeneous cocycles have the same class exactly when their difference is a coboundary
(in degree zero: exactly when they are equal). -/
theorem cochainClass_eq_iff (n : ℕ) {p : ℕ} (hp : (ComplexShape.up ℕ).prev n = p)
    {a b : (homogeneousCochains A).X n}
    (ha : ((homogeneousCochains A).d n (n + 1)).hom a = 0)
    (hb : ((homogeneousCochains A).d n (n + 1)).hom b = 0) :
    A.cochainClass n a ha = A.cochainClass n b hb ↔
      ∃ c : (homogeneousCochains A).X p, a - b = ((homogeneousCochains A).d p n).hom c := by
  rw [cochainClass_def, cochainClass_def, ← sub_eq_zero, ← map_sub,
    (homogeneousCochains A).homologyπ_eq_zero_iff n hp]
  refine exists_congr fun c => ?_
  rw [← (homogeneousCochains A).iCycles_injective n |>.eq_iff, map_sub,
    HomologicalComplex.iCycles_cyclesMkOfEq, HomologicalComplex.iCycles_cyclesMkOfEq,
    HomologicalComplex.iCycles_toCycles_apply, eq_comm]

end Cts

section Quot

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (A : TopRep ℤ G)
  (U : OpenNormalSubgroup G)

theorem d_iCocycles (r : ℕ) (z : ↑(cocycles (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G)) r)) :
    (((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom
      (((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).iCycles r).hom z)) = 0 := by
  have := (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).iCycles_d r (r + 1)
  have h2 := congrArg (fun φ => φ.hom z) this
  simpa using h2

/-- The class in continuous cohomology of the homogeneous cocycle attached to an inhomogeneous
cocycle of the quotient. -/
noncomputable def Cl (r : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X r)
    (hf : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom f = 0) : continuousCohomology r A :=
  A.cochainClass r (theta A U r f) (by rw [← theta_d, hf, map_zero])

theorem Cl_add (r : ℕ)
    (f f' : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X r)
    (hf : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom f = 0)
    (hf' : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom f' = 0) :
    Cl A U r (f + f') (by rw [map_add, hf, hf', add_zero]) = Cl A U r f hf + Cl A U r f' hf' := by
  unfold Cl
  rw [← cochainClass_add]
  congr 1
  exact map_add _ _ _

theorem Cl_zero (r : ℕ) : Cl A U r 0 (map_zero _) = 0 := by
  unfold Cl
  rw [← cochainClass_zero (X := A) (n := r)]
  congr 1
  exact map_zero _

theorem theta_d' (r : ℕ) {p : ℕ} (hp : (ComplexShape.up ℕ).prev r = p)
    (c : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X p) :
    theta A U r (((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d p r).hom c) =
      ((homogeneousCochains A).d p r).hom (theta A U p c) := by
  cases r with
  | zero =>
    have hp0 : p = 0 := by
      rw [← hp]; exact CochainComplex.prev_nat_zero
    subst hp0
    rw [HomologicalComplex.shape _ 0 0 (by simp), HomologicalComplex.shape _ 0 0 (by simp)]
    simp
  | succ j =>
    have hp0 : p = j := by
      rw [← hp]; exact CochainComplex.prev_nat_succ j
    subst hp0
    exact theta_d A U p c

theorem Cl_coboundary (r : ℕ) {p : ℕ} (hp : (ComplexShape.up ℕ).prev r = p)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X r)
    (hf : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom f = 0)
    (c : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X p)
    (hc : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d p r).hom c = f) : Cl A U r f hf = 0 := by
  unfold Cl
  rw [← cochainClass_zero (X := A) (n := r)]
  rw [cochainClass_eq_iff A r hp]
  exact ⟨theta A U p c, by rw [sub_zero, ← theta_d' A U r hp, hc]⟩

theorem exists_of_Cl_eq_zero (r : ℕ) {p : ℕ} (hp : (ComplexShape.up ℕ).prev r = p)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X r)
    (hf : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom f = 0) (h : Cl A U r f hf = 0) :
    ∃ c : (homogeneousCochains A).X p,
      theta A U r f = ((homogeneousCochains A).d p r).hom c := by
  unfold Cl at h
  rw [← cochainClass_zero (X := A) (n := r), cochainClass_eq_iff A r hp] at h
  simpa using h

/-- The class map from cocycles of the quotient to continuous cohomology. -/
noncomputable def Zθ (r : ℕ) : ↑(cocycles (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G)) r) →+ ↑(continuousCohomology r A) where
  toFun z := Cl A U r (((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).iCycles r).hom z) (d_iCocycles A U r z)
  map_zero' := by
    have := Cl_zero A U r
    convert this using 2
    exact map_zero _
  map_add' z z' := by
    rw [← Cl_add]
    congr 1
    exact map_add _ _ _

theorem Zθ_ker_le (r : ℕ) (z : ↑(cocycles (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G)) r))
    (hz : (groupCohomology.π (Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G)) r).hom z
      = 0) : Zθ A U r z = 0 := by
  obtain ⟨y, hy⟩ := ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).moduleCat_homologyπ_eq_zero_iff (n := r) (m := (ComplexShape.up ℕ).prev r)
      rfl z).1 hz
  show Cl A U r _ (d_iCocycles A U r z) = 0
  refine Cl_coboundary A U r rfl _ (d_iCocycles A U r z) y ?_
  rw [← hy, ← ModuleCat.comp_apply, HomologicalComplex.toCycles_i]

/-- The map on group cohomology of the quotient, to continuous cohomology, induced by `theta`. -/
noncomputable def θH (r : ℕ) :
    ↑(groupCohomology (Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G)) r) →+
      ↑(continuousCohomology r A) :=
  let N := Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G)
  have hs : Function.Surjective (groupCohomology.π N r).hom.toAddMonoidHom :=
    (inhomogeneousCochains N).moduleCat_homologyπ_surjective r
  AddMonoidHom.liftOfRightInverse (groupCohomology.π N r).hom.toAddMonoidHom
    (Function.surjInv hs) (Function.rightInverse_surjInv hs) ⟨Zθ A U r, fun z hz => Zθ_ker_le A U r z hz⟩

theorem θH_π (r : ℕ) (z : ↑(cocycles (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G)) r)) :
    θH A U r ((groupCohomology.π (Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G)) r).hom z)
      = Zθ A U r z := by
  unfold θH
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ z

theorem Cl_infl {V : OpenNormalSubgroup G} (h : V ≤ U) (r : ℕ)
    (f : (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).X r)
    (hf : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).d r (r + 1)).hom f = 0)
    (hf' : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (V : Subgroup G))).d r (r + 1)).hom
      (((cochainsMap (QuotientGroup.map (V : Subgroup G) (U : Subgroup G)
        (MonoidHom.id G) h) (inclMorGen (TopRep.toRep A) h)).f r).hom f) = 0) :
    Cl A V r (((cochainsMap (QuotientGroup.map (V : Subgroup G) (U : Subgroup G)
        (MonoidHom.id G) h) (inclMorGen (TopRep.toRep A) h)).f r).hom f) hf' = Cl A U r f hf := by
  unfold Cl
  congr 1

theorem θH_infl {V : OpenNormalSubgroup G} (h : V ≤ U) (r : ℕ)
    (x : ↑(groupCohomology (Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G)) r)) :
    θH A V r ((inflStep (TopRep.toRep A) h r).hom x) = θH A U r x := by
  induction x using groupCohomology_induction_on with
  | h z =>
    unfold inflStep
    rw [← ModuleCat.comp_apply, π_map]
    rw [ModuleCat.comp_apply, θH_π, θH_π]
    have key : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
        (V : Subgroup G))).iCycles r).hom
        ((cocyclesMap (QuotientGroup.map (V : Subgroup G) (U : Subgroup G) (MonoidHom.id G) h)
          (inclMorGen (TopRep.toRep A) h) r).hom z) =
        ((cochainsMap (QuotientGroup.map (V : Subgroup G) (U : Subgroup G)
        (MonoidHom.id G) h) (inclMorGen (TopRep.toRep A) h)).f r).hom
          (((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
            (U : Subgroup G))).iCycles r).hom z) := by
      rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]
    show Cl A V r _ (d_iCocycles A V r _) = Cl A U r _ (d_iCocycles A U r z)
    convert Cl_infl A U h r _ (d_iCocycles A U r z) (by rw [← key]; exact d_iCocycles A V r _)
      using 2

end Quot

end NumberFieldKB.MilneCFT.Prop42
