import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import NumberFieldKB.MilneCFT.Ch2Profinite
import NumberFieldKB.MilneCFT.Ch2Prop42Aux4

/-!
# Milne, *Class Field Theory*, Chapter II, Proposition 4.2: proof

For a profinite group `G` and a discrete `G`-module `M`, continuous cohomology in every degree is
the direct limit over the open normal subgroups `U` of the cohomology groups `H^r(G/U, M^U)`.

Route: an inhomogeneous cochain of `G/U` with values in `M^U` gives a homogeneous continuous cochain
of `G` (file `Ch2Prop42Aux3.lean`), commuting with the differentials and with inflation; every
homogeneous continuous cochain of a compact group with discrete coefficients arises in this way
for some `U` (file `Ch2Prop42Aux1.lean` for the finiteness argument).  Passing to cohomology classes
(file `Ch2Prop42Aux4.lean`) gives a map out of the direct limit, which is surjective because every
class has a cocycle representative and injective because a coboundary relation also comes from some
`U`.
-/

open CategoryTheory _root_.TopRep groupCohomology

namespace NumberFieldKB.MilneCFT.Prop42

/-- A compatible family of additive maps out of a directed system of abelian groups induces a
bijection out of the direct limit as soon as it is surjective and every element killed by one of the
maps is killed by a transition map. -/
theorem directLimit_lift_bijective {ι : Type} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [DecidableEq ι] {G : ι → Type} [∀ i, AddCommGroup (G i)] (f : ∀ i j, i ≤ j → G i →+ G j)
    [DirectedSystem G fun i j h => f i j h] {P : Type} [AddCommGroup P] (g : ∀ i, G i →+ P)
    (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
    (hsurj : ∀ y : P, ∃ i x, g i x = y)
    (hinj : ∀ i x, g i x = 0 → ∃ j, ∃ hij : i ≤ j, f i j hij x = 0) :
    Function.Bijective (AddCommGroup.DirectLimit.lift G f P g Hg) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using AddCommGroup.DirectLimit.induction_on with
    | ih i x =>
      rw [AddCommGroup.DirectLimit.lift_of] at hz
      obtain ⟨j, hij, hj⟩ := hinj i x hz
      rw [← AddCommGroup.DirectLimit.of_f hij, hj, map_zero]
  · intro y
    obtain ⟨i, x, rfl⟩ := hsurj y
    exact ⟨AddCommGroup.DirectLimit.of G f i x, AddCommGroup.DirectLimit.lift_of _ _ _ _ _⟩

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (A : TopRep ℤ G) [DiscreteTopology A.V]

/-- Every continuous cohomology class comes from the cohomology of some finite quotient. -/
theorem exists_preimage (r : ℕ) (y : ↑(continuousCohomology r A)) :
    ∃ (U : OpenNormalSubgroup G) (x : ↑(groupCohomology (Rep.quotientToInvariants
      (TopRep.toRep A) (U : Subgroup G)) r)), θH A U r x = y := by
  obtain ⟨a, ha, rfl⟩ := TopRep.exists_cochainClass_eq (X := A) y
  obtain ⟨U, f, hf⟩ := theta_surjective A r a
  have hdf : (inhomogeneousCochains.d (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G)) r).hom f = 0 := by
    rw [← inhomogeneousCochains.d_def]
    apply theta_injective A U (r + 1)
    rw [theta_d, hf, ha, map_zero]
  refine ⟨U, (groupCohomology.π _ r).hom (groupCohomology.cocyclesMk f hdf), ?_⟩
  rw [θH_π]
  show Cl A U r _ (d_iCocycles A U r _) = _
  have h1 : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      (U : Subgroup G))).iCycles r).hom (groupCohomology.cocyclesMk f hdf) = f :=
    groupCohomology.iCocycles_mk f hdf
  unfold Cl
  subst hf
  congr 1
  rw [h1]

/-- A class of a finite quotient with zero image in continuous cohomology dies in a smaller
quotient. -/
theorem exists_smaller_zero (r : ℕ) (U : OpenNormalSubgroup G)
    (x : ↑(groupCohomology (Rep.quotientToInvariants (TopRep.toRep A) (U : Subgroup G)) r))
    (hx : θH A U r x = 0) :
    ∃ (V : OpenNormalSubgroup G) (h : V ≤ U), (inflStep (TopRep.toRep A) h r).hom x = 0 := by
  induction x using groupCohomology_induction_on with
  | h z =>
  rw [θH_π] at hx
  have hx' : Cl A U r _ (d_iCocycles A U r z) = 0 := hx
  obtain ⟨c, hc⟩ := exists_of_Cl_eq_zero A U r rfl _ (d_iCocycles A U r z) hx'
  obtain ⟨V, c', hc'⟩ := theta_surjective A _ c
  refine ⟨U ⊓ V, inf_le_left, ?_⟩
  set f := ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
    (U : Subgroup G))).iCycles r).hom z with hfdef
  set fW := ((cochainsMap (QuotientGroup.map ((U ⊓ V : OpenNormalSubgroup G) : Subgroup G)
    (U : Subgroup G) (MonoidHom.id G) (inf_le_left : U ⊓ V ≤ U))
    (inclMorGen (TopRep.toRep A) (inf_le_left : U ⊓ V ≤ U))).f r).hom f with hfW
  set cW := ((cochainsMap (QuotientGroup.map ((U ⊓ V : OpenNormalSubgroup G) : Subgroup G)
    (V : Subgroup G) (MonoidHom.id G) (inf_le_right : U ⊓ V ≤ V))
    (inclMorGen (TopRep.toRep A) (inf_le_right : U ⊓ V ≤ V))).f _).hom c' with hcW
  have h1 : theta A (U ⊓ V) r fW = theta A U r f := theta_infl A U _ r f
  have h2 : theta A (U ⊓ V) _ cW = c := by
    rw [hcW, theta_infl A V _ _ c', hc']
  have h3 : ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
      ((U ⊓ V : OpenNormalSubgroup G) : Subgroup G))).d ((ComplexShape.up ℕ).prev r) r).hom cW
      = fW := by
    apply theta_injective A (U ⊓ V) r
    rw [theta_d' A (U ⊓ V) r rfl, h2, h1, hc]
  unfold inflStep
  rw [← ModuleCat.comp_apply, π_map]
  rw [ModuleCat.comp_apply]
  refine ((inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
    ((U ⊓ V : OpenNormalSubgroup G) : Subgroup G))).moduleCat_homologyπ_eq_zero_iff (n := r)
    (m := (ComplexShape.up ℕ).prev r) rfl _).2 ⟨cW, ?_⟩
  apply (inhomogeneousCochains (Rep.quotientToInvariants (TopRep.toRep A)
    ((U ⊓ V : OpenNormalSubgroup G) : Subgroup G))).moduleCat_iCycles_injective r
  rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_i, h3, ← ModuleCat.comp_apply,
    HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply]

end Main

end NumberFieldKB.MilneCFT.Prop42

namespace NumberFieldKB.MilneCFT

open Classical in
/-- **Proposition 4.2** (Milne, *Class Field Theory*, Chapter II, p. 88), proved.  For a profinite
group `G` and a discrete `G`-module `M`, continuous cohomology (Mathlib's `continuousCohomology`,
the homology of the curried homogeneous continuous cochains) in every degree `r` is isomorphic to
the direct limit, over the open normal subgroups `U` of `G` and along the inflation maps, of the
cohomology groups `H^r(G/U, M^U)`. -/
@[kb "milne2020cft" "v4.03, Ch. II, Prop. 4.2, p. 88"]
theorem prop4_2 : Prop4_2 := by
  refine ⟨fun G _ _ _ _ _ A _ _ r => ?_⟩
  classical
  have : Nonempty (OpenNormalSubgroup G)ᵒᵈ :=
    ⟨OrderDual.toDual ⟨⟨⊤, isOpen_univ⟩, Subgroup.normal_top⟩⟩
  have hds : DirectedSystem (fun U : (OpenNormalSubgroup G)ᵒᵈ => ↑(groupCohomology
      (Rep.quotientToInvariants (TopRep.toRep A)
        ((OrderDual.ofDual U : OpenNormalSubgroup G) : Subgroup G)) r))
      (fun i j h => (inflStep (TopRep.toRep A) h r).hom.toAddMonoidHom) :=
    inflStep_directedSystem (TopRep.toRep A) r
  have hbij := Prop42.directLimit_lift_bijective
    (G := fun U : (OpenNormalSubgroup G)ᵒᵈ => ↑(groupCohomology (Rep.quotientToInvariants
      (TopRep.toRep A) ((OrderDual.ofDual U : OpenNormalSubgroup G) : Subgroup G)) r))
    (fun _ _ h => (inflStep (TopRep.toRep A) h r).hom.toAddMonoidHom)
    (P := ↑(continuousCohomology r A))
    (fun U => Prop42.θH A (OrderDual.ofDual U) r)
    (fun i j hij x => Prop42.θH_infl A (OrderDual.ofDual i) hij r x)
    (fun y => by
      obtain ⟨U, x, hx⟩ := Prop42.exists_preimage A r y
      exact ⟨OrderDual.toDual U, x, hx⟩)
    (fun i x hx => by
      obtain ⟨V, h, hV⟩ := Prop42.exists_smaller_zero A r (OrderDual.ofDual i) x hx
      exact ⟨OrderDual.toDual V, h, hV⟩)
  let _ : AddCommGroup (AddCommGroup.DirectLimit (fun U : (OpenNormalSubgroup G)ᵒᵈ =>
      ↑(groupCohomology (Rep.quotientToInvariants (TopRep.toRep A)
        ((OrderDual.ofDual U : OpenNormalSubgroup G) : Subgroup G)) r))
      (fun _ _ h => (inflStep (TopRep.toRep A) h r).hom.toAddMonoidHom)) :=
    AddCommGroup.DirectLimit.addCommGroup _ _
  exact ⟨(AddEquiv.ofBijective _ hbij).symm⟩

end NumberFieldKB.MilneCFT
