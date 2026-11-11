import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Unramified
import NumberFieldKB.MilneCFT.Ch2Profinite

/-!
# Milne, *Class Field Theory*, Chapter III §1: Corollary 1.6 (infinite unramified extensions)

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.
Locators give Milne's printed page numbers (printed page = pdf page − 9).

$L$ is an unramified Galois extension of $K$ inside the separable closure $\Omega$, possibly infinite: every finite
subextension is unramified (Chapter I's `IsUnramifiedExt`). $G = \operatorname{Gal}(L/K)$ carries the Krull
topology (Mathlib's `krullTopology`; compact and totally disconnected), and $U_L$ is a topological $G$-module with
the discrete topology (`unitsTopRep`). Its continuous cohomology is Mathlib's `continuousCohomology`.

Milne's proof: $H^r(G, U_L) = \varinjlim_{K'} H^r(\operatorname{Gal}(K'/K), U_{K'})$ by Chapter II, Proposition 4.2
(`Prop4_2`, a named statement), and each term vanishes by Proposition 1.1 (`prop_1_1`). Here the terms of the
limit are $H^r(G/H, U_L^H)$ for the open normal subgroups $H$; they are identified with
$H^r(\operatorname{Gal}(K'/K), U_{K'})$ for $K' = L^H$ (`groupCohomology.mapIso`, with the infinite Galois
correspondence `InfiniteGalois.normalAutEquivQuotient`).
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The underlying additive group of $U_L$ (the carrier of `unitsRep L`), to be given the discrete topology. -/
def DiscUnits (L : IntermediateField K Ω) : Type := Additive (unitsL L)

namespace DiscUnits

variable (L : IntermediateField K Ω)

instance : AddCommGroup (DiscUnits L) := inferInstanceAs (AddCommGroup (Additive (unitsL L)))

instance : TopologicalSpace (DiscUnits L) := ⊥

instance : DiscreteTopology (DiscUnits L) := ⟨rfl⟩

instance : IsTopologicalAddGroup (DiscUnits L) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

instance : ContinuousSMul ℤ (DiscUnits L) where
  continuous_smul := continuous_of_discreteTopology

end DiscUnits

/-- The action of $\operatorname{Gal}(L/K)$ on $U_L$ (that of `unitsRep L`) as a continuous representation for the
discrete topology on $U_L$. -/
noncomputable def unitsContRep (L : IntermediateField K Ω) :
    ContRepresentation ℤ Gal(L/K) (DiscUnits L) :=
  .ofMonoidHom
    { toFun := fun σ => ⟨(unitsRep L).ρ σ, continuous_of_discreteTopology⟩
      map_one' := by ext x; simp; rfl
      map_mul' := fun σ τ => by ext x; simp; rfl }

/-- **$U_L$ as a discrete $\operatorname{Gal}(L/K)$-module** (Milne, Chapter III, §1, p. 99): the units of $L$ with
the discrete topology, as a topological representation of the Galois group with its Krull topology. -/
@[kb "milne2020cft" "v4.03, Ch. III, §1, the discrete G-module U_L for L/K infinite, p. 99"]
noncomputable def unitsTopRep (L : IntermediateField K Ω) : TopRep ℤ Gal(L/K) :=
  TopRep.of (unitsContRep L)

/-- $U_L$ is a discrete $\operatorname{Gal}(L/K)$-module: the stabilizer of a unit $u$ contains the open subgroup
fixing $K(u)$. -/
theorem isDiscreteModule_unitsTopRep (L : IntermediateField K Ω) [IsGalois K L] :
    IsDiscreteModule (TopRep.toRep (unitsTopRep L)) := by
  intro u
  have h := stabilizer_isOpen_of_isIntegral (K := K) (L := L) (((Additive.toMul u : unitsL L) : Lˣ) : L)
  change IsOpen (stabSubgroup (TopRep.toRep (unitsTopRep L)) u : Set Gal(L/K))
  refine Subgroup.isOpen_mono
    (H₁ := MulAction.stabilizer Gal(L/K) (((Additive.toMul u : unitsL L) : Lˣ) : L)) ?_ h
  intro g hg
  show (unitsRep L).ρ g u = u
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact hg

section Descent

variable (L : IntermediateField K Ω) (E : IntermediateField K L)

/-- The inclusion of the lift of `E` into `L`. -/
noncomputable def liftIncl : (IntermediateField.lift E) →ₐ[K] L :=
  IntermediateField.inclusion (IntermediateField.lift_le E)

theorem liftIncl_injective : Function.Injective (liftIncl L E) :=
  (IntermediateField.inclusion (IntermediateField.lift_le E)).injective

@[simp] theorem liftIncl_val (x : (IntermediateField.lift E)) : ((liftIncl L E x : L) : Ω) = (x : Ω) := rfl

theorem liftIncl_mem_integers_iff (x : (IntermediateField.lift E)) :
    liftIncl L E x ∈ integers L ↔ x ∈ integers (IntermediateField.lift E) := by
  simp only [integers, mem_integralClosure_iff]
  exact isIntegral_algHom_iff ((liftIncl L E).restrictScalars 𝒪[K]) (liftIncl_injective L E)

/-- The inclusion of unit groups `U_{lift E} → U_L`. -/
noncomputable def liftUnitsHom : unitsL (IntermediateField.lift E) →* unitsL L where
  toFun u := ⟨Units.map (liftIncl L E).toMonoidHom (u : (IntermediateField.lift E)ˣ), by
    obtain ⟨h1, h2⟩ := u.2
    refine ⟨?_, ?_⟩
    · exact (liftIncl_mem_integers_iff L E _).2 h1
    · exact (liftIncl_mem_integers_iff L E _).2 h2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

@[simp] theorem liftUnitsHom_coe (u : unitsL (IntermediateField.lift E)) :
    ((liftUnitsHom L E u : unitsL L) : Lˣ) = Units.map (liftIncl L E).toMonoidHom (u : _) := rfl

theorem liftIncl_mem (x : IntermediateField.lift E) : liftIncl L E x ∈ E :=
  (IntermediateField.mem_lift (liftIncl L E x)).1 x.2

theorem liftUnitsHom_injective : Function.Injective (liftUnitsHom L E) := by
  intro a b h
  have h' : Units.map (liftIncl L E).toMonoidHom (a : _) = Units.map (liftIncl L E).toMonoidHom (b : _) :=
    congrArg (fun z : unitsL L => (z : Lˣ)) h
  apply Subtype.ext
  exact Units.map_injective (liftIncl_injective L E) h'

theorem liftUnitsHom_smul (g : Gal(L/K)) (σ : Gal(IntermediateField.lift E/K))
    (hσ : ∀ x : IntermediateField.lift E, ((σ x : IntermediateField.lift E) : Ω) = ((g (liftIncl L E x) : L) : Ω))
    (u : unitsL (IntermediateField.lift E)) :
    g • liftUnitsHom L E u = liftUnitsHom L E (σ • u) := by
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact (hσ _).symm

theorem liftUnitsHom_smul_fixed (H : Subgroup Gal(L/K)) (g : Gal(L/K)) (hg : g ∈ H)
    (u : unitsL (IntermediateField.lift (IntermediateField.fixedField H))) :
    g • liftUnitsHom L _ u = liftUnitsHom L _ u := by
  apply Subtype.ext
  apply Units.ext
  have h1 : (liftIncl L (IntermediateField.fixedField H)
      (u : (IntermediateField.lift (IntermediateField.fixedField H))ˣ)) ∈ IntermediateField.fixedField H :=
    liftIncl_mem L _ _
  have h2 := (IntermediateField.mem_fixedField_iff H _).1 h1 g hg
  exact h2

theorem liftUnitsHom_surj (H : Subgroup Gal(L/K)) (w : unitsL L) (hw : ∀ g ∈ H, g • w = w) :
    ∃ u : unitsL (IntermediateField.lift (IntermediateField.fixedField H)), liftUnitsHom L _ u = w := by
  have hx : ((w : Lˣ) : L) ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    exact congrArg (fun z : unitsL L => (((z : Lˣ)) : L)) (hw g hg)
  have hx' : (((w : Lˣ)⁻¹ : Lˣ) : L) ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have := congrArg (fun z : unitsL L => (((z⁻¹ : unitsL L) : Lˣ) : L)) (hw g hg)
    exact this
  let y : IntermediateField.lift (IntermediateField.fixedField H) :=
    ⟨(((w : Lˣ) : L) : Ω), (IntermediateField.mem_lift ((w : Lˣ) : L)).2 hx⟩
  let y' : IntermediateField.lift (IntermediateField.fixedField H) :=
    ⟨((((w : Lˣ)⁻¹ : Lˣ) : L) : Ω), (IntermediateField.mem_lift (((w : Lˣ)⁻¹ : Lˣ) : L)).2 hx'⟩
  have hy : liftIncl L _ y = ((w : Lˣ) : L) := Subtype.ext rfl
  have hy' : liftIncl L _ y' = (((w : Lˣ)⁻¹ : Lˣ) : L) := Subtype.ext rfl
  let u : (IntermediateField.lift (IntermediateField.fixedField H))ˣ :=
    ⟨y, y', liftIncl_injective L _ (by rw [map_mul, hy, hy', map_one]; simp),
      liftIncl_injective L _ (by rw [map_mul, hy, hy', map_one]; simp)⟩
  refine ⟨⟨u, ?_, ?_⟩, ?_⟩
  · exact (liftIncl_mem_integers_iff L _ _).1 (by change liftIncl L _ y ∈ _; rw [hy]; exact w.2.1)
  · exact (liftIncl_mem_integers_iff L _ _).1 (by change liftIncl L _ y' ∈ _; rw [hy']; exact w.2.2)
  · apply Subtype.ext
    apply Units.ext
    exact hy

end Descent

/-- For an open normal subgroup $H$ of $\operatorname{Gal}(L/K)$, $L$ unramified over $K$, and $r > 0$:
$H^r(G/H, U_L^H) = 0$ (the fixed field $K' = L^H$ is finite Galois and unramified over $K$, $G/H \simeq
\operatorname{Gal}(K'/K)$, $U_L^H = U_{K'}$, and Proposition 1.1 applies). -/
theorem isZero_groupCohomology_quotientToInvariants (h26 : UnitPrimeDecomposition K Ω)
    (hcyc : UnramifiedCyclic K Ω) (L : IntermediateField K Ω) [IsGalois K L]
    (hL : ∀ F : IntermediateField K Ω, F ≤ L → FiniteDimensional K F → IsUnramifiedExt F)
    (H : OpenNormalSubgroup Gal(L/K)) (r : ℕ) (hr : 0 < r) :
    IsZero (groupCohomology (quotientToInvariants (TopRep.toRep (unitsTopRep L)) (H : Subgroup Gal(L/K))) r) := by
  classical
  have hcl : IsClosed ((H : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
    Subgroup.isClosed_of_isOpen _ H.isOpen
  let Hc : ClosedSubgroup Gal(L/K) := ⟨(H : Subgroup Gal(L/K)), hcl⟩
  let E : IntermediateField K L := IntermediateField.fixedField (H : Subgroup Gal(L/K))
  have hfix : E.fixingSubgroup = (H : Subgroup Gal(L/K)) := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hfd : FiniteDimensional K E := by
    rw [← InfiniteGalois.isOpen_iff_finite]
    rw [hfix]
    exact H.isOpen
  have hgal : IsGalois K E := by
    rw [← InfiniteGalois.normal_iff_isGalois, hfix]
    infer_instance
  let F : IntermediateField K Ω := IntermediateField.lift E
  have : FiniteDimensional K F :=
    LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv E).toLinearEquiv
  have : IsGalois K F := IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv E)
  have hF : IsUnramifiedExt F := hL F (IntermediateField.lift_le E) inferInstance
  let M := TopRep.toRep (unitsTopRep L)
  let e : (Gal(L/K) ⧸ (H : Subgroup Gal(L/K))) ≃* Gal(F/K) :=
    (InfiniteGalois.normalAutEquivQuotient Hc).trans (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv E))
  let f₀' : Additive (unitsL F) →+ Additive (unitsL L) := MonoidHom.toAdditive (liftUnitsHom L E)
  let f₀ : Additive (unitsL F) →ₗ[ℤ] M.V := AddMonoidHom.toIntLinearMap f₀'
  have hf₀ : ∀ c, f₀ c ∈ Representation.invariants (M.ρ.comp (H : Subgroup Gal(L/K)).subtype) := by
    intro c g
    exact congrArg Additive.ofMul (liftUnitsHom_smul_fixed L (H : Subgroup Gal(L/K)) g g.2 (Additive.toMul c))
  let f₁ : Additive (unitsL F) →ₗ[ℤ] Representation.invariants (M.ρ.comp (H : Subgroup Gal(L/K)).subtype) :=
    f₀.codRestrict _ hf₀
  have hbij : Function.Bijective f₁ := by
    constructor
    · intro a b hab
      have : f₀ a = f₀ b := congrArg Subtype.val hab
      have h' : liftUnitsHom L E (Additive.toMul a) = liftUnitsHom L E (Additive.toMul b) :=
        Additive.ofMul.injective this
      exact Additive.toMul.injective (liftUnitsHom_injective L E h')
    · rintro ⟨v, hv⟩
      obtain ⟨u, hu⟩ := liftUnitsHom_surj L (H : Subgroup Gal(L/K)) (Additive.toMul v)
        (fun g hg => Additive.ofMul.injective (hv ⟨g, hg⟩))
      exact ⟨Additive.ofMul u, Subtype.ext (congrArg Additive.ofMul hu)⟩
  let φ := LinearEquiv.ofBijective f₁ hbij
  have : NeZero r := ⟨hr.ne'⟩
  have hcoh : IsZero (groupCohomology (unitsRep F) r) :=
    (prop_1_1 h26 hcyc F hF (r : ℤ)).of_iso
      ((TateCohomology.isoGroupCohomology (R := ℤ) (G := Gal(F/K)) r).app _).symm
  refine hcoh.of_iso (groupCohomology.mapIso e φ.symm ?_ r)
  intro g
  induction g using QuotientGroup.induction_on with
  | H g =>
  apply LinearMap.ext
  intro v
  obtain ⟨u, rfl⟩ := φ.surjective v
  apply φ.injective
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  erw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  change M.ρ g (f₀ u) = f₀ ((unitsRep F).ρ (e g) u)
  refine congrArg Additive.ofMul (liftUnitsHom_smul L E g (e g) ?_ (Additive.toMul u))
  intro x
  have h := AlgEquiv.restrictNormalHom_apply E g ((IntermediateField.liftAlgEquiv E).symm x)
  exact congrArg (fun z : L => (z : Ω)) h

/-- **Corollary 1.6** (p. 99). Let $L/K$ be an unramified extension (possibly infinite) with Galois group $G$.
Then $H^r(G, U_L) = 0$ for $r > 0$ (continuous cochains, $G$ with the Krull topology, $U_L$ discrete).
Proved from Proposition 1.1 and Chapter II's Proposition 4.2 (named statement), following Milne's proof.

Hypotheses as stated: "$L/K$ unramified" is that every finite subextension $F \subseteq L$ is unramified
(`IsUnramifiedExt`); "with Galois group $G$" is `IsGalois K L` (true for unramified extensions, which Milne takes for
granted). Milne assumes $L/K$ infinite; the statement and proof hold for finite $L$ as well, so that hypothesis is
omitted. -/
@[kb "milne2020cft" "v4.03, Ch. III, Cor. 1.6, p. 99"]
theorem cor_1_6 (h42 : Prop4_2) (h26 : UnitPrimeDecomposition K Ω)
    (hcyc : UnramifiedCyclic K Ω) (L : IntermediateField K Ω) [IsGalois K L]
    (hL : ∀ F : IntermediateField K Ω, F ≤ L → FiniteDimensional K F → IsUnramifiedExt F)
    (r : ℕ) (hr : 0 < r) :
    Subsingleton (continuousCohomology r (unitsTopRep L)) := by
  classical
  have : DiscreteTopology (unitsTopRep L) := inferInstanceAs (DiscreteTopology (DiscUnits L))
  obtain ⟨e⟩ := h42.iso Gal(L/K) (unitsTopRep L) (isDiscreteModule_unitsTopRep L) r
  have : Nonempty (OpenNormalSubgroup Gal(L/K))ᵒᵈ :=
    ⟨OrderDual.toDual ⟨⟨⊤, isOpen_univ⟩, Subgroup.normal_top⟩⟩
  have : Subsingleton (inflLimit (TopRep.toRep (unitsTopRep L)) r) := by
    refine ⟨fun a b => ?_⟩
    have key : ∀ z : inflLimit (TopRep.toRep (unitsTopRep L)) r, z = 0 := by
      intro z
      refine AddCommGroup.DirectLimit.induction_on z (fun i y => ?_)
      have : y = 0 := by
        have hz := isZero_groupCohomology_quotientToInvariants h26 hcyc L hL
          (OrderDual.ofDual i) r hr
        have := (ModuleCat.isZero_iff_subsingleton.mp hz)
        exact Subsingleton.elim _ _
      rw [this]
      let ofI : (groupCohomology (quotientToInvariants (TopRep.toRep (unitsTopRep L))
          ((OrderDual.ofDual i : OpenNormalSubgroup Gal(L/K)) : Subgroup Gal(L/K))) r) →+
          inflLimit (TopRep.toRep (unitsTopRep L)) r :=
        AddCommGroup.DirectLimit.of
          (fun U : (OpenNormalSubgroup Gal(L/K))ᵒᵈ => groupCohomology (quotientToInvariants
            (TopRep.toRep (unitsTopRep L)) ((OrderDual.ofDual U : OpenNormalSubgroup Gal(L/K)) : Subgroup Gal(L/K))) r)
          (fun _ _ h => (inflStep (TopRep.toRep (unitsTopRep L)) h r).hom.toAddMonoidHom) i
      exact ofI.map_zero
    rw [key a, key b]
  exact e.injective.subsingleton

end NumberFieldKB.MilneCFT.Ch3
