import NumberFieldKB.MilneCFT.Ch3Artin
import NumberFieldKB.MilneCFT.LocalCFT.UniverseTransport
import NumberFieldKB.MilneCFT.Ch8.NormLimitationFormation
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.Restriction
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Local.ClassFormation
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.LocalExistence.NormSubgroup
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter III, Theorem 3.5 (norm limitation), proved

For a finite extension $L$ of a nonarchimedean local field $K$ (not necessarily Galois) with $E$ the largest abelian
subextension, $\mathrm{Nm}_{L/K}(L^\times)=\mathrm{Nm}_{E/K}(E^\times)$ (`thm3_5`, the named statement `Thm3_5`).

Proof (Milne's, in the language of Tau Ceti's local class formation). Let $V$ be the open normal subgroup of $G_K$
fixing the normal closure of $L$. For $F\in\{L,E\}$ the layer of $K^{\mathrm s}/F$ restricts the layer $V\lhd G_K$, and
by Tau Ceti's norm functoriality of the Artin map (`artinMap_groundNorm`, through
`Ch8.range_groundNorm_eq_comap`) the norm group of $F$ is the preimage under the Artin map of
$\mathrm{Gal}(L'/K)^{\mathrm{ab}}$ of the image of $\mathrm{Gal}(L'/F)$. The images for $F=L$ and $F=E$ agree
(`range_inclusionHom_eq`, the argument of `Ch8.NormLimitationTauCeti.range_inclusionHom_eq`, rewritten for an
arbitrary local field and restrictions of layers), since the fixed field of $\mathrm{Gal}(\cdot/L)[G,G]$ is an abelian
subextension of $L$. The general separable closure $\Omega$ is reduced to `SeparableClosure K` by a $K$-isomorphism.
-/

open IntermediateField TauCeti TauCeti.ClassFieldTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.Ch3

open NumberFieldKB.MilneCFT

namespace NormLimitationLocal

section Group

variable {K : Type} [Field K]

/-- **The fixed field of `Gal(·/B)·[G,G]` is an abelian subextension of `B`**: if `S ⊆ B` contains every finite Galois
abelian subextension of `B`, then every element fixing `S` is an element fixing `B` times a commutator. -/
theorem exists_mul_commutator (B S : IntermediateField K (SeparableClosure K)) [FiniteDimensional K B]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hVB : V.toSubgroup ≤ B.fixingSubgroup)
    (hmax : ∀ N : IntermediateField K (SeparableClosure K), FiniteDimensional K N → IsGalois K N →
      (∀ σ τ : Gal(N/K), σ * τ = τ * σ) → N ≤ B → N ≤ S)
    {g : AbsoluteGaloisGroup K} (hg : g ∈ S.fixingSubgroup) :
    ∃ h ∈ B.fixingSubgroup, ∃ k ∈ commutator (AbsoluteGaloisGroup K), h * k = g := by
  set T : Subgroup (AbsoluteGaloisGroup K) := B.fixingSubgroup ⊔ commutator (AbsoluteGaloisGroup K) with hT
  have hVS : V.toSubgroup ≤ T := hVB.trans le_sup_left
  have hSopen : IsOpen (T : Set (AbsoluteGaloisGroup K)) := Subgroup.isOpen_mono hVS V.isOpen'
  have hSclosed : IsClosed (T : Set (AbsoluteGaloisGroup K)) := Subgroup.isClosed_of_isOpen T hSopen
  have hSnormal : T.Normal := Subgroup.Normal.of_commutator_le (AbsoluteGaloisGroup K) le_sup_right
  set N := fixedField T with hN
  have hfixN : N.fixingSubgroup = T := InfiniteGalois.fixingSubgroup_fixedField ⟨T, hSclosed⟩
  have hNE : N ≤ B := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup B]
    exact IntermediateField.fixedField_antitone le_sup_left
  have : FiniteDimensional K N :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hNE).toLinearMap
      (IntermediateField.inclusion hNE).injective
  have : IsGalois K N := (InfiniteGalois.normal_iff_isGalois N).1 (hfixN ▸ hSnormal)
  have hcomm : ∀ σ τ : Gal(N/K), σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := N) (SeparableClosure K) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := N) (SeparableClosure K) τ
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top σ') (Subgroup.mem_top τ')
    rw [commutatorElement_def] at h1
    have hker : σ' * τ' * σ'⁻¹ * τ'⁻¹ ∈
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := SeparableClosure K) N).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hfixN]
      exact (le_sup_right : commutator (AbsoluteGaloisGroup K) ≤ T) h1
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hker
    calc _ = (AlgEquiv.restrictNormalHom N σ' * AlgEquiv.restrictNormalHom N τ' *
          (AlgEquiv.restrictNormalHom N σ')⁻¹ * (AlgEquiv.restrictNormalHom N τ')⁻¹) *
          AlgEquiv.restrictNormalHom N τ' * AlgEquiv.restrictNormalHom N σ' := by group
      _ = _ := by rw [hker, one_mul]
  have hNM := hmax N inferInstance inferInstance hcomm hNE
  have hgS : g ∈ T := hfixN ▸ IntermediateField.fixingSubgroup_antitone hNM hg
  have hgS' : g ∈ ((B.fixingSubgroup ⊔ commutator (AbsoluteGaloisGroup K) :
      Subgroup (AbsoluteGaloisGroup K)) : Set (AbsoluteGaloisGroup K)) := hgS
  rw [Subgroup.mul_normal] at hgS'
  obtain ⟨h, hh, k, hk, hhk⟩ := hgS'
  exact ⟨h, hh, k, hk, hhk⟩

/-- **The images of the two Galois groups in the abelianized Galois group of the layer agree**: for restrictions
`TB`, `TS` of the layer `V ◁ G_K` whose ground subgroups are the fixing subgroups of `B ⊇ S`, where `S` contains every
abelian subextension of `B`. -/
theorem range_inclusionHom_eq (B S : IntermediateField K (SeparableClosure K)) [FiniteDimensional K B]
    (hSB : S ≤ B) (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    {sB sS : NormalLayer (AbsoluteGaloisGroup K)} (TB : LayerRestriction sB (NormalLayer.ofOpenNormal V))
    (TS : LayerRestriction sS (NormalLayer.ofOpenNormal V))
    (hB : sB.ground.toSubgroup = B.fixingSubgroup) (hS : sS.ground.toSubgroup = S.fixingSubgroup)
    (hVB : V.toSubgroup ≤ B.fixingSubgroup)
    (hmax : ∀ N : IntermediateField K (SeparableClosure K), FiniteDimensional K N → IsGalois K N →
      (∀ σ τ : Gal(N/K), σ * τ = τ * σ) → N ≤ B → N ≤ S) :
    TB.inclusionHom.range = TS.inclusionHom.range := by
  have hBS : B.fixingSubgroup ≤ S.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hSB
  have mB : ∀ g : AbsoluteGaloisGroup K, g ∈ sB.ground → g ∈ B.fixingSubgroup := fun g hg => by
    rw [← hB]; exact hg
  have mB' : ∀ g : AbsoluteGaloisGroup K, g ∈ B.fixingSubgroup → g ∈ sB.ground := fun g hg => by
    rw [← hB] at hg; exact hg
  have mS : ∀ g : AbsoluteGaloisGroup K, g ∈ sS.ground → g ∈ S.fixingSubgroup := fun g hg => by
    rw [← hS]; exact hg
  have mS' : ∀ g : AbsoluteGaloisGroup K, g ∈ S.fixingSubgroup → g ∈ sS.ground := fun g hg => by
    rw [← hS] at hg; exact hg
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Additive.rec with | _ y => ?_
    obtain ⟨q, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective
      (Abelianization.of : _ →* Abelianization _)) y
    induction q using QuotientGroup.induction_on with | H w => ?_
    exact ⟨Additive.ofMul (Abelianization.of (QuotientGroup.mk ⟨(w : AbsoluteGaloisGroup K),
      mS' _ (hBS (mB _ w.2))⟩)), rfl⟩
  · rintro _ ⟨y, rfl⟩
    induction y using Additive.rec with | _ y => ?_
    obtain ⟨q, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective
      (Abelianization.of : _ →* Abelianization _)) y
    induction q using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨h, hh, k, hk, hhk⟩ := exists_mul_commutator B S V hVB hmax (mS _ w.2)
    refine ⟨Additive.ofMul (Abelianization.of (QuotientGroup.mk ⟨h, mB' _ hh⟩)), ?_⟩
    change Additive.ofMul (Abelianization.of (TB.galHom (QuotientGroup.mk ⟨h, mB' _ hh⟩))) =
      Additive.ofMul (Abelianization.of (TS.galHom (QuotientGroup.mk w)))
    rw [LayerRestriction.galHom_mk, LayerRestriction.galHom_mk]
    congr 1
    let φ : AbsoluteGaloisGroup K →* (NormalLayer.ofOpenNormal V).Gal :=
      (QuotientGroup.mk' _).comp
        (MonoidHom.codRestrict (MonoidHom.id _) (NormalLayer.ofOpenNormal V).ground.toSubgroup
          fun _ ↦ Subgroup.mem_top _)
    have hk1 : Abelianization.of (φ k) = 1 := by
      rw [← MonoidHom.mem_ker, Abelianization.ker_of]
      have := Subgroup.mem_map_of_mem φ hk
      rw [commutator_def, Subgroup.map_commutator] at this
      rw [commutator_def]
      exact Subgroup.commutator_mono le_top le_top this
    have hw : (QuotientGroup.mk (Subgroup.inclusion TS.ground_toSubgroup_le w) :
        (NormalLayer.ofOpenNormal V).Gal) = φ h * φ k := by
      rw [← map_mul, hhk]
      rfl
    rw [hw, map_mul, hk1, mul_one]
    rfl

end Group

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The norm group of a finite subextension `F` of `Kˢ/K` is the set of `a` whose class in the ground level of the
layer `V ◁ G_K` is a ground norm of the restriction of `V ◁ G_K` to `Gal(Kˢ/F)`. -/
theorem mem_normGroup_iff_mem_range_groundNorm (F : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K F] (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hV : V ≤ (galoisSubgroup K F F.val).toSubgroup) (a : Kˣ) :
    a ∈ LocalCFT.normGroup F ↔ localGroundEquiv K V (Additive.ofMul a) ∈
      ((layerRestriction_localFormationMap K F F.val V hV).groundNorm (unitsFormation K)).range := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨unitsLevelEquiv F.val (fixedField_localFormationMap_ofOpenNormal_ground K F F.val _)
      (Additive.ofMul y), ?_⟩
    exact groundNorm_layerRestriction_localFormationMap K F F.val V hV (Additive.ofMul y)
  · rintro ⟨z, hz⟩
    obtain ⟨x, rfl⟩ := (unitsLevelEquiv F.val
      (fixedField_localFormationMap_ofOpenNormal_ground K F F.val _)).surjective z
    rw [groundNorm_layerRestriction_localFormationMap K F F.val V hV x] at hz
    have := Additive.ofMul.injective ((localGroundEquiv K V).injective hz)
    exact ⟨x.toMul, this⟩

/-- **Norm limitation in `Kˢ`**: for `E` the largest abelian subextension of a finite `L ⊆ Kˢ`, `N(L) = N(E)`. -/
theorem normGroup_eq_of_isMaxAbelianSub (L E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K L] [FiniteDimensional K E] (h : IsMaxAbelianSub L E) :
    LocalCFT.normGroup L = LocalCFT.normGroup E := by
  set V := fixingOpenNormalSubgroup K L with hVdef
  have hVL : V.toSubgroup ≤ L.fixingSubgroup := by
    have : L ≤ normalClosure K L (SeparableClosure K) := by
      have := AlgHom.fieldRange_le_normalClosure (L.val : L →ₐ[K] SeparableClosure K)
      rwa [IntermediateField.fieldRange_val] at this
    exact IntermediateField.fixingSubgroup_antitone this
  have hVE : V.toSubgroup ≤ E.fixingSubgroup :=
    hVL.trans (IntermediateField.fixingSubgroup_antitone h.1)
  have hVL' : V ≤ (galoisSubgroup K L L.val).toSubgroup := by
    rw [galoisSubgroup_toSubgroup, IntermediateField.fieldRange_val]; exact hVL
  have hVE' : V ≤ (galoisSubgroup K E E.val).toSubgroup := by
    rw [galoisSubgroup_toSubgroup, IntermediateField.fieldRange_val]; exact hVE
  have hmax : ∀ N : IntermediateField K (SeparableClosure K), FiniteDimensional K N → IsGalois K N →
      (∀ σ τ : Gal(N/K), σ * τ = τ * σ) → N ≤ L → N ≤ E := by
    intro N _ hN hcomm hNL
    have : IsMulCommutative Gal(N/K) := ⟨⟨hcomm⟩⟩
    have : IsAbelianGalois K N := {}
    exact h.2.2 N hNL inferInstance
  set TL := layerRestriction_localFormationMap K L L.val V hVL'
  set TE := layerRestriction_localFormationMap K E E.val V hVE'
  have hrange := range_inclusionHom_eq L E h.1 V TL TE
    (by rw [localFormationMap_ofOpenNormal_ground_toSubgroup, galoisSubgroup_toSubgroup,
      IntermediateField.fieldRange_val])
    (by rw [localFormationMap_ofOpenNormal_ground_toSubgroup, galoisSubgroup_toSubgroup,
      IntermediateField.fieldRange_val]) hVL hmax
  have e1 := Ch8.range_groundNorm_eq_comap (localClassFormation K) TL
  have e2 := Ch8.range_groundNorm_eq_comap (localClassFormation K) TE
  ext a
  refine (mem_normGroup_iff_mem_range_groundNorm L V hVL' a).trans
    (Iff.trans ?_ (mem_normGroup_iff_mem_range_groundNorm E V hVE' a).symm)
  rw [e1, e2, hrange]

end Local

section Transport

variable {K : Type} [Field K] {Ω Ω' : Type} [Field Ω] [Algebra K Ω] [Field Ω'] [Algebra K Ω']

/-- The largest abelian subextension is preserved by a $K$-isomorphism of the ambient fields. -/
theorem isMaxAbelianSub_map (e : Ω ≃ₐ[K] Ω') {L E : IntermediateField K Ω} (h : IsMaxAbelianSub L E) :
    IsMaxAbelianSub (L.map (e : Ω →ₐ[K] Ω')) (E.map (e : Ω →ₐ[K] Ω')) := by
  refine ⟨IntermediateField.map_mono _ h.1, ?_, ?_⟩
  · have := h.2.1
    exact IsAbelianGalois.of_algHom (IntermediateField.equivMap E (e : Ω →ₐ[K] Ω')).symm.toAlgHom
  · intro E' hE' hab
    have hle : E'.map (e.symm : Ω' →ₐ[K] Ω) ≤ L := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hE' hy
      simpa using hz
    have habel : IsAbelianGalois K (E'.map (e.symm : Ω' →ₐ[K] Ω)) :=
      IsAbelianGalois.of_algHom (IntermediateField.equivMap E' (e.symm : Ω' →ₐ[K] Ω)).symm.toAlgHom
    have hEE := h.2.2 _ hle habel
    intro y hy
    exact ⟨e.symm y, hEE ⟨y, hy, rfl⟩, by simp⟩

end Transport

end NormLimitationLocal

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K) in
/-- **Theorem 3.5, norm limitation theorem, proved** (Milne, *CFT*, III, Theorem 3.5, p. 108): for a finite extension
$L$ of the local field $K$ inside $\Omega$ and $E$ the largest abelian subextension of $L$,
$\mathrm{Nm}_{L/K}(L^\times)=\mathrm{Nm}_{E/K}(E^\times)$. Proof: reduce to $\Omega=K^{\mathrm s}$ by a $K$-isomorphism
and use Tau Ceti's norm functoriality of the local Artin map (see the module docstring). -/
@[kb "milne2020cft" "v4.03, Ch. III, Thm. 3.5, p. 108"]
theorem thm3_5 : Thm3_5 K Ω := by
  refine ⟨fun L E _ _ h => ?_⟩
  let e : Ω ≃ₐ[K] SeparableClosure K := IsSepClosure.equiv K Ω (SeparableClosure K)
  have hL : FiniteDimensional K (L.map (e : Ω →ₐ[K] SeparableClosure K)) :=
    Module.Finite.equiv (IntermediateField.equivMap L (e : Ω →ₐ[K] SeparableClosure K)).toLinearEquiv
  have hE : FiniteDimensional K (E.map (e : Ω →ₐ[K] SeparableClosure K)) :=
    Module.Finite.equiv (IntermediateField.equivMap E (e : Ω →ₐ[K] SeparableClosure K)).toLinearEquiv
  have := NormLimitationLocal.normGroup_eq_of_isMaxAbelianSub _ _
    (NormLimitationLocal.isMaxAbelianSub_map e h)
  rwa [LocalCFT.normGroup_map e L, LocalCFT.normGroup_map e E] at this

end NumberFieldKB.MilneCFT.Ch3
