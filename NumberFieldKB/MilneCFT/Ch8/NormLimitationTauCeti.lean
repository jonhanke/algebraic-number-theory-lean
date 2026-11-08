import NumberFieldKB.MilneCFT.Ch8.NormLimitationFormation
import NumberFieldKB.MilneCFT.Ch8.NormLimitation
import NumberFieldKB.MilneCFT.Ch7.ExistenceTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.IdeleClass.Norm
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ClassFormation

/-!
# Milne, *Class Field Theory*, VIII Theorem 4.8 (norm limitation), from Tau Ceti

For a finite extension $E/K$ of number fields, not necessarily Galois, with maximal abelian subextension $M$:
$\mathrm{Nm}_{E/K}C_E=\mathrm{Nm}_{M/K}C_M$. Proof: inside the idele-class formation of $K$ (Tau Ceti's
`globalFormation`, `globalClassFormation`), with $L$ the normal closure of $E$, both norm groups are preimages under
the Artin map of $L/K$ of the images of $\mathrm{Gal}(L/E)$ and $\mathrm{Gal}(L/M)$ in $\mathrm{Gal}(L/K)^{\mathrm{ab}}$
(`Ch8.range_groundNorm_eq_comap`, from Tau Ceti's `artinMap_groundNorm`), and these images agree because the fixed
field of $\mathrm{Gal}(L/E)\cdot[G,G]$ is an abelian subextension of $E$.
-/

open IntermediateField NumberField TauCeti TauCeti.ClassFieldTheory

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch8

namespace NormLimitationTauCeti

variable {K : Type} [Field K] [NumberField K]

/-- The open subgroup of $G_K$ fixing a finite subextension of $K^{\mathrm s}/K$. -/
def openFix (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] :
    OpenSubgroup (AbsoluteGaloisGroup K) :=
  ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

theorem fixedField_openFix (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E] :
    fixedField (openFix E).toSubgroup = E :=
  InfiniteGalois.fixedField_fixingSubgroup E

/-- The layer `V ◁ openFix E` (in field terms, $L/E$ for $L$ the fixed field of `V`). -/
def layer (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hV : V.toOpenSubgroup ≤ openFix E) :
    NormalLayer (AbsoluteGaloisGroup K) where
  ground := openFix E
  top := V.toOpenSubgroup
  top_le_ground := hV
  normal := Subgroup.normal_subgroupOf

/-- The layer of $L/E$ restricts the layer of $L/K$. -/
theorem restr (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hV : V.toOpenSubgroup ≤ openFix E) :
    LayerRestriction (layer E V hV) (NormalLayer.ofOpenNormal V) :=
  ⟨rfl, le_top⟩

/-- Through `globalGroundEquiv`, the norm from the level of `E` to the ground is $\mathrm{Nm}_{E/K}$ on idele classes:
the bottom subextension $\bot$ of $K^{\mathrm s}/K$ is identified with $K$ by extension of idele classes. -/
theorem groundNorm_ideleClassLevelEquiv (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hV : V.toOpenSubgroup ≤ openFix E)
    [NumberField E] (d : IdeleClassGroup (𝓞 E) E) :
    (restr E V hV).groundNorm (globalFormation K) (ideleClassLevelEquiv (fixedField_openFix E) (.ofMul d)) =
      NormalLayer.groundEquivOfOpenNormal (globalFormation K) V
        (globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E d))) := by
  set B : IntermediateField K (SeparableClosure K) :=
    (⊥ : FiniteGaloisIntermediateField K (SeparableClosure K)).toIntermediateField with hB
  have hBE : B ≤ E := by
    rw [hB]
    exact fun x hx ↦ (show (⊥ : IntermediateField K (SeparableClosure K)) ≤ E from bot_le) hx
  haveI : FiniteDimensional K B := inferInstance
  haveI : NumberField B := NumberField.of_module_finite K B
  letI : Algebra B E := (IntermediateField.inclusion hBE).toRingHom.toAlgebra
  haveI : IsScalarTower B E (SeparableClosure K) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hF : fixedField (⊤ : OpenSubgroup (AbsoluteGaloisGroup K)).toSubgroup = B :=
    TauCeti.fixedField_toSubgroup_top K
  have hsurj : Function.Surjective (algebraMap K B) := fun x ↦
    (mem_bot.1 (show (x : SeparableClosure K) ∈ (⊥ : IntermediateField K (SeparableClosure K)) from x.2)).imp
      fun _ hc ↦ Subtype.ext hc
  have hext := GlobalNumberFields.ideleClassExtension_bijective K B hsurj
  -- `ext ∘ N_{B/K} = id`, since `N_{B/K} ∘ ext = id` and `ext` is bijective
  have hextN : ∀ y : IdeleClassGroup (𝓞 B) B, GlobalNumberFields.ideleClassExtension K B
      (GlobalNumberFields.ideleClassNormMap K B y) = y := fun y ↦ by
    obtain ⟨x, rfl⟩ := hext.2 y
    rw [GlobalNumberFields.ideleClassNormMap_ideleClassExtension, IntermediateField.finrank_eq_one_iff.2
      (by rw [hB]; rfl), pow_one]
  have hbridge : ideleClassLevelEquiv hF (.ofMul (GlobalNumberFields.ideleClassNormMap B E d)) =
      globalGroundEquiv K (.ofMul (GlobalNumberFields.ideleClassNormMap K E d)) := by
    rw [← GlobalNumberFields.ideleClassNormMap_comp K B E]
    change _ = ideleClassLevelEquiv hF (.ofMul (GlobalNumberFields.ideleClassExtension K B
      (GlobalNumberFields.ideleClassNormMap K B (GlobalNumberFields.ideleClassNormMap B E d))))
    rw [hextN]
  refine Subtype.ext ?_
  have h := levelNorm_ideleClassLevelEquiv (K := K) (F := B) (L := E) (W := ⊤) (W' := openFix E) le_top hF
    (fixedField_openFix E) d
  rw [hbridge] at h
  exact congrArg Subtype.val h

/-- **The norm group of `E` in the formation** is $\mathrm{Nm}_{E/K}C_E$. -/
theorem mem_range_groundNorm_iff (E : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hV : V.toOpenSubgroup ≤ openFix E)
    [NumberField E] (c : IdeleClassGroup (𝓞 K) K) :
    NormalLayer.groundEquivOfOpenNormal (globalFormation K) V (globalGroundEquiv K (.ofMul c)) ∈
        ((restr E V hV).groundNorm (globalFormation K)).range ↔
      c ∈ (GlobalNumberFields.ideleClassNormMap K E :
        IdeleClassGroup (𝓞 E) E →* IdeleClassGroup (𝓞 K) K).range := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨d, rfl⟩ := (ideleClassLevelEquiv (fixedField_openFix E)).surjective x
    rw [← ofMul_toMul d, groundNorm_ideleClassLevelEquiv] at hx
    exact ⟨Additive.toMul d, Additive.ofMul.injective ((globalGroundEquiv K).injective
      ((NormalLayer.groundEquivOfOpenNormal (globalFormation K) V).injective hx))⟩
  · rintro ⟨d, rfl⟩
    exact ⟨_, groundNorm_ideleClassLevelEquiv E V hV d⟩

/-- **The fixed field of `Gal(·/E)·[G,G]` is an abelian subextension of `E`**: if `M ⊆ E` contains every finite
Galois abelian subextension of `E`, then every element fixing `M` is an element fixing `E` times a commutator. -/
theorem exists_mul_commutator (E M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    (V : OpenNormalSubgroup (AbsoluteGaloisGroup K)) (hVE : V.toOpenSubgroup ≤ openFix E)
    (hmax : ∀ N : IntermediateField K (SeparableClosure K), FiniteDimensional K N → IsGalois K N →
      (∀ σ τ : Gal(N/K), σ * τ = τ * σ) → N ≤ E → N ≤ M)
    {g : AbsoluteGaloisGroup K} (hg : g ∈ M.fixingSubgroup) :
    ∃ h ∈ E.fixingSubgroup, ∃ k ∈ commutator (AbsoluteGaloisGroup K), h * k = g := by
  set S : Subgroup (AbsoluteGaloisGroup K) := E.fixingSubgroup ⊔ commutator (AbsoluteGaloisGroup K) with hS
  have hVS : V.toSubgroup ≤ S := (show V.toSubgroup ≤ E.fixingSubgroup from hVE).trans le_sup_left
  have hSopen : IsOpen (S : Set (AbsoluteGaloisGroup K)) := Subgroup.isOpen_mono hVS V.isOpen'
  have hSclosed : IsClosed (S : Set (AbsoluteGaloisGroup K)) := Subgroup.isClosed_of_isOpen S hSopen
  haveI hSnormal : S.Normal := Subgroup.Normal.of_commutator_le (AbsoluteGaloisGroup K) le_sup_right
  set N := fixedField S with hN
  have hfixN : N.fixingSubgroup = S := InfiniteGalois.fixingSubgroup_fixedField ⟨S, hSclosed⟩
  have hNE : N ≤ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E]
    exact IntermediateField.fixedField_antitone le_sup_left
  haveI : FiniteDimensional K N :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hNE).toLinearMap
      (IntermediateField.inclusion hNE).injective
  haveI : IsGalois K N := (InfiniteGalois.normal_iff_isGalois N).1 (hfixN ▸ hSnormal)
  have hcomm : ∀ σ τ : Gal(N/K), σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := N) (SeparableClosure K) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := N) (SeparableClosure K) τ
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top σ') (Subgroup.mem_top τ')
    rw [commutatorElement_def] at h1
    have hker : σ' * τ' * σ'⁻¹ * τ'⁻¹ ∈
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := SeparableClosure K) N).ker := by
      rw [IntermediateField.restrictNormalHom_ker, hfixN]
      exact (le_sup_right : commutator (AbsoluteGaloisGroup K) ≤ S) h1
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at hker
    calc _ = (AlgEquiv.restrictNormalHom N σ' * AlgEquiv.restrictNormalHom N τ' *
          (AlgEquiv.restrictNormalHom N σ')⁻¹ * (AlgEquiv.restrictNormalHom N τ')⁻¹) *
          AlgEquiv.restrictNormalHom N τ' * AlgEquiv.restrictNormalHom N σ' := by group
      _ = _ := by rw [hker, one_mul]
  have hNM := hmax N inferInstance inferInstance hcomm hNE
  have hgS : g ∈ S := hfixN ▸ IntermediateField.fixingSubgroup_antitone hNM hg
  have hgS' : g ∈ ((E.fixingSubgroup ⊔ commutator (AbsoluteGaloisGroup K) :
      Subgroup (AbsoluteGaloisGroup K)) : Set (AbsoluteGaloisGroup K)) := hgS
  rw [Subgroup.mul_normal] at hgS'
  obtain ⟨h, hh, k, hk, hhk⟩ := hgS'
  exact ⟨h, hh, k, hk, hhk⟩

/-- **The images of the two Galois groups in the abelianized Galois group of `L/K` agree.** -/
theorem range_inclusionHom_eq (E M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [FiniteDimensional K M] (hME : M ≤ E) (V : OpenNormalSubgroup (AbsoluteGaloisGroup K))
    (hVE : V.toOpenSubgroup ≤ openFix E) (hVM : V.toOpenSubgroup ≤ openFix M)
    (hmax : ∀ N : IntermediateField K (SeparableClosure K), FiniteDimensional K N → IsGalois K N →
      (∀ σ τ : Gal(N/K), σ * τ = τ * σ) → N ≤ E → N ≤ M) :
    (restr E V hVE).inclusionHom.range = (restr M V hVM).inclusionHom.range := by
  have hEM : (openFix E).toSubgroup ≤ (openFix M).toSubgroup :=
    IntermediateField.fixingSubgroup_antitone hME
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using Additive.rec with | _ y => ?_
    obtain ⟨q, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective
      (Abelianization.of : _ →* Abelianization _)) y
    induction q using QuotientGroup.induction_on with | H w => ?_
    exact ⟨Additive.ofMul (Abelianization.of (QuotientGroup.mk ⟨(w : AbsoluteGaloisGroup K),
      hEM (show (w : AbsoluteGaloisGroup K) ∈ (openFix E).toSubgroup from w.2)⟩)), rfl⟩
  · rintro _ ⟨y, rfl⟩
    induction y using Additive.rec with | _ y => ?_
    obtain ⟨q, rfl⟩ := (QuotientGroup.mk_surjective : Function.Surjective
      (Abelianization.of : _ →* Abelianization _)) y
    induction q using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨h, hh, k, hk, hhk⟩ := exists_mul_commutator E M V hVE hmax
      (show (w : AbsoluteGaloisGroup K) ∈ M.fixingSubgroup from w.2)
    refine ⟨Additive.ofMul (Abelianization.of (QuotientGroup.mk ⟨h, by exact hh⟩)), ?_⟩
    change Additive.ofMul (Abelianization.of ((restr E V hVE).galHom (QuotientGroup.mk ⟨h, by exact hh⟩))) =
      Additive.ofMul (Abelianization.of ((restr M V hVM).galHom (QuotientGroup.mk w)))
    rw [LayerRestriction.galHom_mk, LayerRestriction.galHom_mk]
    congr 1
    -- `w = h * k` with `k` a commutator, which dies in the abelianization
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
    have hw : (QuotientGroup.mk (Subgroup.inclusion (restr M V hVM).ground_toSubgroup_le w) :
        (NormalLayer.ofOpenNormal V).Gal) = φ h * φ k := by
      rw [← map_mul, hhk]
      rfl
    rw [hw, map_mul, hk1, mul_one]
    rfl

end NormLimitationTauCeti

open NormLimitationTauCeti in
/-- **Theorem 4.8, the norm limitation theorem, proved** (Milne, *CFT*, VIII, Theorem 4.8, p. 242): for a finite
extension $E/K$ of number fields, not necessarily Galois, and $M$ the maximal subextension of $E$ abelian over $K$,
$\mathrm{Nm}_{E/K}C_E=\mathrm{Nm}_{M/K}C_M$. From Tau Ceti's idele-class formation (`globalClassFormation`) and the
functoriality `artinMap_groundNorm`, read on fields here. -/
@[kb "milne2020cft" "v4.03, Ch. VIII, Thm. 4.8, p. 242"]
theorem theorem4_8 (K : Type) [Field K] [NumberField K] : Theorem4_8 K := by
  refine ⟨fun E _ _ _ M _ hc hmax => ?_⟩
  let ι : E →ₐ[K] SeparableClosure K := IsSepClosed.lift
  set E' := ι.fieldRange with hE'
  set M' := M.map ι with hM'
  haveI : FiniteDimensional K E' := ι.equivFieldRange.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional K M' := (M.equivMap ι).toLinearEquiv.finiteDimensional
  haveI : NumberField E' := NumberField.of_module_finite K E'
  haveI : NumberField M' := NumberField.of_module_finite K M'
  have hME : M' ≤ E' := by
    rintro _ ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩
  set V := fixingOpenNormalSubgroup K E with hV
  have hVE : V.toOpenSubgroup ≤ openFix E' :=
    IntermediateField.fixingSubgroup_antitone ι.fieldRange_le_normalClosure
  have hVM : V.toOpenSubgroup ≤ openFix M' :=
    hVE.trans (IntermediateField.fixingSubgroup_antitone hME)
  have hmax' : ∀ N : IntermediateField K (SeparableClosure K), FiniteDimensional K N → IsGalois K N →
      (∀ σ τ : Gal(N/K), σ * τ = τ * σ) → N ≤ E' → N ≤ M' := by
    intro N _ _ hN hNE
    set N0 : IntermediateField K E := N.comap ι
    have hmapN : N0.map ι = N := IntermediateField.map_comap_eq_self hNE
    let e : N0 ≃ₐ[K] N := (N0.equivMap ι).trans (IntermediateField.equivOfEq hmapN)
    haveI : IsGalois K N0 := IsGalois.of_algEquiv e.symm
    have hN0 : ∀ σ τ : Gal(N0/K), σ * τ = τ * σ := fun σ τ ↦ e.autCongr.injective (by
      rw [map_mul, map_mul, hN])
    rw [← hmapN]
    exact IntermediateField.map_mono ι (hmax N0 inferInstance hN0)
  rw [Ch7.normClasses_eq_tauCeti, Ch7.normClasses_eq_tauCeti,
    TauCeti.GlobalNumberFields.range_ideleClassNormMap_eq_of_algEquiv ι.equivFieldRange,
    TauCeti.GlobalNumberFields.range_ideleClassNormMap_eq_of_algEquiv (M.equivMap ι)]
  ext c
  rw [← mem_range_groundNorm_iff E' V hVE c, ← mem_range_groundNorm_iff M' V hVM c,
    range_groundNorm_eq_of_range_inclusionHom_eq (globalClassFormation K) (restr E' V hVE)
      (restr M' V hVM) (range_inclusionHom_eq E' M' hME V hVE hVM hmax')]

end NumberFieldKB.MilneCFT.Ch8
