import Mathlib
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3InvSystemTop
import NumberFieldKB.MilneCFT.Ch3ArtinMaps
import NumberFieldKB.MilneCFT.Ch3Lemma32
import NumberFieldKB.MilneCFT.Ch2CupUnique
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
import NumberFieldKB.TauCetiPort.FieldTheory.Galois.AbsoluteGaloisGroup.DecompositionRestrict

/-!
# Milne, *Class Field Theory*, Chapter III §3: Proposition 3.6, $\chi(\phi(a)) = \mathrm{inv}_K(a \cup \delta\chi)$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Proof (unconditional). In bidegree $(0, 2)$ every cup-product family is $y \mapsto (n \mapsto a \otimes n)_* y$
(`cup_zero_left`, dimension shifting), so $a \cup \delta\chi$ is the image of $\delta\chi \in H^2(G, \mathbb Z)$
under $\mathbb Z \to L^\times$, $1 \mapsto a$. On cochains $\delta\chi$ is the carry cocycle
$(g, h) \mapsto \tilde\chi(g) + \tilde\chi(h) - \tilde\chi(gh)$ of the representatives $\tilde\chi \in [0, 1)$
(`delta_char`), so $a \cup \delta\chi$ inflates in $\mathrm{Br}(K)$ to Tau Ceti's carry class
`characterCarryCocycle` of $\chi$ and $a$. Every invariant system has the Tau Ceti invariant
(`InvariantSystem.invK_eq_tcInvK`), every local Artin map is Tau Ceti's (`isLocalArtinMap_unique_unconditional`), and
Tau Ceti's character formula `invMap_characterCarryCocycle_of_mk_eq_artinMap` concludes.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory TauCeti.ContCohomology

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

/-! ## The connecting map of a character -/

section Generic

variable {G : Type} [Group G]

/-- The representative in $[0, 1)$ of a class of $\mathbb Q/\mathbb Z$. -/
noncomputable def qzLift (q : QZ) : ℚ := (AddCircle.equivIco 1 0 (Ch4.addCircleEquivQZ.symm q) : ℚ)

theorem mk_qzLift (q : QZ) : (QuotientAddGroup.mk (qzLift q) : QZ) = q := by
  have h : ((qzLift q : ℚ) : AddCircle (1 : ℚ)) = Ch4.addCircleEquivQZ.symm q := AddCircle.coe_equivIco
  have : Ch4.addCircleEquivQZ ((qzLift q : ℚ) : AddCircle (1 : ℚ)) = QuotientAddGroup.mk (qzLift q) := rfl
  rw [← this, h, AddEquiv.apply_symm_apply]

/-- A character $\chi : G \to \mathbb Q/\mathbb Z$ as a character with values in `AddCircle (1 : ℚ)`. -/
noncomputable def toCircle (χ : Additive G →+ QZ) : Additive G →+ AddCircle (1 : ℚ) :=
  Ch4.addCircleEquivQZ.symm.toAddMonoidHom.comp χ

theorem intCast_characterCarry_toCircle (χ : Additive G →+ QZ) (g h : G) :
    (characterCarry (toCircle χ) g h : ℚ) =
      qzLift (χ (.ofMul h)) - qzLift (χ (.ofMul (g * h))) + qzLift (χ (.ofMul g)) := by
  rw [intCast_characterCarry]
  simp only [toCircle, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, qzLift]
  ring

/-- The carry cocycle $(g, h) \mapsto \tilde\chi(g) + \tilde\chi(h) - \tilde\chi(gh) \in \mathbb Z$. -/
noncomputable def carryZ (χ : Additive G →+ QZ) : cocycles₂ (seqZQ G).X₁ :=
  ⟨(fun p => characterCarry (toCircle χ) p.1 p.2 : G × G → (seqZQ G).X₁),
    (mem_cocycles₂_iff (A := (seqZQ G).X₁) _).2 fun g h j =>
      characterCarry_mul_add (toCircle χ) g h j⟩

theorem carryZ_apply (χ : Additive G →+ QZ) (p : G × G) :
    (carryZ χ : G × G → (seqZQ G).X₁) p = (characterCarry (toCircle χ) p.1 p.2 : ℤ) := rfl

/-- **$\delta\chi$ is the carry cocycle** of the representatives of $\chi$ in $[0, 1)$. -/
theorem delta_char (χ : Additive G →+ QZ) :
    (δ (seqZQ_shortExact G) 1 2 rfl).hom ((H1IsoOfIsTrivial (seqZQ G).X₃).inv.hom χ) =
      H2π _ (carryZ χ) := by
  erw [H1IsoOfIsTrivial_inv_apply]
  rw [δ₁_apply (seqZQ_shortExact G) _ (fun g => qzLift (χ (.ofMul g))) ?_ (carryZ χ) ?_]
  · rfl
  · funext g
    exact mk_qzLift _
  · funext p
    change ((characterCarry (toCircle χ) p.1 p.2 : ℤ) : ℚ) = qzLift (χ (.ofMul p.2)) -
      qzLift (χ (.ofMul (p.1 * p.2))) + qzLift (χ (.ofMul p.1))
    exact intCast_characterCarry_toCircle χ p.1 p.2

end Generic

/-! ## Proposition 3.6 -/

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The $G$-map $\mathbb Z \to L^\times$, $k \mapsto a^k$, for $a \in K^\times$. -/
noncomputable def powHom (M : IntermediateField K Ω) (a : Kˣ) :
    Rep.trivial ℤ Gal(M/K) ℤ ⟶ Rep.ofAlgebraAutOnUnits K M :=
  Rep.ofHom ⟨(zmultiplesHom (Additive Mˣ) (Additive.ofMul (embUnits M a))).toIntLinearMap, fun σ => by
    refine LinearMap.ext fun k => ?_
    change k • Additive.ofMul (embUnits M a) = Additive.ofMul (σ • (embUnits M a) ^ k)
    rw [smul_zpow', gal_smul_embUnits]
    rfl⟩

theorem powHom_apply (M : IntermediateField K Ω) (a : Kˣ) (k : ℤ) :
    (powHom M a).hom (show Rep.trivial ℤ Gal(M/K) ℤ from k) = k • Additive.ofMul (embUnits M a) := rfl

/-- **The cup product $a \cup y$ in bidegree $(0, 2)$** is the image of $y$ under $k \mapsto a^k$, for every
cup-product family. -/
theorem tensorIntToSelf_cup (M : IntermediateField K Ω) (c : CupProductFamily Gal(M/K)) (a : Kˣ)
    (y : groupCohomology (Rep.trivial ℤ Gal(M/K) ℤ) 2) :
    ((functor ℤ Gal(M/K) 2).map (tensorIntToSelf M)).hom
        (c.cup _ _ 0 2 2 rfl (unitsH0 M a) y) =
      ((functor ℤ Gal(M/K) 2).map (powHom M a)).hom y := by
  have h := cup_zero_left c (Rep.ofAlgebraAutOnUnits K M) ⟨Additive.ofMul (embUnits M a), fun σ =>
    congrArg Additive.ofMul (gal_smul_embUnits M σ a)⟩ 2 (Rep.trivial ℤ Gal(M/K) ℤ) y
  have hc : tensorLeftOf ⟨Additive.ofMul (embUnits M a), fun σ =>
      congrArg Additive.ofMul (gal_smul_embUnits M σ a)⟩ (Rep.trivial ℤ Gal(M/K) ℤ) ≫ tensorIntToSelf M =
      powHom M a := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro k
    change TensorProduct.lift (unitsIntBil M) (_ ⊗ₜ[ℤ] k) = _
    erw [TensorProduct.lift.tmul]
  rw [unitsH0, h, ← hc, Functor.map_comp]
  rfl

end Local

section Brauer

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable (M : IntermediateField K Ω) [FiniteDimensional K M] [IsGalois K M]

/-- The embedding $M \to K^{\mathrm{sep}}$ used by `toBr`. -/
noncomputable abbrev embM : M →ₐ[K] SeparableClosure K := (sepEquiv K Ω).toAlgHom.comp M.val

theorem isOpen_ker_char (χ : Additive Gal(M/K) →+ AddCircle (1 : ℚ)) :
    IsOpen ((χ.comp (embM M).restrictNormalHom.toAdditive).ker :
      Set (Additive Gal(SeparableClosure K/K))) := by
  have ho := AlgHom.isOpen_ker_restrictNormalHom_comp_restrictScalarsHom (F := K) (embM M)
  refine AddSubgroup.isOpen_mono (H₁ := Subgroup.toAddSubgroup
    ((embM M).restrictNormalHom.comp (AlgEquiv.restrictScalarsHom K :
      Gal(SeparableClosure K/K) →* Gal(SeparableClosure K/K))).ker) (fun x hx => ?_)
    (ho.preimage continuous_toMul)
  rw [Additive.mem_toAddSubgroup, MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
  have e : (AlgEquiv.restrictScalarsHom K : Gal(SeparableClosure K/K) →* Gal(SeparableClosure K/K))
      x.toMul = x.toMul := AlgEquiv.ext fun _ => rfl
  rw [e] at hx
  rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply, hx, ofMul_one,
    map_zero]

/-- **$a \cup \delta\chi$ is Tau Ceti's carry class** in $\mathrm{Br}(K)$. -/
theorem toBr_powHom_carryZ (χ : Additive Gal(M/K) →+ QZ) (a : Kˣ) :
    toBr M (((functor ℤ Gal(M/K) 2).map (powHom M a)).hom (H2π _ (carryZ χ))) =
      unitsRepH2Equiv K (characterCarryCocycle ((toCircle χ).comp (embM M).restrictNormalHom.toAdditive)
        (isOpen_ker_char M _) (TauCeti.baseUnitsEquivInvariants K (.ofMul a))) := by
  obtain ⟨c, hcu, hc⟩ := exists_relBrCocycle_eq K M (embM M)
    (characterCarryCocycle ((toCircle χ).comp (embM M).restrictNormalHom.toAdditive)
      (isOpen_ker_char M _) (TauCeti.baseUnitsEquivInvariants K (.ofMul a)))
    (fun p => embUnits M a ^ characterCarry (toCircle χ) p.1 p.2) fun g h => by
      rw [characterCarryCocycle_apply, characterCarry_comp]
      dsimp only
      rw [ofMul_zpow, map_zsmul, AddSubgroup.coe_zsmul]
      congr 1
      apply Additive.toMul.injective
      apply Units.ext
      rw [TauCeti.embeddedUnitsEquivInvariants_apply, TauCeti.toMul_coe_embeddedUnitsInvariants,
        TauCeti.toMul_coe_baseUnitsEquivInvariants]
      simp [embUnits]
  have hcls : ((functor ℤ Gal(M/K) 2).map (powHom M a)).hom (H2π _ (carryZ χ)) = H2π _ c := by
    rw [functor_map]
    erw [H2π_comp_map_apply]
    congr 1
    apply Subtype.ext
    funext p
    apply Additive.toMul.injective
    refine Eq.trans ?_ (hcu p).symm
    change Additive.toMul ((characterCarry (toCircle χ) p.1 p.2 : ℤ) • Additive.ofMul (embUnits M a)) = _
    rw [toMul_zsmul, toMul_ofMul]
  rw [hcls, toBr]
  exact (relBrInfl_H2π K M (embM M) c).trans (by rw [hc])

end Brauer

section Prop36

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

variable (K Ω) in
/-- **Proposition 3.6** (Milne, *CFT*, III, p. 109, citing Serre), proved unconditionally: for a finite abelian
$L/K$, a character $\chi$ of $\operatorname{Gal}(L/K)$, $a \in K^\times$, every local Artin map $\phi$, every system of
invariant maps and every cup-product family, $\chi(\phi_{L/K}(a)) = \mathrm{inv}_K(a \cup \delta\chi)$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Prop. 3.6, p. 109"]
theorem prop3_6 : Prop3_6 K Ω := by
  refine ⟨fun φ hφ s L c χ a => ?_⟩
  have hφ' : φ = fun L => tauCetiArtin L :=
    isLocalArtinMap_unique_unconditional (hφ := hφ) (hψ := isLocalArtinMap_tauCetiArtin)
  subst hφ'
  erw [tensorIntToSelf_cup, delta_char]
  rw [s.invK_eq_tcInvK]
  erw [tcInvK_apply, toBr_powHom_carryZ]
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K a)
  rw [invMap_characterCarryCocycle_of_mk_eq_artinMap _ _ a σ hσ]
  have hart : tauCetiArtin L a =
      (embM L.toField).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ) := by
    apply (abelianizationOfEquiv Gal(L.toField/K)).injective
    rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L (embM L.toField),
      artinMap_restrict K L.toField (embM L.toField) a σ hσ]
    rfl
  rw [hart]
  simp [toCircle]

end Prop36

end NumberFieldKB.MilneCFT.Ch3
