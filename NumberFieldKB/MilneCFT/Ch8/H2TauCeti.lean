import NumberFieldKB.MilneCFT.Ch8.Brauer
import NumberFieldKB.Ideles.RelativeNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ClassFormation
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter VIII, Theorem 4.7, proved from Tau Ceti

The named statement `NumberFieldKB.MilneCFT.Ch8.Theorem4_7` ($H^2(\mathrm{Gal}(L/K), C_L)$ is cyclic of order
$[L:K]$) is proved here (`Ch8.theorem4_7`) from Tau Ceti's global class formation
`TauCeti.ClassFieldTheory.globalClassFormation` (ported under `NumberFieldKB/TauCetiPort/`, Apache 2.0, the Tau Ceti
contributors): `ClassFormation.isAddCyclic_H2` and `ClassFormation.natCard_H2` on the layer of $L$, read in
$H^2(\mathrm{Gal}(L/K), C_L)$ through `globalLayerCohomologyEquiv`.

The comparison: our Galois action on the adèles (`Ch7.instMulSemiringActionAdeleRing`, through QuadFormsKB's base
change $\mathbb A_L = L\otimes_K\mathbb A_K$) is Tau Ceti's `adeleGaloisAction` (`Ch7.smul_eq_adeleGaloisAction`): both
are continuous ring homomorphisms equal to $\sigma$ on $L$ and fixing the idempotent $(1,0)$, which is extended from
$\mathbb A_K$, so Tau Ceti's `AdeleRing.ringHom_ext` applies. Hence the $G$-modules $C_L$ agree
(`Ch7.ideleClassRep_eq_tauCeti`).
-/

open NumberField IsDedekindDomain NumberFieldKB.Ideles QuadFormsKB.Tamagawa.Measure.Weil

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Our Galois action on the adèles is Tau Ceti's.** -/
theorem smul_eq_adeleGaloisAction (σ : L ≃ₐ[K] L) (y : AdeleRing (𝓞 L) L) :
    σ • y = TauCeti.GlobalNumberFields.adeleGaloisAction K L σ y := by
  let f : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L := MulSemiringAction.toRingHom (L ≃ₐ[K] L) _ σ
  let g : AdeleRing (𝓞 L) L →+* AdeleRing (𝓞 L) L :=
    (TauCeti.GlobalNumberFields.adeleGaloisAction K L σ).toRingHom
  have hf : Continuous f :=
    (continuous_adeleRingEquiv_symm L).comp ((continuous_galAdeleFun σ).comp (continuous_adeleRingEquiv L))
  have hg : Continuous g := TauCeti.GlobalNumberFields.continuous_adeleGaloisAction (K := K) (L := L) σ
  have hext : ∀ t : AdeleRing (𝓞 K) K, f (NumberField.adeleExtension (𝓞 K) K (𝓞 L) L t) =
      NumberField.adeleExtension (𝓞 K) K (𝓞 L) L t := fun t => by
    apply (adeleRingEquiv L).injective
    change adeleRingEquiv L (σ • NumberField.adeleExtension (𝓞 K) K (𝓞 L) L t) = _
    rw [adeleRingEquiv_smul, adeleRingEquiv_adeleExtension]
    exact galAdeleFun_adeleMap σ _
  have h : f = g := by
    refine NumberField.AdeleRing.ringHom_ext (𝓞 L) L hf hg (fun x => ?_) (fun a h1 h0 => ?_)
    · apply (adeleRingEquiv L).injective
      change adeleRingEquiv L (σ • algebraMap L (AdeleRing (𝓞 L) L) x) = adeleRingEquiv L (g _)
      rw [adeleRingEquiv_smul, adeleRingEquiv_algebraMap]
      simp only [g, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        TauCeti.GlobalNumberFields.adeleGaloisAction_algebraMap, adeleRingEquiv_algebraMap]
      exact galAdeleFun_diag σ x
    · have ha : a = NumberField.adeleExtension (𝓞 K) K (𝓞 L) L ((1, 0) : AdeleRing (𝓞 K) K) := by
        obtain ⟨a1, a2⟩ := a
        simp only at h1 h0
        subst h1 h0
        exact Prod.ext (by simp) (by simp)
      rw [ha, hext]
      exact (TauCeti.GlobalNumberFields.adeleGaloisAction_adeleExtension (K := K) (L := L) σ _).symm
  exact RingHom.congr_fun h y

/-- Our Galois action on an idèle is Tau Ceti's: `Units.map` of `adeleGaloisAction`. -/
theorem smul_idele_eq_tauCeti (σ : L ≃ₐ[K] L) (x : IdeleGroup (𝓞 L) L) :
    σ • x = Units.map (TauCeti.GlobalNumberFields.adeleGaloisAction K L σ : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) x := by
  apply Units.ext
  rw [val_smul_idele, smul_eq_adeleGaloisAction]
  rfl

/-- **Our Galois action on the idèles is Tau Ceti's.** -/
theorem instMulDistribMulActionIdeleGroup_eq_tauCeti :
    (instMulDistribMulActionIdeleGroup : MulDistribMulAction (L ≃ₐ[K] L) (IdeleGroup (𝓞 L) L)) =
      TauCeti.GlobalNumberFields.ideleMulDistribMulAction K L := by
  refine MulDistribMulAction.ext (funext fun σ => funext fun x => ?_)
  exact (smul_idele_eq_tauCeti σ x).trans
    (@TauCeti.GlobalNumberFields.idele_smul_def K L _ _ _ _ σ x).symm

/-- **Our Galois action on the idèle classes is Tau Ceti's.** -/
theorem instMulDistribMulActionIdeleClassGroup_eq_tauCeti :
    (instMulDistribMulActionIdeleClassGroup :
        MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup (𝓞 L) L)) =
      TauCeti.GlobalNumberFields.ideleClassMulDistribMulAction K L := by
  refine MulDistribMulAction.ext (funext fun σ => funext fun c => ?_)
  induction c using QuotientGroup.induction_on with
  | H x =>
    refine (smul_mk σ x).trans ((congrArg QuotientGroup.mk ((smul_idele_eq_tauCeti σ x).trans
      (@TauCeti.GlobalNumberFields.idele_smul_def K L _ _ _ _ σ x).symm)).trans ?_)
    exact (@TauCeti.GlobalNumberFields.ideleClass_smul_mk K L _ _ _ _ σ x).symm

variable (K L) in
/-- **The $G$-module $C_L$ is Tau Ceti's.** -/
theorem ideleClassRep_eq_tauCeti : ideleClassRep K L = TauCeti.ClassFieldTheory.ideleClassRep K L := by
  unfold ideleClassRep TauCeti.ClassFieldTheory.ideleClassRep
  rw [instMulDistribMulActionIdeleClassGroup_eq_tauCeti]

end NumberFieldKB.MilneCFT.Ch7

namespace NumberFieldKB.MilneCFT.Ch8

variable (K : Type) [Field K] [NumberField K]

/-- **Theorem 4.7, proved** (Milne, *CFT*, VIII, Theorem 4.7, p. 242): for every finite Galois extension $L/K$ of
number fields, $H^2(\mathrm{Gal}(L/K), C_L)$ is cyclic of order $[L:K]$. From Tau Ceti's global class formation
(ported). -/
@[kb "milne2020cft" "Ch. VIII, Theorem 4.7, p. 242"]
theorem theorem4_7 : Theorem4_7 K := by
  refine ⟨fun L _ _ _ _ => ?_⟩
  let ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let 𝓛 := TauCeti.ClassFieldTheory.NormalLayer.ofOpenNormal (TauCeti.fixingOpenNormalSubgroup K L)
  let e := TauCeti.ClassFieldTheory.globalLayerCohomologyEquiv ι 2
  have hH : H2C K L = groupCohomology (TauCeti.ClassFieldTheory.ideleClassRep K L) 2 := by
    rw [H2C, Ch7.ideleClassRep_eq_tauCeti]
  rw [hH]
  have hcyc := TauCeti.ClassFieldTheory.ClassFormation.isAddCyclic_H2
    (TauCeti.ClassFieldTheory.globalClassFormation K) 𝓛
  have hcard := TauCeti.ClassFieldTheory.ClassFormation.natCard_H2
    (TauCeti.ClassFieldTheory.globalClassFormation K) 𝓛
  refine ⟨isAddCyclic_of_surjective e.toAddMonoidHom e.surjective, ?_⟩
  rw [← Nat.card_congr e.toEquiv, hcard, TauCeti.ClassFieldTheory.NormalLayer.degree_eq_natCard_gal,
    Nat.card_congr (TauCeti.ClassFieldTheory.layerGalEquiv ι).toEquiv]
  exact IsGalois.card_aut_eq_finrank K L

end NumberFieldKB.MilneCFT.Ch8
