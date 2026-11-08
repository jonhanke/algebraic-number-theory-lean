import NumberFieldKB.HeckeL.Arch
import NumberFieldKB.HeckeCharacter.InfinityType

/-!
# A Hecke character on $F_\infty^\times$ is the product of its components

For a Hecke character $\chi$ and $u\in F_\infty^\times = (\mathbb R^\times)^{r_1}\times(\mathbb C^\times)^{r_2}$,
$$\chi(u) = \prod_{w\text{ real}}\chi_w(u_w)\prod_{w\text{ complex}}\chi_w(u_w)$$
(`onIdeles_infEmb`), with the components `realComponent` (on $\mathbb R^\times$) and `complexComponent` (on
$\mathbb C^\times$), read through Mathlib's identifications $F_w\cong\mathbb R$, $F_w\cong\mathbb C$; these are the
identifications used by the mixed space, so the coordinates match.
-/

open IsDedekindDomain NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Filter Set
open QuadFormsKB QuadFormsKB.Tamagawa QuadFormsKB.Tamagawa.Measure.Weil
open scoped Classical

namespace NumberFieldKB.HeckeL

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F]

local notation "V" => mixedSpace F

open GlobalZeta Ideles

/-- The components in Mathlib's infinite adele ring of a unit of $F_\infty$. -/
def unitW (u : Vˣ) (w : InfinitePlace F) : w.Completionˣ :=
  Units.map (Pi.evalMonoidHom (fun w : InfinitePlace F => w.Completion) w)
    (Units.map (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toMonoidHom u)

theorem coe_unitW (u : Vˣ) (w : InfinitePlace F) :
    ((unitW u w : w.Completionˣ) : w.Completion) =
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (u : V) w := rfl

theorem ideleGroupEquiv_symm_infEmb (u : Vˣ) :
    (ideleGroupEquiv F).symm (infEmb F u) = ∏ w, IdeleGroup.ofCompletion (𝓞 F) F w (unitW u w) := by
  apply Units.ext
  rw [val_ideleGroupEquiv_symm, Units.coe_prod]
  have h1 : ((infEmb F u : (Adeles F)ˣ) : Adeles F) = ((u : V), 1) := rfl
  rw [h1, adeleRingEquiv_symm_apply]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_prod]
    simp only [IdeleGroup.val_ofCompletion_apply, coe_unitW]
    exact (Finset.univ_prod_mulSingle _).symm
  · rw [Prod.snd_prod]
    simp [IdeleGroup.val_ofCompletion_apply]

/-- $\chi(u) = \prod_w\chi_w(u_w)$ over all infinite places. -/
theorem onIdeles_infEmb_eq_prod (χ : HeckeCharacter F) (u : Vˣ) :
    (χ.onIdeles (infEmb F u) : ℂ) = ∏ w, (χ.infiniteComponent w (unitW u w) : ℂ) := by
  rw [HeckeCharacter.onIdeles_apply, ideleGroupEquiv_symm_infEmb, ← Units.coe_prod]
  congr 1
  rw [QuotientGroup.mk_prod, map_prod]
  rfl

theorem unitW_real_eq (u : Vˣ) (w : {w : InfinitePlace F // w.IsReal}) :
    unitW u w.1 = (Units.mapContinuousMulEquiv (completionMulEquivReal w.2)).symm (unitR u w) := by
  rw [ContinuousMulEquiv.eq_symm_apply]
  apply Units.ext
  change Completion.ringEquivRealOfIsReal w.2 _ = (u : V).1 w
  rw [Completion.ringEquivRealOfIsReal_apply, coe_unitW]
  conv_rhs => rw [← (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (u : V)]
  rfl

theorem unitW_complex_eq (u : Vˣ) (w : {w : InfinitePlace F // w.IsComplex}) :
    unitW u w.1 = (Units.mapContinuousMulEquiv (completionMulEquivComplex w.2)).symm (unitC u w) := by
  rw [ContinuousMulEquiv.eq_symm_apply]
  apply Units.ext
  change Completion.ringEquivComplexOfIsComplex w.2 _ = (u : V).2 w
  rw [Completion.ringEquivComplexOfIsComplex_apply, coe_unitW]
  conv_rhs => rw [← (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (u : V)]
  rfl

/-- **A Hecke character on $F_\infty^\times$ is the product of its components** at the real and complex places:
$\chi(u) = \prod_{w\text{ real}}\chi_w(u_w)\prod_{w\text{ complex}}\chi_w(u_w)$ (`realComponent`, `complexComponent`). -/
theorem onIdeles_infEmb (χ : HeckeCharacter F) (u : Vˣ) :
    (χ.onIdeles (infEmb F u) : ℂ) =
      (∏ w : {w : InfinitePlace F // w.IsReal}, (χ.realComponent w.2 (unitR u w) : ℂ)) *
        ∏ w : {w : InfinitePlace F // w.IsComplex}, (χ.complexComponent w.2 (unitC u w) : ℂ) := by
  rw [onIdeles_infEmb_eq_prod, ← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  · refine Fintype.prod_congr _ _ fun w => ?_
    rw [unitW_real_eq]
    rfl
  · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex) _ _ fun w => ?_
    have hw : (Equiv.subtypeEquivRight (fun w => not_isReal_iff_isComplex) w : {w : InfinitePlace F //
      w.IsComplex}).1 = w.1 := rfl
    rw [show unitW u w.1 = unitW u (Equiv.subtypeEquivRight (fun w => not_isReal_iff_isComplex) w).1 from rfl,
      unitW_complex_eq]
    rfl

end

end NumberFieldKB.HeckeL
