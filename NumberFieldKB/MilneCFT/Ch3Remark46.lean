import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import QuadFormsKB.Citation
import NumberFieldKB.MilneCFT.Ch3Prop43
import NumberFieldKB.MilneCFT.CharSeparation
import NumberFieldKB.MilneCFT.LocalCFT.UnconditionalYamaguchi
import NumberFieldKB.TauCetiPort.NumberTheory.LocalField.PowerSubgroup.Open

/-!
# Milne, *Class Field Theory*, Chapter III, Remark 4.6: the right kernel of $(\chi, b)$ is $K^{\times n}$

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`.

Milne deduces it from the existence theorem. Here: $K^{\times n}$ is open of finite index, hence the norm group of a
finite abelian $L/K$ (local existence theorem, `isNormGroup_iff_unconditional`) of exponent dividing $n$, so
$L \subseteq M$. If $(\chi, b) = \chi(\phi_K(b))/n$ vanishes for every $\chi$, it vanishes for all characters of
$\operatorname{Gal}(L/K)$, which separate points (`exists_zmod_char_ne_zero`), so $\phi_{L/K}(b) = 1$ and
$b \in \mathrm{Nm}(L^\times) = K^{\times n}$.
-/

open scoped ValuativeRel

namespace NumberFieldKB.MilneCFT.Ch3

open CategoryTheory Rep groupCohomology Limits NumberFieldKB.MilneCFT NumberFieldKB.MilneCFT.LocalCFT
open TauCeti.ClassFieldTheory
open scoped IsMulCommutative

set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The Artin symbol of `tauCetiArtin` is the restriction of a representative of the absolute Artin symbol. -/
theorem tauCetiArtin_eq_restrict (L : FiniteAbelianExt K Ω) (b : Kˣ) (σ : Field.absoluteGaloisGroup K)
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization K) = TauCeti.ClassFieldTheory.artinMap K b) :
    tauCetiArtin L b = (embM L.toField).restrictNormalHom (TauCeti.absoluteGaloisGroupRestrictEquiv K σ) := by
  apply (abelianizationOfEquiv Gal(L.toField/K)).injective
  rw [abelianizationOfEquiv_apply, abelianizationOfEquiv_apply, abelianizationOf_tauCetiArtin L (embM L.toField),
    artinMap_restrict K L.toField (embM L.toField) b σ hσ]
  rfl

/-- Restriction from $M$ to $L \subseteq M$ of the restriction of $\tau \in G_K$. -/
theorem galRestrict_embM {L M : IntermediateField K Ω} [FiniteDimensional K L] [Normal K L]
    [FiniteDimensional K M] [Normal K M] (h : L ≤ M) (τ : Gal(SeparableClosure K/K)) :
    galRestrict h ((embM M).restrictNormalHom τ) = (embM L).restrictNormalHom τ := by
  refine AlgEquiv.ext fun y => Subtype.ext ?_
  rw [LocalCFT.galRestrict_apply]
  apply (sepEquiv K Ω).injective
  have h1 := AlgHom.restrictNormalHom_commutes (embM M) τ (IntermediateField.inclusion h y)
  have h2 := AlgHom.restrictNormalHom_commutes (embM L) τ y
  exact h1.trans h2.symm

variable (K Ω) in
/-- **Remark 4.6** (Milne, *CFT*, III, p. 114), first part, proved unconditionally (corrected finite-level statement,
see `Remark4_6`): if $(\chi, b) = 0$ for every character $\chi$ of $\operatorname{Gal}(M/K)$ into $\mathbb Z/n$, then
$b \in K^{\times n}$. -/
@[kb "milne2020cft" "v4.03, Ch. III, Remark 4.6, p. 114"]
theorem remark4_6 : Remark4_6 K Ω := by
  refine ⟨fun n _ hn s M _ _ c _ hab b β hβ H => ?_⟩
  set N : Subgroup Kˣ := (powMonoidHom n : Kˣ →* Kˣ).range
  obtain ⟨L, hL⟩ := (isNormGroup_iff_unconditional (Ω := Ω) N).2
    ⟨TauCeti.isOpen_range_powMonoidHom hn, TauCeti.finiteIndex_range_powMonoidHom hn⟩
  have hexp : ∀ σ : Gal(L.toField/K), σ ^ n = 1 := by
    intro σ
    obtain ⟨a, rfl⟩ := surjective_tauCetiArtin L σ
    rw [← map_pow, ← MonoidHom.mem_ker, ker_tauCetiArtin, hL]
    exact ⟨a, rfl⟩
  have hLM := hab L hexp
  obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (TauCeti.ClassFieldTheory.artinMap K b)
  have hart := tauCetiArtin_eq_restrict L b σ hσ
  have hone : tauCetiArtin L b = 1 := by
    by_contra hne
    have hg : Additive.ofMul (tauCetiArtin L b) ≠ 0 := fun h0 => hne (Additive.ofMul.injective h0)
    obtain ⟨χL, hχL⟩ := exists_zmod_char_ne_zero (G := Additive Gal(L.toField/K)) (n := n)
      (fun g => Additive.toMul.injective (by rw [toMul_nsmul, toMul_zero]; exact hexp _)) _ hg
    let χ : Additive Gal(M/K) →+ ZMod n := χL.comp (galRestrict hLM).toAdditive
    have h0 := H χ
    rw [charKummerPairing_eq n s M c χ β b hβ σ hσ] at h0
    have h1 := (zmodToQZ_injective n) (h0.trans (map_zero _).symm)
    apply hχL
    rw [hart, ← galRestrict_embM hLM]
    exact h1
  have hb : b ∈ normGroup L.toField := by rw [← ker_tauCetiArtin]; exact hone
  rw [hL] at hb
  obtain ⟨x, hx⟩ := hb
  exact ⟨x, hx⟩

end NumberFieldKB.MilneCFT.Ch3
