import NumberFieldKB.MilneCFT.Ch7.Existence
import NumberFieldKB.MilneCFT.Ch7.IdelicExistence
import NumberFieldKB.MilneCFT.Ch5IdelicReciprocityTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.GlobalExistence.Existence
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.GlobalExistence.NormLimitation
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Milne, *Class Field Theory*, Chapter VII §9 (the existence theorem), proved from Tau Ceti

Proved here from Tau Ceti's global existence theorem `TauCeti.ClassFieldTheory.globalAbelianExistence` (ported under
`NumberFieldKB/TauCetiPort/`, Apache 2.0, the Tau Ceti contributors):

* `Ch7.theorem9_5` (Theorem 9.5): every open subgroup of finite index of $C_K$ is a norm group. Tau Ceti produces an
  abelian layer $V$ of the absolute Galois group whose norm subgroup is the given one; its class field
  `TauCeti.ClassFieldTheory.classField K V` is the finite abelian extension
  (`isAbelianGalois_classField_iff`, `globalNormSubgroup_eq_range_classField`);
* `Ch7.lemma9_3` (Lemma 9.3): a special case of Theorem 9.5;
* `Ch7.normLimitation` (the named statement `Ch7.NormLimitation`, as used in Lemma 9.4): $\mathrm{Nm}_{L/K}(C_L)$ is
  open of finite index (`isOpen_range_ideleClassNormMap`, `finiteIndex_range_ideleClassNormMap`), hence a norm group,
  and it is contained in $\mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}(C_L))$ by transitivity of norms
  (`ideleClassNormMap_comp`);
* `idelicExistence` (Chapter V, Theorem 5.5, the named statement `IdelicExistence`): from Theorem 9.5 and the
  reciprocity law (`idelicExistence_of_theorem9_5`, `idelicReciprocity`).

The comparison: our idèle class norm `Ch7.ideleClassNorm K L` is Tau Ceti's `ideleClassNormMap K L`
(`Ch7.ideleClassNorm_eq_tauCeti`, from `NumberFieldKB.Ideles.ideleRelNorm_eq_ideleNormMap`).
-/

open NumberField IsDedekindDomain

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable (K : Type) [Field K] [NumberField K]

/-- **Our idèle class norm is Tau Ceti's.** -/
theorem ideleClassNorm_eq_tauCeti (L : Type) [Field L] [NumberField L] [Algebra K L] :
    ideleClassNorm K L =
      (TauCeti.GlobalNumberFields.ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K) := by
  refine MonoidHom.ext fun c => ?_
  induction c using QuotientGroup.induction_on with
  | H x =>
    change Ideles.ideleClassRelNorm (Module.finBasis K L) (x : IdeleClassGroup (𝓞 L) L) = _
    rw [Ideles.ideleClassRelNorm_mk, Ideles.ideleRelNorm_eq_ideleNormMap]
    exact (TauCeti.GlobalNumberFields.ideleClassNormMap_mk x).symm

theorem normClasses_eq_tauCeti (L : Type) [Field L] [NumberField L] [Algebra K L] :
    normClasses K L =
      (TauCeti.GlobalNumberFields.ideleClassNormMap K L : IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  rw [normClasses, ideleClassNorm_eq_tauCeti]

/-- **Theorem 9.5, the existence theorem, proved** (Milne, *CFT*, VII, Theorem 9.5, p. 226): every open subgroup of
finite index of $C_K$ is a norm group. From Tau Ceti's `globalAbelianExistence` (ported). -/
@[kb "milne2020cft" "Ch. VII, Thm. 9.5"]
theorem theorem9_5 : Theorem9_5 K := by
  refine ⟨fun U hU hfin => ?_⟩
  obtain ⟨V, hV, hVU⟩ := TauCeti.ClassFieldTheory.globalAbelianExistence (K := K) (N := U) hU
  have hab : IsAbelianGalois K (TauCeti.ClassFieldTheory.classField K V) :=
    TauCeti.ClassFieldTheory.isAbelianGalois_classField_iff.mpr hV
  refine ⟨TauCeti.ClassFieldTheory.classField K V, inferInstance, inferInstance, inferInstance, inferInstance,
    fun σ τ => hab.toIsMulCommutative.is_comm.comm σ τ, ?_⟩
  rw [normClasses_eq_tauCeti, ← hVU, TauCeti.ClassFieldTheory.globalNormSubgroup_eq_range_classField]

/-- **Lemma 9.3, proved** (Milne, *CFT*, VII, Lemma 9.3, p. 224): a special case of the existence theorem. -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.3"]
theorem lemma9_3 : Lemma9_3 K :=
  ⟨fun _ _ _ V hV hfin _ => (theorem9_5 K).isNormGroup V hV hfin⟩

/-- The idèle class norm group of a finite extension is a norm group (Theorem 9.5). -/
theorem isNormGroup_normClasses (L : Type) [Field L] [NumberField L] [Algebra K L] :
    IsNormGroup K (normClasses K L) := by
  rw [normClasses_eq_tauCeti]
  have := TauCeti.GlobalNumberFields.finiteIndex_range_ideleClassNormMap K L
  exact (theorem9_5 K).isNormGroup _ (TauCeti.GlobalNumberFields.isOpen_range_ideleClassNormMap K L) this

/-- **The norm limitation input of Lemma 9.4, proved** (the named statement `NormLimitation`, Milne, *CFT*, VII,
Lemma 9.4 and VIII): for finite extensions $L/K'/K$, $\mathrm{Nm}_{L/K}(C_L)$ is a norm group contained in
$\mathrm{Nm}_{K'/K}(\mathrm{Nm}_{L/K'}(C_L))$. -/
@[kb "milne2020cft" "Ch. VII, Lemma 9.4 (norm limitation input)"]
theorem normLimitation : NormLimitation K := by
  refine ⟨fun K' _ _ _ L _ _ _ _ _ => ⟨normClasses K L, isNormGroup_normClasses K L, ?_⟩⟩
  rintro _ ⟨c, rfl⟩
  refine ⟨ideleClassNorm K' L c, ⟨c, rfl⟩, ?_⟩
  rw [ideleClassNorm_eq_tauCeti, ideleClassNorm_eq_tauCeti, ideleClassNorm_eq_tauCeti]
  exact congrArg (fun f : IdeleClassGroup (𝓞 L) L →ₜ* IdeleClassGroup (𝓞 K) K => f c)
    (TauCeti.GlobalNumberFields.ideleClassNormMap_comp K K' L)

end NumberFieldKB.MilneCFT.Ch7

namespace NumberFieldKB.MilneCFT

variable (K : Type) [Field K] [NumberField K]

/-- **Theorem 5.5, the existence theorem, proved** (Milne, *CFT*, V, Theorem 5.5, p. 179): from Chapter VII's
Theorem 9.5 and the reciprocity law, both proved from Tau Ceti. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.5"]
theorem idelicExistence : IdelicExistence K :=
  idelicExistence_of_theorem9_5 (idelicReciprocity K) (Ch7.theorem9_5 K)

/-- **Chapter VII's reciprocity law, proved** (Milne, *CFT*, V, Theorem 5.3 (b) with Proposition 5.2, as used in
VII §9): from Chapter V's, proved from Tau Ceti. -/
@[kb "milne2020cft" "Ch. V, Thm. 5.3 (b) (as used in Ch. VII §9)"]
theorem ch7_reciprocityLaw : Ch7.ReciprocityLaw K :=
  reciprocityLaw_of_idelic (idelicReciprocity K)

end NumberFieldKB.MilneCFT
