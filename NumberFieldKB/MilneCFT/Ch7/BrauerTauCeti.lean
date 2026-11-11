import NumberFieldKB.MilneCFT.Ch7.Brauer
import NumberFieldKB.MilneCFT.Ch8.LocalRelBrTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Cyclotomic.Splitting
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII §7 (application to the Brauer group) from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, course notes, version 4.03 (2020), bib key `milne2020cft`, Chapter VII,
Theorem 7.1 and Proposition 7.2 (pp. 219–221).

* **Proposition 7.2, unconditional** (`prop7_2`): every central simple algebra over a number field $K$ splits over a
  cyclic cyclotomic extension. Milne's proof: Lemma 7.3 (`lemma_7_3`, proved in this library) gives a totally complex
  cyclic cyclotomic $L/K$ whose local degrees at the ramified places of the algebra are divisible by its order; the
  local classes die in $L_w$ (base change multiplies the local invariant by the degree, Tau Ceti's
  `brBaseChange_eq_zero_of_dvd_finrank`), so the class dies in every completion of $L$
  (`brLocalization_brBaseChange_eq_zero_of_forall`) and hence in $L$ by the Hasse principle (`brLocalization_injective`).
* **Theorem 7.1, concrete form** (`theorem7_1_splits`): a central simple algebra over $K$ split by every completion is
  split, from Tau Ceti's `brLocalization_injective`.

Tau Ceti's Brauer group is the cohomological one; it is identified with the Brauer group of central simple algebras by
`brauerGroupEquivBr`, compatibly with base change (`BrauerBaseChange.brauerGroupEquivBr_baseChange`,
`Ch4.baseChange_eq_tauCeti`).
-/

open IsDedekindDomain NumberField TauCeti.ClassFieldTheory
open scoped TensorProduct AdicCompletionExtension

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch7

variable {K : Type} [Field K] [NumberField K]

/-- The Brauer class of a central simple algebra. -/
abbrev brClass (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] : BrauerGroup.{0, 0} K :=
  Ch4.BrauerGroup.mk (⟨.of K A⟩ : CSA.{0, 0} K)

omit [NumberField K] in
/-- $A$ is split by $F$ exactly when its class dies in $\mathrm{Br}(F)$. -/
theorem splitsOver_iff_baseChange_eq_one (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (F : Type) [Field F] [Algebra K F] :
    SplitsOver K A F ↔ Ch4.baseChange F (brClass (K := K) A) = 1 := by
  rw [Ch4.baseChange_mk, Ch4.BrauerGroup.mk_eq_one_iff]
  constructor
  · rintro ⟨n, ⟨e⟩⟩
    refine ⟨n, fun hn => ?_, ⟨e⟩⟩
    subst hn
    have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] A) :=
      Algebra.TensorProduct.includeLeft_injective (S := K) (FaithfulSMul.algebraMap_injective K A)
    have : Subsingleton (F ⊗[K] A) := e.toEquiv.subsingleton
    exact one_ne_zero (hinj (Subsingleton.elim _ _) : (1 : F) = 0)
  · rintro ⟨n, -, ⟨e⟩⟩
    exact ⟨n, ⟨e⟩⟩

/-- In Tau Ceti's Brauer group: $A$ is split by $F$ exactly when its class dies under base change to $F$. -/
theorem splitsOver_iff_brBaseChange_eq_zero (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (F : Type) [Field F] [Algebra K F] :
    SplitsOver K A F ↔ brBaseChange K F (brauerGroupEquivBr K (Additive.ofMul (brClass (K := K) A))) = 0 := by
  rw [splitsOver_iff_baseChange_eq_one, ← Ch4.brauerGroupEquivBr_eq_zero_iff, Ch4.baseChange_eq_tauCeti,
    BrauerBaseChange.brauerGroupEquivBr_baseChange]

/-- **Theorem 7.1, concrete form** (Milne, *CFT*, Chapter VII, p. 220): a central simple algebra over a number field
$K$ that splits over $K_v$ for every place $v$ splits over $K$. From Tau Ceti's Hasse principle
`brLocalization_injective`. -/
@[kb "milne2020cft" "Ch. VII, Thm. 7.1 (concrete form, p. 220)"]
theorem theorem7_1_splits (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A]
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), SplitsOver K A (v.adicCompletion K))
    (hinf : ∀ w : InfinitePlace K, SplitsOver K A w.Completion) : SplitsOver K A K := by
  set x := brauerGroupEquivBr K (Additive.ofMul (brClass (K := K) A))
  have hx : x = 0 := by
    apply brLocalization_injective K
    rw [map_zero]
    refine Prod.ext (DFinsupp.ext fun v => ?_) (funext fun w => ?_)
    · rw [brLocalization_fst_apply]
      exact (splitsOver_iff_brBaseChange_eq_zero A _).1 (hfin v)
    · rw [brLocalization_snd_apply]
      exact (splitsOver_iff_brBaseChange_eq_zero A _).1 (hinf w)
  rw [splitsOver_iff_baseChange_eq_one, ← Ch4.brauerGroupEquivBr_eq_zero_iff, Ch4.baseChange_eq_tauCeti,
    BrauerBaseChange.brauerGroupEquivBr_baseChange]
  change brBaseChange K K x = 0
  rw [hx, map_zero]

set_option maxRecDepth 8000 in
/-- Milne's proof of Proposition 7.2 for a class of Tau Ceti's Brauer group: a totally complex cyclic cyclotomic
extension from Lemma 7.3 kills it. -/
theorem exists_cyclic_cyclotomic_brBaseChange_eq_zero (x : Br K) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : IsGalois K L),
      IsCyclic Gal(L/K) ∧ IsCyclotomicExt K L ∧ brBaseChange K L x = 0 := by
  obtain ⟨n, hn, hxn⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
    (TauCeti.ContinuousCohomology.isAddTorsion_continuousCohomology (X := unitsRep K) 1 x)
  obtain ⟨L, _, _, _, hG, hC, hcyc, hT, hdeg⟩ := lemma_7_3 K (brauerSupport K x) n hn
  have : IsTotallyComplex L := ⟨hT⟩
  refine ⟨L, inferInstance, inferInstance, inferInstance, hG, hC, hcyc, ?_⟩
  have hloc : brLocalization L (brBaseChange K L x) = 0 := by
    refine brLocalization_brBaseChange_eq_zero_of_forall K L x fun w hw => ?_
    have : Finite (𝓞 L ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    have := HeightOneSpectrum.adicCompletion_isSeparable (w.under (𝓞 K)) w
    have hdvd : n ∣ Module.finrank ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion L) := by
      rw [HeightOneSpectrum.finrank_adicCompletion]
      exact hdeg _ hw ⟨w.asIdeal, w.isPrime, inferInstance⟩
    exact brBaseChange_eq_zero_of_dvd_finrank _ _ hdvd _ (by rw [← map_nsmul, hxn, map_zero])
  exact (injective_iff_map_eq_zero (brLocalization L)).1 (brLocalization_injective L) _ hloc

/-- **Proposition 7.2, unconditional** (Milne, *CFT*, Chapter VII, p. 220): every central simple algebra over a number
field $K$ splits over a cyclic cyclotomic extension of $K$. Milne's proof, with Lemma 7.3 and Tau Ceti's Hasse
principle. -/
@[kb "milne2020cft" "Ch. VII, Prop. 7.2"]
theorem prop7_2 (K : Type) [Field K] [NumberField K] : Prop7_2 K where
  splits A _ _ _ _ _ := by
    obtain ⟨L, i1, i2, i3, i4, hC, hcyc, h⟩ := exists_cyclic_cyclotomic_brBaseChange_eq_zero
      (brauerGroupEquivBr K (Additive.ofMul (brClass (K := K) A)))
    exact ⟨L, i1, i2, i3, i4, hC, hcyc, (splitsOver_iff_brBaseChange_eq_zero A L).2 h⟩

end NumberFieldKB.MilneCFT.Ch7
