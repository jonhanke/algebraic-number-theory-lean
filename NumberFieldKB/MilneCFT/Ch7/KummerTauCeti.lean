import NumberFieldKB.MilneCFT.Ch7.KeyCase
import NumberFieldKB.MilneCFT.Ch8.HasseNormTauCeti
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Units.LocalPowerClass
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Kummer.Unramified
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Kummer.Ramification
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.ExponentNorms
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.Frobenius.DecompositionGroup
import NumberFieldKB.TauCetiPort.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.SInteger
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
# Milne, *Class Field Theory*, Chapter VII §6 and Appendix: the Kummer lemmas from the Tau Ceti port

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020), bib key `milne2020cft`, Chapter VII, §6 (pp. 215-218)
and the Appendix (Theorem A.3).

The named statements `KummerAppendix`, `Lemma6_2`, `Lemma6_3`, `Lemma6_4`, `Lemma6_9` are proved here, for all
arguments, from the ported Tau Ceti library (`NumberFieldKB/TauCetiPort/`, Apache 2.0).

Tau Ceti theorems used:
* `TauCeti.kummerField`, `TauCeti.finrank_kummerField`, `TauCeti.isAbelianGalois_kummerField`,
  `TauCeti.adjoin_pow_eq_algebraMap_kummerField_eq_top` (Kummer theory; `KummerAppendix`);
* `Set.ker_unitLocalPowerClassMap` and `Set.unitLocalPowerClassMap_eq_one_iff` (Lemma 6.3);
* `Set.unitLocalPowerClassMap_surjective` (Lemma 6.9);
* `TauCeti.ClassFieldTheory.mem_range_ideleNormMap_of_exponent_dvd`,
  `IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion_fixedField_eq_one_iff`,
  `Ideal.stabilizer_le_of_forall_isArithFrobAt_mem` (Lemma 6.4);
* `TauCeti.NumberField.isUnramifiedIn_adjoin_of_pow_eq_of_valuation_eq_one` (unramifiedness outside `S`).
-/

open IsDedekindDomain NumberField NumberFieldKB.Chebotarev NumberFieldKB.HilbertClassField
open scoped Classical TensorProduct AdicCompletionExtension NumberField.LiesOver

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT.Ch7

section Facts

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

theorem KummerSetting.neZero (h : KummerSetting p S M) : NeZero p := ⟨h.prime.ne_zero⟩

theorem KummerSetting.hasEnoughRoots (h : KummerSetting p S M) : HasEnoughRootsOfUnity K p := by
  haveI := h.neZero
  obtain ⟨ζ, hζ⟩ := h.zeta
  exact .of_card_le hζ.card_rootsOfUnity.ge

theorem KummerSetting.kummerField_eq_top (h : KummerSetting p S M) :
    TauCeti.kummerField M p (S.unit K) = ⊤ := by
  rw [TauCeti.kummerField_def]
  exact h.generates

theorem KummerSetting.isFiniteRelIndex (h : KummerSetting p S M) :
    (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex (S.unit K) := by
  haveI := h.neZero
  haveI := h.hasEnoughRoots
  haveI : Finite S := h.finite.to_subtype
  exact ⟨by
    rw [TauCeti.relIndex_range_powMonoidHom_sUnits_numberField]
    exact (pow_pos h.prime.pos _).ne'⟩

theorem KummerSetting.finiteDimensional (h : KummerSetting p S M) : FiniteDimensional K M := by
  haveI := h.neZero
  haveI := h.hasEnoughRoots
  haveI := h.isFiniteRelIndex
  have h1 : FiniteDimensional K (TauCeti.kummerField M p (S.unit K)) := inferInstance
  rw [h.kummerField_eq_top] at h1
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

/-- Two automorphisms of `M` agreeing on all `p`-th roots of `S`-units agree. -/
theorem KummerSetting.algEquiv_ext (h : KummerSetting p S M) {σ τ : Gal(M/K)}
    (hστ : ∀ y : M, ∀ u ∈ S.unit K, y ^ p = algebraMap K M (u : K) → σ y = τ y) : σ = τ := by
  have key : (σ : M →ₐ[K] M).comp (IntermediateField.val (IntermediateField.adjoin K
      {y : M | ∃ u ∈ S.unit K, y ^ p = algebraMap K M (u : K)})) =
      (τ : M →ₐ[K] M).comp (IntermediateField.val (IntermediateField.adjoin K
      {y : M | ∃ u ∈ S.unit K, y ^ p = algebraMap K M (u : K)})) := by
    apply IntermediateField.adjoin_algHom_ext K
    rintro x ⟨u, hu, hx⟩
    exact hστ x u hu hx
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin K
      {y : M | ∃ u ∈ S.unit K, y ^ p = algebraMap K M (u : K)} := by
    rw [h.generates]; trivial
  exact AlgHom.congr_fun key ⟨x, hx⟩

theorem KummerSetting.comm (h : KummerSetting p S M) (σ τ : Gal(M/K)) : σ * τ = τ * σ := by
  haveI := h.neZero
  haveI := h.hasEnoughRoots
  refine h.algEquiv_ext fun y u hu hy => ?_
  obtain ⟨z, hz⟩ := σ.exists_apply_eq_algebraMap_mul_of_pow_eq hy
  obtain ⟨w, hw⟩ := τ.exists_apply_eq_algebraMap_mul_of_pow_eq hy
  simp only [AlgEquiv.mul_apply, hz, hw, map_mul, AlgEquiv.commutes]
  ring

theorem KummerSetting.pow_eq_one (h : KummerSetting p S M) (σ : Gal(M/K)) : σ ^ p = 1 := by
  haveI := h.neZero
  haveI := h.hasEnoughRoots
  refine h.algEquiv_ext fun y u hu hy => ?_
  have hy0 : y ≠ 0 := TauCeti.ne_zero_of_pow_eq_algebraMap (a := u) hy
  have hpow (k : ℕ) : (σ ^ k) y / y = (σ y / y) ^ k := by
    induction k with
    | zero => simp [hy0]
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply_div_self_of_pow_eq _ _ hy, ih, pow_succ]
  have hone : (σ y / y) ^ p = 1 := by
    rw [div_pow, ← map_pow, hy, AlgEquiv.commutes, div_self (by simp)]
  rw [AlgEquiv.one_apply, ← div_eq_one_iff_eq hy0, hpow, hone]

end Facts

section Bridge

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

/-- Consequences of `FrobBasis` for the Frobenius elements. -/
theorem KummerSetting.frobBridge (h : KummerSetting p S M) {L : IntermediateField K M}
    {T : Finset (HeightOneSpectrum (𝓞 K))} {Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)}
    (hF : FrobBasis p L T Q) :
    (∀ v : T, frobAt K M v.1 (Q v) ∈ L.fixingSubgroup) ∧
      L.fixingSubgroup = Subgroup.closure (Set.range fun v : T => frobAt K M v.1 (Q v)) ∧
      Nat.card L.fixingSubgroup = p ^ T.card := by
  letI : CommGroup Gal(M/K) := { (inferInstance : Group Gal(M/K)) with mul_comm := h.comm }
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fact (1 < p) := ⟨h.prime.one_lt⟩
  have hprod : ∀ e : T → ZMod p,
      ((Finset.univ : Finset T).toList.map fun v => frobAt K M v.1 (Q v) ^ (e v).val).prod =
        ∏ v, frobAt K M v.1 (Q v) ^ (e v).val := fun e => Finset.prod_map_toList _ _
  have hsingle : ∀ v : T, frobAt K M v.1 (Q v) =
      ((Finset.univ : Finset T).toList.map fun w =>
        frobAt K M w.1 (Q w) ^ ((Pi.single v 1 : T → ZMod p) w).val).prod := by
    intro v
    rw [hprod, Finset.prod_eq_single v]
    · simp [ZMod.val_one]
    · intro w _ hw
      simp [Pi.single_eq_of_ne hw]
    · simp
  have hmem : ∀ v : T, frobAt K M v.1 (Q v) ∈ L.fixingSubgroup := by
    intro v
    rw [hsingle v]
    exact hF.mapsTo (Set.mem_univ _)
  refine ⟨hmem, le_antisymm ?_ ?_, ?_⟩
  · intro g hg
    obtain ⟨e, -, rfl⟩ := hF.surjOn hg
    beta_reduce
    rw [hprod]
    exact Subgroup.prod_mem _ fun v _ =>
      Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self v)) _
  · rw [Subgroup.closure_le]
    rintro _ ⟨v, rfl⟩
    exact hmem v
  · have e := hF.equiv
    have h1 : Nat.card (Set.univ : Set (T → ZMod p)) = Nat.card (L.fixingSubgroup : Set Gal(M/K)) :=
      Nat.card_congr e
    have h2 : Nat.card (Set.univ : Set (T → ZMod p)) = p ^ T.card := by
      rw [Nat.card_univ, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_coe]
    rw [← h2, h1]
    rfl

end Bridge

section Lemma63

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

/-- A primitive `p`-th root of unity of `K` is integral. -/
theorem KummerSetting.exists_integral_root (h : KummerSetting p S M) :
    ∃ ζ : 𝓞 K, IsPrimitiveRoot ζ p := by
  obtain ⟨ζ, hζ⟩ := h.zeta
  have hint : IsIntegral ℤ ζ := hζ.isIntegral h.prime.pos
  refine ⟨⟨ζ, hint⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 K) K) hζ
    (FaithfulSMul.algebraMap_injective (𝓞 K) K)

theorem KummerSetting.not_mem_of_disjoint (h : KummerSetting p S M)
    {T : Finset (HeightOneSpectrum (𝓞 K))} (hTS : Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S)
    (v : T) : (p : 𝓞 K) ∉ v.1.asIdeal := fun hv =>
  Set.disjoint_left.mp hTS v.2 (h.dvd v.1 hv)

/-- The hypotheses of Tau Ceti's `ker_unitLocalPowerClassMap`, packaged. -/
theorem KummerSetting.lemma63_aux (h : KummerSetting p S M) {L : IntermediateField K M}
    {T : Finset (HeightOneSpectrum (𝓞 K))} {Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)}
    (hTS : Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S) (hF : FrobBasis p L T Q)
    (a : Kˣ) (ha : a ∈ S.unit K) :
    ((∃ y : L, y ^ p = algebraMap K L (a : K)) ↔ ∀ v ∈ T, IsPowAt v p (a : K)) := by
  obtain ⟨-, hL, -⟩ := h.frobBridge hF
  obtain ⟨ζ, hζ⟩ := h.exists_integral_root
  have hn : p ≠ 0 := h.prime.ne_zero
  haveI : ∀ v : (T : Set (HeightOneSpectrum (𝓞 K))), (Q v).1.IsPrime := fun v => (Q v).2.1
  haveI : ∀ v : (T : Set (HeightOneSpectrum (𝓞 K))), (Q v).1.LiesOver v.1.asIdeal :=
    fun v => (Q v).2.2
  have hker := Set.ker_unitLocalPowerClassMap S (T : Set (HeightOneSpectrum (𝓞 K))) hTS.symm hn L
    (fun v : (T : Set (HeightOneSpectrum (𝓞 K))) => frobAt K M v.1 (Q v)) (fun v => (Q v).1)
    (fun v => isArithFrobAt_frobAt K M v.1 (Q v)) hL hζ (fun v => h.not_mem_of_disjoint hTS v) h.roots
  have hu := Set.unitLocalPowerClassMap_eq_one_iff S (T : Set (HeightOneSpectrum (𝓞 K))) hTS.symm hn
    ⟨a, ha⟩
  have hmem : (⟨a, ha⟩ : S.unit K) ∈
      (Set.unitLocalPowerClassMap S (T : Set (HeightOneSpectrum (𝓞 K))) hTS.symm p).ker ↔
      (∃ b : Lˣ, b ^ p = Units.map (algebraMap K L).toMonoidHom a) := by
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.mem_range]
    rfl
  rw [MonoidHom.mem_ker, hu] at hmem
  constructor
  · rintro ⟨y, hy⟩ v hv
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hy
      exact a.ne_zero (by simpa using hy.symm)
    have := hmem.2 ⟨Units.mk0 y hy0, Units.ext hy⟩ ⟨v, hv⟩
    exact this
  · intro hv
    obtain ⟨b, hb⟩ := hmem.1 fun v => hv v.1 v.2
    exact ⟨b, congrArg Units.val hb⟩

end Lemma63

section Lemma69

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

/-- Surjectivity of Tau Ceti's local power-class map gives surjectivity of `sUnitsToLocalQuot`
(the targets are the same quotient of the same subgroup of `(K_v)ˣ`). -/
theorem sUnitsToLocalQuot_surjective_of {S T : Set (HeightOneSpectrum (𝓞 K))} (hST : Disjoint S T)
    {n : ℕ} (hsurj : Function.Surjective (Set.unitLocalPowerClassMap S T hST n)) :
    Function.Surjective (sUnitsToLocalQuot S T hST n) := by
  intro x
  choose g hg using fun v : T => QuotientGroup.mk_surjective (x v)
  have hgv : ∀ v : T, (g v).1 ∈ TauCeti.unitFiltration (v.1.adicCompletion K) 0 := fun v =>
    (HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v.1).2
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.1 (g v).2)
  obtain ⟨u, hu⟩ := hsurj fun v => QuotientGroup.mk ⟨(g v).1, hgv v⟩
  refine ⟨u, funext fun v => ?_⟩
  rw [← hg v]
  have h1 := congrFun hu v
  rw [Set.unitLocalPowerClassMap_apply] at h1
  obtain ⟨b, hb⟩ := QuotientGroup.eq.1 h1
  show QuotientGroup.mk (sUnitToLocal S v.1 (Set.disjoint_right.mp hST v.2) u) = _
  refine QuotientGroup.eq.2 ⟨⟨b.1, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.2
    ((HeightOneSpectrum.mem_unitFiltration_zero_adicCompletion_iff v.1).1 b.2)⟩, ?_⟩
  have hb' := congrArg Subtype.val hb
  exact Subtype.ext hb'

/-- **Lemma 6.3** (Milne, *CFT*, Chapter VII, p. 216), proved from Tau Ceti's
`Set.ker_unitLocalPowerClassMap`. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.3"]
theorem lemma6_3 (K : Type) [Field K] [NumberField K] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_3 p S M where
  iff h _ _ _ hTS _ hF a ha := h.lemma63_aux hTS hF a ha

/-- **Lemma 6.9** (Milne, *CFT*, Chapter VII, p. 218), proved from Tau Ceti's
`Set.unitLocalPowerClassMap_surjective`. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.9"]
theorem lemma6_9 (K : Type) [Field K] [NumberField K] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_9 p S M where
  surjective h L T Q hTS _ hF := by
    obtain ⟨-, hL, hcard⟩ := h.frobBridge hF
    obtain ⟨ζ, hζ⟩ := h.exists_integral_root
    have hn : p ≠ 0 := h.prime.ne_zero
    haveI := h.finiteDimensional
    haveI : Finite S := h.finite.to_subtype
    haveI : Finite (T : Set (HeightOneSpectrum (𝓞 K))) := T.finite_toSet.to_subtype
    haveI : ∀ v : (T : Set (HeightOneSpectrum (𝓞 K))), (Q v).1.IsPrime := fun v => (Q v).2.1
    haveI : ∀ v : (T : Set (HeightOneSpectrum (𝓞 K))), (Q v).1.LiesOver v.1.asIdeal :=
      fun v => (Q v).2.2
    have hL' : L.fixingSubgroup = Subgroup.closure
        (Set.range fun v : (T : Set (HeightOneSpectrum (𝓞 K))) => frobAt K M v.1 (Q v)) := hL
    have hT : p ^ Nat.card (T : Set (HeightOneSpectrum (𝓞 K))) ≤ Module.finrank L M := by
      rw [← IsGalois.card_fixingSubgroup_eq_finrank L, hcard]
      simp
    exact sUnitsToLocalQuot_surjective_of hTS.symm
      (Set.unitLocalPowerClassMap_surjective S (T : Set (HeightOneSpectrum (𝓞 K))) hTS.symm hn L
        (fun v : (T : Set (HeightOneSpectrum (𝓞 K))) => frobAt K M v.1 (Q v)) (fun v => (Q v).1)
        (fun v => isArithFrobAt_frobAt K M v.1 (Q v)) hL' hζ
        (fun v => h.not_mem_of_disjoint hTS v) h.roots h.kummerField_eq_top hT)

end Lemma69

section Lemma64

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

/-- The Kummer extension `M` is unramified outside `S`: the inertia groups at primes outside `S` are trivial. -/
theorem KummerSetting.inertia_le_bot (h : KummerSetting p S M) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ S) (Q : Ideal (𝓞 M)) (hQ : Q ∈ v.asIdeal.primesOver (𝓞 M)) :
    Q.inertia (M ≃ₐ[K] M) ≤ ⊥ := by
  have hn : (p : 𝓞 K) ∉ v.asIdeal := fun hp => hv (h.dvd v hp)
  have hur := TauCeti.NumberField.isUnramifiedIn_adjoin_of_pow_eq_of_valuation_eq_one
    (K := K) (M := M) (n := p)
    (s := {y : M | ∃ u ∈ S.unit K, y ^ p = algebraMap K M (u : K)}) (v := v)
    (fun α ⟨u, hu, hα⟩ => ⟨u, hα, Set.unit_valuation_eq_one S K ⟨u, hu⟩ hv⟩) hn
  have := (Ideal.isUnramifiedIn_iff_forall_inertia_le v.asIdeal _).1 hur Q hQ
  rwa [h.generates, IntermediateField.fixingSubgroup_top] at this

theorem KummerSetting.kummerE_le (h : KummerSetting p S M) {L : IntermediateField K M}
    {T : Finset (HeightOneSpectrum (𝓞 K))} {Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)}
    (hunr : ∀ v ∈ T, v ∈ unramifiedPrimes K M) (hF : FrobBasis p L T Q) :
    kummerE S T p ≤ normIdeles K L := by
  obtain ⟨hmem, -, -⟩ := h.frobBridge hF
  have hfin := h.finiteDimensional
  obtain ⟨H, rfl⟩ : ∃ H : Subgroup Gal(M/K), IntermediateField.fixedField H = L :=
    ⟨_, IsGalois.fixedField_fixingSubgroup L⟩
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    IntermediateField.fixingSubgroup_fixedField H
  rw [hfix] at hmem
  haveI : H.Normal := ⟨fun n hn g => by
    rw [h.comm g n, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  haveI : IsGalois K (IntermediateField.fixedField H) := inferInstance
  haveI : NumberField (IntermediateField.fixedField H) := NumberField.of_module_finite K _
  have hexp : Monoid.exponent (IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H) ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro τ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective M τ
    rw [← map_pow, h.pow_eq_one, map_one]
  have hT : ∀ v ∈ (T : Set (HeightOneSpectrum (𝓞 K))),
      ∃ w : {w : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) //
        w.asIdeal.LiesOver v.asIdeal},
        Module.finrank (v.adicCompletion K)
          (w.1.adicCompletion (IntermediateField.fixedField H)) = 1 := by
    intro v hv
    have hvT : v ∈ T := hv
    set Qv := Q ⟨v, hvT⟩ with hQv
    haveI : Qv.1.IsPrime := Qv.2.1
    haveI : Qv.1.LiesOver v.asIdeal := Qv.2.2
    haveI hu1 : (Qv.1.under (𝓞 (IntermediateField.fixedField H))).LiesOver v.asIdeal :=
      ⟨by rw [Ideal.under_under]; exact Qv.2.2.over⟩
    let wM : HeightOneSpectrum (𝓞 M) :=
      ⟨Qv.1, Qv.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Qv.1⟩
    let u : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) :=
      ⟨Qv.1.under (𝓞 (IntermediateField.fixedField H)), inferInstance,
        Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _⟩
    haveI : wM.asIdeal.LiesOver v.asIdeal := Qv.2.2
    haveI : u.asIdeal.LiesOver v.asIdeal := hu1
    haveI : wM.asIdeal.LiesOver u.asIdeal :=
      inferInstanceAs (Qv.1.LiesOver (Qv.1.under (𝓞 (IntermediateField.fixedField H))))
    refine ⟨⟨u, hu1⟩, ?_⟩
    refine (HeightOneSpectrum.finrank_adicCompletion_fixedField_eq_one_iff v wM H u).2 ?_
    refine Ideal.stabilizer_le_of_forall_isArithFrobAt_mem Qv.1 wM.ne_bot ?_
    intro σ hσ
    rw [← frobAt_eq_of_isArithFrobAt K M (hunr v hvT) Qv hσ]
    exact hmem ⟨v, hvT⟩
  have hU : ∀ v ∉ S, v ∉ (T : Set (HeightOneSpectrum (𝓞 K))) →
      ∃ w : {w : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) //
        w.asIdeal.LiesOver v.asIdeal}, Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
    intro v hvS _
    have hur : Algebra.IsUnramifiedIn (𝓞 (IntermediateField.fixedField H)) v.asIdeal :=
      (Ideal.isUnramifiedIn_iff_forall_inertia_le v.asIdeal _).2 fun Q hQ =>
        (h.inertia_le_bot hvS Q hQ).trans bot_le
    obtain ⟨P, hP, hPv⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (IntermediateField.fixedField H))
        v.asIdeal
    refine ⟨⟨⟨P, hP.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, hPv⟩, ?_⟩
    exact hur P hP.isPrime hPv
  have hp := h.prime.pos
  rw [Ch8.normIdeles_eq_range_ideleNormMap K (IntermediateField.fixedField H)]
  intro x hx
  obtain ⟨hx1, hx2, hx3⟩ := hx
  refine TauCeti.ClassFieldTheory.mem_range_ideleNormMap_of_exponent_dvd K
    (IntermediateField.fixedField H) hexp (S := S) (T := (T : Set (HeightOneSpectrum (𝓞 K)))) hT hU
    ?_ ?_ ?_
  · intro v hv
    rw [TauCeti.mem_powerSubgroup_iff]
    obtain ⟨d, hd⟩ := (mem_range_pow_iff hp (v.ideleFiniteCoord x)).2 (hx2 v hv)
    exact ⟨d, hd⟩
  · intro v hvS hvT
    exact hx3 v hvS hvT
  · intro w
    rw [TauCeti.mem_powerSubgroup_iff]
    obtain ⟨d, hd⟩ := (mem_range_pow_iff hp (w.ideleInfiniteCoord x)).2 (hx1 w)
    exact ⟨d, hd⟩

/-- **Lemma 6.4** (Milne, *CFT*, Chapter VII, p. 216), proved from Tau Ceti's
`TauCeti.ClassFieldTheory.mem_range_ideleNormMap_of_exponent_dvd`. -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.4"]
theorem lemma6_4 (K : Type) [Field K] [NumberField K] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_4 p S M where
  le h _ _ _ _ hunr hF := h.kummerE_le hunr hF

end Lemma64

section Appendix

/-- **Kummer theory for `S`-units** (Milne, *CFT*, Chapter VII, Appendix, Theorem A.3 for `B = U(S) K^{×p}`),
proved from Tau Ceti's Kummer theory with `E` an algebraic closure of `K` and `M = K(U(S)^{1/p}) ⊆ E`. -/
@[kb "milne2020cft" "Ch. VII, App., Thm. A.3"]
theorem kummerAppendix (K : Type) [Field K] [NumberField K] : KummerAppendix K where
  exists_ext p S hp hz hS hdvd hcl := by
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := hz
    haveI : HasEnoughRootsOfUnity K p := .of_card_le hζ.card_rootsOfUnity.ge
    haveI : Finite S := hS.to_subtype
    haveI : (powMonoidHom p : Kˣ →* Kˣ).range.IsFiniteRelIndex (S.unit K) :=
      ⟨by
        rw [TauCeti.relIndex_range_powMonoidHom_sUnits_numberField]
        exact (pow_pos hp.pos _).ne'⟩
    have hroots : ∀ a ∈ S.unit K, ∃ x : AlgebraicClosure K, x ^ p = algebraMap K _ (a : K) :=
      fun a _ => IsAlgClosed.exists_pow_nat_eq _ hp.pos
    refine ⟨TauCeti.kummerField (AlgebraicClosure K) p (S.unit K), inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, ?_, ?_⟩
    · intro σ τ
      exact Std.Commutative.comm σ τ
    · refine ⟨hp, ⟨ζ, hζ⟩, hS, hdvd, hcl, ?_, ?_⟩
      · intro u hu
        obtain ⟨x, hx⟩ := hroots u hu
        exact ⟨⟨x, TauCeti.mem_kummerField_of_pow_eq hu hx⟩, Subtype.ext (by simpa using hx)⟩
      · exact TauCeti.adjoin_pow_eq_algebraMap_kummerField_eq_top
    · exact TauCeti.finrank_kummerField hroots

end Appendix

section Lemma62

/-- Infinitely many choices allow an injective selection. -/
theorem exists_injective_mem_of_infinite {ι α : Type*} [Finite ι] (A : ι → Set α)
    (hA : ∀ i, (A i).Infinite) : ∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ A i := by
  classical
  haveI := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
  · exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  obtain ⟨a0⟩ := (hA i0).nonempty
  have key : ∀ s : Finset ι, ∃ f : ι → α, Set.InjOn f (s : Set ι) ∧ ∀ i ∈ s, f i ∈ A i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ => a0, by simp, by simp⟩
    | insert a s ha ih =>
      obtain ⟨f, hinj, hmem⟩ := ih
      obtain ⟨x, hxA, hx⟩ := ((hA a).sdiff (s.finite_toSet.image f)).nonempty
      refine ⟨Function.update f a x, ?_, ?_⟩
      · intro i hi j hj hij
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
        rcases hi with rfl | hi <;> rcases hj with rfl | hj
        · rfl
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hj)] at hij
          exact absurd ⟨j, hj, hij.symm⟩ hx
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi)] at hij
          exact absurd ⟨i, hi, hij⟩ hx
        · rw [Function.update_of_ne (by rintro rfl; exact ha hi),
            Function.update_of_ne (by rintro rfl; exact ha hj)] at hij
          exact hinj hi hj hij
      · intro i hi
        by_cases hia : i = a
        · subst hia; rw [Function.update_self]; exact hxA
        · rw [Function.update_of_ne hia]
          exact hmem i ((Finset.mem_insert.1 hi).resolve_left hia)
  obtain ⟨f, hinj, hmem⟩ := key Finset.univ
  exact ⟨f, fun i j h => hinj (by simp) (by simp) h, fun i => hmem i (by simp)⟩

/-- A finite `𝔽_p`-vector space has a finite basis (stated without the `Basis` coercion). -/
theorem exists_zmod_basis (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → V),
      Function.Bijective (fun e : ι → ZMod p => ∑ i, (e i).val • g i) := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod p) V
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  haveI : Finite (Module.Basis.ofVectorSpaceIndex (ZMod p) V) := Module.Finite.finite_basis b
  haveI : Fintype (Module.Basis.ofVectorSpaceIndex (ZMod p) V) := Fintype.ofFinite _
  refine ⟨↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V), inferInstance, fun i => b i, ?_⟩
  have : (fun e : ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) V) → ZMod p =>
      ∑ i, (e i).val • b i) = b.equivFun.symm := by
    funext e
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  rw [this]
  exact b.equivFun.symm.bijective

/-- A subgroup of a finite abelian group of exponent `p` has an `𝔽_p`-basis in the sense of `FrobBasis`. -/
theorem exists_basis_of_exponent {p : ℕ} (hp : p.Prime) {G : Type} [CommGroup G] [Finite G]
    (hpow : ∀ g : G, g ^ p = 1) (H : Subgroup G) :
    ∃ (ι : Type) (_ : Fintype ι) (g : ι → G),
      Set.BijOn (fun e : ι → ZMod p => ∏ i, g i ^ (e i).val) Set.univ (H : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Module (ZMod p) (Additive H) := AddCommMonoid.zmodModule (n := p) (fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul]
    exact Subtype.ext (by simpa using hpow (Additive.toMul x : H)))
  haveI : Finite (Additive H) := inferInstanceAs (Finite H)
  obtain ⟨ι, hι, g, hg⟩ := exists_zmod_basis p (V := Additive H)
  refine ⟨ι, hι, fun i => ((Additive.toMul (g i) : H) : G), ?_⟩
  have hΨ : ∀ e : ι → ZMod p, ∏ i, ((Additive.toMul (g i) : H) : G) ^ (e i).val =
      H.subtype (Additive.toMul (∑ i, (e i).val • g i)) := by
    intro e
    rw [toMul_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [toMul_nsmul]
    simp
  refine ⟨fun e _ => ?_, fun e _ e' _ h => ?_, fun y hy => ?_⟩
  · beta_reduce
    rw [hΨ e]
    exact (Additive.toMul (∑ i, (e i).val • g i)).2
  · beta_reduce at h
    rw [hΨ, hΨ] at h
    exact hg.1 (Additive.toMul.injective (H.subtype_injective h))
  · obtain ⟨e, he⟩ := hg.2 (Additive.ofMul ⟨y, hy⟩)
    refine ⟨e, trivial, ?_⟩
    beta_reduce
    rw [hΨ]
    have he' : (∑ i, (e i).val • g i) = Additive.ofMul ⟨y, hy⟩ := he
    rw [he']
    simp

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [Field M] [NumberField M] [Algebra K M] [IsGalois K M]

/-- **Lemma 6.2** (existence of `T`), by the unconditional Chebotarev density theorem. -/
theorem KummerSetting.exists_T (h : KummerSetting p S M) (L : IntermediateField K M) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (Q : ∀ v : T, v.1.asIdeal.primesOver (𝓞 M)),
      Disjoint (T : Set (HeightOneSpectrum (𝓞 K))) S ∧ (∀ v ∈ T, v ∈ unramifiedPrimes K M) ∧
        FrobBasis p L T Q := by
  classical
  haveI := h.finiteDimensional
  letI : CommGroup Gal(M/K) := { (inferInstance : Group Gal(M/K)) with mul_comm := h.comm }
  obtain ⟨ι, hι, g, hg⟩ := exists_basis_of_exponent (G := Gal(M/K)) h.prime h.pow_eq_one
    L.fixingSubgroup
  let A : ι → Set (HeightOneSpectrum (𝓞 K)) := fun i =>
    {𝔭 | 𝔭 ∈ unramifiedPrimes K M ∧ ∃ Q : 𝔭.asIdeal.primesOver (𝓞 M), frobAt K M 𝔭 Q = g i} \ S
  have hA : ∀ i, (A i).Infinite := fun i =>
    (NumberFieldKB.HilbertClassField.setOf_frobAt_eq_infinite K M (g i)).sdiff h.finite
  obtain ⟨π, hπinj, hπ⟩ := exists_injective_mem_of_infinite A hA
  let T : Finset (HeightOneSpectrum (𝓞 K)) := Finset.univ.image π
  let eT : ι ≃ T := Equiv.ofBijective
    (fun i => ⟨π i, Finset.mem_image_of_mem π (Finset.mem_univ i)⟩)
    ⟨fun i j hij => hπinj (congrArg Subtype.val hij), fun v => by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 v.2
      exact ⟨i, Subtype.ext hi⟩⟩
  have hQ' : ∀ v : T, ∃ Q : v.1.asIdeal.primesOver (𝓞 M), frobAt K M v.1 Q = g (eT.symm v) := by
    intro v
    obtain ⟨i, rfl⟩ := eT.surjective v
    rw [Equiv.symm_apply_apply]
    exact (hπ i).1.2
  choose Q hQ using hQ'
  refine ⟨T, Q, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
    exact (hπ i).2
  · intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
    exact (hπ i).1.1
  · have hfun : ∀ e : T → ZMod p,
        ((Finset.univ : Finset T).toList.map fun v => frobAt K M v.1 (Q v) ^ (e v).val).prod =
          ∏ i, g i ^ (e (eT i)).val := by
      intro e
      rw [Finset.prod_map_toList, ← Equiv.prod_comp eT]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hQ (eT i), Equiv.symm_apply_apply]
    have hc : Function.Bijective (fun e : T → ZMod p => fun i => e (eT i)) := by
      constructor
      · intro e e' hee
        funext v
        obtain ⟨i, rfl⟩ := eT.surjective v
        exact congrFun hee i
      · intro d
        exact ⟨fun v => d (eT.symm v), by funext i; simp⟩
    have := hg.comp (Set.bijOn_univ.2 hc)
    refine this.congr fun e _ => ?_
    simp only [Function.comp]
    rw [hfun e]

/-- **Lemma 6.2** (Milne, *CFT*, Chapter VII, p. 215), proved from the unconditional Chebotarev density theorem
(`NumberFieldKB.HilbertClassField.setOf_frobAt_eq_infinite`). -/
@[kb "milne2020cft" "Ch. VII, Lemma 6.2"]
theorem lemma6_2 (K : Type) [Field K] [NumberField K] (p : ℕ) (S : Set (HeightOneSpectrum (𝓞 K)))
    (M : Type) [Field M] [NumberField M] [Algebra K M] [IsGalois K M] : Lemma6_2 p S M where
  exists_T h L := h.exists_T L

end Lemma62

end NumberFieldKB.MilneCFT.Ch7
