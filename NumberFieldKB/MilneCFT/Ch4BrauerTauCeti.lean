import NumberFieldKB.MilneCFT.Ch4Global
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Brauer.Sequence
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Global.Brauer.Exactness
import NumberFieldKB.TauCetiPort.NumberTheory.ClassFieldTheory.Brauer.CentralSimple.Basic
import NumberFieldKB.MilneCFT.Ch4BrauerBaseChange
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Milne, *Class Field Theory*, IV Example 2.14(e) = VIII Theorem 4.2 (the fundamental exact sequence), from Tau Ceti

Tau Ceti proves the fundamental exact sequence $0\to\mathrm{Br}(K)\to\bigoplus_v\mathrm{Br}(K_v)\to\mathbb Q/\mathbb Z\to0$
for its cohomological Brauer group `TauCeti.ClassFieldTheory.Br K` $=H^2(G_K,(K^{\mathrm s})^\times)$, with
localization `brBaseChange` (`brLocalization_injective`, `sumLocalInv_brLocalization_eq_zero`,
`exists_br_of_sum_eq_zero`, `sumLocalInv_surjective`), and identifies Mathlib's Brauer group of central simple algebras
with it through crossed products (`brauerGroupEquivBr`). Our statement `Ch4.Example2_14e` is for Mathlib's
`BrauerGroup` with the base change $[A]\mapsto[A\otimes_KK_v]$ (`Ch4.baseChange`).

Tau Ceti proves that the crossed-product identification commutes with base change only for finite extensions. The
statement for the completions of $K$ was the named input `Ch4.BrauerBaseChangeTauCeti K`; it is now proved
(`Ch4.brauerBaseChangeTauCeti`) from `BrauerBaseChange.brauerGroupEquivBr_baseChange`
(MilneCFT/Ch4BrauerBaseChange.lean), which holds for every field extension.

Proved here: `Ch4.example2_14e_of_brauerBaseChange` (Example 2.14(e) from that statement) and the unconditional
`Ch4.example2_14e`. The local invariants are Tau
Ceti's `invMap` (finite places) and `infiniteInvMap` (infinite places) read on `BrauerGroup` through
`brauerGroupEquivBr`, with values in $\mathbb Q/\mathbb Z$ through `addCircleEquivQZ`.
-/

open IsDedekindDomain NumberField TauCeti.ClassFieldTheory

noncomputable section

namespace NumberFieldKB.MilneCFT.Ch4

variable (K : Type) [Field K] [NumberField K]

/-- **The crossed-product identification commutes with base change to the completions** (named input; Gille–Szamuely,
§4.4 [unverified locator]): for every place of $K$, Tau Ceti's `brauerGroupEquivBr` carries the base change
$[A]\mapsto[A\otimes_KK_v]$ of central simple algebras to Tau Ceti's cohomological base change `brBaseChange`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §3 (crossed products and base change; input) [unverified locator]"]
structure BrauerBaseChangeTauCeti : Prop where
  finite : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : BrauerGroup.{0, 0} K),
    brauerGroupEquivBr (v.adicCompletion K) (Additive.ofMul (baseChange (v.adicCompletion K) x)) =
      brBaseChange K (v.adicCompletion K) (brauerGroupEquivBr K (Additive.ofMul x))
  infinite : ∀ (w : InfinitePlace K) (x : BrauerGroup.{0, 0} K),
    brauerGroupEquivBr w.Completion (Additive.ofMul (baseChange w.Completion x)) =
      brBaseChange K w.Completion (brauerGroupEquivBr K (Additive.ofMul x))

/-- $\mathbb Q/\mathbb Z$ as `AddCircle (1 : ℚ)` (Tau Ceti) is our `QZ`. -/
def addCircleEquivQZ : AddCircle (1 : ℚ) ≃+ QZ :=
  QuotientAddGroup.quotientAddEquivOfEq (by
    ext q
    simp only [AddSubgroup.mem_zmultiples_iff, AddMonoidHom.mem_range, Int.coe_castAddHom, zsmul_one])

theorem finsum_addCircleEquivQZ {ι : Type*} (f : ι → AddCircle (1 : ℚ)) (S : Finset ι)
    (hS : ∀ i ∉ S, f i = 0) : ∑ᶠ i, addCircleEquivQZ (f i) = addCircleEquivQZ (∑ i ∈ S, f i) := by
  rw [finsum_eq_sum_of_support_subset (s := S) _ (fun i hi => by
    by_contra h
    exact hi (show addCircleEquivQZ (f i) = 0 by rw [hS i h, map_zero])), map_sum]

/-- The local invariant at a finite place, on Mathlib's Brauer group. -/
def invFin (v : HeightOneSpectrum (𝓞 K)) : Additive (BrauerGroup.{0, 0} (v.adicCompletion K)) →+ QZ :=
  addCircleEquivQZ.toAddMonoidHom.comp
    ((invMap (v.adicCompletion K)).toAddMonoidHom.comp (brauerGroupEquivBr (v.adicCompletion K)).toAddMonoidHom)

/-- The local invariant at an infinite place, on Mathlib's Brauer group. -/
def invInf (w : InfinitePlace K) : Additive (BrauerGroup.{0, 0} w.Completion) →+ QZ :=
  addCircleEquivQZ.toAddMonoidHom.comp
    ((infiniteInvMap w).comp (brauerGroupEquivBr w.Completion).toAddMonoidHom)

theorem invFin_apply (v : HeightOneSpectrum (𝓞 K)) (y : Additive (BrauerGroup.{0, 0} (v.adicCompletion K))) :
    invFin K v y = addCircleEquivQZ (invMap (v.adicCompletion K) (brauerGroupEquivBr _ y)) := rfl

theorem invInf_apply (w : InfinitePlace K) (y : Additive (BrauerGroup.{0, 0} w.Completion)) :
    invInf K w y = addCircleEquivQZ (infiniteInvMap w (brauerGroupEquivBr _ y)) := rfl

variable {K}

theorem brauerGroupEquivBr_eq_zero_iff {F : Type} [Field F] (y : BrauerGroup.{0, 0} F) :
    brauerGroupEquivBr F (Additive.ofMul y) = 0 ↔ y = 1 := by
  rw [map_eq_zero_iff _ (brauerGroupEquivBr F).injective]
  rfl

/-- **Example 2.14(e) (Theorem VIII.4.2), from the named comparison `BrauerBaseChangeTauCeti`** (Milne, *CFT*, IV,
Example 2.14(e), p. 130): the sequence $0\to\mathrm{Br}(K)\to\bigoplus_v\mathrm{Br}(K_v)\to\mathbb Q/\mathbb Z\to0$ is
exact. From Tau Ceti's fundamental exact sequence (ported). -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(e), p. 130"]
theorem example2_14e_of_brauerBaseChange (hB : BrauerBaseChangeTauCeti K) : Example2_14e K := by
  classical
  set e := fun F [Field F] => brauerGroupEquivBr.{0} F
  have hfin : ∀ v (x : BrauerGroup.{0, 0} K), invFin K v (Additive.ofMul (baseChange (v.adicCompletion K) x)) =
      addCircleEquivQZ (finiteInvAt K v (brauerGroupEquivBr K (Additive.ofMul x))) := fun v x => by
    rw [invFin_apply, hB.finite, finiteInvAt_apply]
  have hinf : ∀ w (x : BrauerGroup.{0, 0} K), invInf K w (Additive.ofMul (baseChange w.Completion x)) =
      addCircleEquivQZ (infiniteInvAt K w (brauerGroupEquivBr K (Additive.ofMul x))) := fun w x => by
    rw [invInf_apply, hB.infinite, infiniteInvAt_apply]
  refine ⟨invFin K, invInf K, fun v => ?_, fun w => ?_, fun x => ?_, ?_, fun x => ?_, ?_, ?_⟩
  · exact addCircleEquivQZ.bijective.comp
      ((invMap (v.adicCompletion K)).bijective.comp (brauerGroupEquivBr (v.adicCompletion K)).bijective)
  · exact addCircleEquivQZ.injective.comp
      ((infiniteInvMap_injective w).comp (brauerGroupEquivBr w.Completion).injective)
  · -- finitely many nonzero components
    refine (hasFiniteSupport_finiteInvAt K (brauerGroupEquivBr K (Additive.ofMul x))).subset fun v hv => ?_
    rw [Function.mem_support, Ne, finiteInvAt_eq_zero_iff, ← hB.finite, brauerGroupEquivBr_eq_zero_iff]
    exact hv
  · -- injectivity
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hloc : brLocalization K (brauerGroupEquivBr K (Additive.ofMul x)) =
        brLocalization K (brauerGroupEquivBr K (Additive.ofMul y)) := by
      refine Prod.ext (DFinsupp.ext fun v => ?_) (funext fun w => ?_)
      · rw [brLocalization_fst_apply, brLocalization_fst_apply, ← hB.finite, ← hB.finite,
          congrFun h1 v]
      · rw [brLocalization_snd_apply, brLocalization_snd_apply, ← hB.infinite, ← hB.infinite,
          congrFun h2 w]
    exact Additive.ofMul.injective ((brauerGroupEquivBr K).injective (brLocalization_injective K hloc))
  · -- the composite is zero
    set z := brauerGroupEquivBr K (Additive.ofMul x)
    have hS : ∀ v ∉ brauerSupport K z, finiteInvAt K v z = 0 := fun v hv =>
      finiteInvAt_eq_zero_of_notMem_brauerSupport K hv
    have e1 : ∑ᶠ v, invFin K v (Additive.ofMul (baseChange (v.adicCompletion K) x)) =
        addCircleEquivQZ (∑ v ∈ brauerSupport K z, finiteInvAt K v z) :=
      (finsum_congr (fun v => hfin v x)).trans (finsum_addCircleEquivQZ _ (brauerSupport K z) hS)
    have e2 : ∑ w, invInf K w (Additive.ofMul (baseChange w.Completion x)) =
        addCircleEquivQZ (∑ w, infiniteInvAt K w z) :=
      (Finset.sum_congr rfl (fun w _ => hinf w x)).trans (map_sum _ _ _).symm
    refine (congrArg₂ (· + ·) e1 e2).trans ?_
    rw [← map_add, ← sumLocalInv_brLocalization K z subset_rfl, sumLocalInv_brLocalization_eq_zero, map_zero]
  · -- exactness in the middle
    intro y z hy hsum
    set S := hy.toFinset
    let f : HeightOneSpectrum (𝓞 K) → AddCircle (1 : ℚ) := fun v =>
      invMap (v.adicCompletion K) (brauerGroupEquivBr _ (Additive.ofMul (y v)))
    let g : InfinitePlace K → AddCircle (1 : ℚ) := fun w =>
      infiniteInvMap w (brauerGroupEquivBr _ (Additive.ofMul (z w)))
    have hfS : ∀ v ∉ S, f v = 0 := fun v hv => by
      have : y v = 1 := by
        by_contra h
        exact hv (hy.mem_toFinset.mpr h)
      show invMap _ (brauerGroupEquivBr _ (Additive.ofMul (y v))) = 0
      rw [this, ofMul_one, map_zero, map_zero]
    have hgr : ∀ w : InfinitePlace K, w.IsReal → g w ∈ AddSubgroup.torsionBy (AddCircle (1 : ℚ)) 2 :=
      fun w hw => by
        have := range_infiniteInvMap_of_isReal w hw
        have hm : g w ∈ Set.range (infiniteInvMap w) := ⟨_, rfl⟩
        rw [this] at hm
        exact hm
    have hgc : ∀ w : InfinitePlace K, w.IsComplex → g w = 0 := fun w hw =>
      infiniteInvMap_eq_zero_of_isComplex w hw _
    have hsum' : ∑ v ∈ S, f v + ∑ w, g w = 0 := by
      apply addCircleEquivQZ.injective
      rw [map_add, map_zero, ← finsum_addCircleEquivQZ f S hfS, map_sum]
      exact (congrArg₂ (· + ·) (finsum_congr fun v => (invFin_apply K v _).symm)
        (Finset.sum_congr rfl fun w _ => (invInf_apply K w _).symm)).trans hsum
    obtain ⟨x', hx'f, hx'g⟩ := exists_br_of_sum_eq_zero K S f hfS g hgr hgc hsum'
    refine ⟨Additive.toMul ((brauerGroupEquivBr K).symm x'), fun v => ?_, fun w => ?_⟩
    · apply Additive.ofMul.injective
      apply (brauerGroupEquivBr (v.adicCompletion K)).injective
      apply (invMap (v.adicCompletion K)).injective
      rw [hB.finite, ofMul_toMul, AddEquiv.apply_symm_apply, ← finiteInvAt_apply, hx'f]
    · apply Additive.ofMul.injective
      apply (brauerGroupEquivBr w.Completion).injective
      apply infiniteInvMap_injective w
      rw [hB.infinite, ofMul_toMul, AddEquiv.apply_symm_apply, ← infiniteInvAt_apply, hx'g]
  · -- surjectivity of the sum
    intro q
    obtain ⟨Y, hY⟩ := sumLocalInv_surjective K (addCircleEquivQZ.symm q)
    refine ⟨fun v => Additive.toMul ((brauerGroupEquivBr (v.adicCompletion K)).symm (Y.1 v)),
      fun w => Additive.toMul ((brauerGroupEquivBr w.Completion).symm (Y.2 w)), ?_, ?_⟩
    · refine (Y.1.support.finite_toSet).subset fun v hv => ?_
      rw [Finset.mem_coe, DFinsupp.mem_support_iff]
      intro h0
      apply hv
      show Additive.toMul ((brauerGroupEquivBr (v.adicCompletion K)).symm (Y.1 v)) = 1
      rw [h0, map_zero]
      rfl
    · have hS : ∀ v ∉ Y.1.support, Y.1 v = 0 := fun v hv => DFinsupp.notMem_support_iff.mp hv
      have h1 : ∀ v, invFin K v ((brauerGroupEquivBr (v.adicCompletion K)).symm (Y.1 v)) =
          addCircleEquivQZ (invMap (v.adicCompletion K) (Y.1 v)) := fun v => by
        rw [invFin_apply, AddEquiv.apply_symm_apply]
      have h2 : ∀ w, invInf K w ((brauerGroupEquivBr w.Completion).symm (Y.2 w)) =
          addCircleEquivQZ (infiniteInvMap w (Y.2 w)) := fun w => by
        rw [invInf_apply, AddEquiv.apply_symm_apply]
      have e1 : ∑ᶠ v, invFin K v ((brauerGroupEquivBr (v.adicCompletion K)).symm (Y.1 v)) =
          addCircleEquivQZ (∑ v ∈ Y.1.support, invMap (v.adicCompletion K) (Y.1 v)) :=
        (finsum_congr h1).trans (finsum_addCircleEquivQZ _ Y.1.support (fun v hv => by rw [hS v hv, map_zero]))
      have e2 : ∑ w, invInf K w ((brauerGroupEquivBr w.Completion).symm (Y.2 w)) =
          addCircleEquivQZ (∑ w, infiniteInvMap w (Y.2 w)) :=
        (Finset.sum_congr rfl (fun w _ => h2 w)).trans (map_sum _ _ _).symm
      refine (congrArg₂ (· + ·) e1 e2).trans ?_
      rw [← map_add, ← sumLocalInv_eq_sum K Y hS, hY, AddEquiv.apply_symm_apply]

omit [NumberField K] in
/-- Our base change `Ch4.baseChange` is Tau Ceti's `BrauerGroup.baseChange`: both are $[A]\mapsto[L\otimes_KA]$. -/
theorem baseChange_eq_tauCeti (L : Type) [Field L] [Algebra K L] (x : BrauerGroup.{0, 0} K) :
    baseChange L x = TauCeti.BrauerGroup.baseChange K L x := by
  induction x using Quotient.inductionOn with
  | h A => exact TauCeti.BrauerGroup.mk_eq_mk_of_algEquiv AlgEquiv.refl

/-- **The crossed-product identification commutes with base change to the completions** (formerly a named input):
the case $L=K_v$ of `BrauerBaseChange.brauerGroupEquivBr_baseChange`. -/
@[kb "milne2020cft" "v4.03, Ch. IV, §3 (crossed products and base change)"]
theorem brauerBaseChangeTauCeti (K : Type) [Field K] [NumberField K] : BrauerBaseChangeTauCeti K where
  finite v x := by
    rw [baseChange_eq_tauCeti]
    exact BrauerBaseChange.brauerGroupEquivBr_baseChange K (v.adicCompletion K) x
  infinite w x := by
    rw [baseChange_eq_tauCeti]
    exact BrauerBaseChange.brauerGroupEquivBr_baseChange K w.Completion x

/-- **Example 2.14(e) (Theorem VIII.4.2)** (Milne, *CFT*, IV, Example 2.14(e), p. 130), unconditional: the sequence
$0\to\mathrm{Br}(K)\to\bigoplus_v\mathrm{Br}(K_v)\to\mathbb Q/\mathbb Z\to0$ is exact. -/
@[kb "milne2020cft" "v4.03, Ch. IV, Ex. 2.14(e), p. 130"]
theorem example2_14e (K : Type) [Field K] [NumberField K] : Example2_14e K :=
  example2_14e_of_brauerBaseChange (brauerBaseChangeTauCeti K)

end NumberFieldKB.MilneCFT.Ch4
