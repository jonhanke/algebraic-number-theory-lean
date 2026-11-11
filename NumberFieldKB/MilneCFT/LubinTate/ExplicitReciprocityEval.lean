import NumberFieldKB.MilneCFT.LubinTate.PowerSeriesEvalAlg
import NumberFieldKB.MilneCFT.LubinTate.LevelPolynomial
import NumberFieldKB.MilneCFT.LubinTate.ThetaConstructionProof
import NumberFieldKB.MilneCFT.LubinTate.ExtensionYamaguchi
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Evaluating Lubin–Tate series at torsion points over the completed unramified ring

Auxiliary lemmas for the explicit reciprocity law (Milne, *Class Field Theory*, Chapter I, proof of Theorem 3.9).
Let `B` be a ring with `IsCompletedUnramifiedInt K B σ` (the valuation ring of the completion of the maximal
unramified extension) and `E` a field which is an algebra over `B` and over `K`, compatibly on `𝒪[K]`. A torsion point
`y ∈ E` of level `N` (a root of `f^{(N)}`) is a root of a distinguished polynomial over `B`, so power series over `B`
can be evaluated at `y` (`PowerSeriesEval.evalHom`, purely algebraically). This file proves:

* `lubinTateEnd_pow_toPowerSeries`: `[π^N]_f = f^{(N)}` as power series;
* `evalHom_map_eq_aeval`: the evaluation of (the image of) a series over `𝒪[K]` at a torsion point of level `N` is
  the evaluation of its Weierstrass remainder modulo `f^{(N)}`, which is how `ltAct` is defined in `Ω`;
* `algHom_ltAct`: a `K`-embedding `ι` of an intermediate field `M ⊆ Ω` into `E` carries `[a]_f(z)` to the
  evaluation of `[a]_f` at `ι z`.
-/

open scoped ValuativeRel
open Polynomial NumberFieldKB.MilneCFT.PowerSeriesEval

noncomputable section

set_option linter.unusedSectionVars false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- `[π^N]_f = f^{(N)}` for `f = πT + T^q`. -/
theorem lubinTateEnd_pow_toPowerSeries {π : 𝒪[K]} (hπ : Irreducible π) (N : ℕ) :
    (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ) (π ^ N)).toPowerSeries =
      ((ltPolyIter π N : 𝒪[K][X]) : PowerSeries 𝒪[K]) := by
  induction N with
  | zero =>
    rw [pow_zero, ← lubinTateEndRingHom_apply, map_one, FormalGroupHom.one_toPowerSeries]
    simp [ltPolyIter]
  | succ N ih =>
    rw [pow_succ', ← lubinTateEndRingHom_apply, map_mul, FormalGroupHom.mul_toPowerSeries,
      lubinTateEndRingHom_apply, lubinTateEndRingHom_apply, ih, lubinTateEnd_pi, ltPolyIter_succ]
    have hc : PowerSeries.constantCoeff ((ltPolyIter π N : 𝒪[K][X]) : PowerSeries 𝒪[K]) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
      exact ltPolyIter_eval_zero hπ N
    rw [PowerSeries.subst_coe (PowerSeries.HasSubst.of_constantCoeff_zero' hc), Polynomial.comp_eq_aeval]
    exact Polynomial.aeval_algHom_apply (Polynomial.coeToPowerSeries.algHom 𝒪[K]) (ltPolyIter π N) (ltPoly π)

section Eval

variable {B : Type} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra 𝒪[K] B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

theorem algebraMap_mem_maximalIdeal_of {σ : B ≃+* B} (hB : IsCompletedUnramifiedInt K B σ) {a : 𝒪[K]}
    (ha : a ∈ 𝓂[K]) : algebraMap 𝒪[K] B a ∈ IsLocalRing.maximalIdeal B := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [map_mul]
  exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hB.irreducible π hπ).not_isUnit)

theorem isDistinguishedAt_map {σ : B ≃+* B} (hB : IsCompletedUnramifiedInt K B σ) {p : 𝒪[K][X]}
    (hp : p.IsDistinguishedAt 𝓂[K]) :
    (p.map (algebraMap 𝒪[K] B)).IsDistinguishedAt (IsLocalRing.maximalIdeal B) where
  mem {i} hi := by
    rw [hp.monic.natDegree_map] at hi
    rw [coeff_map]
    exact algebraMap_mem_maximalIdeal_of hB (hp.toIsWeaklyEisensteinAt.mem hi)
  monic := hp.monic.map _

variable {E : Type} [Field E] [Algebra B E] [Algebra K E]

/-- Evaluating a polynomial over `𝒪[K]` in `E`, through `K` or through `B`. -/
theorem aeval_map_K_eq_B (hKE : ∀ a : 𝒪[K], algebraMap K E a = algebraMap B E (algebraMap 𝒪[K] B a))
    (p : 𝒪[K][X]) (y : E) :
    aeval y (p.map (algebraMap 𝒪[K] K)) = aeval y (p.map (algebraMap 𝒪[K] B)) := by
  rw [aeval_def, aeval_def, eval₂_map, eval₂_map]
  congr 1
  exact RingHom.ext hKE

theorem isDistRoot_of_aeval {σ : B ≃+* B} (hB : IsCompletedUnramifiedInt K B σ)
    (hKE : ∀ a : 𝒪[K], algebraMap K E a = algebraMap B E (algebraMap 𝒪[K] B a)) {π : 𝒪[K]}
    (hπ : Irreducible π) {N : ℕ} {y : E} (hy : aeval y ((ltPolyIter π N).map (algebraMap 𝒪[K] K)) = 0) :
    IsDistRoot (B := B) y :=
  ⟨_, isDistinguishedAt_map hB (ltPolyIter_isDistinguishedAt hπ N), by rwa [← aeval_map_K_eq_B hKE]⟩

theorem evalHom_congr {y y' : E} (hy : IsDistRoot (B := B) y) (hy' : IsDistRoot (B := B) y') (h : y = y')
    (φ : PowerSeries B) : evalHom hy φ = evalHom hy' φ := by
  subst h; rfl

/-- The evaluation of a series over `𝒪[K]` at a torsion point of level `N` is the evaluation of its Weierstrass
remainder modulo `f^{(N)}`. -/
theorem evalHom_map_eq_aeval
    (hKE : ∀ a : 𝒪[K], algebraMap K E a = algebraMap B E (algebraMap 𝒪[K] B a)) {π : 𝒪[K]}
    (hπ : Irreducible π) {N : ℕ} {y : E} (hyN : aeval y ((ltPolyIter π N).map (algebraMap 𝒪[K] K)) = 0)
    (hy : IsDistRoot (B := B) y) (P : PowerSeries 𝒪[K]) :
    evalHom hy (PowerSeries.map (algebraMap 𝒪[K] B) P) =
      aeval y ((P %ʷ ((ltPolyIter π N : 𝒪[K][X]) : PowerSeries 𝒪[K])).map (algebraMap 𝒪[K] K)) := by
  have hg := ltPolyIter_map_residue_ne_zero hπ N
  have h := PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod (f := P) hg
  conv_lhs => rw [h]
  rw [map_add, map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe, map_add, map_mul,
    evalHom_coe, evalHom_coe, ← aeval_map_K_eq_B hKE, hyN, zero_mul, zero_add, aeval_map_K_eq_B hKE]

variable {Ω : Type} [Field Ω] [Algebra K Ω]

/-- A `K`-embedding `ι : M → E` carries `[a]_f(z)` (`ltAct`, computed in `Ω`) to the evaluation of `[a]_f` at
`ι z`. -/
theorem algHom_ltAct
    (hKE : ∀ a : 𝒪[K], algebraMap K E a = algebraMap B E (algebraMap 𝒪[K] B a)) {π : 𝒪[K]}
    (hπ : Irreducible π) {N : ℕ} {M : IntermediateField K Ω} (ι : M →ₐ[K] E) (z : M)
    (hz : (z : Ω) ∈ ltTorsion Ω π N) (hy : IsDistRoot (B := B) (ι z)) (a : 𝒪[K])
    (hzM : ltAct hπ N a (z : Ω) ∈ M) :
    ι ⟨ltAct hπ N a (z : Ω), hzM⟩ = evalHom hy (PowerSeries.map (algebraMap 𝒪[K] B)
      (lubinTateEnd (lubinTateHyp_of_isNonarchimedeanLocalField K hπ) (ltPoly_mem hπ) a).toPowerSeries) := by
  have hz0 : aeval (z : Ω) ((ltPolyIter π N).map (algebraMap 𝒪[K] K)) = 0 := ((mem_rootSet.1 hz).2)
  have hzM0 : aeval z ((ltPolyIter π N).map (algebraMap 𝒪[K] K)) = 0 := by
    apply Subtype.ext
    rw [← IntermediateField.coe_val, ← aeval_algHom_apply]
    simpa using hz0
  have hyN : aeval (ι z) ((ltPolyIter π N).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [aeval_algHom_apply, hzM0, map_zero]
  rw [evalHom_map_eq_aeval hKE hπ hyN hy, aeval_algHom_apply]
  congr 1
  apply Subtype.ext
  show aeval (z : Ω) _ = _
  exact aeval_algHom_apply M.val z _

end Eval

end NumberFieldKB.MilneCFT.LocalCFT
