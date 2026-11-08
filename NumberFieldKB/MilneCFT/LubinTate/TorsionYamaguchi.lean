import NumberFieldKB.MilneCFT.LubinTate.YamaguchiBridge

/-!
# Proposition 3.4 (the torsion points form a cyclic module) (Milne, *CFT*, I, §3)

Through the bridge of `LubinTate/YamaguchiBridge.lean`: a `K`-embedding `ι` of Yamaguchi's level field
`K(λ_n)` into `Ω` turns his analytic evaluation at a point `x` of the level valuation ring into a ring homomorphism
`𝒪_K[[T]] → Ω` extending polynomial evaluation at `ι x`; hence (`ltEval_eq_of_ringHom`) our
`ltAct a (ι x) = ι([a](x))` whenever `f^{(n+1)}(x) = 0` (`ltAct_toΩ`). With `x₀ = ι λ_n` (the primitive point):
* `[a] x₀ = [b] x₀ ↔ a ≡ b (mod π^{n+1})`, from Yamaguchi's annihilator `m^{n+1}` of `λ_n` and the formal group
  addition (`ltAct_x0_eq_iff`);
* every root of `f^{(n+1)}` is some `[a] x₀`: the map `A/(π^{n+1}) → Λ_{n+1}` is injective and both sides have at
  most `q^{n+1}` elements (`exists_ltAct_x0`).

The universe: Yamaguchi's package `standardLocalField K` is for `K : Type`.
-/

open scoped ValuativeRel
open Polynomial

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NumberFieldKB.MilneCFT.LocalCFT

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local notation "𝔽" => LubinTate.standardLocalField K
local notation "𝔢" => LubinTate.standardLocalFieldIntegerEquiv K

/-! The topologies of Yamaguchi's evaluation (`FiniteLevel/CompletedEvaluation.lean`, local instances there):
discrete on the coefficients, maximal-ideal adic on the level valuation ring. -/


local instance (priority := 50) coeffUniformSpace (F : LocalFieldTheory.DiscreteValuationField.LocalField K) : UniformSpace F.valuationSubring := ⊥

local instance levWithIdeal {F : LocalFieldTheory.DiscreteValuationField.LocalField K} {ϖ : F.valuationSubring}
    (hY : F.toCompleteDVF.valuation.IsUniformizer (ϖ : K)) (n : ℕ) :
    WithIdeal (LubinTate.standardLubinTateLevelCompleteDVF hY n).valuationSubring where
  i := (LubinTate.standardLubinTateLevelCompleteDVF hY n).maximalIdeal

local instance levCompleteSpace {F : LocalFieldTheory.DiscreteValuationField.LocalField K} {ϖ : F.valuationSubring}
    (hY : F.toCompleteDVF.valuation.IsUniformizer (ϖ : K)) (n : ℕ) :
    CompleteSpace (LubinTate.standardLubinTateLevelCompleteDVF hY n).valuationSubring := by
  let target := LubinTate.standardLubinTateLevelCompleteDVF hY n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).1

local instance levT2Space {F : LocalFieldTheory.DiscreteValuationField.LocalField K} {ϖ : F.valuationSubring}
    (hY : F.toCompleteDVF.valuation.IsUniformizer (ϖ : K)) (n : ℕ) :
    T2Space (LubinTate.standardLubinTateLevelCompleteDVF hY n).valuationSubring := by
  let target := LubinTate.standardLubinTateLevelCompleteDVF hY n
  have hadic : IsAdic target.maximalIdeal := rfl
  exact (hadic.isAdicComplete_iff.mp target.isAdicComplete).2


section Level

variable {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)

local notation "𝔥" => isUniformizer_of_irreducible hπ

include hπ

/-- Yamaguchi's level field `K(λ_n)` (a root of `(f^{(n)})^{q-1} + π`, level `n + 1` in Milne's numbering). -/
abbrev LevF : IntermediateField K (SeparableClosure K) := LubinTate.standardLubinTateLevelField 𝔥 n

/-- Its valuation ring. -/
abbrev LevR : Type :=
  (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring

/-- A `K`-embedding of the level field into `Ω`. -/
def levEmb : LevF hπ n →ₐ[K] Ω :=
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  IsSepClosed.lift

/-- The level valuation ring, embedded in `Ω`. -/
def toΩ : LevR hπ n →+* Ω := ((levEmb Ω hπ n : LevF hπ n →ₐ[K] Ω) : LevF hπ n →+* Ω).comp
  (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuation.valuationSubring.subtype

theorem toΩ_injective : Function.Injective (toΩ Ω hπ n) :=
  (levEmb Ω hπ n).injective.comp Subtype.val_injective

theorem toΩ_coeff (a : 𝒪[K]) :
    toΩ Ω hπ n (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n (𝔢 a)) = algebraMap K Ω (a : K) := by
  simp only [toΩ, RingHom.comp_apply]
  change levEmb Ω hπ n (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n (𝔢 a)).1 = _
  rw [LubinTate.standardLubinTateLevelCoefficientHom_apply]
  exact (levEmb Ω hπ n).commutes _

theorem toΩ_eval₂ (p : 𝒪[K][X]) (x : (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring) :
    toΩ Ω hπ n (eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n) x
        (p.map (𝔢 : 𝒪[K] →+* (𝔽).valuationSubring))) =
      aeval (toΩ Ω hπ n x) (p.map (algebraMap 𝒪[K] K)) := by
  rw [Polynomial.hom_eval₂, eval₂_map, aeval_def, eval₂_map]
  congr 1
  ext a
  simp only [RingHom.comp_apply]
  exact toΩ_coeff Ω hπ n a

/-- The analytic evaluation at `x`, with coefficients in `𝒪[K]` and values in `Ω`. -/
def evalΩ (x : (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring) (hx : PowerSeries.HasEval x) : PowerSeries 𝒪[K] →+* Ω :=
  (toΩ Ω hπ n).comp ((LubinTate.standardLubinTateLevelPowerSeriesEval 𝔥 n x hx).comp
    (PowerSeries.map (𝔢 : 𝒪[K] →+* (𝔽).valuationSubring)))

theorem evalΩ_coe (x : (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring) (hx : PowerSeries.HasEval x) (p : 𝒪[K][X]) :
    evalΩ Ω hπ n x hx (p : PowerSeries 𝒪[K]) = aeval (toΩ Ω hπ n x) (p.map (algebraMap 𝒪[K] K)) := by
  simp only [evalΩ, RingHom.comp_apply]
  rw [← Polynomial.polynomial_map_coe, LubinTate.standardLubinTateLevelPowerSeriesEval_coe, toΩ_eval₂]

/-- The value of `f^{(m)}` at a point of the level ring, in our terms. -/
theorem aeval_ltPolyIter_toΩ (x : (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring) (m : ℕ) :
    aeval (toΩ Ω hπ n x) ((ltPolyIter π m).map (algebraMap 𝒪[K] K)) =
      toΩ Ω hπ n (eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n) x
        (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) m)) := by
  rw [polynomialIterate_eq_map, toΩ_eval₂]

theorem toΩ_mem_ltTorsion (x : (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring)
    (hx0 : eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n) x
      (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) (n + 1)) = 0) :
    toΩ Ω hπ n x ∈ ltTorsion Ω π (n + 1) := by
  rw [ltTorsion, mem_rootSet]
  refine ⟨((ltPolyIter_aux hπ (n + 1)).1.map _).ne_zero, ?_⟩
  rw [aeval_ltPolyIter_toΩ, hx0, map_zero]

/-- **Our action is Yamaguchi's**: `ltAct a (ι x) = ι([a](x))` at a root `x` of `f^{(n+1)}`. -/
theorem ltAct_toΩ (x : (LubinTate.standardLubinTateLevelCompleteDVF 𝔥 n).valuationSubring) (hx : PowerSeries.HasEval x)
    (hx0 : eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n) x
      (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) (n + 1)) = 0) (a : 𝒪[K]) :
    ltAct hπ (n + 1) a (toΩ Ω hπ n x) =
      toΩ Ω hπ n (LubinTate.standardLubinTateEndomorphismEvalAt 𝔥 n x hx (𝔢 a)) := by
  rw [ltAct, ltEval_eq_of_ringHom hπ (n + 1) (evalΩ Ω hπ n x hx) _ (evalΩ_coe Ω hπ n x hx)
    (by rw [aeval_ltPolyIter_toΩ, hx0, map_zero])]
  simp only [evalΩ, RingHom.comp_apply]
  rw [map_lubinTateEnd hπ]
  rfl

/-! ## The primitive point -/

/-- `x₀ = ι λ_n`, a root of `(f^{(n)})^{q-1} + π`. -/
def x0 : Ω := toΩ Ω hπ n (LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n)

theorem x0_iterate :
    eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n)
      (LubinTate.standardLubinTatePrimitivePointInteger 𝔥 n)
      (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) (n + 1)) = 0 :=
  LubinTate.standardLubinTatePrimitivePointInteger_iterate_succ_eq_zero 𝔥 n

theorem x0_mem : x0 Ω hπ n ∈ ltTorsion Ω π (n + 1) := toΩ_mem_ltTorsion Ω hπ n _ (x0_iterate hπ n)

theorem ltAct_x0 (a : 𝒪[K]) :
    ltAct hπ (n + 1) a (x0 Ω hπ n) = toΩ Ω hπ n (LubinTate.standardLubinTateEndomorphismValue 𝔥 n (𝔢 a)) :=
  ltAct_toΩ Ω hπ n _ (LubinTate.standardLubinTatePrimitivePointInteger_hasEval 𝔥 n) (x0_iterate hπ n) a

theorem mem_pow_iff (c : 𝒪[K]) (k : ℕ) :
    𝔢 c ∈ (𝔽).toCompleteDVF.maximalIdeal ^ k ↔ c ∈ Ideal.span {π ^ k} := by
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
  exact LubinTate.standardLocalFieldIntegerEquiv_mem_maximalIdeal_pow_iff K k c

theorem value_eq_zero_iff (c : 𝒪[K]) :
    LubinTate.standardLubinTateEndomorphismValue 𝔥 n (𝔢 c) = 0 ↔ c ∈ Ideal.span {π ^ (n + 1)} := by
  rw [LubinTate.standardLubinTateEndomorphismValue_eq_zero_iff_mem_maximalIdeal_pow, mem_pow_iff hπ]

/-- **`[a] x₀ = [b] x₀` iff `a ≡ b (mod π^{n+1})`.** -/
theorem ltAct_x0_eq_iff (a b : 𝒪[K]) :
    ltAct hπ (n + 1) a (x0 Ω hπ n) = ltAct hπ (n + 1) b (x0 Ω hπ n) ↔ a - b ∈ Ideal.span {π ^ (n + 1)} := by
  rw [ltAct_x0, ltAct_x0, (toΩ_injective Ω hπ n).eq_iff]
  have hadd := LubinTate.standardLubinTateEndomorphismValue_add 𝔥 n
  have h0 := LubinTate.standardLubinTateEndomorphismValue_zero 𝔥 n
  constructor
  · intro h
    rw [← value_eq_zero_iff hπ n]
    have e1 : 𝔢 (a - b) = 𝔢 a + 𝔢 (-b) := by rw [sub_eq_add_neg, map_add]
    have e2 : (0 : (𝔽).valuationSubring) = 𝔢 b + 𝔢 (-b) := by rw [← map_add, add_neg_cancel, map_zero]
    rw [e1, hadd, h, ← hadd, ← e2, h0]
  · intro h
    have hz := (value_eq_zero_iff hπ n (a - b)).2 h
    have e1 : 𝔢 a = 𝔢 b + 𝔢 (a - b) := by rw [← map_add, add_sub_cancel]
    rw [e1, hadd, hz, ← h0, ← hadd, add_zero]

theorem value_iterate (k : ℕ) (a : 𝒪[K]) :
    eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n)
      (LubinTate.standardLubinTateEndomorphismValue 𝔥 n (𝔢 a))
      (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) k) =
      LubinTate.standardLubinTateEndomorphismValue 𝔥 n (𝔢 (π ^ k * a)) := by
  rw [← LubinTate.standardLubinTateEndomorphismEvalAt_uniformizer_pow 𝔥 n _
      (LubinTate.standardLubinTateEndomorphismValue_hasEval 𝔥 n (𝔢 a)),
    ← LubinTate.standardLubinTateEndomorphismValue_mul, ← map_pow, ← map_mul]

theorem value_iterate_succ (a : 𝒪[K]) :
    eval₂ (LubinTate.standardLubinTateLevelCoefficientHom 𝔥 n)
      (LubinTate.standardLubinTateEndomorphismValue 𝔥 n (𝔢 a))
      (LubinTate.standardLubinTatePolynomialIterate 𝔽 (𝔢 π) (n + 1)) = 0 := by
  rw [value_iterate hπ, value_eq_zero_iff hπ n]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem ltAct_x0_mem (a : 𝒪[K]) : ltAct hπ (n + 1) a (x0 Ω hπ n) ∈ ltTorsion Ω π (n + 1) := by
  rw [ltAct_x0]
  exact toΩ_mem_ltTorsion Ω hπ n _ (value_iterate_succ hπ n a)

/-- `f^{(k)}([a] x₀) = [π^k a] x₀`. -/
theorem aeval_iter_ltAct_x0 (k : ℕ) (a : 𝒪[K]) :
    aeval (ltAct hπ (n + 1) a (x0 Ω hπ n)) ((ltPolyIter π k).map (algebraMap 𝒪[K] K)) =
      ltAct hπ (n + 1) (π ^ k * a) (x0 Ω hπ n) := by
  rw [ltAct_x0, aeval_ltPolyIter_toΩ, value_iterate hπ, ← ltAct_x0 Ω hπ n]

/-- `[b]([a] x₀) = [b a] x₀`. -/
theorem ltAct_ltAct_x0 (a b : 𝒪[K]) :
    ltAct hπ (n + 1) b (ltAct hπ (n + 1) a (x0 Ω hπ n)) = ltAct hπ (n + 1) (b * a) (x0 Ω hπ n) := by
  rw [ltAct_x0 Ω hπ n a, ltAct_toΩ Ω hπ n _ (LubinTate.standardLubinTateEndomorphismValue_hasEval 𝔥 n (𝔢 a))
    (value_iterate_succ hπ n a), ← LubinTate.standardLubinTateEndomorphismValue_mul, ← map_mul, ← ltAct_x0 Ω hπ n]

theorem ltAct_one_x0 : ltAct hπ (n + 1) 1 (x0 Ω hπ n) = x0 Ω hπ n := by
  rw [ltAct_x0, map_one, LubinTate.standardLubinTateEndomorphismValue_one]
  rfl

theorem ltAct_zero_x0 : ltAct hπ (n + 1) 0 (x0 Ω hπ n) = 0 := by
  rw [ltAct_x0, map_zero, LubinTate.standardLubinTateEndomorphismValue_zero, map_zero]

theorem card_quot_span_pow (k : ℕ) : Nat.card (𝒪[K] ⧸ Ideal.span {π ^ k}) = resCard K ^ k := by
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq]
  have hm : 𝓂[K] ≠ ⊥ := IsDiscreteValuationRing.not_a_field _
  rw [← Submodule.cardQuot_apply, cardQuot_pow_of_prime hm, Submodule.cardQuot_apply]
  rfl

theorem ltTorsion_finite (m : ℕ) : (ltTorsion Ω π m).Finite := Polynomial.rootSet_finite _ _

theorem ncard_ltTorsion_le (m : ℕ) : (ltTorsion Ω π m).ncard ≤ resCard K ^ m := by
  exact (Polynomial.ncard_rootSet_le _ _).trans (natDegree_map_le.trans (ltPolyIter_natDegree hπ m).le)

/-- **Every point of `Λ_{n+1}` is some `[a] x₀`.** -/
theorem exists_ltAct_x0 (α : Ω) (hα : α ∈ ltTorsion Ω π (n + 1)) :
    ∃ a : 𝒪[K], α = ltAct hπ (n + 1) a (x0 Ω hπ n) := by
  classical
  let I := Ideal.span {π ^ (n + 1)}
  let g : 𝒪[K] ⧸ I → ltTorsion Ω π (n + 1) := fun c =>
    ⟨ltAct hπ (n + 1) (Quotient.out c) (x0 Ω hπ n), ltAct_x0_mem Ω hπ n _⟩
  have hg : Function.Injective g := by
    intro c c' h
    have h' := congrArg Subtype.val h
    simp only [g] at h'
    rw [ltAct_x0_eq_iff] at h'
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 h'
  haveI : Finite (ltTorsion Ω π (n + 1)) := (ltTorsion_finite Ω hπ (n + 1)).to_subtype
  have hc : Nat.card (ltTorsion Ω π (n + 1)) ≤ Nat.card (𝒪[K] ⧸ I) := by
    rw [card_quot_span_pow hπ, Nat.card_coe_set_eq]
    exact ncard_ltTorsion_le Ω hπ (n + 1)
  obtain ⟨c, hc'⟩ := (hg.bijective_of_nat_card_le hc).2 ⟨α, hα⟩
  exact ⟨Quotient.out c, (congrArg Subtype.val hc').symm⟩

end Level

end NumberFieldKB.MilneCFT.LocalCFT
