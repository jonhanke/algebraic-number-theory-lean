import NumberFieldKB.ModularCurves.ComplexX0
import NumberFieldKB.ModularCurves.FibreCount
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Henselian
import Mathlib.Basic.Complex.Basic
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Extending embeddings of $\mathbb Q(X_0(N))$ to $\mathbb C(X_0(N))$

J. S. Milne, *Elliptic Curves* (`milne2006ec`), Ch. V, §2 (pdf p. 196). The ramification of
$j : X_0(N) \to X_0(1)$ over $\mathbb Q$ was computed from embeddings $\sigma_c$ of $\mathbb Q(X_0(N))$ into
valued fields $L$ (germs at a point of $\mathbb H$, Laurent series at the cusp) which are $\mathbb C$-algebras. Here:

* `extC hφ σ : X0C N →ₐ[RatFunc ℂ] L`, the extension of $\sigma : \mathbb Q(X_0(N)) \to L$ to
  $\mathbb C(X_0(N))$, for a compatible $\mathbb C(j)$-algebra structure on $L$ (`extC_toX0C`);
* `scale_extC_dvd`: the scaling factor of the extension divides that of $\sigma$ (both valuations are read off the
  same $v_L$).
-/

open Polynomial TauCeti
open scoped WithZero

noncomputable section

namespace NumberFieldKB.ModularCurves

/-- See `RiemannHurwitz.lean`: the $\mathbb Q$-algebra structure of $\mathbb Q(t)$ through $\mathbb Q[t]$. -/
local instance (priority := high) ratFuncAlgebraRatC : Algebra ℚ (RatFunc ℚ) :=
  RatFunc.instAlgebraOfPolynomial ℚ ℚ

variable (N : ℕ) [NeZero N]

section Ext

variable {N} {L : Type*} [Field L] [Algebra (RatFunc ℚ) L] [Algebra (RatFunc ℂ) L]
  (hφ : (algebraMap (RatFunc ℂ) L).comp ratFuncQC = algebraMap (RatFunc ℚ) L)

include hφ in
theorem eval₂_extC_root (σ : X0 N →ₐ[RatFunc ℚ] L) :
    ((modPolyQC N).map (algebraMap ℂ[X] (RatFunc ℂ))).eval₂ (algebraMap (RatFunc ℂ) L)
      (σ (AdjoinRoot.root _)) = 0 := by
  have h0 : ((modPoly N).map (algebraMap ℚ[X] (RatFunc ℚ))).eval₂ (algebraMap (RatFunc ℚ) L)
      (σ (AdjoinRoot.root _)) = 0 := by
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  rw [Polynomial.eval₂_map] at h0
  rw [modPolyQC, Polynomial.eval₂_map, Polynomial.eval₂_map]
  convert h0 using 2
  refine RingHom.ext fun p => ?_
  rw [← hφ]
  simp only [RingHom.comp_apply, ratFuncQC_algebraMap, polyQC]

/-- **The extension of $\sigma$ to $\mathbb C(X_0(N))$**: $\mathbb C(j) \to L$ by the given structure, $j_N \mapsto
\sigma(j_N)$. -/
def extC (σ : X0 N →ₐ[RatFunc ℚ] L) : X0C N →ₐ[RatFunc ℂ] L :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId (RatFunc ℂ) L) (σ (AdjoinRoot.root _)) (eval₂_extC_root hφ σ)

theorem extC_root (σ : X0 N →ₐ[RatFunc ℚ] L) :
    extC hφ σ (AdjoinRoot.root _) = σ (AdjoinRoot.root _) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem extC_toX0C (σ : X0 N →ₐ[RatFunc ℚ] L) (z : X0 N) : extC hφ σ (toX0C N z) = σ z := by
  have h : (extC hφ σ).toRingHom.comp (toX0C N) = σ.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← AdjoinRoot.algebraMap_eq, toX0C_algebraMap, AlgHom.commutes, AlgHom.commutes,
        ← RingHom.comp_apply, hφ]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toX0C_root]
      exact extC_root hφ σ
  exact RingHom.congr_fun h z

theorem extC_injective {ι : Type*} {σ : ι → (X0 N →ₐ[RatFunc ℚ] L)} (hσ : Function.Injective σ) :
    Function.Injective fun i => extC hφ (σ i) := by
  intro i i' h
  apply hσ
  refine AlgHom.ext fun z => ?_
  have := congrArg (fun φ : X0C N →ₐ[RatFunc ℂ] L => φ (toX0C N z)) h
  simpa only [extC_toX0C] using this

/-! ### The scaling factors -/

variable {vL : Valuation L ℤᵐ⁰} {P : Place ℚ (RatFunc ℚ)} {PC : Place ℂ (RatFunc ℂ)} {M : ℕ}
  (hvF : ∀ x : RatFunc ℚ, vL (algebraMap (RatFunc ℚ) L x) = P.valuation x ^ M)
  (hvC : ∀ x : RatFunc ℂ, vL (algebraMap (RatFunc ℂ) L x) = PC.valuation x ^ M)

/-- **The scaling factor of the extension divides that of $\sigma$.** -/
theorem scale_extC_dvd (σ : X0 N →ₐ[RatFunc ℚ] L) (hM : 0 < M) :
    scale (isFunctionField_X0C N) hvC (extC hφ σ) hM ∣ scale (isFunctionField_X0 N) hvF σ hM := by
  have : FiniteDimensional (RatFunc ℚ) (X0 N) := functionField_X0
  obtain ⟨t, ht⟩ := (placeOf (isFunctionField_X0 N) hvF σ hM).exists_isUniformizer
  have ht1 := (placeOf (isFunctionField_X0 N) hvF σ hM).isUniformizer_iff_ord_eq_one.1 ht
  have ht0 : t ≠ 0 := by rintro rfl; simp at ht1
  have htC : toX0C N t ≠ 0 := (map_ne_zero_iff _ (toX0C N).injective).2 ht0
  have h1 := valuation_apply_eq_exp (isFunctionField_X0 N) hvF σ hM ht0
  have h2 := valuation_apply_eq_exp (isFunctionField_X0C N) hvC (extC hφ σ) hM htC
  rw [extC_toX0C, h1, ht1, mul_one, WithZero.exp_inj, neg_inj] at h2
  exact ⟨_, h2⟩

end Ext

end NumberFieldKB.ModularCurves
