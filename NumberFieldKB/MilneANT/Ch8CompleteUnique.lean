import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import QuadFormsKB.Citation
import NumberFieldKB.MilneANT.Ch7Basic

/-!
# Milne, *Algebraic Number Theory*, Chapter 8: extensions of absolute values from complete fields

Source: J. S. Milne, *Algebraic Number Theory*, course notes, version 3.08 (2020), bib key `milne2020ant`.

Uniqueness of the extension of an absolute value from a complete field to a finite extension (Theorem 7.38, used
in the proof of Proposition 8.1), and completeness of the extension, in the archimedean and nonarchimedean cases at once.
-/

namespace NumberFieldKB.MilneANT

open Filter Topology

/-- The power trick: if `a ^ n ≤ C * b ^ n` for all natural numbers `n`, then `a ≤ b`. -/
theorem le_of_pow_le_mul_pow {a b C : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ n : ℕ, a ^ n ≤ C * b ^ n) :
    a ≤ b := by
  by_contra hlt
  push Not at hlt
  rcases hb.eq_or_lt with hb0 | hbpos
  · have := h 1
    rw [← hb0] at this hlt
    simp at this
    linarith
  have h1 : 1 < a / b := (one_lt_div hbpos).2 hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h1
  have := h n
  rw [div_pow] at hn
  have hbn : 0 < b ^ n := pow_pos hbpos n
  rw [lt_div_iff₀ hbn] at hn
  linarith

section

variable {E F : Type*} [NormedField E] [Field F] [Algebra E F]

/-- If the norm of `E` is trivial and `w` extends it, then `w` is trivial. -/
theorem abv_eq_one_of_trivial [FiniteDimensional E F] (htriv : ∀ c : E, c ≠ 0 → ‖c‖ = 1)
    (w : AbsoluteValue F ℝ) (hw : ∀ c : E, w (algebraMap E F c) = ‖c‖) {x : F} (hx : x ≠ 0) : w x = 1 := by
  have hle1 : ∀ c : E, w (algebraMap E F c) ≤ 1 := by
    intro c
    rw [hw]
    by_cases hc : c = 0
    · simp [hc]
    · rw [htriv c hc]
  have hnat : ∀ n : ℕ, w (n : F) ≤ 1 := by
    intro n
    have := hle1 (n : E)
    simpa using this
  have hna := isNonarchimedean_of_natCast_le_one w hnat
  have key : ∀ y : F, w y ≤ 1 := by
    intro y
    have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
    let _ : Algebra E (absValuationSubring w hna) :=
      ((algebraMap E F).codRestrict (absValuationSubring w hna).toSubring (fun c => hle1 c)).toAlgebra
    have : IsScalarTower E (absValuationSubring w hna) F :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hint' : IsIntegral (absValuationSubring w hna) y := hint.tower_top
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
    rw [← hz]
    exact z.2
  apply le_antisymm (key x)
  have h2 := key x⁻¹
  rw [map_inv₀] at h2
  have hpos : 0 < w x := w.pos hx
  rwa [inv_le_one₀ hpos] at h2

/-- `WithAbs w` is a normed space over `E` when `w` extends the norm of `E`. -/
noncomputable abbrev normedSpaceWithAbs (w : AbsoluteValue F ℝ) (hw : ∀ c : E, w (algebraMap E F c) = ‖c‖) :
    NormedSpace E (WithAbs w) where
  norm_smul_le c x := by
    show w (c • x.ofAbs) ≤ ‖c‖ * w x.ofAbs
    rw [Algebra.smul_def, map_mul, hw]

/-- The identity map from `F` to `WithAbs w` as a linear equivalence over `E`. -/
def withAbsLinearEquiv (w : AbsoluteValue F ℝ) : F ≃ₗ[E] WithAbs w where
  toFun := WithAbs.toAbs w
  invFun := WithAbs.ofAbs
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finiteDimensional_withAbs [FiniteDimensional E F] (w : AbsoluteValue F ℝ) :
    FiniteDimensional E (WithAbs w) :=
  Module.Finite.equiv (withAbsLinearEquiv w)

end

section

variable {E F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [Field F] [Algebra E F]
  [FiniteDimensional E F]

/-- One half of uniqueness for a nontrivially normed complete field: `v₂ ≤ v₁`. -/
theorem abv_le_of_nontrivial (v₁ v₂ : AbsoluteValue F ℝ) (g₁ : ∀ c : E, v₁ (algebraMap E F c) = ‖c‖)
    (g₂ : ∀ c : E, v₂ (algebraMap E F c) = ‖c‖) (x : F) : v₂ x ≤ v₁ x := by
  letI : NormedSpace E (WithAbs v₁) := normedSpaceWithAbs v₁ g₁
  letI : NormedSpace E (WithAbs v₂) := normedSpaceWithAbs v₂ g₂
  let e : WithAbs v₁ ≃ₗ[E] WithAbs v₂ :=
    (withAbsLinearEquiv v₁).symm.trans (withAbsLinearEquiv v₂)
  haveI : FiniteDimensional E (WithAbs v₁) := finiteDimensional_withAbs v₁
  let L : WithAbs v₁ →L[E] WithAbs v₂ :=
    LinearMap.toContinuousLinearMap (e : WithAbs v₁ →ₗ[E] WithAbs v₂)
  apply le_of_pow_le_mul_pow (v₂.nonneg x) (v₁.nonneg x) (C := ‖L‖)
  intro n
  have := L.le_opNorm (WithAbs.toAbs v₁ (x ^ n))
  have e1 : ‖L (WithAbs.toAbs v₁ (x ^ n))‖ = v₂ x ^ n := by
    show v₂ (x ^ n) = _
    rw [map_pow]
  have e2 : ‖WithAbs.toAbs v₁ (x ^ n)‖ = v₁ x ^ n := by
    show v₁ (x ^ n) = _
    rw [map_pow]
  rw [e1, e2] at this
  exact this

/-- Completeness for a nontrivially normed complete field. -/
theorem completeSpace_withAbs_of_nontrivial (w : AbsoluteValue F ℝ)
    (hw : ∀ c : E, w (algebraMap E F c) = ‖c‖) : CompleteSpace (WithAbs w) := by
  letI : NormedSpace E (WithAbs w) := normedSpaceWithAbs w hw
  haveI : FiniteDimensional E (WithAbs w) := finiteDimensional_withAbs w
  exact FiniteDimensional.complete E (WithAbs w)

end

/-- **Uniqueness of the extension of an absolute value** from a complete field to a finite extension
(Milne, Theorem 7.38). -/
@[kb "milne2020ant" "v3.08, Thm. 7.38, p. 123"]
theorem absoluteValue_eq_of_complete {E F : Type*} [NormedField E] [CompleteSpace E] [Field F] [Algebra E F]
    [FiniteDimensional E F] (w₁ w₂ : AbsoluteValue F ℝ) (h₁ : ∀ c : E, w₁ (algebraMap E F c) = ‖c‖)
    (h₂ : ∀ c : E, w₂ (algebraMap E F c) = ‖c‖) : w₁ = w₂ := by
  by_cases htriv : ∀ c : E, c ≠ 0 → ‖c‖ = 1
  · ext x
    by_cases hx : x = 0
    · simp [hx]
    · rw [abv_eq_one_of_trivial htriv w₁ h₁ hx, abv_eq_one_of_trivial htriv w₂ h₂ hx]
  · push Not at htriv
    letI : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne htriv
    exact AbsoluteValue.ext fun x => le_antisymm
      (abv_le_of_nontrivial w₂ w₁ h₂ h₁ x)
      (abv_le_of_nontrivial w₁ w₂ h₁ h₂ x)

/-- **Completeness of the extension**: a finite extension of a complete field, with an absolute value extending
the given one, is complete. -/
theorem completeSpace_withAbs_of_complete {E F : Type*} [NormedField E] [CompleteSpace E] [Field F] [Algebra E F]
    [FiniteDimensional E F] (w : AbsoluteValue F ℝ) (hw : ∀ c : E, w (algebraMap E F c) = ‖c‖) :
    CompleteSpace (WithAbs w) := by
  by_cases htriv : ∀ c : E, c ≠ 0 → ‖c‖ = 1
  · apply Metric.complete_of_cauchySeq_tendsto
    intro u hu
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu 1 one_pos
    have hconst : ∀ n ≥ N, u n = u N := by
      intro n hn
      by_contra hne
      have hd := hN n hn N le_rfl
      have hne' : (u n - u N).ofAbs ≠ 0 := by
        intro h0
        apply hne
        have : u n - u N = 0 := (WithAbs.ofAbs_eq_zero w).1 h0
        exact sub_eq_zero.1 this
      have h1 : w (u n - u N).ofAbs = 1 := abv_eq_one_of_trivial htriv w hw hne'
      rw [dist_eq_norm] at hd
      have : ‖u n - u N‖ = 1 := h1
      linarith
    exact ⟨u N, tendsto_atTop_of_eventually_const (i₀ := N) hconst⟩
  · push Not at htriv
    letI : NontriviallyNormedField E := NontriviallyNormedField.ofNormNeOne htriv
    exact completeSpace_withAbs_of_nontrivial w hw

end NumberFieldKB.MilneANT
