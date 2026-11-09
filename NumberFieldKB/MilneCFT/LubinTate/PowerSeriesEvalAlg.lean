import Mathlib

/-!
# Evaluating power series at a root of a distinguished polynomial (purely algebraic)

Let `B` be a complete local ring and `E` a `B`-algebra.  If `y ∈ E` is a root of a polynomial
`g` that is distinguished at the maximal ideal of `B`, then Weierstrass division by `g` writes every
power series `φ` as `g * q + r` with `r` a polynomial.  Consequently there is exactly one
`B`-algebra map `B⟦X⟧ → E` sending `X` to `y`; we call it `evalHom`.  No topology on `E` is used.

We prove uniqueness, existence, compatibility with substitution, with ring twists, and with change
of coefficient ring, and that power series with unit constant term evaluate to units.
-/

open Polynomial

noncomputable section

namespace NumberFieldKB.MilneCFT.PowerSeriesEval

variable {B : Type*} [CommRing B] [IsLocalRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
variable {E : Type*} [CommRing E] [Algebra B E]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- `y` is a root of a polynomial distinguished at the maximal ideal of `B`. -/
def IsDistRoot (y : E) : Prop :=
  ∃ g : B[X], g.IsDistinguishedAt (IsLocalRing.maximalIdeal B) ∧ aeval y g = 0

theorem isDistRoot_zero : IsDistRoot (B := B) (0 : E) := by
  refine ⟨Polynomial.X, ⟨⟨fun {n} hn => ?_⟩, Polynomial.monic_X⟩, by simp⟩
  rw [Polynomial.natDegree_X] at hn
  have : n = 0 := by omega
  subst this
  simp

/-- A `B`-algebra map from power series agreeing with `aeval y` on polynomials. -/
theorem algHom_coe_eq {y : E} {h : PowerSeries B →ₐ[B] E} (hX : h PowerSeries.X = y) (p : B[X]) :
    h (p : PowerSeries B) = aeval y p := by
  have : (h.comp (Polynomial.coeToPowerSeries.algHom B)) = aeval y := by
    apply Polynomial.algHom_ext
    simp [hX]
  exact congrArg (fun f => f p) this

theorem algHom_ext_of_isDistRoot {y : E} (hy : IsDistRoot (B := B) y)
    {h₁ h₂ : PowerSeries B →ₐ[B] E}
    (h₁X : h₁ PowerSeries.X = y) (h₂X : h₂ PowerSeries.X = y) : h₁ = h₂ := by
  obtain ⟨g, hg, hgy⟩ := hy
  have hdiv := (hg.isWeierstrassDivisorAt' (A := B)).isWeierstrassDivisionAt_div_mod
  apply AlgHom.ext
  intro φ
  have h := (hdiv φ).eq_mul_add
  rw [h, map_add, map_add, map_mul, map_mul, algHom_coe_eq h₁X g, algHom_coe_eq h₂X g,
    algHom_coe_eq h₁X, algHom_coe_eq h₂X, hgy]
  simp

theorem exists_evalHom {y : E} (hy : IsDistRoot (B := B) y) :
    ∃ h : PowerSeries B →ₐ[B] E, h PowerSeries.X = y := by
  obtain ⟨g, hg, hgy⟩ := hy
  let I := Ideal.span {g}
  let lift : (B[X] ⧸ Ideal.span {g}) →ₐ[B] E :=
    Ideal.Quotient.liftₐ (Ideal.span {g}) (aeval y) (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      simp [hgy])
  let e := hg.algEquivQuotient
  refine ⟨(lift.comp e.symm.toAlgHom).comp (Ideal.Quotient.mkₐ B (Ideal.span {(g : PowerSeries B)})),
    ?_⟩
  have : (Ideal.Quotient.mkₐ B (Ideal.span {(g : PowerSeries B)})) PowerSeries.X
      = e (Ideal.Quotient.mkₐ B (Ideal.span {g}) Polynomial.X) := by
    simp [e, Polynomial.IsDistinguishedAt.algEquivQuotient]
  simp only [AlgHom.comp_apply, this, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  show aeval y (Polynomial.X : B[X]) = y
  simp

/-- Evaluation at a root of a distinguished polynomial. -/
def evalHom {y : E} (hy : IsDistRoot (B := B) y) : PowerSeries B →ₐ[B] E :=
  (exists_evalHom hy).choose

theorem evalHom_X {y : E} (hy : IsDistRoot (B := B) y) : evalHom hy PowerSeries.X = y :=
  (exists_evalHom hy).choose_spec

theorem evalHom_coe {y : E} (hy : IsDistRoot (B := B) y) (p : B[X]) :
    evalHom hy (p : PowerSeries B) = aeval y p :=
  algHom_coe_eq (evalHom_X hy) p

theorem evalHom_zero_apply (hy : IsDistRoot (B := B) (0 : E)) (φ : PowerSeries B) :
    evalHom hy φ = algebraMap B E (PowerSeries.constantCoeff φ) := by
  let c : PowerSeries B →ₐ[B] E :=
    { ((algebraMap B E).comp (PowerSeries.constantCoeff (R := B))) with
      commutes' := fun b => by simp }
  have : evalHom hy = c := algHom_ext_of_isDistRoot hy (evalHom_X hy) (by show algebraMap B E (PowerSeries.constantCoeff PowerSeries.X) = 0; simp)
  rw [this]
  rfl

theorem evalHom_subst {y : E} (hy : IsDistRoot (B := B) y) {ψ : PowerSeries B}
    (hψ : PowerSeries.constantCoeff ψ = 0) (hψy : IsDistRoot (B := B) (evalHom hy ψ))
    (φ : PowerSeries B) :
    evalHom hy (φ.subst ψ) = evalHom hψy φ := by
  have hs : PowerSeries.HasSubst ψ := PowerSeries.HasSubst.of_constantCoeff_zero' hψ
  have : (evalHom hy).comp (PowerSeries.substAlgHom hs) = evalHom hψy := by
    apply algHom_ext_of_isDistRoot hψy
    · simp [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
    · exact evalHom_X hψy
  have := congrArg (fun f => f φ) this
  simpa [PowerSeries.coe_substAlgHom] using this

theorem evalHom_twist {y : E} (hy : IsDistRoot (B := B) y) (σ : B ≃+* B) (τ : E →+* E)
    (hτ : ∀ b : B, τ (algebraMap B E b) = algebraMap B E (σ b)) (hτy : IsDistRoot (B := B) (τ y))
    (φ : PowerSeries B) :
    τ (evalHom hy φ) = evalHom hτy (PowerSeries.map (σ : B →+* B) φ) := by
  let c : PowerSeries B →ₐ[B] E :=
    { (τ.comp (evalHom hy : PowerSeries B →+* E)).comp
        (PowerSeries.map (σ.symm : B →+* B)) with
      commutes' := fun b => by
        have h1 : PowerSeries.map (σ.symm : B →+* B) (algebraMap B (PowerSeries B) b)
            = algebraMap B (PowerSeries B) (σ.symm b) := by
          simp [PowerSeries.algebraMap_apply']
        simp only [RingHom.toMonoidHom_eq_coe, RingHom.coe_comp, Function.comp_apply]
        show τ (evalHom hy (PowerSeries.map (σ.symm : B →+* B) (algebraMap B (PowerSeries B) b)))
          = algebraMap B E b
        rw [h1, AlgHom.commutes, hτ]
        simp }
  have hc : evalHom hτy = c := by
    apply algHom_ext_of_isDistRoot hτy (evalHom_X hτy)
    show τ (evalHom hy (PowerSeries.map (σ.symm : B →+* B) PowerSeries.X)) = τ y
    simp [evalHom_X]
  rw [hc]
  show _ = τ (evalHom hy (PowerSeries.map (σ.symm : B →+* B) (PowerSeries.map (σ : B →+* B) φ)))
  have : PowerSeries.map (σ.symm : B →+* B) (PowerSeries.map (σ : B →+* B) φ) = φ := by
    ext n; simp
  rw [this]

theorem isUnit_evalHom {y : E} (hy : IsDistRoot (B := B) y) {φ : PowerSeries B}
    (hφ : IsUnit (PowerSeries.constantCoeff φ)) : IsUnit (evalHom hy φ) :=
  ((PowerSeries.isUnit_iff_constantCoeff).2 hφ).map (evalHom hy)

/-- `θ(y) = y · θ₁(y)` when `θ` has constant coefficient `0`: there is `θ₁` with constant coefficient
the linear coefficient of `θ` and `evalHom hy θ = y * evalHom hy θ₁`. -/
theorem evalHom_eq_mul {y : E} (hy : IsDistRoot (B := B) y) {θ : PowerSeries B}
    (hθ : PowerSeries.constantCoeff θ = 0) :
    ∃ θ₁ : PowerSeries B, PowerSeries.constantCoeff θ₁ = PowerSeries.coeff 1 θ ∧
      evalHom hy θ = y * evalHom hy θ₁ := by
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 1) θ, by simp, ?_⟩
  have : θ = PowerSeries.X * PowerSeries.mk fun n => PowerSeries.coeff (n + 1) θ := by
    ext n
    cases n with
    | zero => simpa using hθ
    | succ n => simp [PowerSeries.coeff_succ_X_mul]
  conv_lhs => rw [this]
  rw [map_mul, evalHom_X]

/-- Change of coefficients: for a local ring map `A → B` (A also complete local), evaluating the image
of a power series over `A` at a root `y` of a polynomial distinguished over `A`. -/
theorem isDistRoot_of_map {A : Type*} [CommRing A] [IsLocalRing A] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Algebra A E] [IsScalarTower A B E] {g : A[X]}
    (hg : g.IsDistinguishedAt (IsLocalRing.maximalIdeal A))
    {y : E} (hy : aeval y g = 0) : IsDistRoot (B := B) y := by
  refine ⟨g.map (algebraMap A B), ⟨⟨fun {n} hn => ?_⟩, hg.monic.map _⟩, ?_⟩
  · rw [hg.monic.natDegree_map] at hn
    rw [Polynomial.coeff_map, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := (isUnit_of_map_unit (algebraMap A B) _ hu)
    exact (IsLocalRing.mem_maximalIdeal _).1 (hg.mem hn) this
  · rw [Polynomial.aeval_map_algebraMap]
    exact hy

end NumberFieldKB.MilneCFT.PowerSeriesEval
